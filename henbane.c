/* Automorphism-reduced whole-permutation search in S_n.
 * Input:  N D R, followed by R lines: lu u... lv v...
 * Output: D*N permutation images on one line.
 */
#define _POSIX_C_SOURCE 200809L

#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 15
#define MAXD 26
#define MAXREL 4096
#define MAXLEN 512
#define MAXWORKERS 128

typedef struct { uint8_t image[MAXN]; } Perm;
typedef struct { uint8_t generator; int8_t direction; } Step;
typedef struct { uint32_t offset; uint16_t length; } Relation;
typedef struct { int generator, relation; } Force;
typedef struct { Perm value, inverse; } CentralizerElement;
typedef struct { Perm *value; size_t count, capacity; } PermVector;

static int degree, dimension, relation_count, worker_count = 1;
static Relation relations[MAXREL];
static Step *steps;
static size_t step_count;
static unsigned order_multiple[MAXD];
static int required_parity[MAXD];
static long long node_budget = -1;
static int candidate_limit = 1;
static atomic_llong nodes, rejected, forced, verified;
static atomic_int solutions, stop_search, capped, max_branch_depth;
static pthread_mutex_t output_lock = PTHREAD_MUTEX_INITIALIZER;
static struct timespec started;

static double elapsed(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)(now.tv_sec - started.tv_sec)
         + 1e-9 * (double)(now.tv_nsec - started.tv_nsec);
}

static Perm identity(void) {
    Perm out = {{0}};
    for (int i = 0; i < degree; i++) out.image[i] = (uint8_t)i;
    return out;
}

/* The repository's word convention is compose(left,right)=right o left. */
static Perm compose(Perm left, Perm right) {
    Perm out = {{0}};
    for (int i = 0; i < degree; i++)
        out.image[i] = right.image[left.image[i]];
    return out;
}

static Perm inverse(Perm value) {
    Perm out = {{0}};
    for (int i = 0; i < degree; i++) out.image[value.image[i]] = (uint8_t)i;
    return out;
}

static int equal(Perm left, Perm right) {
    return !memcmp(left.image, right.image, (size_t)degree);
}

static int compare(Perm left, Perm right) {
    return memcmp(left.image, right.image, (size_t)degree);
}

static int parity(Perm value) {
    uint16_t seen = 0;
    int cycles = 0;
    for (int start = 0; start < degree; start++) {
        if ((seen >> start) & 1u) continue;
        cycles++;
        for (int point = start; !((seen >> point) & 1u);
             point = value.image[point])
            seen |= (uint16_t)(1u << point);
    }
    return (degree - cycles) & 1;
}

static int order_matches(Perm value, unsigned multiple) {
    if (!multiple) return 1;
    uint16_t seen = 0;
    for (int start = 0; start < degree; start++) {
        if ((seen >> start) & 1u) continue;
        int length = 0;
        for (int point = start; !((seen >> point) & 1u);
             point = value.image[point]) {
            seen |= (uint16_t)(1u << point);
            length++;
        }
        if (multiple % (unsigned)length) return 0;
    }
    return 1;
}

static int next_permutation(Perm *value) {
    int i = degree - 2;
    while (i >= 0 && value->image[i] >= value->image[i + 1]) i--;
    if (i < 0) return 0;
    int j = degree - 1;
    while (value->image[j] <= value->image[i]) j--;
    uint8_t swap = value->image[i];
    value->image[i] = value->image[j]; value->image[j] = swap;
    for (int a = i + 1, b = degree - 1; a < b; a++, b--) {
        swap = value->image[a]; value->image[a] = value->image[b];
        value->image[b] = swap;
    }
    return 1;
}

static uint64_t factorial(int n) {
    uint64_t result = 1;
    for (int i = 2; i <= n; i++) result *= (unsigned)i;
    return result;
}

static Perm permutation_at(uint64_t rank) {
    uint8_t available[MAXN];
    Perm out = {{0}};
    for (int i = 0; i < degree; i++) available[i] = (uint8_t)i;
    for (int position = 0; position < degree; position++) {
        uint64_t block = factorial(degree - position - 1);
        int selected = (int)(rank / block);
        rank %= block;
        out.image[position] = available[selected];
        memmove(available + selected, available + selected + 1,
                (size_t)(degree - position - selected - 1));
    }
    return out;
}

static void vector_push(PermVector *vector, Perm value) {
    if (vector->count == vector->capacity) {
        vector->capacity = vector->capacity ? 2 * vector->capacity : 64;
        Perm *grown = realloc(vector->value, vector->capacity * sizeof(*grown));
        if (!grown) abort();
        vector->value = grown;
    }
    vector->value[vector->count++] = value;
}

static Perm canonical_cycle_type(const int *parts, int count) {
    Perm value = identity();
    int base = 0;
    for (int c = 0; c < count; c++) {
        int length = parts[c];
        for (int i = 0; i < length; i++)
            value.image[base + i] = (uint8_t)(base + (i + 1) % length);
        base += length;
    }
    return value;
}

static void partition_visit(int remaining, int maximum, int *parts, int count,
                            int generator, PermVector *out) {
    if (!remaining) {
        Perm value = canonical_cycle_type(parts, count);
        if ((required_parity[generator] < 0
                    || parity(value) == required_parity[generator])
                && order_matches(value, order_multiple[generator]))
            vector_push(out, value);
        return;
    }
    if (maximum > remaining) maximum = remaining;
    for (int part = maximum; part >= 1; part--) {
        parts[count] = part;
        partition_visit(remaining - part, part, parts, count + 1,
                        generator, out);
    }
}

static PermVector conjugacy_representatives(int generator) {
    PermVector out = {0};
    int parts[MAXN];
    partition_visit(degree, degree, parts, 0, generator, &out);
    return out;
}

static int commutes(Perm left, Perm right) {
    for (int i = 0; i < degree; i++)
        if (left.image[right.image[i]] != right.image[left.image[i]]) return 0;
    return 1;
}

static CentralizerElement *centralizer(Perm gauge, size_t *count) {
    size_t capacity = 64;
    CentralizerElement *out = malloc(capacity * sizeof(*out));
    if (!out) abort();
    Perm candidate = identity();
    uint64_t total = factorial(degree);
    *count = 0;
    for (uint64_t rank = 0; rank < total; rank++) {
        if (commutes(gauge, candidate)) {
            if (*count == capacity) {
                capacity *= 2;
                CentralizerElement *grown = realloc(out, capacity * sizeof(*out));
                if (!grown) abort();
                out = grown;
            }
            out[*count].value = candidate;
            out[*count].inverse = inverse(candidate);
            (*count)++;
        }
        if (rank + 1 < total && !next_permutation(&candidate)) abort();
    }
    return out;
}

static int centralizer_canonical(
        Perm partner, const CentralizerElement *elements, size_t count) {
    for (size_t index = 0; index < count; index++) {
        Perm conjugate = {{0}};
        /* c^-1 partner c, applied as maps. */
        for (int point = 0; point < degree; point++)
            conjugate.image[point] = elements[index].inverse.image[
                partner.image[elements[index].value.image[point]]];
        if (compare(conjugate, partner) < 0) return 0;
    }
    return 1;
}

static void force_prefix(int first, int second, Force out[MAXD], int *length) {
    uint32_t assigned = (UINT32_C(1) << first) | (UINT32_C(1) << second);
    *length = 0;
    for (;;) {
        int selected = -1, selected_generator = -1, selected_length = INT32_MAX;
        for (int relation = 0; relation < relation_count; relation++) {
            int unknown_count = 0, unknown_generator = -1;
            Relation value = relations[relation];
            for (int i = 0; i < value.length; i++) {
                int generator = steps[value.offset + (uint32_t)i].generator;
                if (!((assigned >> generator) & 1u)) {
                    unknown_count++;
                    unknown_generator = generator;
                }
            }
            if (unknown_count == 1 && value.length < selected_length) {
                selected = relation;
                selected_generator = unknown_generator;
                selected_length = value.length;
            }
        }
        if (selected < 0) break;
        out[(*length)++] = (Force){selected_generator, selected};
        assigned |= UINT32_C(1) << selected_generator;
    }
}

static Perm step_value(Step step, const Perm value[MAXD],
                       const Perm inverses[MAXD]) {
    return step.direction > 0 ? value[step.generator] : inverses[step.generator];
}

static int apply_force(Force force, Perm value[MAXD], Perm inverses[MAXD]) {
    Relation relation = relations[force.relation];
    int position = -1;
    for (int i = 0; i < relation.length; i++)
        if (steps[relation.offset + (uint32_t)i].generator == force.generator) {
            if (position >= 0) abort();
            position = i;
        }
    if (position < 0) abort();
    Perm prefix = identity(), suffix = identity();
    for (int i = 0; i < position; i++)
        prefix = compose(prefix, step_value(
            steps[relation.offset + (uint32_t)i], value, inverses));
    for (int i = position + 1; i < relation.length; i++)
        suffix = compose(suffix, step_value(
            steps[relation.offset + (uint32_t)i], value, inverses));
    Perm unknown = compose(inverse(prefix), inverse(suffix));
    if (steps[relation.offset + (uint32_t)position].direction < 0)
        unknown = inverse(unknown);
    if ((required_parity[force.generator] >= 0
                && parity(unknown) != required_parity[force.generator])
            || !order_matches(unknown, order_multiple[force.generator]))
        return 0;
    value[force.generator] = unknown;
    inverses[force.generator] = inverse(unknown);
    atomic_fetch_add_explicit(&forced, 1, memory_order_relaxed);
    return 1;
}

static int relation_holds(int index, const Perm value[MAXD],
                          const Perm inverses[MAXD]) {
    Perm product = identity();
    Relation relation = relations[index];
    for (int i = 0; i < relation.length; i++)
        product = compose(product, step_value(
            steps[relation.offset + (uint32_t)i], value, inverses));
    return equal(product, identity());
}

static int should_stop(void) {
    return atomic_load_explicit(&stop_search, memory_order_acquire);
}

static int reserve_node(void) {
    if (should_stop()) return 0;
    long long node = atomic_fetch_add_explicit(
        &nodes, 1, memory_order_relaxed) + 1;
    if (node_budget >= 0 && node > node_budget) {
        atomic_store_explicit(&capped, 1, memory_order_release);
        atomic_store_explicit(&stop_search, 1, memory_order_release);
        return 0;
    }
    return 1;
}

static void record_branch_depth(int depth) {
    int previous = atomic_load_explicit(&max_branch_depth, memory_order_relaxed);
    while (previous < depth
            && !atomic_compare_exchange_weak_explicit(
                &max_branch_depth, &previous, depth,
                memory_order_relaxed, memory_order_relaxed)) {}
}

static void emit_solution(const Perm value[MAXD]) {
    pthread_mutex_lock(&output_lock);
    int count = atomic_load_explicit(&solutions, memory_order_relaxed);
    if (!atomic_load_explicit(&capped, memory_order_relaxed)
            && (candidate_limit == 0 || count < candidate_limit)) {
        for (int generator = 0; generator < dimension; generator++)
            for (int point = 0; point < degree; point++)
                printf("%u%c", value[generator].image[point],
                       generator + 1 == dimension && point + 1 == degree ? '\n' : ' ');
        fflush(stdout);
        count = atomic_fetch_add_explicit(
            &solutions, 1, memory_order_relaxed) + 1;
        if (candidate_limit > 0 && count >= candidate_limit)
            atomic_store_explicit(&stop_search, 1, memory_order_release);
    }
    pthread_mutex_unlock(&output_lock);
}

static int propagate(Perm value[MAXD], Perm inverses[MAXD],
                     uint32_t *assigned) {
    for (;;) {
        int selected = -1, selected_generator = -1;
        int selected_length = INT32_MAX;
        for (int relation = 0; relation < relation_count; relation++) {
            Relation rel = relations[relation];
            int unknown_occurrences = 0, unknown_generator = -1;
            for (int i = 0; i < rel.length; i++) {
                int generator = steps[rel.offset + (uint32_t)i].generator;
                if (!((*assigned >> generator) & 1u)) {
                    unknown_occurrences++;
                    unknown_generator = generator;
                }
            }
            if (!unknown_occurrences) {
                atomic_fetch_add_explicit(&verified, 1, memory_order_relaxed);
                if (!relation_holds(relation, value, inverses)) return 0;
            } else if (unknown_occurrences == 1
                    && rel.length < selected_length) {
                selected = relation;
                selected_generator = unknown_generator;
                selected_length = rel.length;
            }
        }
        if (selected < 0) return 1;
        if (!apply_force((Force){selected_generator, selected}, value, inverses))
            return 0;
        *assigned |= UINT32_C(1) << selected_generator;
    }
}

static void search_state(Perm value[MAXD], Perm inverses[MAXD],
                         uint32_t assigned, int branch_depth) {
    if (should_stop()) return;
    if (!propagate(value, inverses, &assigned)) {
        atomic_fetch_add_explicit(&rejected, 1, memory_order_relaxed);
        return;
    }
    uint32_t complete = (UINT32_C(1) << dimension) - 1;
    if (assigned == complete) {
        emit_solution(value);
        return;
    }

    int generator = 0;
    while ((assigned >> generator) & 1u) generator++;
    int child_depth = branch_depth + 1;
    record_branch_depth(child_depth);
    uint64_t total = factorial(degree);
    Perm candidate = identity();
    for (uint64_t rank = 0; rank < total && !should_stop(); rank++) {
        if ((required_parity[generator] < 0
                    || parity(candidate) == required_parity[generator])
                && order_matches(candidate, order_multiple[generator])) {
            if (!reserve_node()) break;
            value[generator] = candidate;
            inverses[generator] = inverse(candidate);
            search_state(value, inverses,
                         assigned | (UINT32_C(1) << generator), child_depth);
        }
        if (rank + 1 < total && !next_permutation(&candidate)) abort();
    }
}

typedef struct {
    int gauge_generator, partner_generator;
    Perm gauge;
    const CentralizerElement *centralizer;
    size_t centralizer_count;
    int worker;
} Worker;

static void *search_worker(void *opaque) {
    Worker *job = opaque;
    uint64_t total = factorial(degree);
    uint64_t begin = total * (uint64_t)job->worker / (uint64_t)worker_count;
    uint64_t end = total * (uint64_t)(job->worker + 1) / (uint64_t)worker_count;
    if (begin >= end) return NULL;
    Perm partner = permutation_at(begin);
    for (uint64_t rank = begin; rank < end && !should_stop(); rank++) {
        if ((required_parity[job->partner_generator] < 0
                    || parity(partner) == required_parity[job->partner_generator])
                && order_matches(partner, order_multiple[job->partner_generator])
                && centralizer_canonical(partner, job->centralizer,
                                         job->centralizer_count)) {
            if (!reserve_node()) break;
            Perm value[MAXD], inverses[MAXD];
            value[job->gauge_generator] = job->gauge;
            inverses[job->gauge_generator] = inverse(job->gauge);
            value[job->partner_generator] = partner;
            inverses[job->partner_generator] = inverse(partner);
            search_state(value, inverses,
                         (UINT32_C(1) << job->gauge_generator)
                         | (UINT32_C(1) << job->partner_generator), 0);
        }
        if (rank + 1 < end && !next_permutation(&partner)) abort();
    }
    return NULL;
}

static int load_presentation(const char *path) {
    FILE *source = fopen(path, "r");
    if (!source) { perror(path); return 0; }
    if (fscanf(source, "%d %d %d", &degree, &dimension, &relation_count) != 3
            || degree < 1 || degree > MAXN || dimension < 1 || dimension > MAXD
            || relation_count < 0 || relation_count > MAXREL) {
        fprintf(stderr, "invalid flat header\n"); fclose(source); return 0;
    }
    size_t capacity = 65536;
    steps = malloc(capacity * sizeof(*steps));
    if (!steps) abort();
    for (int relation = 0; relation < relation_count; relation++) {
        int left_length, right_length, generator;
        if (fscanf(source, "%d", &left_length) != 1 || left_length < 0
                || left_length > MAXLEN) return 0;
        int *left = malloc((size_t)(left_length ? left_length : 1) * sizeof(*left));
        if (!left) abort();
        for (int i = 0; i < left_length; i++)
            if (fscanf(source, "%d", &left[i]) != 1) return 0;
        if (fscanf(source, "%d", &right_length) != 1 || right_length < 0
                || left_length + right_length < 1
                || left_length + right_length > MAXLEN) return 0;
        int *right = malloc((size_t)(right_length ? right_length : 1) * sizeof(*right));
        if (!right) abort();
        for (int i = 0; i < right_length; i++)
            if (fscanf(source, "%d", &right[i]) != 1) return 0;
        size_t length = (size_t)left_length + (size_t)right_length;
        while (step_count + length > capacity) capacity *= 2;
        Step *grown = realloc(steps, capacity * sizeof(*grown));
        if (!grown) abort();
        steps = grown;
        relations[relation].offset = (uint32_t)step_count;
        relations[relation].length = (uint16_t)length;
        for (int i = 0; i < left_length; i++) {
            generator = left[i];
            if (generator < 0 || generator >= dimension) return 0;
            steps[step_count++] = (Step){(uint8_t)generator, 1};
        }
        for (int i = right_length; i-- > 0;) {
            generator = right[i];
            if (generator < 0 || generator >= dimension) return 0;
            steps[step_count++] = (Step){(uint8_t)generator, -1};
        }
        free(right); free(left);
    }
    char extra;
    if (fscanf(source, " %c", &extra) == 1) return 0;
    fclose(source);
    return 1;
}

static void usage(const char *program) {
    fprintf(stderr,
        "usage: %s FLAT [-n N] [-d D] [-w W] [-b NODES] "
        "[--stop-after K|--all-candidates] "
        "[-p p0..pD-1] [-o k0..kD-1]\n", program);
}

int main(int argc, char **argv) {
    const char *path = NULL;
    int cli_n = -1, cli_d = -1, parity_at = -1, orders_at = -1;
    for (int i = 0; i < MAXD; i++) required_parity[i] = -1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            usage(argv[0]); return 0;
        } else if (!strcmp(argv[i], "-n") && i + 1 < argc) cli_n = atoi(argv[++i]);
        else if (!strcmp(argv[i], "-d") && i + 1 < argc) cli_d = atoi(argv[++i]);
        else if ((!strcmp(argv[i], "-w") || !strcmp(argv[i], "--workers"))
                && i + 1 < argc) worker_count = atoi(argv[++i]);
        else if ((!strcmp(argv[i], "-b") || !strcmp(argv[i], "--budget"))
                && i + 1 < argc) node_budget = atoll(argv[++i]);
        else if (!strcmp(argv[i], "--stop-after") && i + 1 < argc)
            candidate_limit = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--all-candidates")) candidate_limit = 0;
        else if (!strcmp(argv[i], "-p") || !strcmp(argv[i], "--parity"))
            parity_at = i + 1;
        else if (!strcmp(argv[i], "-o") || !strcmp(argv[i], "--orders"))
            orders_at = i + 1;
        else if (argv[i][0] == '-' && argv[i][1]) {
            fprintf(stderr, "unknown or incomplete option %s\n", argv[i]); return 2;
        } else if (!path) path = argv[i];
    }
    if (!path || !load_presentation(path)) { usage(argv[0]); return 2; }
    if ((cli_n >= 0 && cli_n != degree) || (cli_d >= 0 && cli_d != dimension)) {
        fprintf(stderr, "flat dimensions do not match -n/-d\n"); return 2;
    }
    if (worker_count < 1) return 2;
    if (worker_count > MAXWORKERS) worker_count = MAXWORKERS;
    if (candidate_limit < 0) return 2;
    if (parity_at >= 0) {
        if (parity_at + dimension > argc) return 2;
        for (int i = 0; i < dimension; i++) {
            required_parity[i] = atoi(argv[parity_at + i]);
            if (required_parity[i] < 0 || required_parity[i] > 1) return 2;
        }
    }
    if (orders_at >= 0) {
        if (orders_at + dimension > argc) return 2;
        for (int i = 0; i < dimension; i++) {
            errno = 0;
            order_multiple[i] = (unsigned)strtoul(argv[orders_at + i], NULL, 10);
            if (errno) return 2;
        }
    }

    int best_first = 0, best_second = -1, best_count = 0, best_cost = INT32_MAX;
    if (dimension >= 2) {
        best_count = -1;
        for (int first = 0; first < dimension; first++)
            for (int second = first + 1; second < dimension; second++) {
                Force chain[MAXD]; int count = 0;
                force_prefix(first, second, chain, &count);
                int cost = 0;
                for (int i = 0; i < count; i++)
                    cost += relations[chain[i].relation].length;
                if (count > best_count || (count == best_count && cost < best_cost)) {
                    best_first = first; best_second = second;
                    best_count = count; best_cost = cost;
                }
            }
    }

    clock_gettime(CLOCK_MONOTONIC, &started);
    PermVector gauges = conjugacy_representatives(best_first);
    fprintf(stderr, "[permutation] S_%d D=%d R=%d seed=%d",
            degree, dimension, relation_count, best_first);
    if (best_second >= 0) fprintf(stderr, ",%d", best_second);
    fprintf(stderr, " structurally-forced=%d fallback-decisions=%d "
                    "gauge-classes=%zu workers=%d\n",
            best_count, dimension - (best_second >= 0 ? 2 : 1) - best_count,
            gauges.count, worker_count);
    for (size_t index = 0; index < gauges.count && !should_stop(); index++) {
        if (best_second < 0) {
            if (!reserve_node()) break;
            Perm value[MAXD], inverses[MAXD];
            value[best_first] = gauges.value[index];
            inverses[best_first] = inverse(gauges.value[index]);
            search_state(value, inverses, UINT32_C(1) << best_first, 0);
            continue;
        }
        size_t centralizer_count = 0;
        CentralizerElement *elements = centralizer(gauges.value[index],
                                                   &centralizer_count);
        fprintf(stderr, "[permutation] gauge-class=%zu/%zu centralizer=%zu\n",
                index + 1, gauges.count, centralizer_count);
        pthread_t threads[MAXWORKERS];
        Worker jobs[MAXWORKERS];
        for (int worker = 0; worker < worker_count; worker++) {
            jobs[worker] = (Worker){best_first, best_second, gauges.value[index],
                elements, centralizer_count, worker};
            if (pthread_create(&threads[worker], NULL, search_worker,
                               &jobs[worker])) abort();
        }
        for (int worker = 0; worker < worker_count; worker++)
            pthread_join(threads[worker], NULL);
        free(elements);
    }
    const char *status = atomic_load(&capped) ? "INCONCLUSIVE"
        : (candidate_limit > 0 && atomic_load(&solutions) >= candidate_limit)
            ? "CANDIDATE_LIMIT" : "EXHAUSTED";
    fprintf(stderr, "STATUS %s\n", status);
    fprintf(stderr, "STATS nodes=%lld rejected=%lld forced=%lld verified=%lld "
                    "solutions=%d max-branch-depth=%d wall=%.3f\n",
            atomic_load(&nodes), atomic_load(&rejected), atomic_load(&forced),
            atomic_load(&verified), atomic_load(&solutions),
            atomic_load(&max_branch_depth), elapsed());
    free(gauges.value); free(steps);
    if (atomic_load(&capped)) return 3;
    return atomic_load(&solutions) ? 0 : 1;
}
