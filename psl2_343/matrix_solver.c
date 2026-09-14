/* Whole-matrix presentation search in PSL(2,343). */
#define _POSIX_C_SOURCE 200809L

#include "group.h"

#include <errno.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 26
#define MAXREL 200000
#define MAXLEN 4096

typedef struct {
    uint8_t generator;
    int8_t direction;
} Step;

typedef struct {
    uint32_t off;
    uint16_t len;
} Relation;

typedef struct {
    int generator;
    int relation;
} Force;

typedef struct {
    psl2_343 *value;
    size_t count, capacity;
} MatrixVector;

static int d, nrelations;
static Relation *relations;
static Step *steps;
static size_t nsteps;
static unsigned order_multiple[MAXD];
static long long node_limit = 10000000, nodes, rejected, forced, verified;
static double timeout_seconds = -1.0;
static struct timespec started;
static int stop_after = 1, solutions, capped, max_branch_depth;
static int representative_shard, representative_shards = 1;
static int count_elements_only;

static double elapsed(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)(now.tv_sec - started.tv_sec)
         + 1e-9 * (double)(now.tv_nsec - started.tv_nsec);
}

static int candidate_limit_reached(void) {
    return stop_after > 0 && solutions >= stop_after;
}

static int time_limit_reached(void) {
    if (timeout_seconds >= 0.0 && elapsed() >= timeout_seconds) {
        capped = 1;
        return 1;
    }
    return 0;
}

static int resource_limit_reached(void) {
    if (node_limit >= 0 && nodes >= node_limit) {
        capped = 1;
        return 1;
    }
    return time_limit_reached();
}

static int should_stop(void) {
    return candidate_limit_reached() || resource_limit_reached();
}

static int reserve_node(void) {
    if (should_stop()) return 0;
    nodes++;
    return 1;
}

static int matrix_cmp(psl2_343 left, psl2_343 right) {
    for (int i = 0; i < 4; i++)
        if (left.v[i] != right.v[i]) return left.v[i] < right.v[i] ? -1 : 1;
    return 0;
}

static void vector_push(MatrixVector *vector, psl2_343 value) {
    if (vector->count == vector->capacity) {
        vector->capacity = vector->capacity ? 2 * vector->capacity : 65536;
        psl2_343 *grown = realloc(vector->value,
                                 vector->capacity * sizeof(*vector->value));
        if (!grown) abort();
        vector->value = grown;
    }
    vector->value[vector->count++] = value;
}

static gf343 frobenius_orbit_min(gf343 value) {
    gf343 first = gf343_frobenius(value);
    gf343 second = gf343_frobenius(first);
    if (first < value) value = first;
    if (second < value) value = second;
    return value;
}

static int representative_cmp(const void *left, const void *right) {
    return matrix_cmp(*(const psl2_343 *)left, *(const psl2_343 *)right);
}

static int conjugacy_representatives(int generator, psl2_343 out[GF343_Q]) {
    uint8_t seen[4][GF343_Q] = {{0}};
    int count = 0;
    for (gf343 trace = 0; trace < GF343_Q; trace++) {
        psl2_343 element = {{0, gf343_neg(1), 1, trace}};
        if (!psl2_343_canonicalize(&element) || !psl2_343_is_psl(element)) abort();
        if (!psl2_343_order_matches(element, order_multiple[generator]))
            continue;
        int kind = psl2_343_element_kind(element);
        gf343 invariant = frobenius_orbit_min(psl2_343_trace_invariant(element));
        if (seen[kind][invariant]) continue;
        seen[kind][invariant] = 1;
        out[count++] = element;
    }
    qsort(out, (size_t)count, sizeof(*out), representative_cmp);
    return count;
}

static size_t centralizer_elements(
        psl2_343 matrix, psl2_343 out[GF343_Q + 1]) {
    size_t count = 0;
    for (int i = 0; i <= GF343_Q; i++) {
        gf343 scalar = i == GF343_Q ? 0 : 1;
        gf343 weight = i == GF343_Q ? 1 : (gf343)i;
        psl2_343 value = {{
            gf343_add(scalar, gf343_mul(weight, matrix.v[0])),
            gf343_mul(weight, matrix.v[1]),
            gf343_mul(weight, matrix.v[2]),
            gf343_add(scalar, gf343_mul(weight, matrix.v[3]))
        }};
        if (!psl2_343_canonicalize(&value) || !psl2_343_is_pgl(value)) continue;
        out[count++] = value;
    }
    return count;
}

static void commutator_coordinates(
        psl2_343 gauge, psl2_343 matrix, gf343 *u, gf343 *v) {
    *u = gf343_add(
        gf343_mul(gauge.v[1], matrix.v[2]),
        gf343_neg(gf343_mul(gauge.v[2], matrix.v[1])));
    *v = gf343_add(
        gf343_mul(gauge.v[1],
                  gf343_add(matrix.v[3], gf343_neg(matrix.v[0]))),
        gf343_mul(gf343_add(gauge.v[0], gf343_neg(gauge.v[3])),
                  matrix.v[1]));
}

static psl2_343 direction_matrix(psl2_343 gauge, uint16_t point) {
    gf343 u = point == GF343_Q ? 1 : (gf343)point;
    gf343 v = point == GF343_Q ? 0 : 1;
    gf343 numerator = gf343_add(
        gf343_mul(gf343_add(gauge.v[3], gf343_neg(gauge.v[0])), u),
        gf343_neg(gf343_mul(gauge.v[2], v)));
    gf343 lower = gf343_mul(numerator, gf343_inv(gauge.v[1]));
    psl2_343 result = {{u, v, lower, gf343_neg(u)}};
    if (!psl2_343_canonicalize(&result)) abort();
    return result;
}

static uint16_t direction_of(psl2_343 matrix) {
    return !matrix.v[1] ? GF343_Q
                        : gf343_mul(matrix.v[0], gf343_inv(matrix.v[1]));
}

/* Rescale a conjugate whose commutator has the same projective direction as K
 * so that [R,M] is exactly K again, then recover M=M0+xI+yR. */
static size_t parameter_index(
        psl2_343 gauge, psl2_343 matrix, psl2_343 commutator) {
    gf343 u, v;
    commutator_coordinates(gauge, matrix, &u, &v);
    gf343 scale = commutator.v[0]
        ? gf343_mul(u, gf343_inv(commutator.v[0]))
        : gf343_mul(v, gf343_inv(commutator.v[1]));
    if (!scale) abort();
    gf343 inverse = gf343_inv(scale);
    for (int i = 0; i < 4; i++) matrix.v[i] = gf343_mul(matrix.v[i], inverse);
    gf343 y = gf343_mul(matrix.v[1], gf343_inv(gauge.v[1]));
    gf343 x = gf343_add(matrix.v[0], gf343_neg(gf343_mul(y, gauge.v[0])));
    return (size_t)x * GF343_Q + y;
}

static MatrixVector partner_representatives(psl2_343 gauge, int generator) {
    MatrixVector result = {0};
    psl2_343 centralizer[GF343_Q + 1], inverse[GF343_Q + 1];
    size_t ncentral = centralizer_elements(gauge, centralizer);
    for (size_t i = 0; i < ncentral; i++) {
        inverse[i] = psl2_343_inverse(centralizer[i]);
        if (psl2_343_is_psl(centralizer[i])
                && psl2_343_order_matches(
                    centralizer[i], order_multiple[generator]))
            vector_push(&result, centralizer[i]);
    }

    uint8_t direction_seen[GF343_Q + 1] = {0};
    uint8_t *parameter_seen = malloc((size_t)GF343_Q * GF343_Q);
    if (!parameter_seen) abort();
    gf343 inv_b = gf343_inv(gauge.v[1]);
    for (uint16_t seed = 0; seed <= GF343_Q; seed++) {
        if (direction_seen[seed]) continue;
        psl2_343 seed_matrix = direction_matrix(gauge, seed);
        uint16_t orbit[GF343_Q + 1], stabilizer[GF343_Q + 1];
        size_t norbit = 0, nstabilizer = 0;
        uint16_t minimum = GF343_Q;
        for (size_t c = 0; c < ncentral; c++) {
            psl2_343 image_matrix = psl2_343_mul(
                psl2_343_mul(centralizer[c], seed_matrix), inverse[c]);
            uint16_t image = direction_of(image_matrix);
            int known = 0;
            for (size_t i = 0; i < norbit; i++) known |= orbit[i] == image;
            if (!known) orbit[norbit++] = image;
            if (image < minimum) minimum = image;
        }
        for (size_t i = 0; i < norbit; i++) direction_seen[orbit[i]] = 1;
        psl2_343 commutator = direction_matrix(gauge, minimum);
        for (size_t c = 0; c < ncentral; c++) {
            psl2_343 image_matrix = psl2_343_mul(
                psl2_343_mul(centralizer[c], commutator), inverse[c]);
            if (direction_of(image_matrix) == minimum)
                stabilizer[nstabilizer++] = (uint16_t)c;
        }

        memset(parameter_seen, 0, (size_t)GF343_Q * GF343_Q);
        gf343 base_lower = gf343_mul(commutator.v[0], inv_b);
        gf343 base_diagonal = gf343_mul(commutator.v[1], inv_b);
        for (gf343 x = 0; x < GF343_Q; x++)
            for (gf343 y = 0; y < GF343_Q; y++) {
                size_t index = (size_t)x * GF343_Q + y;
                if (parameter_seen[index]) continue;
                psl2_343 matrix = {{
                    gf343_add(x, gf343_mul(y, gauge.v[0])),
                    gf343_mul(y, gauge.v[1]),
                    gf343_add(base_lower, gf343_mul(y, gauge.v[2])),
                    gf343_add(base_diagonal,
                        gf343_add(x, gf343_mul(y, gauge.v[3])))
                }};
                psl2_343 canonical = matrix;
                if (!psl2_343_canonicalize(&canonical)) abort();
                psl2_343 best = canonical;
                for (size_t i = 0; i < nstabilizer; i++) {
                    size_t c = stabilizer[i];
                    psl2_343 image = psl2_343_mul(
                        psl2_343_mul(centralizer[c], canonical), inverse[c]);
                    size_t image_index = parameter_index(
                        gauge, image, commutator);
                    parameter_seen[image_index] = 1;
                    if (matrix_cmp(image, best) < 0) best = image;
                }
                if (psl2_343_is_psl(best)
                        && psl2_343_order_matches(
                            best, order_multiple[generator]))
                    vector_push(&result, best);
            }
    }
    free(parameter_seen);
    return result;
}

static int load_flat(const char *path) {
    FILE *source = fopen(path, "r");
    if (!source) { perror(path); return 0; }
    if (fscanf(source, "%d %d", &d, &nrelations) != 2
            || d < 1 || d > MAXD
            || nrelations < 0 || nrelations > MAXREL) {
        fprintf(stderr, "invalid flat header\n"); fclose(source); return 0;
    }
    relations = calloc((size_t)(nrelations ? nrelations : 1),
                       sizeof(*relations));
    size_t capacity = 4096;
    steps = malloc(capacity * sizeof(*steps));
    if (!relations || !steps) abort();
    for (int relation = 0; relation < nrelations; relation++) {
        int left_length, right_length;
        if (fscanf(source, "%d", &left_length) != 1 || left_length < 0
                || left_length > MAXLEN) return 0;
        int *left = malloc((size_t)(left_length ? left_length : 1) * sizeof(*left));
        if (!left) abort();
        for (int i = 0; i < left_length; i++)
            if (fscanf(source, "%d", &left[i]) != 1 || left[i] < 0 || left[i] >= d)
                return 0;
        if (fscanf(source, "%d", &right_length) != 1 || right_length < 0
                || left_length + right_length < 1
                || left_length + right_length > MAXLEN) return 0;
        int *right = malloc((size_t)(right_length ? right_length : 1) * sizeof(*right));
        if (!right) abort();
        for (int i = 0; i < right_length; i++)
            if (fscanf(source, "%d", &right[i]) != 1 || right[i] < 0 || right[i] >= d)
                return 0;
        size_t length = (size_t)left_length + (size_t)right_length;
        while (nsteps + length > capacity) capacity *= 2;
        Step *grown = realloc(steps, capacity * sizeof(*steps));
        if (!grown) abort();
        steps = grown;
        relations[relation].off = (uint32_t)nsteps;
        relations[relation].len = (uint16_t)length;
        for (int i = 0; i < left_length; i++)
            steps[nsteps++] = (Step){(uint8_t)left[i], 1};
        for (int i = right_length; i-- > 0; )
            steps[nsteps++] = (Step){(uint8_t)right[i], -1};
        free(right); free(left);
    }
    char extra;
    if (fscanf(source, " %c", &extra) == 1) return 0;
    fclose(source);
    return 1;
}

static uint32_t force_prefix(uint32_t assigned, Force out[MAXD], int *nout) {
    *nout = 0;
    for (;;) {
        int found = 0;
        for (int relation = 0; relation < nrelations && !found; relation++) {
            int unknown_count = 0, unknown_generator = -1;
            Relation *value = &relations[relation];
            for (int i = 0; i < value->len; i++) {
                int generator = steps[value->off + (uint32_t)i].generator;
                if (!((assigned >> generator) & 1u)) {
                    unknown_count++;
                    unknown_generator = generator;
                }
            }
            if (unknown_count == 1) {
                out[(*nout)++] = (Force){unknown_generator, relation};
                assigned |= 1u << unknown_generator;
                found = 1;
            }
        }
        if (!found) break;
    }
    return assigned;
}

static psl2_343 step_value(
        Step step, const psl2_343 value[MAXD], const psl2_343 inverse[MAXD]) {
    return step.direction > 0 ? value[step.generator] : inverse[step.generator];
}

static int apply_force(
        Force force, psl2_343 value[MAXD], psl2_343 inverse[MAXD]) {
    Relation *relation = &relations[force.relation];
    int position = -1;
    for (int i = 0; i < relation->len; i++)
        if (steps[relation->off + (uint32_t)i].generator == force.generator) {
            if (position >= 0) abort();
            position = i;
        }
    if (position < 0) abort();
    psl2_343 prefix = psl2_343_identity(), suffix = psl2_343_identity();
    for (int i = 0; i < position; i++)
        prefix = psl2_343_compose(
            prefix, step_value(steps[relation->off + (uint32_t)i], value, inverse));
    for (int i = position + 1; i < relation->len; i++)
        suffix = psl2_343_compose(
            suffix, step_value(steps[relation->off + (uint32_t)i], value, inverse));
    psl2_343 unknown = psl2_343_mul(
        psl2_343_inverse(suffix), psl2_343_inverse(prefix));
    if (steps[relation->off + (uint32_t)position].direction < 0)
        unknown = psl2_343_inverse(unknown);
    if (!psl2_343_is_psl(unknown)
            || !psl2_343_order_matches(
                unknown, order_multiple[force.generator]))
        return 0;
    value[force.generator] = unknown;
    inverse[force.generator] = psl2_343_inverse(unknown);
    forced++;
    return 1;
}

static int relation_holds(
        int index, const psl2_343 value[MAXD], const psl2_343 inverse[MAXD]) {
    psl2_343 product = psl2_343_identity();
    Relation *relation = &relations[index];
    for (int i = 0; i < relation->len; i++)
        product = psl2_343_compose(
            product, step_value(steps[relation->off + (uint32_t)i], value, inverse));
    return psl2_343_equal(product, psl2_343_identity());
}

static void emit_solution(const psl2_343 value[MAXD]) {
    printf("M");
    for (int generator = 0; generator < d; generator++)
        for (int i = 0; i < 4; i++) printf(" %u", value[generator].v[i]);
    putchar('\n');
    fflush(stdout);
}

static int propagate(psl2_343 value[MAXD], psl2_343 inverse[MAXD],
                     uint32_t *assigned) {
    for (;;) {
        int selected = -1, selected_generator = -1;
        int selected_length = INT32_MAX;
        for (int relation = 0; relation < nrelations; relation++) {
            Relation *rel = &relations[relation];
            int unknown_occurrences = 0, unknown_generator = -1;
            for (int i = 0; i < rel->len; i++) {
                int generator = steps[rel->off + (uint32_t)i].generator;
                if (!((*assigned >> generator) & 1u)) {
                    unknown_occurrences++;
                    unknown_generator = generator;
                }
            }
            if (!unknown_occurrences) {
                verified++;
                if (!relation_holds(relation, value, inverse)) return 0;
            } else if (unknown_occurrences == 1
                    && rel->len < selected_length) {
                selected = relation;
                selected_generator = unknown_generator;
                selected_length = rel->len;
            }
        }
        if (selected < 0) return 1;
        if (!apply_force((Force){selected_generator, selected}, value, inverse))
            return 0;
        *assigned |= 1u << selected_generator;
    }
}

static void search_state(psl2_343 value[MAXD], psl2_343 inverse[MAXD],
                         uint32_t assigned, int branch_depth);

static void branch_over_group(psl2_343 value[MAXD], psl2_343 inverse[MAXD],
                              uint32_t assigned, int generator,
                              int branch_depth) {
    psl2_343 candidate;
    candidate.v[0] = 1;
    for (gf343 b = 0; b < GF343_Q && !should_stop(); b++)
        for (gf343 c = 0; c < GF343_Q && !should_stop(); c++)
            for (gf343 diagonal = 0;
                 diagonal < GF343_Q && !should_stop(); diagonal++) {
                candidate.v[1] = b; candidate.v[2] = c; candidate.v[3] = diagonal;
                if (!psl2_343_is_psl(candidate)
                        || !psl2_343_order_matches(
                            candidate, order_multiple[generator])) continue;
                if (!reserve_node()) return;
                value[generator] = candidate;
                inverse[generator] = psl2_343_inverse(candidate);
                search_state(value, inverse, assigned | (1u << generator),
                             branch_depth);
            }

    candidate.v[0] = 0; candidate.v[1] = 1;
    for (gf343 c = 0; c < GF343_Q && !should_stop(); c++)
        for (gf343 diagonal = 0;
             diagonal < GF343_Q && !should_stop(); diagonal++) {
            candidate.v[2] = c; candidate.v[3] = diagonal;
            if (!psl2_343_is_psl(candidate)
                    || !psl2_343_order_matches(
                        candidate, order_multiple[generator])) continue;
            if (!reserve_node()) return;
            value[generator] = candidate;
            inverse[generator] = psl2_343_inverse(candidate);
            search_state(value, inverse, assigned | (1u << generator),
                         branch_depth);
        }
}

static void search_state(psl2_343 value[MAXD], psl2_343 inverse[MAXD],
                         uint32_t assigned, int branch_depth) {
    if (candidate_limit_reached() || time_limit_reached()) return;
    if (!propagate(value, inverse, &assigned)) {
        rejected++;
        return;
    }
    uint32_t complete = (1u << d) - 1;
    if (assigned == complete) {
        int nonidentity = 0;
        for (int generator = 0; generator < d; generator++)
            nonidentity |= !psl2_343_equal(
                value[generator], psl2_343_identity());
        if (!nonidentity) { rejected++; return; }
        emit_solution(value);
        solutions++;
        return;
    }
    int generator = 0;
    while ((assigned >> generator) & 1u) generator++;
    int child_depth = branch_depth + 1;
    if (child_depth > max_branch_depth) max_branch_depth = child_depth;
    branch_over_group(value, inverse, assigned, generator, child_depth);
}

static uint64_t count_group_elements(void) {
    uint64_t count = 0;
    psl2_343 candidate;
    candidate.v[0] = 1;
    for (gf343 b = 0; b < GF343_Q; b++)
        for (gf343 c = 0; c < GF343_Q; c++)
            for (gf343 diagonal = 0; diagonal < GF343_Q; diagonal++) {
                candidate.v[1] = b; candidate.v[2] = c; candidate.v[3] = diagonal;
                count += psl2_343_is_psl(candidate) != 0;
            }
    candidate.v[0] = 0; candidate.v[1] = 1;
    for (gf343 c = 0; c < GF343_Q; c++)
        for (gf343 diagonal = 0; diagonal < GF343_Q; diagonal++) {
            candidate.v[2] = c; candidate.v[3] = diagonal;
            count += psl2_343_is_psl(candidate) != 0;
        }
    return count;
}

static void search_orientation(int gauge_generator, int partner_generator) {
    psl2_343 gauge_reps[GF343_Q + 1];
    int ngauge = conjugacy_representatives(gauge_generator, gauge_reps);
    for (int r = 0; r < ngauge && !should_stop(); r++) {
        if (r % representative_shards != representative_shard) continue;
        MatrixVector partners = partner_representatives(
            gauge_reps[r], partner_generator);
        fprintf(stderr, "[matrix] gauge=%d partner=%d class=%d/%d candidates=%zu\n",
                gauge_generator, partner_generator, r + 1, ngauge, partners.count);
        for (size_t p = 0; p < partners.count && !should_stop(); p++) {
            if (!reserve_node()) break;
            psl2_343 value[MAXD], inverse[MAXD];
            value[gauge_generator] = gauge_reps[r];
            inverse[gauge_generator] = psl2_343_inverse(gauge_reps[r]);
            value[partner_generator] = partners.value[p];
            inverse[partner_generator] = psl2_343_inverse(partners.value[p]);
            search_state(value, inverse,
                         (1u << gauge_generator) | (1u << partner_generator), 0);
        }
        free(partners.value);
    }
}

static void search_generic(int gauge_generator) {
    psl2_343 gauge_reps[GF343_Q + 1];
    int ngauge = 0;
    psl2_343 one = psl2_343_identity();
    if (psl2_343_order_matches(one, order_multiple[gauge_generator]))
        gauge_reps[ngauge++] = one;
    ngauge += conjugacy_representatives(
        gauge_generator, gauge_reps + ngauge);
    for (int r = 0; r < ngauge && !should_stop(); r++) {
        if (r % representative_shards != representative_shard) continue;
        if (!reserve_node()) break;
        psl2_343 value[MAXD], inverse[MAXD];
        value[gauge_generator] = gauge_reps[r];
        inverse[gauge_generator] = psl2_343_inverse(gauge_reps[r]);
        search_state(value, inverse, 1u << gauge_generator, 0);
    }
}

static int parse_unsigned(const char *text, unsigned *out) {
    char *end = NULL;
    errno = 0;
    unsigned long value = strtoul(text, &end, 10);
    if (errno || !text[0] || text[0] == '-' || !end || *end
            || value > UINT32_MAX) return 0;
    *out = (unsigned)value;
    return 1;
}

static void usage(const char *program) {
    fprintf(stderr,
        "usage: %s FLAT [-o k0..kD-1] "
        "[-b NODES] [--timeout SEC] [--stop-after K] [--rep-shard I N] "
        "[--count-elements]\n",
        program);
}

int main(int argc, char **argv) {
    const char *flat = NULL;
    for (int i = 1; i < argc; i++)
        if (argv[i][0] != '-') { flat = argv[i]; break; }
    if (!flat || !load_flat(flat)) { usage(argv[0]); return 2; }
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], flat)) continue;
        if (!strcmp(argv[i], "-o")) {
            if (i + d >= argc) return 2;
            for (int g = 0; g < d; g++)
                if (!parse_unsigned(argv[++i], &order_multiple[g])) return 2;
        } else if (!strcmp(argv[i], "-b") && i + 1 < argc) {
            node_limit = atoll(argv[++i]);
        } else if (!strcmp(argv[i], "--timeout") && i + 1 < argc) {
            timeout_seconds = strtod(argv[++i], NULL);
        } else if (!strcmp(argv[i], "--stop-after") && i + 1 < argc) {
            stop_after = atoi(argv[++i]);
        } else if (!strcmp(argv[i], "--rep-shard") && i + 2 < argc) {
            representative_shard = atoi(argv[++i]);
            representative_shards = atoi(argv[++i]);
        } else if (!strcmp(argv[i], "--count-elements")) {
            count_elements_only = 1;
        } else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            usage(argv[0]); return 0;
        } else {
            fprintf(stderr, "unknown option %s\n", argv[i]); return 2;
        }
    }
    if (node_limit < -1 || stop_after < 0 || timeout_seconds == 0.0
            || representative_shards < 1 || representative_shards > GF343_Q
            || representative_shard < 0
            || representative_shard >= representative_shards) return 2;
    psl2_343_init();
    clock_gettime(CLOCK_MONOTONIC, &started);
    if (count_elements_only) {
        uint64_t count = count_group_elements();
        printf("ELEMENTS %" PRIu64 "\n", count);
        free(relations); free(steps);
        return count == PSL2_343_ORDER ? 0 : 1;
    }

    int first = -1, second = -1, nforce = 0;
    int best_single = 0, best_single_forced = -1;
    for (int a = 0; a < d; a++) {
        Force prefix[MAXD]; int count = 0;
        uint32_t assigned = force_prefix(1u << a, prefix, &count);
        int assigned_count = __builtin_popcount(assigned) - 1;
        if (assigned_count > best_single_forced) {
            best_single = a; best_single_forced = assigned_count;
        }
    }
    for (int a = 0; a < d && first < 0; a++)
        for (int b = a + 1; b < d; b++) {
            Force prefix[MAXD]; int count = 0;
            uint32_t assigned = force_prefix(
                (1u << a) | (1u << b), prefix, &count);
            if (assigned == ((1u << d) - 1)) {
                first = a; second = b; nforce = count; break;
            }
        }
    if (first >= 0) {
        fprintf(stderr, "[matrix] D=%d R=%d steps=%zu seed=%d,%d "
                        "structurally-forced=%d fallback-decisions=0\n",
                d, nrelations, nsteps, first, second, nforce);
        search_orientation(first, second);
        if (!should_stop()) search_orientation(second, first);
    } else {
        fprintf(stderr, "[matrix] D=%d R=%d steps=%zu seed=%d "
                        "structurally-forced=%d fallback-decisions=%d\n",
                d, nrelations, nsteps, best_single, best_single_forced,
                d - 1 - best_single_forced);
        search_generic(best_single);
    }
    const char *status = capped ? "INCONCLUSIVE"
        : candidate_limit_reached() ? "CANDIDATE_LIMIT" : "EXHAUSTED";
    fprintf(stderr, "STATUS %s\n", status);
    fprintf(stderr,
        "STATS nodes=%lld rejected=%lld forced=%lld verified=%lld "
        "solutions=%d max-branch-depth=%d wall=%.3f\n",
        nodes, rejected, forced, verified, solutions, max_branch_depth, elapsed());
    free(relations); free(steps);
    if (capped) return 3;
    return solutions ? 0 : 1;
}
