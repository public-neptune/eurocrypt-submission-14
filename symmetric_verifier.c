/* Streaming verifier for S_n challenge solutions. */
#define _POSIX_C_SOURCE 200809L

#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <zlib.h>

#define MAXN 15
#define SUBGROUP_CAP 4000000
#define EMPTY UINT64_MAX

typedef struct { uint8_t image[MAXN]; } Perm;
typedef struct { char *data; size_t capacity; } Line;
typedef struct { uint64_t *value; size_t count, capacity; } Vector;
typedef struct { uint64_t *slot; size_t count, capacity; } Set;
typedef enum { TOP_LEVEL, CHALLENGE_WORDS, ZERO_WORDS, ONE_WORDS, RULE_WORDS } ParseState;

static int degree;
static Perm generators[128];
static uint8_t generator_present[128];
static int8_t generator_index[128];
static Perm indexed_generators[128];
static int indexed_count, block_length;
static Perm *block_table[8];
static size_t block_count[8];
static int rules_only, selected_case; /* 0=all, 1=lowercase, 2=uppercase */

static Perm identity(void) {
    Perm out;
    for (int i = 0; i < degree; i++) out.image[i] = (uint8_t)i;
    return out;
}

static Perm compose(Perm left, Perm right) {
    Perm out;
    for (int i = 0; i < degree; i++)
        out.image[i] = right.image[left.image[i]];
    return out;
}

static Perm inverse(Perm value) {
    Perm out;
    for (int i = 0; i < degree; i++) out.image[value.image[i]] = (uint8_t)i;
    return out;
}

static int equal(Perm left, Perm right) {
    return !memcmp(left.image, right.image, (size_t)degree);
}

static uint64_t pack(Perm value) {
    uint64_t out = 0;
    for (int i = 0; i < degree; i++) out |= (uint64_t)value.image[i] << (4 * i);
    return out;
}

static Perm unpack(uint64_t value) {
    Perm out;
    for (int i = 0; i < degree; i++) out.image[i] = (uint8_t)((value >> (4 * i)) & 15);
    return out;
}

static uint64_t mix(uint64_t value) {
    value ^= value >> 30;
    value *= UINT64_C(0xbf58476d1ce4e5b9);
    value ^= value >> 27;
    value *= UINT64_C(0x94d049bb133111eb);
    return value ^ (value >> 31);
}

static void set_init(Set *set, size_t capacity) {
    size_t power = 16;
    while (power < capacity) power *= 2;
    set->slot = malloc(power * sizeof(*set->slot));
    if (!set->slot) abort();
    for (size_t i = 0; i < power; i++) set->slot[i] = EMPTY;
    set->count = 0; set->capacity = power;
}

static int set_contains(const Set *set, uint64_t value) {
    if (!set->capacity) return 0;
    size_t mask = set->capacity - 1;
    size_t index = (size_t)mix(value) & mask;
    while (set->slot[index] != EMPTY) {
        if (set->slot[index] == value) return 1;
        index = (index + 1) & mask;
    }
    return 0;
}

static void set_rehash(Set *set) {
    Set grown;
    set_init(&grown, set->capacity * 2);
    for (size_t i = 0; i < set->capacity; i++) {
        uint64_t value = set->slot[i];
        if (value == EMPTY) continue;
        size_t mask = grown.capacity - 1;
        size_t index = (size_t)mix(value) & mask;
        while (grown.slot[index] != EMPTY) index = (index + 1) & mask;
        grown.slot[index] = value; grown.count++;
    }
    free(set->slot); *set = grown;
}

static int set_insert(Set *set, uint64_t value) {
    if ((set->count + 1) * 10 > set->capacity * 7) set_rehash(set);
    size_t mask = set->capacity - 1;
    size_t index = (size_t)mix(value) & mask;
    while (set->slot[index] != EMPTY) {
        if (set->slot[index] == value) return 0;
        index = (index + 1) & mask;
    }
    set->slot[index] = value; set->count++;
    return 1;
}

static void vector_push(Vector *vector, uint64_t value) {
    if (vector->count == vector->capacity) {
        vector->capacity = vector->capacity ? 2 * vector->capacity : 16384;
        uint64_t *grown = realloc(vector->value,
                                  vector->capacity * sizeof(*grown));
        if (!grown) abort();
        vector->value = grown;
    }
    vector->value[vector->count++] = value;
}

static int valid_permutation(Perm value) {
    uint16_t seen = 0;
    for (int i = 0; i < degree; i++) {
        if (value.image[i] >= degree || ((seen >> value.image[i]) & 1u)) return 0;
        seen |= (uint16_t)(1u << value.image[i]);
    }
    return 1;
}

static void block_tables_init(void) {
    memset(generator_index, -1, sizeof(generator_index));
    for (int letter = 0; letter < 128; letter++)
        if (generator_present[letter]) {
            generator_index[letter] = (int8_t)indexed_count;
            indexed_generators[indexed_count++] = generators[letter];
        }
    block_length = 1;
    size_t power = (size_t)indexed_count;
    while (block_length < 7 && power * (size_t)indexed_count <= 65536) {
        power *= (size_t)indexed_count;
        block_length++;
    }
    block_count[0] = 1;
    for (int length = 1; length <= block_length; length++) {
        block_count[length] = block_count[length - 1] * (size_t)indexed_count;
        block_table[length] = malloc(block_count[length] * sizeof(Perm));
        if (!block_table[length]) abort();
        for (size_t code = 0; code < block_count[length]; code++) {
            size_t value = code;
            uint8_t digits[8];
            for (int position = length; position-- > 0;) {
                digits[position] = (uint8_t)(value % (size_t)indexed_count);
                value /= (size_t)indexed_count;
            }
            Perm product = identity();
            for (int position = 0; position < length; position++)
                product = compose(product, indexed_generators[digits[position]]);
            block_table[length][code] = product;
        }
    }
}

static int word_image(const char *word, Perm *out) {
    Perm value = identity();
    const unsigned char *cursor = (const unsigned char *)word;
    while (*cursor) {
        size_t code = 0;
        int length = 0;
        while (length < block_length && cursor[length]) {
            unsigned char letter = cursor[length];
            if (letter >= 128 || generator_index[letter] < 0) return 0;
            code = code * (size_t)indexed_count
                 + (unsigned)generator_index[letter];
            length++;
        }
        value = compose(value, block_table[length][code]);
        cursor += length;
    }
    *out = value;
    return 1;
}

static int word_matches_case(const char *word) {
    if (!selected_case) return 1;
    for (const unsigned char *cursor = (const unsigned char *)word;
         *cursor; cursor++)
        if ((selected_case == 1 && !islower(*cursor))
                || (selected_case == 2 && !isupper(*cursor))) return 0;
    return 1;
}

static double elapsed(struct timespec start) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (double)(now.tv_sec - start.tv_sec)
         + 1e-9 * (double)(now.tv_nsec - start.tv_nsec);
}

static int read_line(gzFile source, Line *line) {
    if (!line->capacity) {
        line->capacity = 4096;
        line->data = malloc(line->capacity);
        if (!line->data) abort();
    }
    size_t length = 0;
    line->data[0] = '\0';
    for (;;) {
        if (line->capacity - length < 2) {
            line->capacity *= 2;
            char *grown = realloc(line->data, line->capacity);
            if (!grown) abort();
            line->data = grown;
        }
        int available = line->capacity - length > INT_MAX
            ? INT_MAX : (int)(line->capacity - length);
        if (!gzgets(source, line->data + length, available)) return length ? 1 : 0;
        length += strlen(line->data + length);
        if ((length && line->data[length - 1] == '\n') || gzeof(source)) return 1;
    }
}

static char *trim(char *text) {
    while (isspace((unsigned char)*text)) text++;
    size_t length = strlen(text);
    while (length && isspace((unsigned char)text[length - 1])) text[--length] = '\0';
    return text;
}

static int parse_u64(const char *text, uint64_t *out) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno || !*text || *text == '-' || !end || *end) return 0;
    *out = (uint64_t)value;
    return 1;
}

static int quoted_word(char *line, char **word, int *closes) {
    char *first = strchr(line, '"');
    *closes = strchr(line, ']') != NULL;
    if (!first) return *closes ? 0 : -1;
    char *second = strchr(first + 1, '"');
    if (!second || strchr(first + 1, '\\')) return -1;
    *closes = strchr(second + 1, ']') != NULL;
    *second = '\0'; *word = first + 1;
    return 1;
}

static int quoted_rule(char *line, char **left, char **right, int *closes) {
    char *q1 = strchr(line, '"');
    *closes = strchr(line, '}') != NULL;
    if (!q1) return *closes ? 0 : -1;
    char *q2 = strchr(q1 + 1, '"');
    char *q3 = q2 ? strchr(q2 + 1, '"') : NULL;
    char *q4 = q3 ? strchr(q3 + 1, '"') : NULL;
    if (!q2 || !q3 || !q4 || strchr(q1 + 1, '\\') || !strchr(q2 + 1, ':'))
        return -1;
    *closes = strchr(q4 + 1, '}') != NULL;
    *q2 = *q4 = '\0'; *left = q1 + 1; *right = q3 + 1;
    return 1;
}

static void fail_once(char *buffer, size_t capacity, const char *message) {
    if (!buffer[0]) snprintf(buffer, capacity, "%s", message);
}

static int build_subgroup(const Vector *zeros, Set *subgroup, Vector *members,
                          char *failure, size_t failure_capacity) {
    Set generator_set;
    Vector group_generators = {0};
    set_init(&generator_set, 16384);
    size_t split = zeros->count < 5000 ? zeros->count : 5000;
    for (size_t i = 0; i < split; i++) {
        Perm value = unpack(zeros->value[i]);
        uint64_t direct = pack(value), reverse = pack(inverse(value));
        if (set_insert(&generator_set, direct)) vector_push(&group_generators, direct);
        if (set_insert(&generator_set, reverse)) vector_push(&group_generators, reverse);
    }
    set_init(subgroup, 1024);
    uint64_t one = pack(identity());
    set_insert(subgroup, one); vector_push(members, one);
    for (size_t head = 0; head < members->count; head++) {
        Perm current = unpack(members->value[head]);
        for (size_t j = 0; j < group_generators.count; j++) {
            uint64_t product = pack(compose(current, unpack(group_generators.value[j])));
            if (set_insert(subgroup, product)) {
                if (subgroup->count > SUBGROUP_CAP) {
                    fail_once(failure, failure_capacity,
                              "zero words generate a subgroup above the safety cap");
                    free(generator_set.slot); free(group_generators.value);
                    return 0;
                }
                vector_push(members, product);
            }
        }
    }
    free(generator_set.slot); free(group_generators.value);
    return 1;
}

static int build_coset(const Set *subgroup, const Vector *members,
                       const Vector *ones, Set *coset) {
    if (!ones->count) return 0;
    Perm representative = unpack(ones->value[0]);
    for (int side = 0; side < 2; side++) {
        Set candidate;
        set_init(&candidate, members->count * 2 + 16);
        int disjoint = 1;
        for (size_t i = 0; i < members->count; i++) {
            Perm h = unpack(members->value[i]);
            uint64_t value = pack(side ? compose(h, representative)
                                       : compose(representative, h));
            if (set_contains(subgroup, value)) disjoint = 0;
            set_insert(&candidate, value);
        }
        size_t split = ones->count < 5000 ? ones->count : 5000;
        int fits = disjoint;
        for (size_t i = 0; i < split && fits; i++)
            fits = set_contains(&candidate, ones->value[i]);
        if (fits) { *coset = candidate; return 1; }
        free(candidate.slot);
    }
    return 0;
}

static void usage(const char *program) {
    fprintf(stderr, "usage: %s CHALLENGE -n N -g LETTER p0..pN-1 [-g ...] "
                    "[--labels BITS] [--max-rules N] "
                    "[--rules-only] [--case lower|upper]\n", program);
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(argv[0]); return 2; }
    const char *path = argv[1], *expected_labels = NULL;
    uint64_t max_rules = UINT64_MAX;
    for (int i = 2; i < argc; i++) {
        if (!strcmp(argv[i], "-n") && i + 1 < argc) {
            degree = atoi(argv[++i]);
            if (degree < 1 || degree > MAXN) return 2;
        } else if (!strcmp(argv[i], "-g") && degree && i + degree + 1 < argc) {
            const char *name = argv[++i];
            if (strlen(name) != 1 || !isalpha((unsigned char)name[0])) return 2;
            unsigned char letter = (unsigned char)name[0];
            for (int point = 0; point < degree; point++) {
                char *end = NULL;
                long value = strtol(argv[++i], &end, 10);
                if (!end || *end || value < 0 || value >= degree) return 2;
                generators[letter].image[point] = (uint8_t)value;
            }
            if (!valid_permutation(generators[letter])) return 2;
            generator_present[letter] = 1;
        } else if (!strcmp(argv[i], "--labels") && i + 1 < argc) {
            expected_labels = argv[++i];
            for (const char *p = expected_labels; *p; p++)
                if (*p != '0' && *p != '1') return 2;
        } else if (!strcmp(argv[i], "--max-rules") && i + 1 < argc) {
            if (!parse_u64(argv[++i], &max_rules)) return 2;
        } else if (!strcmp(argv[i], "--rules-only")) {
            rules_only = 1;
        } else if (!strcmp(argv[i], "--case") && i + 1 < argc) {
            const char *value = argv[++i];
            if (!strcmp(value, "lower")) selected_case = 1;
            else if (!strcmp(value, "upper")) selected_case = 2;
            else return 2;
        } else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            usage(argv[0]); return 0;
        } else return 2;
    }
    if (!degree) { usage(argv[0]); return 2; }
    block_tables_init();

    gzFile source = gzopen(path, "rb");
    if (!source) { perror(path); return 2; }
    gzbuffer(source, 1 << 20);
    struct timespec started;
    clock_gettime(CLOCK_MONOTONIC, &started);
    ParseState state = TOP_LEVEL;
    Line line = {0};
    Vector challenges = {0}, zeros = {0}, ones = {0};
    uint64_t rules_total = 0, rules_selected = 0, rules_checked = 0;
    int saw_rules = 0, saw_challenge = 0, saw_zeros = 0, saw_ones = 0;
    char rules_failure[512] = "", class_failure[512] = "";

    while (read_line(source, &line)) {
        char *text = trim(line.data);
        if (state == TOP_LEVEL) {
            if (*text == '{') text = trim(text + 1);
            char *open = NULL;
            if (strstr(text, "\"challenge\"") && (open = strchr(text, '['))) {
                state = CHALLENGE_WORDS; saw_challenge = 1;
            } else if (strstr(text, "\"zeros\"") && (open = strchr(text, '['))) {
                state = ZERO_WORDS; saw_zeros = 1;
            } else if (strstr(text, "\"ones\"") && (open = strchr(text, '['))) {
                state = ONE_WORDS; saw_ones = 1;
            } else if (strstr(text, "\"rules\"") && (open = strchr(text, '{'))) {
                state = RULE_WORDS; saw_rules = 1;
            } else continue;
            text = trim(open + 1);
            if (!*text) continue;
        }
        if (state == RULE_WORDS) {
            char *left = NULL, *right = NULL; int closes = 0;
            int parsed = quoted_rule(text, &left, &right, &closes);
            if (parsed < 0) return 2;
            if (parsed > 0) {
                rules_total++;
                if (word_matches_case(left) && word_matches_case(right)) {
                    rules_selected++;
                if (rules_checked < max_rules) {
                    Perm lhs, rhs;
                    rules_checked++;
                    if (!word_image(left, &lhs) || !word_image(right, &rhs))
                        fail_once(rules_failure, sizeof(rules_failure),
                                  "a rule uses an unknown generator");
                    else if (!equal(lhs, rhs) && !rules_failure[0])
                        snprintf(rules_failure, sizeof(rules_failure),
                                 "rule #%" PRIu64 " (%s = %s) fails",
                                 rules_total, left, right);
                }
                }
            }
            if (closes) state = TOP_LEVEL;
            continue;
        }
        char *word = NULL; int closes = 0;
        int parsed = quoted_word(text, &word, &closes);
        if (parsed < 0) return 2;
        if (parsed > 0 && !rules_only) {
            Perm value;
            if (!word_image(word, &value))
                fail_once(class_failure, sizeof(class_failure),
                          "a labelled word uses an unknown generator");
            else if (state == ZERO_WORDS) vector_push(&zeros, pack(value));
            else if (state == ONE_WORDS) vector_push(&ones, pack(value));
            else vector_push(&challenges, pack(value));
        }
        if (closes) state = TOP_LEVEL;
    }
    int zerror = Z_OK;
    const char *zmessage = gzerror(source, &zerror);
    if (!gzeof(source) && zerror != Z_OK && zerror != Z_STREAM_END) {
        fprintf(stderr, "gzip read failed: %s\n", zmessage); return 2;
    }
    gzclose(source);
    if (state != TOP_LEVEL) return 2;
    if (!saw_rules) fail_once(rules_failure, sizeof(rules_failure),
                              "challenge has no rules object");
    if (!rules_only && (!saw_challenge || !saw_zeros || !saw_ones))
        fail_once(class_failure, sizeof(class_failure),
                  "challenge is missing a labelled word list");

    Set subgroup = {0}, coset = {0};
    Vector members = {0};
    if (!rules_only && !class_failure[0]
            && build_subgroup(&zeros, &subgroup, &members,
                              class_failure, sizeof(class_failure))
            && !build_coset(&subgroup, &members, &ones, &coset))
        fail_once(class_failure, sizeof(class_failure),
                  "no subgroup coset fits the class-1 words");
    size_t split0 = zeros.count < 5000 ? zeros.count : 5000;
    size_t split1 = ones.count < 5000 ? ones.count : 5000;
    for (size_t i = split0; i < zeros.count && !class_failure[0]; i++)
        if (!set_contains(&subgroup, zeros.value[i]))
            fail_once(class_failure, sizeof(class_failure),
                      "a held-out zero word is outside H");
    for (size_t i = split1; i < ones.count && !class_failure[0]; i++)
        if (!set_contains(&coset, ones.value[i]))
            fail_once(class_failure, sizeof(class_failure),
                      "a held-out one word is outside the selected coset");

    char *labels = malloc(challenges.count + 1);
    if (!labels) abort();
    for (size_t i = 0; i < challenges.count; i++) {
        labels[i] = set_contains(&subgroup, challenges.value[i]) ? '0'
                  : set_contains(&coset, challenges.value[i]) ? '1' : '?';
        if (labels[i] == '?')
            fail_once(class_failure, sizeof(class_failure),
                      "a challenge word lies outside H and its coset");
        if (expected_labels && (i >= strlen(expected_labels)
                    || labels[i] != expected_labels[i]))
            fail_once(class_failure, sizeof(class_failure),
                      "classified labels disagree with the solution");
    }
    labels[challenges.count] = '\0';
    if (expected_labels && challenges.count != strlen(expected_labels))
        fail_once(class_failure, sizeof(class_failure),
                  "solution label count does not match the challenge");

    if (rules_failure[0]) printf("RULES FAIL %s\n", rules_failure);
    else if (max_rules != UINT64_MAX && rules_checked < rules_selected)
        printf("RULES PASS first %" PRIu64 " of %" PRIu64
               " selected rules hold (--max-rules limit)\n",
               rules_checked, rules_selected);
    else printf("RULES PASS all %" PRIu64 " selected rules hold\n", rules_checked);
    if (rules_only) printf("CLASSIFICATION SKIP rules-only verification\n");
    else if (class_failure[0]) printf("CLASSIFICATION FAIL %s\n", class_failure);
    else printf("CLASSIFICATION PASS |H|=%zu, held-out perfect on %zu words; "
                "labels match\n", subgroup.count,
                zeros.count - split0 + ones.count - split1);
    if (!rules_only && !expected_labels) printf("LABELS %s\n", labels);
    printf("STATS rules_total=%" PRIu64 " rules_selected=%" PRIu64
           " rules_checked=%" PRIu64 " wall=%.3f\n",
           rules_total, rules_selected, rules_checked, elapsed(started));

    int ok = !rules_failure[0] && (rules_only || !class_failure[0]);
    free(labels); free(line.data); free(challenges.value); free(zeros.value);
    free(ones.value); free(members.value); free(subgroup.slot); free(coset.slot);
    for (int length = 1; length <= block_length; length++) free(block_table[length]);
    return ok ? 0 : 1;
}
