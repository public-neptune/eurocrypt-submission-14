/* Streaming verifier for exact SL(2,343) challenge solutions. */
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

#define Q 343
#define P 7

typedef uint16_t gf343;
typedef struct { gf343 v[4]; } Matrix;
typedef struct { char *data; size_t capacity; } Line;

typedef enum {
    TOP_LEVEL,
    CHALLENGE_WORDS,
    ZERO_WORDS,
    ONE_WORDS,
    RULE_WORDS
} ParseState;

static gf343 add_table[Q][Q], mul_table[Q][Q], neg_table[Q];
static uint8_t square[Q];
static Matrix generators[128];
static uint8_t generator_present[128];
static int projective_mode, rules_only, selected_case;

static gf343 add_raw(gf343 a, gf343 b) {
    unsigned a0 = a % P, a1 = (a / P) % P, a2 = a / (P * P);
    unsigned b0 = b % P, b1 = (b / P) % P, b2 = b / (P * P);
    return (gf343)((a0 + b0) % P
        + P * ((a1 + b1) % P)
        + P * P * ((a2 + b2) % P));
}

static gf343 mul_raw(gf343 a, gf343 b) {
    unsigned a0 = a % P, a1 = (a / P) % P, a2 = a / (P * P);
    unsigned b0 = b % P, b1 = (b / P) % P, b2 = b / (P * P);
    unsigned c0 = a0 * b0 + 2 * (a1 * b2 + a2 * b1);
    unsigned c1 = a0 * b1 + a1 * b0 + 2 * a2 * b2;
    unsigned c2 = a0 * b2 + a1 * b1 + a2 * b0;
    return (gf343)(c0 % P + P * (c1 % P) + P * P * (c2 % P));
}

static void field_init(void) {
    for (int a = 0; a < Q; a++) {
        for (int b = 0; b < Q; b++) {
            add_table[a][b] = add_raw((gf343)a, (gf343)b);
            mul_table[a][b] = mul_raw((gf343)a, (gf343)b);
            if (!add_table[a][b]) neg_table[a] = (gf343)b;
        }
        square[mul_table[a][a]] = 1;
    }
}

static Matrix matrix_identity(void) {
    Matrix value = {{1, 0, 0, 1}};
    return value;
}

static Matrix matrix_negative_identity(void) {
    Matrix value = {{neg_table[1], 0, 0, neg_table[1]}};
    return value;
}

static Matrix matrix_multiply(Matrix left, Matrix right) {
    Matrix out;
    gf343 a = left.v[0], b = left.v[1], c = left.v[2], d = left.v[3];
    gf343 e = right.v[0], f = right.v[1], g = right.v[2], h = right.v[3];
    out.v[0] = add_table[mul_table[a][e]][mul_table[b][g]];
    out.v[1] = add_table[mul_table[a][f]][mul_table[b][h]];
    out.v[2] = add_table[mul_table[c][e]][mul_table[d][g]];
    out.v[3] = add_table[mul_table[c][f]][mul_table[d][h]];
    return out;
}

static int matrix_equal(Matrix left, Matrix right) {
    return !memcmp(&left, &right, sizeof(left));
}

static int matrix_projective_equal(Matrix left, Matrix right) {
    int pivot = 0;
    while (pivot < 4 && !left.v[pivot]) pivot++;
    if (pivot == 4 || !right.v[pivot]) return 0;
    for (int i = 0; i < 4; i++)
        if (mul_table[left.v[i]][right.v[pivot]]
                != mul_table[right.v[i]][left.v[pivot]]) return 0;
    return 1;
}

static gf343 matrix_determinant(Matrix matrix) {
    gf343 ad = mul_table[matrix.v[0]][matrix.v[3]];
    gf343 bc = mul_table[matrix.v[1]][matrix.v[2]];
    return add_table[ad][neg_table[bc]];
}

static int word_image(const char *word, Matrix *out) {
    Matrix value = matrix_identity();
    for (const unsigned char *p = (const unsigned char *)word; *p; p++) {
        if (*p >= 128 || !generator_present[*p]) return 0;
        /* Words act left-to-right: compose(value,g) is g*value. */
        value = matrix_multiply(generators[*p], value);
    }
    *out = value;
    return 1;
}

static int central_bit(Matrix matrix) {
    if (matrix_equal(matrix, matrix_identity())) return 0;
    if (matrix_equal(matrix, matrix_negative_identity())) return 1;
    return -1;
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
        char *result = gzgets(source, line->data + length, available);
        if (!result) return length ? 1 : 0;
        length += strlen(line->data + length);
        if (length && line->data[length - 1] == '\n') return 1;
        if (gzeof(source)) return 1;
    }
}

static char *trim(char *text) {
    while (isspace((unsigned char)*text)) text++;
    size_t length = strlen(text);
    while (length && isspace((unsigned char)text[length - 1]))
        text[--length] = '\0';
    return text;
}

static int parse_unsigned(const char *text, unsigned *out) {
    char *end = NULL;
    errno = 0;
    unsigned long value = strtoul(text, &end, 10);
    if (errno || !*text || *text == '-' || !end || *end || value >= Q)
        return 0;
    *out = (unsigned)value;
    return 1;
}

static int parse_u64(const char *text, uint64_t *out) {
    char *end = NULL;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (errno || !*text || *text == '-' || !end || *end) return 0;
    *out = (uint64_t)value;
    return 1;
}

static int valid_word(const char *word) {
    for (const unsigned char *p = (const unsigned char *)word; *p; p++)
        if (!isalpha(*p) || *p >= 128 || !generator_present[*p]) return 0;
    return 1;
}

static int word_matches_case(const char *word) {
    if (!selected_case) return 1;
    for (const unsigned char *p = (const unsigned char *)word; *p; p++)
        if ((selected_case == 1 && !islower(*p))
                || (selected_case == 2 && !isupper(*p))) return 0;
    return 1;
}

static int quoted_word(char *line, char **word, int *closes, char close_char) {
    char *first = strchr(line, '"');
    *closes = strchr(line, close_char) != NULL;
    if (!first) return *closes ? 0 : -1;
    char *second = strchr(first + 1, '"');
    if (!second || strchr(first + 1, '\\')) return -1;
    *closes = strchr(second + 1, close_char) != NULL;
    *second = '\0';
    *word = first + 1;
    return 1;
}

static int quoted_rule(char *line, char **left, char **right, int *closes) {
    char *q1 = strchr(line, '"');
    *closes = strchr(line, '}') != NULL;
    if (!q1) return *closes ? 0 : -1;
    char *q2 = strchr(q1 + 1, '"');
    char *q3 = q2 ? strchr(q2 + 1, '"') : NULL;
    char *q4 = q3 ? strchr(q3 + 1, '"') : NULL;
    if (!q2 || !q3 || !q4 || strchr(q1 + 1, '\\')
            || !strchr(q2 + 1, ':')) return -1;
    *closes = strchr(q4 + 1, '}') != NULL;
    *q2 = *q4 = '\0';
    *left = q1 + 1;
    *right = q3 + 1;
    return 1;
}

static void record_failure(char *buffer, size_t capacity, const char *message) {
    if (!buffer[0]) snprintf(buffer, capacity, "%s", message);
}

static void usage(const char *program) {
    fprintf(stderr,
        "usage: %s CHALLENGE -g LETTER a b c d [-g ...] "
        "[--labels BITS] [--max-rules N] "
        "[--projective --rules-only] [--case lower|upper]\n", program);
}

int main(int argc, char **argv) {
    if (argc < 2) { usage(argv[0]); return 2; }
    const char *path = argv[1], *expected_labels = NULL;
    uint64_t max_rules = UINT64_MAX;
    field_init();

    for (int i = 2; i < argc; i++) {
        if (!strcmp(argv[i], "-g") && i + 5 < argc) {
            const char *name = argv[++i];
            if (strlen(name) != 1 || !isalpha((unsigned char)name[0]))
                return 2;
            unsigned char letter = (unsigned char)name[0];
            for (int j = 0; j < 4; j++) {
                unsigned value;
                if (!parse_unsigned(argv[++i], &value)) return 2;
                generators[letter].v[j] = (gf343)value;
            }
            generator_present[letter] = 1;
        } else if (!strcmp(argv[i], "--labels") && i + 1 < argc) {
            expected_labels = argv[++i];
            for (const char *p = expected_labels; *p; p++)
                if (*p != '0' && *p != '1') return 2;
        } else if (!strcmp(argv[i], "--max-rules") && i + 1 < argc) {
            if (!parse_u64(argv[++i], &max_rules)) return 2;
        } else if (!strcmp(argv[i], "--projective")) {
            projective_mode = 1;
        } else if (!strcmp(argv[i], "--rules-only")) {
            rules_only = 1;
        } else if (!strcmp(argv[i], "--case") && i + 1 < argc) {
            const char *value = argv[++i];
            if (!strcmp(value, "lower")) selected_case = 1;
            else if (!strcmp(value, "upper")) selected_case = 2;
            else return 2;
        } else if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
            usage(argv[0]); return 0;
        } else {
            fprintf(stderr, "unknown or incomplete option %s\n", argv[i]);
            return 2;
        }
    }

    int ngenerators = 0;
    for (int i = 0; i < 128; i++) ngenerators += generator_present[i] != 0;
    if (!ngenerators) { usage(argv[0]); return 2; }
    if (projective_mode && !rules_only) {
        fprintf(stderr, "--projective currently requires --rules-only\n");
        return 2;
    }
    for (int letter = 0; letter < 128; letter++) {
        if (!generator_present[letter]) continue;
        gf343 determinant = matrix_determinant(generators[letter]);
        if ((!projective_mode && determinant != 1)
                || (projective_mode && (!determinant || !square[determinant]))) {
            fprintf(stderr, "generator %c is outside %s\n", letter,
                    projective_mode ? "PSL(2,343)" : "SL(2,343)");
            return 2;
        }
    }

    gzFile source = gzopen(path, "rb");
    if (!source) { perror(path); return 2; }
    gzbuffer(source, 1 << 20);

    struct timespec started;
    clock_gettime(CLOCK_MONOTONIC, &started);
    ParseState state = TOP_LEVEL;
    Line line = {0};
    uint64_t rules_total = 0, rules_selected = 0, rules_checked = 0;
    uint64_t zeros = 0, ones = 0, challenges = 0;
    int saw_rules = 0, saw_challenge = 0, saw_zeros = 0, saw_ones = 0;
    char rules_failure[512] = "", class_failure[512] = "";
    size_t labels_capacity = 16384;
    char *observed_labels = malloc(labels_capacity);
    if (!observed_labels) abort();

    while (read_line(source, &line)) {
        char *text = trim(line.data);
        if (state == TOP_LEVEL) {
            if (*text == '{') text = trim(text + 1);
            char *open = NULL, *rest = NULL;
            if (strstr(text, "\"challenge\"")
                    && (open = strchr(text, '['))) {
                state = CHALLENGE_WORDS;
                saw_challenge = 1;
                rest = open + 1;
            } else if (strstr(text, "\"zeros\"")
                    && (open = strchr(text, '['))) {
                state = ZERO_WORDS;
                saw_zeros = 1;
                rest = open + 1;
            } else if (strstr(text, "\"ones\"")
                    && (open = strchr(text, '['))) {
                state = ONE_WORDS;
                saw_ones = 1;
                rest = open + 1;
            } else if (strstr(text, "\"rules\"")
                    && (open = strchr(text, '{'))) {
                state = RULE_WORDS;
                saw_rules = 1;
                rest = open + 1;
            } else {
                continue;
            }
            text = trim(rest);
            if (!*text) continue;
        }

        if (state == RULE_WORDS) {
            char *left = NULL, *right = NULL;
            int closes = 0;
            int parsed = quoted_rule(text, &left, &right, &closes);
            if (parsed < 0) {
                fprintf(stderr, "malformed line-oriented rule JSON\n");
                return 2;
            }
            if (parsed > 0) {
                rules_total++;
                if (word_matches_case(left) && word_matches_case(right)) {
                    if (!valid_word(left) || !valid_word(right)) {
                        record_failure(rules_failure, sizeof(rules_failure),
                                       "a rule uses an unknown generator");
                    } else {
                        rules_selected++;
                        if (rules_checked < max_rules) {
                            Matrix lhs, rhs;
                            if (!word_image(left, &lhs)
                                    || !word_image(right, &rhs)) abort();
                            rules_checked++;
                            int equal = projective_mode
                                ? matrix_projective_equal(lhs, rhs)
                                : matrix_equal(lhs, rhs);
                            if (!equal && !rules_failure[0]) {
                                snprintf(rules_failure, sizeof(rules_failure),
                                         "rule #%" PRIu64 " (%s = %s) fails",
                                         rules_total, left, right);
                            }
                            if (!(rules_checked % 5000000))
                                fprintf(stderr, "    ... %" PRIu64
                                        " %s rules checked\n", rules_checked,
                                        projective_mode
                                            ? "projective" : "exact SL");
                        }
                    }
                }
            }
            if (closes) state = TOP_LEVEL;
            continue;
        }

        char *word = NULL;
        int closes = 0;
        int parsed = quoted_word(text, &word, &closes, ']');
        if (parsed < 0) {
            fprintf(stderr, "malformed line-oriented word-list JSON\n");
            return 2;
        }
        if (parsed > 0 && !rules_only) {
            if (!valid_word(word)) {
                record_failure(class_failure, sizeof(class_failure),
                               "a labelled word uses an unknown generator");
            } else {
                Matrix value;
                if (!word_image(word, &value)) abort();
                int bit = central_bit(value);
                if (state == ZERO_WORDS) {
                    zeros++;
                    if (bit != 0)
                        record_failure(class_failure, sizeof(class_failure),
                                       "a public zero word is not I");
                } else if (state == ONE_WORDS) {
                    ones++;
                    if (bit != 1)
                        record_failure(class_failure, sizeof(class_failure),
                                       "a public one word is not -I");
                } else {
                    if (challenges + 2 > labels_capacity) {
                        labels_capacity *= 2;
                        char *grown = realloc(observed_labels, labels_capacity);
                        if (!grown) abort();
                        observed_labels = grown;
                    }
                    if (bit < 0) {
                        record_failure(class_failure, sizeof(class_failure),
                                       "a challenge word is neither I nor -I");
                        observed_labels[challenges] = '?';
                    } else {
                        observed_labels[challenges] = (char)('0' + bit);
                        if (expected_labels
                                && (challenges >= strlen(expected_labels)
                                    || expected_labels[challenges] != '0' + bit))
                            record_failure(class_failure, sizeof(class_failure),
                                           "classified labels disagree with the solution");
                    }
                    challenges++;
                }
            }
        }
        if (closes) state = TOP_LEVEL;
    }

    int reached_eof = gzeof(source);
    int zerror = Z_OK;
    const char *zmessage = gzerror(source, &zerror);
    if (!reached_eof && zerror != Z_OK && zerror != Z_STREAM_END) {
        fprintf(stderr, "gzip read failed: %s\n", zmessage);
        gzclose(source);
        return 2;
    }
    gzclose(source);
    if (state != TOP_LEVEL) {
        fprintf(stderr, "truncated challenge JSON\n");
        return 2;
    }
    if (!saw_rules)
        record_failure(rules_failure, sizeof(rules_failure),
                       "challenge has no rules object");
    if (!rules_only && (!saw_challenge || !saw_zeros || !saw_ones))
        record_failure(class_failure, sizeof(class_failure),
                       "challenge is missing a labelled word list");
    if (!rules_only && expected_labels && challenges != strlen(expected_labels))
        record_failure(class_failure, sizeof(class_failure),
                       "solution label count does not match the challenge");
    observed_labels[challenges] = '\0';

    if (rules_failure[0])
        printf("RULES FAIL %s\n", rules_failure);
    else if (max_rules != UINT64_MAX && rules_checked < rules_selected)
        printf("RULES PASS first %" PRIu64 " of %" PRIu64
               " selected rules hold (--max-rules limit)\n",
               rules_checked, rules_selected);
    else
        printf("RULES PASS all %" PRIu64 " selected rules hold %s\n",
               rules_checked, projective_mode ? "in PSL" : "exactly in SL");

    if (rules_only)
        printf("CLASSIFICATION SKIP rules-only verification\n");
    else if (class_failure[0])
        printf("CLASSIFICATION FAIL %s\n", class_failure);
    else
        printf("CLASSIFICATION PASS %" PRIu64 " zero, %" PRIu64
               " one, and %" PRIu64 " challenge words are exact; labels match\n",
               zeros, ones, challenges);
    if (!rules_only && !expected_labels) printf("LABELS %s\n", observed_labels);
    printf("STATS rules_total=%" PRIu64 " rules_selected=%" PRIu64
           " rules_checked=%" PRIu64 " wall=%.3f\n",
           rules_total, rules_selected, rules_checked, elapsed(started));

    int ok = !rules_failure[0] && (rules_only || !class_failure[0]);
    free(observed_labels);
    free(line.data);
    return ok ? 0 : 1;
}
