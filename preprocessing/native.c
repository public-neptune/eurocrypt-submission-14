#define _POSIX_C_SOURCE 200809L

/* Native streaming front end for Henbane preprocessing.
 *
 * Reads the bundled line-oriented JSON from stdin, selects the same bounded
 * rule/coupling pools used by reconstruction and writes one compact binary
 * harvest. This is the sole production pool-selection path.
 */

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAGIC "HENPRE3"

typedef struct {
    char *u, *v;
    uint32_t lu, lv;
    uint64_t seen;
} Pair;

typedef struct {
    Pair *items;
    uint32_t size, cap;
} Pool;

typedef struct {
    char **items;
    uint32_t size, cap;
} Strings;

static void fail(const char *message) {
    fprintf(stderr, "[preprocess/native] %s\n", message);
    exit(1);
}

static void unsupported(const char *message) {
    fprintf(stderr, "[preprocess/native] unsupported input: %s\n", message);
    exit(3);
}

static void *xmalloc(size_t size) {
    void *value = malloc(size ? size : 1);
    if (!value) fail("out of memory");
    return value;
}

static void *xrealloc(void *old, size_t size) {
    void *value = realloc(old, size ? size : 1);
    if (!value) fail("out of memory");
    return value;
}

static char *copy_text(const char *source, size_t length) {
    char *value = xmalloc(length + 1);
    memcpy(value, source, length);
    value[length] = '\0';
    return value;
}

static int pair_worse(const Pair *a, const Pair *b) {
    uint32_t ka = a->lu + a->lv, kb = b->lu + b->lv;
    if (ka != kb) return ka > kb;
    return a->seen < b->seen;
}

static void pair_free(Pair *pair) {
    free(pair->u);
    free(pair->v);
}

static Pair pair_make(const char *u, size_t lu, const char *v, size_t lv,
                      uint64_t seen) {
    Pair result;
    result.u = copy_text(u, lu);
    result.v = copy_text(v, lv);
    result.lu = (uint32_t)lu;
    result.lv = (uint32_t)lv;
    result.seen = seen;
    return result;
}

static void pool_sift_up(Pool *pool, uint32_t index) {
    while (index) {
        uint32_t parent = (index - 1) >> 1;
        if (!pair_worse(&pool->items[index], &pool->items[parent])) break;
        Pair temporary = pool->items[index];
        pool->items[index] = pool->items[parent];
        pool->items[parent] = temporary;
        index = parent;
    }
}

static void pool_sift_down(Pool *pool, uint32_t index) {
    for (;;) {
        uint32_t left = index * 2 + 1, right = left + 1, worst = index;
        if (left < pool->size &&
            pair_worse(&pool->items[left], &pool->items[worst])) worst = left;
        if (right < pool->size &&
            pair_worse(&pool->items[right], &pool->items[worst])) worst = right;
        if (worst == index) return;
        Pair temporary = pool->items[index];
        pool->items[index] = pool->items[worst];
        pool->items[worst] = temporary;
        index = worst;
    }
}

static void pool_init(Pool *pool, uint32_t cap) {
    pool->items = xmalloc((size_t)(cap ? cap : 1) * sizeof(Pair));
    pool->size = 0;
    pool->cap = cap;
}

static void pool_consider(Pool *pool, const char *u, size_t lu,
                          const char *v, size_t lv, uint64_t seen) {
    if (!pool->cap || lu > UINT32_MAX || lv > UINT32_MAX) return;
    uint32_t key = (uint32_t)(lu + lv);
    if (pool->size < pool->cap) {
        pool->items[pool->size] = pair_make(u, lu, v, lv, seen);
        pool_sift_up(pool, pool->size++);
    } else if (key < pool->items[0].lu + pool->items[0].lv) {
        pair_free(&pool->items[0]);
        pool->items[0] = pair_make(u, lu, v, lv, seen);
        pool_sift_down(pool, 0);
    }
}

static int pair_output_compare(const void *left, const void *right) {
    const Pair *a = left, *b = right;
    uint32_t ka = a->lu + a->lv, kb = b->lu + b->lv;
    if (ka != kb) return ka > kb ? -1 : 1;
    if (a->seen != b->seen) return a->seen < b->seen ? -1 : 1;
    return 0;
}

static void strings_add(Strings *strings, const char *value, size_t length) {
    if (strings->size == strings->cap) {
        strings->cap = strings->cap ? strings->cap * 2 : 1024;
        strings->items = xrealloc(
            strings->items, (size_t)strings->cap * sizeof(char *));
    }
    strings->items[strings->size++] = copy_text(value, length);
}

static int ascii_upper(const char *word, size_t length) {
    if (!length) return 0;
    for (size_t i = 0; i < length; i++)
        if (word[i] < 'A' || word[i] > 'Z') return 0;
    return 1;
}

static int ascii_lower(const char *word, size_t length) {
    if (!length) return 0;
    for (size_t i = 0; i < length; i++)
        if (word[i] < 'a' || word[i] > 'z') return 0;
    return 1;
}

static int valid_coupling(const char *left, size_t ll,
                          const char *right, size_t lr) {
    size_t li = 0, ri = 0;
    while (li < ll && left[li] >= 'A' && left[li] <= 'Z') li++;
    while (ri < lr && right[ri] >= 'a' && right[ri] <= 'z') ri++;
    if (!li || li == ll || !ri || ri == lr || ll - li != ri) return 0;
    if (memcmp(left + li, right, ri)) return 0;
    for (size_t i = li; i < ll; i++)
        if (left[i] < 'a' || left[i] > 'z') return 0;
    for (size_t i = ri; i < lr; i++)
        if (right[i] < 'A' || right[i] > 'Z') return 0;
    return 1;
}

static int quoted_pair(const char *line, const char **u, size_t *lu,
                       const char **v, size_t *lv) {
    const char *q1 = strchr(line, '"');
    if (!q1) return 0;
    const char *q2 = strchr(q1 + 1, '"');
    if (!q2) return 0;
    const char *q3 = strchr(q2 + 1, '"');
    if (!q3) return 0;
    const char *q4 = strchr(q3 + 1, '"');
    if (!q4) return 0;
    if (memchr(q1 + 1, '\\', (size_t)(q2 - q1 - 1)) ||
        memchr(q3 + 1, '\\', (size_t)(q4 - q3 - 1)))
        unsupported("escaped JSON strings");
    const char *colon = q2 + 1;
    while (colon < q3 && *colon != ':') colon++;
    if (colon == q3) unsupported("malformed rule separator");
    *u = q1 + 1;
    *lu = (size_t)(q2 - q1 - 1);
    *v = q3 + 1;
    *lv = (size_t)(q4 - q3 - 1);
    return 1;
}

static void array_words(Strings *target, const char *line) {
    const char *cursor = line;
    while ((cursor = strchr(cursor, '"')) != NULL) {
        const char *end = strchr(cursor + 1, '"');
        if (!end) unsupported("unterminated array string");
        if (memchr(cursor + 1, '\\', (size_t)(end - cursor - 1)))
            unsupported("escaped JSON strings");
        strings_add(target, cursor + 1, (size_t)(end - cursor - 1));
        cursor = end + 1;
    }
}

static void write_u8(FILE *file, uint8_t value) {
    if (fputc(value, file) == EOF) fail("cannot write harvest");
}

static void write_u32(FILE *file, uint32_t value) {
    for (int shift = 0; shift < 32; shift += 8)
        write_u8(file, (uint8_t)(value >> shift));
}

static void write_string(FILE *file, const char *value, uint32_t length) {
    write_u32(file, length);
    if (length && fwrite(value, 1, length, file) != length)
        fail("cannot write harvest");
}

static void write_pool(FILE *file, Pool *pool) {
    qsort(pool->items, pool->size, sizeof(Pair), pair_output_compare);
    write_u32(file, pool->size);
    for (uint32_t i = 0; i < pool->size; i++) {
        write_string(file, pool->items[i].u, pool->items[i].lu);
        write_string(file, pool->items[i].v, pool->items[i].lv);
    }
}

static void write_strings(FILE *file, const Strings *strings) {
    write_u32(file, strings->size);
    for (uint32_t i = 0; i < strings->size; i++)
        write_string(file, strings->items[i],
                     (uint32_t)strlen(strings->items[i]));
}

int main(int argc, char **argv) {
    const char *output = NULL;
    uint32_t poolcap = 5000, coupcap = 2000;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--out") && i + 1 < argc) output = argv[++i];
        else if (!strcmp(argv[i], "--poolcap") && i + 1 < argc)
            poolcap = (uint32_t)strtoul(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--coupcap") && i + 1 < argc)
            coupcap = (uint32_t)strtoul(argv[++i], NULL, 10);
        else {
            fprintf(stderr, "usage: %s --out FILE "
                    "[--poolcap N] [--coupcap N]\n", argv[0]);
            return 2;
        }
    }
    if (!output) fail("--out is required");

    Pool upper, lower, coupling;
    pool_init(&upper, poolcap);
    pool_init(&lower, poolcap);
    pool_init(&coupling, coupcap);
    Strings data[3] = {{0}};

    int in_rules = 0, array = -1;
    uint64_t seen = 0;
    char *line = NULL;
    size_t linecap = 0;
    ssize_t length;
    while ((length = getline(&line, &linecap, stdin)) >= 0) {
        (void)length;
        const char *segment = line;
        if (in_rules) {
            const char *u, *v;
            size_t lu, lv;
            if (quoted_pair(segment, &u, &lu, &v, &lv)) {
                int is_upper = ascii_upper(u, lu) && ascii_upper(v, lv);
                int is_lower = ascii_lower(u, lu) && ascii_lower(v, lv);
                if (is_upper) pool_consider(&upper, u, lu, v, lv, seen);
                else if (is_lower) pool_consider(&lower, u, lu, v, lv, seen);
                else if (valid_coupling(u, lu, v, lv))
                    pool_consider(&coupling, u, lu, v, lv, seen);
                seen++;
                if (seen % 5000000 == 0) {
                    fprintf(stderr, "[preprocess/native] streamed %.0fM rules\n",
                            (double)seen / 1000000.0);
                    fflush(stderr);
                }
            }
            if (strchr(segment, '}')) in_rules = 0;
            continue;
        }

        if (array >= 0) {
            const char *end = strchr(segment, ']');
            if (end) {
                char saved = *(char *)end;
                *(char *)end = '\0';
                array_words(&data[array], segment);
                *(char *)end = saved;
                array = -1;
            } else {
                array_words(&data[array], segment);
            }
            continue;
        }

        const char *names[3] = {"\"challenge\"", "\"zeros\"", "\"ones\""};
        int matched = 0;
        for (int kind = 0; kind < 3; kind++) {
            const char *key = strstr(segment, names[kind]);
            if (!key) continue;
            const char *open = strchr(key, '[');
            if (!open) unsupported("malformed classification array");
            const char *end = strchr(open + 1, ']');
            if (end) {
                char saved = *(char *)end;
                *(char *)end = '\0';
                array_words(&data[kind], open + 1);
                *(char *)end = saved;
            } else {
                array = kind;
                array_words(&data[kind], open + 1);
            }
            matched = 1;
            break;
        }
        if (matched) continue;

        const char *rules = strstr(segment, "\"rules\"");
        if (rules) {
            const char *open = strchr(rules, '{');
            if (!open) unsupported("malformed rules object");
            in_rules = 1;
            segment = open + 1;
            const char *u, *v;
            size_t lu, lv;
            if (quoted_pair(segment, &u, &lu, &v, &lv)) {
                int is_upper = ascii_upper(u, lu) && ascii_upper(v, lv);
                int is_lower = ascii_lower(u, lu) && ascii_lower(v, lv);
                if (is_upper) pool_consider(&upper, u, lu, v, lv, seen);
                else if (is_lower) pool_consider(&lower, u, lu, v, lv, seen);
                else if (valid_coupling(u, lu, v, lv))
                    pool_consider(&coupling, u, lu, v, lv, seen);
                seen++;
            }
            if (strchr(segment, '}')) in_rules = 0;
        }
    }
    free(line);
    if (ferror(stdin)) fail("cannot read input");
    if (in_rules || array >= 0) unsupported("truncated input");

    FILE *file = fopen(output, "wb");
    if (!file) {
        fprintf(stderr, "[preprocess/native] cannot open %s: %s\n",
                output, strerror(errno));
        return 1;
    }
    if (fwrite(MAGIC, 1, 8, file) != 8) fail("cannot write harvest");
    write_pool(file, &upper);
    write_pool(file, &lower);
    write_pool(file, &coupling);
    for (int kind = 0; kind < 3; kind++) write_strings(file, &data[kind]);
    if (fclose(file)) fail("cannot finish harvest");

    fprintf(stderr, "[preprocess/native] pools=%u/%u couplings=%u\n",
            upper.size, lower.size, coupling.size);
    return 0;
}
