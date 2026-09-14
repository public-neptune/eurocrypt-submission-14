#include "../psl2_343/group.h"

#include <stdio.h>
#include <stdlib.h>

static void check(int condition, const char *message) {
    if (!condition) {
        fprintf(stderr, "psl2-selftest: %s\n", message);
        exit(1);
    }
}

static int direct_kind(psl2_343 element) {
    if (psl2_343_equal(element, psl2_343_identity()))
        return PSL2_343_KIND_IDENTITY;
    gf343 trace = psl2_343_trace(element);
    gf343 discriminant = gf343_sub(
        gf343_mul(trace, trace), gf343_mul(4, psl2_343_det(element)));
    if (!discriminant) return PSL2_343_KIND_UNIPOTENT;
    return gf343_is_square(discriminant)
        ? PSL2_343_KIND_SPLIT : PSL2_343_KIND_NONSPLIT;
}

int main(void) {
    psl2_343_init();
    for (gf343 a = 1; a < GF343_Q; a++) {
        check(gf343_mul(a, gf343_inv(a)) == 1, "field inverse");
        check(gf343_pow(a, GF343_Q) == a, "field Frobenius identity");
    }
    check(gf343_pow(7, 3) == 2, "field modulus t^3=2");

    for (gf343 trace = 0; trace < GF343_Q; trace++) {
        psl2_343 sample = {{0, gf343_neg(1), 1, trace}};
        check(psl2_343_canonicalize(&sample), "canonical companion");
        check(psl2_343_is_psl(sample), "companion belongs to PSL");
        check(psl2_343_equal(
            psl2_343_mul(sample, psl2_343_inverse(sample)),
            psl2_343_identity()), "companion inverse");
        unsigned order = psl2_343_element_order(sample);
        check(order != 0, "known PSL element order");
        check(psl2_343_order_matches(sample, order),
              "exact and multiple order filters");
        check(psl2_343_element_kind(sample) == direct_kind(sample),
              "algebraic element kind");
    }

    printf("psl2-selftest: PASS\n");
    return 0;
}
