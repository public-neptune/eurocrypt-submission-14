#!/usr/bin/env python3
import gzip
import json
import os
import random
import subprocess
import tempfile
import unittest

import psl2_343 as psl2
from psl2_343 import sl
from check_solution import check_instance_sl_native, sl_matrices_from_solution
from recover_coupled import projective_alignments, recover_alpha_psl
from reconstruct import check_complete_projective_rules, recover_sl_solutions


class FieldTests(unittest.TestCase):
    def test_field_inverses_and_frobenius(self):
        for a in range(1, psl2.Q):
            self.assertEqual(psl2.fmul(a, psl2.finv(a)), 1)
            self.assertEqual(psl2.fpow(a, psl2.Q - 1), 1)
            self.assertEqual(psl2.fpow(a, psl2.Q), a)

    def test_defining_polynomial(self):
        t = 7
        self.assertEqual(psl2.fpow(t, 3), 2)

    def test_distributivity(self):
        rng = random.Random(11)
        for _ in range(10_000):
            a, b, c = (rng.randrange(psl2.Q) for _ in range(3))
            self.assertEqual(psl2.fmul(a, psl2.fadd(b, c)),
                             psl2.fadd(psl2.fmul(a, b), psl2.fmul(a, c)))


class SLLiftTests(unittest.TestCase):
    def test_binary_system_enumerates_affine_solution_space(self):
        system = sl.BinarySystem(("a", "b", "c"))
        system.add(0b101, 1)
        system.add(0b010, 0)
        solutions = list(system.solve_all())
        self.assertEqual(len(solutions), 2)
        self.assertEqual({tuple(value[letter] for letter in "abc")
                          for value in solutions}, {(1, 0, 0), (0, 0, 1)})

    def test_rank_deficient_lift_enumerates_every_sign_choice(self):
        candidates = sl.recover_lift_candidates(
            {"a": psl2.IDENTITY, "b": psl2.IDENTITY},
            zero_words=["a"], one_words=[])
        self.assertEqual(len(candidates), 2)
        self.assertTrue(all(candidate.nullity == 1 for candidate in candidates))
        self.assertEqual({candidate.signs["b"] for candidate in candidates}, {0, 1})
        self.assertTrue(all(sl.central_bit(
            sl.word_image("a", candidate.generators)) == 0
            for candidate in candidates))

    def test_unconstrained_lift_has_full_affine_family(self):
        candidates = sl.recover_lift_candidates(
            {"a": psl2.IDENTITY, "b": psl2.IDENTITY}, [], [])
        self.assertEqual(len(candidates), 4)
        self.assertTrue(all(candidate.nullity == 2 for candidate in candidates))

    def test_driver_exposes_every_rank_deficient_lift(self):
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            path = out.name
        try:
            with gzip.open(path, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {"a": ""}}, target, indent=2)
            identity_permutation = list(range(psl2.DEGREE))
            solutions = recover_sl_solutions(
                path, [identity_permutation, identity_permutation], "lower", {})
        finally:
            os.unlink(path)
        self.assertEqual(len(solutions), 2)
        self.assertTrue(all(details["nullity"] == 1
                            for _labels, details in solutions))

    def test_inconsistent_binary_system_is_rejected(self):
        system = sl.BinarySystem(("a",))
        system.add(1, 0)
        with self.assertRaises(sl.InconsistentLifts):
            system.add(1, 1)

    def test_determinant_one_lifts_preserve_projective_products(self):
        projective = psl2.standard_generators()
        lifted = tuple(sl.determinant_one_lift(matrix) for matrix in projective)
        self.assertTrue(all(psl2.mdet(matrix) == 1 for matrix in lifted))
        self.assertEqual([psl2.mcanonical(matrix) for matrix in lifted],
                         list(projective))
        self.assertEqual(
            psl2.mcanonical(sl.compose(lifted[0], lifted[1])),
            psl2.compose(projective[0], projective[1]))

    def test_labelled_words_recover_central_generator_signs(self):
        recovery = sl.recover_lifts(
            {"a": psl2.IDENTITY, "b": psl2.IDENTITY},
            zero_words=["aa", "b"],
            one_words=["a", "ab"],
        )
        self.assertEqual(recovery.signs, {"a": 1, "b": 0})
        self.assertEqual(recovery.rank, 2)
        self.assertEqual(recovery.relation_equations, 0)
        self.assertEqual(sl.classify(
            ["aa", "a", "b", "ab"], recovery.generators), "0101")

    def test_nontrivial_order_seven_lift_recovers_negative_sign(self):
        translation = psl2.standard_generators()[0]
        recovery = sl.recover_lifts(
            {"a": translation},
            zero_words=["a" * 14],
            one_words=["a" * 7],
        )
        self.assertEqual(recovery.signs, {"a": 1})
        self.assertEqual(sl.central_bit(
            sl.word_image("a" * 7, recovery.generators)), 1)
        self.assertEqual(sl.central_bit(
            sl.word_image("a" * 14, recovery.generators)), 0)

    def test_noncentral_labelled_word_rejects_projective_candidate(self):
        translation = psl2.standard_generators()[0]
        with self.assertRaises(sl.InconsistentLifts):
            sl.recover_lifts({"a": translation}, ["a"], [])

    def test_streaming_sl_checker_validates_center_and_rules(self):
        projective = {"a": psl2.IDENTITY}
        solution = {"sl2_343": {"generators": {
            "a": list(sl.NEGATIVE_IDENTITY)}}}
        lifted, detail = sl_matrices_from_solution(solution, projective)
        self.assertIsNotNone(lifted, detail)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            path = out.name
        try:
            with gzip.open(path, "wt") as target:
                json.dump({
                    "challenge": ["a", "aa"],
                    "rules": {"aa": ""},
                    "ones": ["a"],
                    "zeros": ["aa"],
                }, target, indent=2)
            rules, classification, labels = check_instance_sl_native(
                path, lifted, expected_labels="10",
                executable="build/henbane-sl-verify")
        finally:
            os.unlink(path)
        self.assertTrue(rules[0], rules[1])
        self.assertTrue(classification[0], classification[1])
        self.assertEqual(labels, "10")


class MobiusTests(unittest.TestCase):
    def setUp(self):
        self.rng = random.Random(343)

    def test_group_operations_and_permutations(self):
        for _ in range(100):
            g = psl2.random_element(self.rng)
            h = psl2.random_element(self.rng)
            self.assertEqual(psl2.mmul(g, psl2.minverse(g)), psl2.IDENTITY)
            pg, ph = psl2.permutation(g), psl2.permutation(h)
            composed = tuple(ph[x] for x in pg)
            self.assertEqual(psl2.permutation(psl2.compose(g, h)), composed)

    def test_three_points_reconstruct(self):
        anchors = (0, 1, psl2.INF)
        for _ in range(100):
            g = psl2.random_element(self.rng)
            targets = [psl2.mapply(g, x) for x in anchors]
            self.assertEqual(psl2.from_three_points(anchors, targets, require_psl=True), g)

    def test_orders(self):
        allowed = {1, 2, 3, 4, 7, 9, 19, 43, 57, 86, 171, 172}
        for _ in range(100):
            g = psl2.random_element(self.rng)
            order = psl2.element_order(g)
            self.assertIn(order, allowed)
            self.assertEqual(psl2.mpow(g, order), psl2.IDENTITY)

    def test_permutation_roundtrip(self):
        for _ in range(20):
            g = psl2.random_element(self.rng)
            self.assertEqual(psl2.matrix_from_permutation(psl2.permutation(g)), g)

    def test_conjugators(self):
        for _ in range(20):
            p = psl2.random_element(self.rng, nonidentity=True)
            x = psl2.random_element(self.rng)
            q = psl2.compose(psl2.compose(psl2.minverse(x), p), x)
            domain = psl2.conjugators(p, q)
            self.assertIn(x, domain)
            self.assertLessEqual(len(domain), 344)
            self.assertTrue(all(psl2.compose(p, c) == psl2.compose(c, q)
                                for c in domain))

    def test_standard_generating_triple(self):
        from permutation_group import schreier_sims_order
        generators = psl2.standard_generators()
        self.assertEqual([psl2.element_order(g) for g in generators], [7, 2, 171])
        self.assertEqual(schreier_sims_order(
            [psl2.permutation(g) for g in generators], psl2.DEGREE),
            psl2.GROUP_ORDER)

    def test_pgamma_automorphisms_preserve_products(self):
        conjugator = psl2.mcanonical((1, 0, 0, 3))  # PGL, outside PSL.
        self.assertTrue(psl2.mis_invertible(conjugator))
        self.assertFalse(psl2.mis_psl(conjugator))
        for twist in range(3):
            for _ in range(20):
                left = psl2.random_element(self.rng)
                right = psl2.random_element(self.rng)
                image = psl2.apply_automorphism(
                    psl2.compose(left, right), conjugator, twist)
                expected = psl2.compose(
                    psl2.apply_automorphism(left, conjugator, twist),
                    psl2.apply_automorphism(right, conjugator, twist))
                self.assertEqual(image, expected)
                self.assertTrue(psl2.mis_psl(image))


class SLQuotientSolverTests(unittest.TestCase):
    def run_matrix_flat(self, d, relations, *options):
        with tempfile.NamedTemporaryFile("w", suffix=".flat", delete=False) as flat:
            path = flat.name
            flat.write(f"{d} {len(relations)}\n")
            for left, right in relations:
                flat.write(f"{len(left)} {' '.join(map(str, left))} "
                           f"{len(right)} {' '.join(map(str, right))}\n")
        try:
            return subprocess.run(
                ["build/henbane-psl-matrix", path, *options],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False)
        finally:
            os.unlink(path)

    def test_complete_projective_element_enumerator_count(self):
        completed = self.run_matrix_flat(
            1, [((0,), (0,))], "--count-elements")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(completed.stdout.strip(),
                         f"ELEMENTS {psl2.GROUP_ORDER}")

    def test_matrix_backend_accepts_empty_portfolio(self):
        completed = self.run_matrix_flat(
            1, [], "-b", "1000", "--timeout", "5", "--stop-after", "1")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertTrue(any(line.startswith("M ")
                            for line in completed.stdout.splitlines()))
        self.assertIn("R=0", completed.stderr)

    def test_matrix_backend_branches_when_forcing_stalls(self):
        completed = self.run_matrix_flat(
            3, [((0, 2), (2, 0))],
            "-b", "100", "--timeout", "5", "--stop-after", "1")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertTrue(any(line.startswith("M ")
                            for line in completed.stdout.splitlines()))
        self.assertIn("fallback-decisions=2", completed.stderr)
        self.assertIn("max-branch-depth=2", completed.stderr)

    def test_matrix_backend_node_cap_is_inconclusive(self):
        completed = self.run_matrix_flat(
            3, [((0, 2), (2, 0))],
            "-b", "1", "--timeout", "5", "--stop-after", "0")
        self.assertEqual(completed.returncode, 3, completed.stderr)
        self.assertIn("STATUS INCONCLUSIVE", completed.stderr)
        self.assertNotIn("STATUS EXHAUSTED", completed.stderr)

    def test_matrix_backend_candidate_then_cap_is_inconclusive(self):
        completed = self.run_matrix_flat(
            3, [((0, 2), (2, 0))],
            "-b", "10", "--timeout", "5", "--stop-after", "0")
        self.assertTrue(completed.stdout.strip())
        self.assertEqual(completed.returncode, 3, completed.stderr)
        self.assertIn("STATUS INCONCLUSIVE", completed.stderr)

    def test_projective_rules_only_streaming_verifier(self):
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            path = out.name
        try:
            with gzip.open(path, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {"aaaaaaa": ""}}, target, indent=2)
            passed, detail = check_complete_projective_rules(
                path, [psl2.standard_generators()[0]], "lower",
                "build/henbane-sl-verify")
        finally:
            os.unlink(path)
        self.assertTrue(passed, detail)

    def test_matrix_backend_forces_whole_generator(self):
        with tempfile.NamedTemporaryFile("w", suffix=".flat", delete=False) as flat:
            path = flat.name
            flat.write("3 1\n1 2 2 0 1\n")
        try:
            completed = subprocess.run(
                ["build/henbane-psl-matrix", path, "-b", "100",
                 "--timeout", "5"],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False)
        finally:
            os.unlink(path)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        line = next(value for value in completed.stdout.splitlines()
                    if value.startswith("M "))
        raw = list(map(int, line.split()[1:]))
        matrices = [tuple(raw[4 * i:4 * i + 4]) for i in range(3)]
        self.assertEqual(matrices[2], psl2.compose(matrices[0], matrices[1]))
        self.assertIn("seed=0,1 structurally-forced=1", completed.stderr)
        self.assertIn("max-branch-depth=0", completed.stderr)
        self.assertIn("nodes=1", completed.stderr)

class PSLRecoveryTests(unittest.TestCase):
    def test_independent_projective_tuple_aligns_by_known_automorphism(self):
        alpha = psl2.standard_generators()
        beta = alpha
        conjugator = psl2.mcanonical((1, 0, 0, 3))
        independent = tuple(psl2.apply_automorphism(
            value, psl2.minverse(conjugator), 0) for value in alpha)
        aligned = list(projective_alignments(
            independent, beta, [], [],
            automorphism_source=[(conjugator, 0)]))
        self.assertEqual(aligned, [alpha])

    def test_intersected_singleton_couplings_recover_conjugator(self):
        rng = random.Random(9001)
        conjugator = psl2.random_element(rng, nonidentity=True)
        beta = []
        couplings = []
        for index in range(2):
            p = psl2.random_element(rng, nonidentity=True)
            q = psl2.compose(psl2.compose(psl2.minverse(conjugator), p), conjugator)
            beta.extend((p, q))
            couplings.append({"V": [2 * index], "u": [0], "W": [2 * index + 1]})
        recovered, stats = recover_alpha_psl(
            beta, couplings, [], d=1,
            require_generation=False, stop_after=None)
        recovered_matrices = {
            psl2.matrix_from_permutation(candidate[0]) for candidate in recovered
        }
        self.assertIn(conjugator, recovered_matrices)
        self.assertLessEqual(stats.generator_domain_sizes[0], 344)
        self.assertLessEqual(stats.cartesian_size, 344)


if __name__ == "__main__":
    unittest.main()
