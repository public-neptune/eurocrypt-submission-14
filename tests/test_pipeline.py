#!/usr/bin/env python3
import contextlib
import gzip
import io
import json
import itertools
import os
import random
import signal
import subprocess
import sys
import tempfile
import time
import types
import unittest
from unittest import mock

from check_solution import (check_instance_symmetric_native,
                            generators_from_solution)
from reconstruct import (BackendFailure, _drain_candidate_stdout,
                         _parse_psl_candidate,
                         _run_verifier, _stop_psl_jobs, _verifier_result,
                         cancelled_shortest, check_complete_symmetric_rules,
                         infer_dimension, prepare_inputs,
                         permutation_force_chain, solve_tuple,
                         whole_permutation_portfolio)
from permutation_group import compose, invert, schreier_sims_order, word_perm
from recover_coupled import symmetric_alignments
import psl2_343 as psl2


class PipelineTests(unittest.TestCase):
    def run_symmetric_flat(self, n, d, relations, *options):
        executable = os.path.join("build", "henbane")
        if not os.path.exists(executable):
            self.skipTest("native symmetric solver is not built")
        with tempfile.NamedTemporaryFile("w", suffix=".flat", delete=False) as flat:
            path = flat.name
            flat.write(f"{n} {d} {len(relations)}\n")
            for left, right in relations:
                flat.write(f"{len(left)} {' '.join(map(str, left))} "
                           f"{len(right)} {' '.join(map(str, right))}\n")
        try:
            return subprocess.run(
                [executable, path, "-w", "1", *options],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False)
        finally:
            os.unlink(path)

    def symmetric_solver_args(self, exhaustive=True):
        return types.SimpleNamespace(
            max_rules=100, max_total=18, closure="unused",
            cache_dir=None, target="symmetric", workers=1, budget=10,
            exhaustive=exhaustive,
            henbane=os.path.join("build", "henbane"),
            henbane_symmetric_verify=os.path.join(
                "build", "henbane-symmetric-verify"))

    def run_closure(self, rules):
        closure = os.path.join("build", "closure")
        if not os.path.exists(closure):
            self.skipTest("closure is not built")
        with tempfile.TemporaryDirectory() as directory:
            output = os.path.join(directory, "relations.flat")
            completed = subprocess.run(
                [closure, "--case", "upper",
                 "--max-emit", "24", "--out", output],
                input="".join(f'{{"{left}":"{right}"}}\n'
                              for left, right in rules),
                text=True, capture_output=True, check=True)
            relations = set()
            with open(output, encoding="utf-8") as source:
                for line in source:
                    values = list(map(int, line.split()))
                    left_len = values[0]
                    right_at = 1 + left_len
                    right_len = values[right_at]
                    left = tuple(values[1:right_at])
                    right = tuple(values[right_at + 1:right_at + 1 + right_len])
                    relations.add(tuple(sorted((left, right))))
            orders = next(
                tuple(map(int, line.split()[1:]))
                for line in completed.stderr.splitlines()
                if line.startswith("orders:"))
            return relations, orders

    def test_closure_extracts_generator_order_evidence(self):
        _, orders = self.run_closure([
            ("A", "AAAAAAAAA"),
        ])
        self.assertEqual(orders[0], 8)

    def test_matrix_candidate_protocol(self):
        matrices = psl2.standard_generators()
        line = "M " + " ".join(str(entry) for matrix in matrices
                                for entry in matrix)
        self.assertEqual(
            _parse_psl_candidate(line, len(matrices), psl2), matrices)

    def test_verifier_result_distinguishes_rejection_from_failure(self):
        passed = subprocess.CompletedProcess([], 0, "RULES PASS\n", "")
        rejected = subprocess.CompletedProcess([], 1, "RULES FAIL relation\n", "")
        self.assertEqual(_verifier_result("test", passed),
                         (True, "RULES PASS"))
        self.assertEqual(_verifier_result("test", rejected),
                         (False, "RULES FAIL relation"))
        for returncode in (2, -signal.SIGSEGV):
            failed = subprocess.CompletedProcess([], returncode, "", "failure")
            with self.subTest(returncode=returncode), \
                    self.assertRaises(BackendFailure):
                _verifier_result("test", failed)
        with self.assertRaises(BackendFailure):
            _run_verifier("test", ["/nonexistent/henbane-verifier"])

    def test_projective_driver_continues_after_downstream_rejection(self):
        first = psl2.standard_generators()
        conjugator = psl2.mcanonical((1, 0, 0, 3))
        second = tuple(psl2.apply_automorphism(
            matrix, conjugator, 0) for matrix in first)

        def line(matrices):
            return "M " + " ".join(str(entry) for matrix in matrices
                                    for entry in matrix)

        payload = (line(first) + "\n" + line(second) + "\n").encode()
        with tempfile.NamedTemporaryFile("w", delete=False) as source:
            executable = source.name
            source.write("#!/usr/bin/env python3\n")
            source.write("import os, time\n")
            source.write(f"os.write(1, {payload!r})\n")
            source.write("time.sleep(10)\n")
        os.chmod(executable, 0o755)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {}}, target)
            args = types.SimpleNamespace(
                max_rules=100, max_total=18, closure="unused",
                cache_dir=None, target="sl2_343", workers=1, budget=10,
                exhaustive=False, psl_node_limit=100,
                henbane_psl_matrix=executable, psl_candidates=16)
            seen = []

            def accept(candidate, _deadline):
                seen.append(candidate)
                return candidate if len(seen) == 2 else None

            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0, 0])):
                candidate = solve_tuple(
                    challenge, "lower", [], psl2.DEGREE, 3, args,
                    accept_candidate=accept)
        finally:
            os.unlink(challenge)
            os.unlink(executable)
        self.assertEqual(len(seen), 2)
        self.assertEqual(candidate, seen[1])

    def test_projective_backend_failure_is_not_exhaustion(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as source:
            executable = source.name
            source.write("#!/usr/bin/env python3\n")
            source.write("import sys\n")
            source.write("sys.stderr.write('STATUS EXHAUSTED\\n')\n")
            source.write("raise SystemExit(2)\n")
        os.chmod(executable, 0o755)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {}}, target)
            args = types.SimpleNamespace(
                max_rules=100, max_total=18, closure="unused",
                cache_dir=None, target="sl2_343", workers=1, budget=10,
                exhaustive=True, psl_node_limit=100,
                henbane_psl_matrix=executable, psl_candidates=16)
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0, 0])), \
                    self.assertRaises(BackendFailure):
                solve_tuple(challenge, "lower", [], psl2.DEGREE, 3, args)
        finally:
            os.unlink(challenge)
            os.unlink(executable)

    def test_dimension_uses_highest_letter_not_support_size(self):
        self.assertEqual(infer_dimension([((0, 2), (2,))], "upper"), 3)

    def test_whole_permutation_portfolio_preserves_force_chain(self):
        relations = [
            ((0, 1), (2,)),       # seeds 0,1 force 2
            ((2, 1), (3,)),       # then force 3
            ((3, 0), (4,)),       # then force 4
        ] + [((0,) * length, (1,) * length) for length in range(2, 20)]
        portfolio = whole_permutation_portfolio(relations, 5, 6)
        self.assertIsNotNone(portfolio)
        self.assertLessEqual(len(portfolio), 6)
        self.assertIsNotNone(permutation_force_chain(portfolio, 5, (0, 1)))

    def test_force_chain_rejects_repeated_unknown(self):
        relations = [((0, 2), (2, 1))]
        self.assertIsNone(permutation_force_chain(relations, 3, (0, 1)))

    def test_whole_permutation_portfolio_survives_without_force_chain(self):
        relations = [((0, 2), (2, 0)), ((1, 2), (2, 1))]
        self.assertTrue(whole_permutation_portfolio(relations, 3, 10))
        for seeds in ((0, 1), (0, 2), (1, 2)):
            self.assertIsNone(permutation_force_chain(relations, 3, seeds))

    def test_native_symmetric_branches_when_forcing_stalls(self):
        executable = os.path.join("build", "henbane")
        if not os.path.exists(executable):
            self.skipTest("native symmetric solver is not built")
        with tempfile.NamedTemporaryFile("w", suffix=".flat", delete=False) as flat:
            path = flat.name
            flat.write("3 3 1\n2 0 2 2 2 0\n")
        try:
            completed = subprocess.run(
                [executable, path, "-w", "1", "--stop-after", "1"],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False)
        finally:
            os.unlink(path)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(len(completed.stdout.split()), 9)
        self.assertIn("fallback-decisions=1", completed.stderr)
        self.assertIn("max-branch-depth=1", completed.stderr)
        self.assertIn("STATUS CANDIDATE_LIMIT", completed.stderr)

    def test_native_symmetric_empty_portfolio_uses_complete_branching(self):
        completed = self.run_symmetric_flat(
            3, 3, [], "--stop-after", "1")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertEqual(len(completed.stdout.split()), 9)
        self.assertIn("R=0", completed.stderr)
        self.assertIn("fallback-decisions=1", completed.stderr)

    def test_native_symmetric_node_cap_is_inconclusive(self):
        completed = self.run_symmetric_flat(
            3, 3, [((0, 2), (2, 0))], "-b", "1", "--all-candidates")
        self.assertEqual(completed.returncode, 3, completed.stderr)
        self.assertIn("STATUS INCONCLUSIVE", completed.stderr)
        self.assertNotIn("STATUS EXHAUSTED", completed.stderr)

    def test_native_symmetric_candidate_then_cap_is_inconclusive(self):
        completed = self.run_symmetric_flat(
            3, 1, [], "-b", "1", "--all-candidates")
        self.assertTrue(completed.stdout.strip())
        self.assertEqual(completed.returncode, 3, completed.stderr)
        self.assertIn("STATUS INCONCLUSIVE", completed.stderr)

    def test_native_symmetric_stream_continues_past_nongenerating_candidate(self):
        executable = os.path.join("build", "henbane")
        if not os.path.exists(executable):
            self.skipTest("native symmetric solver is not built")
        with tempfile.NamedTemporaryFile("w", suffix=".flat", delete=False) as flat:
            path = flat.name
            flat.write("3 3 1\n2 0 2 2 2 0\n")
        try:
            completed = subprocess.run(
                [executable, path, "-w", "1", "--stop-after", "50"],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                check=False)
        finally:
            os.unlink(path)
        tuples = []
        for line in completed.stdout.splitlines():
            raw = list(map(int, line.split()))
            tuples.append([raw[index:index + 3] for index in range(0, 9, 3)])
        self.assertGreater(len(tuples), 1, completed.stderr)
        generating = [schreier_sims_order(value, 3) == 6 for value in tuples]
        self.assertFalse(generating[0])
        self.assertIn(True, generating[1:])

    def test_native_symmetric_fallback_matches_bruteforce_orbits(self):
        relations = [((0, 2), (2, 0))]
        completed = self.run_symmetric_flat(
            3, 3, relations, "--all-candidates")
        self.assertEqual(completed.returncode, 0, completed.stderr)

        permutations = list(itertools.permutations(range(3)))

        def canonical_orbit(value):
            images = []
            for coordinate_change in permutations:
                inverse_change = invert(coordinate_change)
                images.append(tuple(
                    tuple(compose(compose(inverse_change, generator),
                                  coordinate_change))
                    for generator in value))
            return min(images)

        brute = set()
        for value in itertools.product(permutations, repeat=3):
            if all(word_perm(left, value, 3) == word_perm(right, value, 3)
                   for left, right in relations):
                brute.add(canonical_orbit(value))

        observed = set()
        for line in completed.stdout.splitlines():
            raw = list(map(int, line.split()))
            value = tuple(tuple(raw[index:index + 3])
                          for index in range(0, 9, 3))
            self.assertTrue(all(
                word_perm(left, value, 3) == word_perm(right, value, 3)
                for left, right in relations))
            observed.add(canonical_orbit(value))
        self.assertEqual(observed, brute)
        stats = next(line for line in completed.stderr.splitlines()
                     if line.startswith("STATS "))
        nodes = int(next(field.split("=", 1)[1] for field in stats.split()
                         if field.startswith("nodes=")))
        self.assertLessEqual(nodes, 11 * (1 + 6))
        self.assertIn("max-branch-depth=1", stats)

    def test_native_symmetric_random_tiny_presentations_match_bruteforce(self):
        rng = random.Random(0xBADC0DE)
        permutations = list(itertools.permutations(range(3)))
        words = [word for length in range(5)
                 for word in itertools.product(range(3), repeat=length)]

        def canonical_orbit(value):
            return min(tuple(
                tuple(compose(compose(invert(change), generator), change))
                for generator in value) for change in permutations)

        for _case in range(6):
            secret = tuple(rng.choice(permutations) for _ in range(3))
            buckets = {}
            for word in words:
                buckets.setdefault(tuple(word_perm(word, secret, 3)), []).append(word)
            choices = [bucket for bucket in buckets.values() if len(bucket) >= 2]
            relations = []
            while len(relations) < 3:
                left, right = rng.sample(rng.choice(choices), 2)
                relation = (left, right)
                if relation not in relations:
                    relations.append(relation)

            completed = self.run_symmetric_flat(
                3, 3, relations, "--all-candidates")
            self.assertEqual(completed.returncode, 0, completed.stderr)

            brute = set()
            for value in itertools.product(permutations, repeat=3):
                if all(word_perm(left, value, 3) ==
                       word_perm(right, value, 3)
                       for left, right in relations):
                    brute.add(canonical_orbit(value))

            observed = set()
            for line in completed.stdout.splitlines():
                raw = list(map(int, line.split()))
                value = tuple(tuple(raw[index:index + 3])
                              for index in range(0, 9, 3))
                observed.add(canonical_orbit(value))
            self.assertEqual(observed, brute, relations)

    def test_native_symmetric_exhaustion_can_prove_no_generating_tuple(self):
        completed = self.run_symmetric_flat(
            3, 2, [((0,), (1,))], "--all-candidates")
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("STATUS EXHAUSTED", completed.stderr)
        for line in completed.stdout.splitlines():
            raw = list(map(int, line.split()))
            value = [raw[:3], raw[3:]]
            self.assertNotEqual(schreier_sims_order(value, 3), 6)

    def test_exhaustive_driver_continues_after_complete_corpus_rejection(self):
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {"aa": "", "bbb": ""}},
                          target, indent=2)
            diagnostics = io.StringIO()
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0])), \
                    contextlib.redirect_stderr(diagnostics):
                candidate = solve_tuple(
                    challenge, "lower", [((0, 0), ())], 3, 2,
                    self.symmetric_solver_args())
        finally:
            os.unlink(challenge)
        self.assertIsNotNone(candidate, diagnostics.getvalue())
        self.assertIn("rejected by complete corpus", diagnostics.getvalue())
        self.assertEqual(word_perm((1, 1, 1), candidate, 3), list(range(3)))

    def test_exhaustive_driver_reports_no_generating_solution(self):
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {"a": "b"}}, target, indent=2)
            diagnostics = io.StringIO()
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0])), \
                    contextlib.redirect_stderr(diagnostics):
                candidate = solve_tuple(
                    challenge, "lower", [((0,), (1,))], 3, 2,
                    self.symmetric_solver_args())
        finally:
            os.unlink(challenge)
        self.assertIsNone(candidate)
        self.assertIn("EXHAUSTED", diagnostics.getvalue())

    def test_symmetric_driver_continues_after_downstream_rejection(self):
        first = "1 0 2 1 2 0"
        second = "2 1 0 1 2 0"
        payload = (first + "\n" + second + "\n").encode()
        with tempfile.NamedTemporaryFile("w", delete=False) as source:
            executable = source.name
            source.write("#!/usr/bin/env python3\n")
            source.write("import os, time\n")
            source.write(f"os.write(1, {payload!r})\n")
            source.write("time.sleep(10)\n")
        os.chmod(executable, 0o755)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {}}, target)
            args = self.symmetric_solver_args(exhaustive=False)
            args.henbane = executable
            seen = []

            def accept(candidate, _deadline):
                seen.append(candidate)
                return candidate if len(seen) == 2 else None

            started = time.monotonic()
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0])):
                candidate = solve_tuple(
                    challenge, "lower", [], 3, 2, args,
                    accept_candidate=accept)
            elapsed = time.monotonic() - started
        finally:
            os.unlink(challenge)
            os.unlink(executable)
        self.assertEqual(len(seen), 2)
        self.assertEqual(candidate, seen[1])
        self.assertLess(elapsed, 3)

    def test_symmetric_backend_failure_is_not_exhaustion(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as source:
            executable = source.name
            source.write("#!/usr/bin/env python3\n")
            source.write("raise SystemExit(2)\n")
        os.chmod(executable, 0o755)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {}}, target)
            args = self.symmetric_solver_args()
            args.henbane = executable
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0])), \
                    self.assertRaises(BackendFailure):
                solve_tuple(challenge, "lower", [], 3, 2, args)
        finally:
            os.unlink(challenge)
            os.unlink(executable)

    def test_symmetric_cleanup_respects_global_deadline(self):
        with tempfile.NamedTemporaryFile("w", delete=False) as source:
            executable = source.name
            source.write("#!/usr/bin/env python3\n")
            source.write("import signal, time\n")
            source.write("signal.signal(signal.SIGTERM, signal.SIG_IGN)\n")
            source.write("time.sleep(30)\n")
        os.chmod(executable, 0o755)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {}}, target)
            args = self.symmetric_solver_args(exhaustive=False)
            args.budget = 1
            args.henbane = executable
            started = time.monotonic()
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0])):
                candidate = solve_tuple(
                    challenge, "lower", [], 3, 2, args)
            elapsed = time.monotonic() - started
        finally:
            os.unlink(challenge)
            os.unlink(executable)
        self.assertIsNone(candidate)
        self.assertLess(elapsed, 1.5)

    def test_budget_interrupts_downstream_callback(self):
        payload = b"1 0 2 1 2 0\n"
        with tempfile.NamedTemporaryFile("w", delete=False) as source:
            executable = source.name
            source.write("#!/usr/bin/env python3\n")
            source.write("import os, time\n")
            source.write(f"os.write(1, {payload!r})\n")
            source.write("time.sleep(10)\n")
        os.chmod(executable, 0o755)
        with tempfile.NamedTemporaryFile(suffix=".json.gz", delete=False) as out:
            challenge = out.name
        try:
            with gzip.open(challenge, "wt") as target:
                json.dump({"challenge": [], "zeros": [], "ones": [],
                           "rules": {}}, target)
            args = self.symmetric_solver_args(exhaustive=False)
            args.budget = 1
            args.henbane = executable

            def accept(candidate, _deadline):
                time.sleep(2)
                return candidate

            started = time.monotonic()
            with mock.patch("reconstruct.closure_relations",
                            return_value=([], [0, 0])):
                candidate = solve_tuple(
                    challenge, "lower", [], 3, 2, args,
                    accept_candidate=accept)
            elapsed = time.monotonic() - started
        finally:
            os.unlink(challenge)
            os.unlink(executable)
        self.assertIsNone(candidate)
        self.assertLess(elapsed, 1.5)

    def test_native_symmetric_rules_only_case_verification(self):
        executable = os.path.join("build", "henbane-symmetric-verify")
        if not os.path.exists(executable):
            self.skipTest("native symmetric verifier is not built")
        challenge = "challenges/chal_semi_direct_s7_n2.json.gz"
        if not os.path.exists(challenge):
            self.skipTest("symmetric challenge data has not been downloaded")
        with open("challenges/solutions/chal_semi_direct_s7_n2.solution.json") as source:
            solution = json.load(source)
        beta = solution["tuple"]["beta_uppercase"]
        candidate = [beta[letter] for letter in sorted(beta)]
        passed, detail = check_complete_symmetric_rules(
            challenge, candidate, 7, "upper", executable)
        self.assertTrue(passed, detail)

    def test_independent_symmetric_copies_align_by_automorphism(self):
        transposition = (1, 0, 2)
        three_cycle = (1, 2, 0)
        alpha = [transposition, three_cycle]
        beta = [transposition, three_cycle]

        words = [word for length in range(5)
                 for word in itertools.product(range(2), repeat=length)]
        couplings = []
        for generator, value in enumerate(alpha):
            for beta_generator in range(2):
                left = compose(beta[beta_generator], value)
                target = next(word for word in words
                              if compose(value, word_perm(word, beta, 3)) == left)
                couplings.append({"V": [beta_generator], "u": [generator],
                                  "W": list(target)})

        change = three_cycle
        change_inverse = invert(change)
        independent = [compose(compose(change, value), change_inverse)
                       for value in alpha]
        aligned = list(symmetric_alignments(
            independent, beta, couplings, relations=[]))
        self.assertEqual(aligned, [[list(value) for value in alpha]])
        impossible = [{"V": [], "u": [0], "W": [0]}]
        self.assertEqual(list(symmetric_alignments(
            independent, beta, impossible, relations=[])), [])

    def test_degree_six_inner_alignment_is_supported(self):
        identity = tuple(range(6))
        aligned = next(symmetric_alignments(
            [identity], [identity], couplings=[], relations=[]))
        self.assertEqual(aligned, [list(identity)])

    def test_native_symmetric_streaming_verifier(self):
        executable = os.path.join("build", "henbane-symmetric-verify")
        if not os.path.exists(executable):
            self.skipTest("native symmetric verifier is not built")
        challenge = "challenges/chal_s7_n2.json.gz"
        if not os.path.exists(challenge):
            self.skipTest("symmetric challenge data has not been downloaded")
        with open("challenges/solutions/chal_s7_n2.solution.json") as source:
            solution = json.load(source)
        rules, classification, labels = check_instance_symmetric_native(
            challenge, generators_from_solution(solution), 7, solution["labels"],
            executable=executable)
        self.assertTrue(rules[0], rules[1])
        self.assertTrue(classification[0], classification[1])
        self.assertEqual(labels, solution["labels"])

    def test_psl_candidate_pipe_is_drained_before_eof(self):
        read_fd, write_fd = os.pipe()
        stream = os.fdopen(read_fd, "rb", buffering=0)
        os.set_blocking(stream.fileno(), False)
        job = {"stdout": stream, "stdout_buffer": b"", "stdout_eof": False}
        try:
            os.write(write_fd, b"first candidate\npartial")
            self.assertEqual(_drain_candidate_stdout(job), ["first candidate"])
            self.assertFalse(job["stdout_eof"])
            os.write(write_fd, b" candidate\n")
            os.close(write_fd)
            write_fd = -1
            self.assertEqual(_drain_candidate_stdout(job), ["partial candidate"])
            self.assertTrue(job["stdout_eof"])
        finally:
            if write_fd >= 0:
                os.close(write_fd)
            stream.close()

    def test_matrix_job_cleanup_is_broadcast(self):
        jobs = []
        try:
            for _ in range(3):
                stderr = tempfile.TemporaryFile(mode="w+")
                process = subprocess.Popen(
                    ["sleep", "30"], stdout=subprocess.PIPE, stderr=stderr,
                    start_new_session=True)
                self.assertIsNotNone(process.stdout)
                jobs.append({"process": process, "stdout": process.stdout,
                             "stderr": stderr})
            _stop_psl_jobs(jobs, grace=0.5)
            self.assertTrue(all(job["process"].poll() is not None for job in jobs))
            jobs = []
        finally:
            if jobs:
                _stop_psl_jobs(jobs, grace=0.1)

    def test_matrix_job_cleanup_respects_global_deadline(self):
        stderr = tempfile.TemporaryFile(mode="w+")
        process = subprocess.Popen(
            [sys.executable, "-c",
             "import signal,time; "
             "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
             "print('ready', flush=True); time.sleep(30)"],
            text=True, stdout=subprocess.PIPE, stderr=stderr,
            start_new_session=True)
        self.assertIsNotNone(process.stdout)
        self.assertEqual(process.stdout.readline().strip(), "ready")
        jobs = [{"process": process, "stdout": process.stdout,
                 "stderr": stderr}]
        started = time.monotonic()
        _stop_psl_jobs(
            jobs, grace=5.0, deadline=time.monotonic() + 0.1)
        self.assertLess(time.monotonic() - started, 0.75)
        self.assertIsNotNone(process.poll())

    def test_relation_selection_cancels_common_context_before_ranking(self):
        relations = [
            ((0, 1, 2), (0, 3, 2)),
            ((1,), (3,)),
            ((4, 1, 2), (4, 3, 2)),
        ]
        self.assertEqual(cancelled_shortest(relations, 10), [((1,), (3,))])

    def test_native_production_preparation_is_cached(self):
        preprocessor = os.path.join("build", "preprocess")
        if not os.path.exists(preprocessor):
            self.skipTest("native preprocessor is not built")
        challenge = "challenges/chal_s7_n2.json.gz"
        if not os.path.exists(challenge):
            self.skipTest("symmetric challenge data has not been downloaded")
        with tempfile.TemporaryDirectory() as directory:
            cache = os.path.join(directory, "prepared.json.gz")
            first = prepare_inputs(
                challenge, preprocessor, poolcap=100, coupcap=20,
                cache_path=cache)
            self.assertFalse(first[0])
            self.assertEqual(len(first[1]), 100)
            self.assertEqual(set(first[3]), {"zeros", "ones", "challenge"})
            second = prepare_inputs(
                challenge, preprocessor, poolcap=100, coupcap=20,
                cache_path=cache)
            self.assertEqual(second, first)


if __name__ == "__main__":
    unittest.main()
