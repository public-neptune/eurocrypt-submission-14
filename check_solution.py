#!/usr/bin/env python3
"""Verify a recovered tuple against an instance.

Runs four independent checks and only exits 0 if all of them pass:

  1. every generator row is a permutation of {0, ..., n-1};
  2. the generators generate the declared target;
  3. every given rule u = v holds under the recovered generators;
  4. the labelled-word split is exact. SL challenges require evaluation to I
     and -I; both verifiers stream the instance without loading the full JSON.

A word is evaluated left to right with lowercase letters read as the first-copy
generators and uppercase letters as the second-copy generators, so the same
routine covers the single-copy and semidirect cases and the combined map
f(uV) = alpha(u) beta(V).

    python3 check_solution.py challenges/chal_s7_n2.json.gz \
            challenges/solutions/chal_s7_n2.solution.json
"""
import argparse
import gzip
import json
import math
import os
import subprocess
import sys

from sympy.combinatorics import Permutation, PermutationGroup

import psl2_343 as psl2

HERE = os.path.dirname(os.path.abspath(__file__))


def load_json(path):
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as f:
        return json.load(f)


def generators_from_solution(sol):
    """Map each letter to its permutation; lowercase = copy A, uppercase = copy B."""
    t = sol["tuple"]
    gen = {}
    for field in ("generators", "alpha_lowercase", "beta_uppercase"):
        for letter, perm in t.get(field, {}).items():
            gen[letter] = list(perm)
    return gen


def is_symmetric(gen_perms, n):
    group = PermutationGroup([Permutation(p) for p in gen_perms])
    return group.order() == math.factorial(n)


def check_permutations(gen, n):
    for letter, p in sorted(gen.items()):
        if sorted(p) != list(range(n)):
            return False, f"generator {letter} is not a permutation of 0..{n - 1}"
    return True, f"{len(gen)} generators are valid permutations of 0..{n - 1}"


def check_generation(gen, n):
    lower = [p for c, p in gen.items() if c.islower()]
    upper = [p for c, p in gen.items() if c.isupper()]
    if lower and not is_symmetric(lower, n):
        return False, "lowercase copy does not generate S_n"
    if upper and not is_symmetric(upper, n):
        return False, "uppercase copy does not generate S_n"
    which = "both copies" if lower and upper else "the tuple"
    return True, f"{which} generate S_{n}"


def psl_matrices(gen):
    matrices = {}
    for letter, permutation in gen.items():
        try:
            matrices[letter] = psl2.matrix_from_permutation(permutation)
        except ValueError as error:
            return None, f"generator {letter} is not in standard PSL(2,343): {error}"
    return matrices, f"{len(matrices)} generators are Möbius maps in PSL(2,343)"


def sl_matrices_from_solution(sol, projective_matrices):
    payload = sol.get("sl2_343", {})
    raw = payload.get("generators")
    if not isinstance(raw, dict):
        return None, "solution has no exact SL generator lifts"
    if set(raw) != set(projective_matrices):
        return None, "SL lift letters do not match the projective tuple"
    matrices = {}
    for letter, values in raw.items():
        if (not isinstance(values, list) or len(values) != 4
                or any(not isinstance(value, int) or value < 0 or value >= psl2.Q
                       for value in values)):
            return None, f"SL lift {letter} is not a four-entry GF(343) matrix"
        matrix = tuple(values)
        if psl2.mdet(matrix) != 1:
            return None, f"SL lift {letter} does not have determinant one"
        if psl2.mcanonical(matrix) != projective_matrices[letter]:
            return None, f"SL lift {letter} does not project to its recovered generator"
        matrices[letter] = matrix
    return matrices, f"{len(matrices)} exact determinant-one lifts match the quotient tuple"


def check_generation_psl(gen):
    lower = [p for c, p in gen.items() if c.islower()]
    upper = [p for c, p in gen.items() if c.isupper()]
    if not lower and not upper:
        return False, "solution contains no generators"
    for label, values in (("lowercase", lower), ("uppercase", upper)):
        if not values:
            continue
        order = PermutationGroup([Permutation(p) for p in values]).order()
        if order != psl2.GROUP_ORDER:
            return False, (f"{label} copy generates order {order:,}, expected "
                           f"{psl2.GROUP_ORDER:,}")
    which = "both copies" if lower and upper else "the tuple"
    return True, f"{which} generate PSL(2,343) of order {psl2.GROUP_ORDER:,}"


def check_instance_sl_native(path, matrices, expected_labels=None,
                             max_rules=None, executable=None):
    """Check exact SL rules/labels with the independent native streamer."""
    executable = executable or os.path.join(
        HERE, "build", "henbane-sl-verify")
    if not os.path.isfile(executable) or not os.access(executable, os.X_OK):
        detail = f"native SL verifier is unavailable at {executable!r}; run 'make'"
        return (False, detail), (False, detail), None

    command = [executable, path]
    for letter, matrix in sorted(matrices.items()):
        command += ["-g", letter, *map(str, matrix)]
    if expected_labels is not None:
        command += ["--labels", expected_labels]
    if max_rules is not None:
        command += ["--max-rules", str(max_rules)]

    completed = subprocess.run(
        command, text=True, stdout=subprocess.PIPE, check=False)
    if completed.returncode not in (0, 1):
        detail = f"native SL verifier failed with status {completed.returncode}"
        return (False, detail), (False, detail), None

    rules_line = next((line for line in completed.stdout.splitlines()
                       if line.startswith("RULES ")), None)
    class_line = next((line for line in completed.stdout.splitlines()
                       if line.startswith("CLASSIFICATION ")), None)
    labels_line = next((line for line in completed.stdout.splitlines()
                        if line.startswith("LABELS ")), None)
    if rules_line is None or class_line is None:
        detail = "native SL verifier returned an incomplete result"
        return (False, detail), (False, detail), None

    def result(line, prefix):
        payload = line[len(prefix):]
        passed = payload.startswith("PASS ")
        detail = payload[5:] if passed else payload[5:] if payload.startswith(
            "FAIL ") else payload
        return passed, detail

    labels = labels_line[len("LABELS "):] if labels_line else expected_labels
    return (result(rules_line, "RULES "),
            result(class_line, "CLASSIFICATION "), labels)


def check_instance_symmetric_native(path, gen, n, expected_labels=None,
                                    max_rules=None, executable=None):
    """Stream rules and labelled words through the native S_n verifier."""
    executable = executable or os.path.join(
        HERE, "build", "henbane-symmetric-verify")
    if not os.path.isfile(executable) or not os.access(executable, os.X_OK):
        detail = (f"native symmetric verifier is unavailable at {executable!r}; "
                  "run 'make'")
        return (False, detail), (False, detail), None
    command = [executable, path, "-n", str(n)]
    for letter, permutation in sorted(gen.items()):
        command += ["-g", letter, *map(str, permutation)]
    if expected_labels is not None:
        command += ["--labels", expected_labels]
    if max_rules is not None:
        command += ["--max-rules", str(max_rules)]
    completed = subprocess.run(
        command, text=True, stdout=subprocess.PIPE, check=False)
    if completed.returncode not in (0, 1):
        detail = f"native symmetric verifier failed with status {completed.returncode}"
        return (False, detail), (False, detail), None
    rules_line = next((line for line in completed.stdout.splitlines()
                       if line.startswith("RULES ")), None)
    class_line = next((line for line in completed.stdout.splitlines()
                       if line.startswith("CLASSIFICATION ")), None)
    labels_line = next((line for line in completed.stdout.splitlines()
                        if line.startswith("LABELS ")), None)
    if rules_line is None or class_line is None:
        detail = "native symmetric verifier returned an incomplete result"
        return (False, detail), (False, detail), None

    def result(line, prefix):
        payload = line[len(prefix):]
        passed = payload.startswith("PASS ")
        detail = payload[5:] if passed or payload.startswith("FAIL ") else payload
        return passed, detail

    labels = labels_line[len("LABELS "):] if labels_line else expected_labels
    return (result(rules_line, "RULES "),
            result(class_line, "CLASSIFICATION "), labels)


def main():
    ap = argparse.ArgumentParser(description="check a recovered tuple")
    ap.add_argument("challenge", help="challenge .json or .json.gz")
    ap.add_argument("solution", help="solution .json with the recovered tuple")
    args = ap.parse_args()

    sol = load_json(args.solution)
    gen = generators_from_solution(sol)
    n = sol.get("n") or len(next(iter(gen.values())))
    target = sol.get("target", "sl2_343" if "sl2_343" in sol else "symmetric")
    if target not in ("symmetric", "sl2_343"):
        ap.error(f"unsupported solution target {target!r}")
    if target == "sl2_343" and n != psl2.DEGREE:
        ap.error(f"the SL quotient action has degree {psl2.DEGREE}, not {n}")

    if target == "sl2_343":
        ok = True
        basic = [("permutations", check_permutations(gen, n))]
        matrices, membership_detail = psl_matrices(gen)
        basic.append(("PSL quotient membership",
                      (matrices is not None, membership_detail)))
        lifts = None
        if matrices is not None:
            basic.append(("quotient generation", check_generation_psl(gen)))
            lifts, lift_detail = sl_matrices_from_solution(sol, matrices)
            basic.append(("SL lifts", (lifts is not None, lift_detail)))
        for name, (passed, detail) in basic:
            print(f"[{'PASS' if passed else 'FAIL'}] {name}: {detail}")
            ok = ok and passed
        if lifts is not None:
            rules_result, classification_result, _labels = check_instance_sl_native(
                args.challenge, lifts, sol.get("labels"))
            for name, (passed, detail) in (
                    ("SL rules", rules_result),
                    ("central classification", classification_result)):
                print(f"[{'PASS' if passed else 'FAIL'}] {name}: {detail}")
                ok = ok and passed
        print("RESULT:", "genuine solution" if ok else "INVALID")
        sys.exit(0 if ok else 1)

    if target == "symmetric":
        ok = True
        for name, (passed, detail) in (
                ("permutations", check_permutations(gen, n)),
                ("generation", check_generation(gen, n))):
            print(f"[{'PASS' if passed else 'FAIL'}] {name}: {detail}")
            ok = ok and passed
        rules_result, classification_result, _labels = \
            check_instance_symmetric_native(
                args.challenge, gen, n, sol.get("labels"))
        for name, (passed, detail) in (
                ("rules", rules_result),
                ("classification", classification_result)):
            print(f"[{'PASS' if passed else 'FAIL'}] {name}: {detail}")
            ok = ok and passed
        print("RESULT:", "genuine solution" if ok else "NOT a valid solution")
        sys.exit(0 if ok else 1)

    ap.error(f"unsupported solution target {target!r}")


if __name__ == "__main__":
    main()
