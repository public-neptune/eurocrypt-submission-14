#!/usr/bin/env python3
"""Recover the first-copy tuple alpha from the given couplings.

Each coupling V u = u W states that alpha(u) conjugates beta(V) to beta(W).
Propagating those constraints pins every alpha generator to a small domain,
and the surviving Cartesian product is filtered by the A-relations and target
generation. The PSL path constructs conjugator cosets algebraically inside
PSL(2,343), rather than enumerating symmetric-group cycle matchings.
"""
from __future__ import annotations

import itertools
import math
from collections import Counter
from dataclasses import dataclass
from typing import Iterable, Iterator, Sequence

from permutation_group import compose, invert, schreier_sims_order, word_perm

Perm = tuple[int, ...]

class CouplingRecoveryError(RuntimeError):
    pass

class DomainTooLarge(CouplingRecoveryError):
    pass

class CandidateSpaceTooLarge(CouplingRecoveryError):

    pass

def _as_perm(p: Sequence[int]) -> Perm:
    return tuple(p)

def cycle_decomposition(p: Sequence[int]) -> dict[int, list[tuple[int, ...]]]:
    n = len(p)
    seen = [False] * n
    result: dict[int, list[tuple[int, ...]]] = {}
    for start in range(n):
        if seen[start]:
            continue
        cyc = []
        x = start
        while not seen[x]:
            seen[x] = True
            cyc.append(x)
            x = p[x]
        result.setdefault(len(cyc), []).append(tuple(cyc))
    return result

def cycle_type(p: Sequence[int]) -> tuple[int, ...]:
    groups = cycle_decomposition(p)
    return tuple(sorted(length for length, cs in groups.items() for _ in cs))

def centralizer_size(p: Sequence[int]) -> int:
    multiplicities = Counter(cycle_type(p))
    result = 1
    for length, count in multiplicities.items():
        result *= length ** count * math.factorial(count)
    return result

def conjugators(p: Sequence[int], q: Sequence[int], *,
                max_domain: int = 200_000) -> Iterator[Perm]:
    p = _as_perm(p)
    q = _as_perm(q)
    if len(p) != len(q):
        return
    pg = cycle_decomposition(p)
    qg = cycle_decomposition(q)
    if {k: len(v) for k, v in pg.items()} != {k: len(v) for k, v in qg.items()}:
        return
    size = centralizer_size(p)
    if size > max_domain:
        raise DomainTooLarge(
            f"conjugator domain has {size:,} elements (limit {max_domain:,})")

    source_cycles = []
    targets: dict[int, list[tuple[int, ...]]] = {}
    for length in sorted(pg):
        source_cycles.extend(pg[length])
        targets[length] = qg[length]

    n = len(p)
    image = [-1] * n
    used: dict[int, set[int]] = {length: set() for length in targets}

    def visit(index: int) -> Iterator[Perm]:
        if index == len(source_cycles):
            c = tuple(image)

            assert tuple(compose(p, c)) == tuple(compose(c, q))
            yield c
            return
        src = source_cycles[index]
        length = len(src)
        for target_index, dst in enumerate(targets[length]):
            if target_index in used[length]:
                continue
            used[length].add(target_index)
            for phase in range(length):
                for k, x in enumerate(src):
                    image[x] = dst[(k + phase) % length]
                yield from visit(index + 1)
            used[length].remove(target_index)

    yield from visit(0)

def conjugator_domain(p: Sequence[int], q: Sequence[int], *,
                      max_domain: int = 200_000) -> set[Perm]:
    return set(conjugators(p, q, max_domain=max_domain))

def _intersect(old: set[Perm] | None, new: set[Perm]) -> tuple[set[Perm], bool]:
    value = new if old is None else old & new
    return value, old is None or value != old

def _product(a: Perm, b: Perm) -> Perm:
    return tuple(compose(a, b))

def _inverse(a: Perm) -> Perm:
    return tuple(invert(a))

@dataclass
class RecoveryStats:
    coupling_domain_sizes: list[tuple[tuple[int, ...], int]]
    generator_domain_sizes: list[int | None]
    cartesian_size: int | None
    tuples_checked: int = 0

def _coupling_domains(beta: Sequence[Sequence[int]], couplings: Sequence[dict],
                      max_domain: int) -> tuple[list[tuple[tuple[int, ...], set[Perm]]],
                                                list[tuple[tuple[int, ...], int]]]:
    constraints = []
    sizes = []
    for cp in couplings:
        u = tuple(cp["u"])
        p = word_perm(cp["V"], beta, len(beta[0]))
        q = word_perm(cp["W"], beta, len(beta[0]))
        domain = conjugator_domain(p, q, max_domain=max_domain)
        if not domain:
            return [], [(u, 0)]
        constraints.append((u, domain))
        sizes.append((u, len(domain)))
    return constraints, sizes

def _propagate_short_constraints(
    d: int,
    constraints: Sequence[tuple[tuple[int, ...], set[Perm]]],
    max_domain: int,
    max_arc_work: int,
) -> list[set[Perm] | None]:
    domains: list[set[Perm] | None] = [None] * d

    for u, product_domain in constraints:
        if len(u) == 1:
            i = u[0]
            domains[i], _ = _intersect(domains[i], product_domain)
            if not domains[i]:
                return domains

    changed = True
    while changed:
        changed = False
        for u, product_domain in constraints:
            if len(u) != 2:
                continue
            i, j = u
            di, dj = domains[i], domains[j]
            if i == j:
                if di is not None:
                    keep = {x for x in di if _product(x, x) in product_domain}
                    domains[i], moved = _intersect(di, keep)
                    changed |= moved
                continue

            if di is not None:

                work = len(di) * len(product_domain)
                if work > max_arc_work:
                    raise DomainTooLarge(
                        f"binary coupling needs {work:,} arc checks "
                        f"(limit {max_arc_work:,}); retain more singleton couplings")
                supported_i: set[Perm] = set()
                possible_j: set[Perm] = set()
                for x in di:
                    xi = _inverse(x)
                    for c in product_domain:
                        y = _product(xi, c)
                        if dj is None or y in dj:
                            supported_i.add(x)
                            possible_j.add(y)
                            if len(possible_j) > max_domain:
                                raise DomainTooLarge(
                                    f"propagated generator domain exceeds "
                                    f"{max_domain:,} elements")
                domains[i], moved_i = _intersect(di, supported_i)
                domains[j], moved_j = _intersect(dj, possible_j)
                changed |= moved_i or moved_j
            elif dj is not None:

                work = len(dj) * len(product_domain)
                if work > max_arc_work:
                    raise DomainTooLarge(
                        f"binary coupling needs {work:,} arc checks "
                        f"(limit {max_arc_work:,}); retain more singleton couplings")
                possible_i: set[Perm] = set()
                supported_j: set[Perm] = set()
                for y in dj:
                    yi = _inverse(y)
                    for c in product_domain:
                        x = _product(c, yi)
                        possible_i.add(x)
                        supported_j.add(y)
                        if len(possible_i) > max_domain:
                            raise DomainTooLarge(
                                f"propagated generator domain exceeds "
                                f"{max_domain:,} elements")
                domains[i], moved_i = _intersect(di, possible_i)
                domains[j], moved_j = _intersect(dj, supported_j)
                changed |= moved_i or moved_j

            for domain in (domains[i], domains[j]):
                if domain is not None and len(domain) > max_domain:
                    raise DomainTooLarge(
                        f"propagated generator domain has {len(domain):,} elements "
                        f"(limit {max_domain:,})")
                if domain is not None and not domain:
                    return domains
    return domains

def _satisfies_couplings(alpha: Sequence[Perm], beta: Sequence[Sequence[int]],
                         couplings: Sequence[dict]) -> bool:
    n = len(beta[0])
    for cp in couplings:
        p = word_perm(cp["V"], beta, n)
        c = word_perm(cp["u"], alpha, n)
        q = word_perm(cp["W"], beta, n)
        if compose(p, c) != compose(c, q):
            return False
    return True

def _satisfies_relations(alpha: Sequence[Perm], relations: Sequence,
                         n: int) -> bool:
    for u, v in relations:
        if word_perm(u, alpha, n) != word_perm(v, alpha, n):
            return False
    return True


def symmetric_alignments(
    alpha: Sequence[Sequence[int]],
    beta: Sequence[Sequence[int]],
    couplings: Sequence[dict],
    relations: Sequence,
    *,
    stop_requested=None,
) -> Iterator[list[list[int]]]:
    """Yield inner images of ``alpha`` aligned with ``beta``.

    For S_6, outer-related tuples remain separate classes in the complete
    backend stream, so enumerating inner alignments here is still sufficient.
    """
    if not alpha or not beta or len(alpha) != len(beta):
        raise ValueError("alignment needs two nonempty tuples of equal width")
    n = len(alpha[0])
    if any(len(generator) != n for generator in itertools.chain(alpha, beta)):
        raise ValueError("alignment generators have inconsistent degrees")
    for coordinate_change in itertools.permutations(range(n)):
        if stop_requested is not None and stop_requested():
            return
        inverse_change = _inverse(coordinate_change)
        candidate = [tuple(compose(
            compose(coordinate_change, generator), inverse_change))
            for generator in alpha]
        if not _satisfies_couplings(candidate, beta, couplings):
            continue
        if not _satisfies_relations(candidate, relations, n):
            continue
        yield [list(generator) for generator in candidate]


def projective_alignments(
    alpha: Sequence[Sequence[int]],
    beta: Sequence[Sequence[int]],
    couplings: Sequence[dict],
    relations: Sequence,
    *,
    automorphism_source=None,
    stop_requested=None,
):
    """Yield PΓL automorphic images of an independently recovered PSL tuple."""
    import psl2_343 as psl2

    def as_matrix(value):
        if len(value) == 4:
            matrix = psl2.mcanonical(value)
            if not psl2.mis_psl(matrix):
                raise ValueError("alignment tuple contains a matrix outside PSL")
            return matrix
        return psl2.matrix_from_permutation(value)

    alpha_matrices = tuple(as_matrix(value) for value in alpha)
    beta_matrices = tuple(as_matrix(value) for value in beta)
    source = automorphism_source if automorphism_source is not None \
        else psl2.automorphisms()
    for conjugator, frobenius_power in source:
        if stop_requested is not None and stop_requested():
            return
        candidate = tuple(psl2.apply_automorphism(
            value, conjugator, frobenius_power) for value in alpha_matrices)
        if any(psl2.word_element(left, candidate)
               != psl2.word_element(right, candidate)
               for left, right in relations):
            continue
        valid = True
        for coupling in couplings:
            p = psl2.word_element(coupling["V"], beta_matrices)
            c = psl2.word_element(coupling["u"], candidate)
            q = psl2.word_element(coupling["W"], beta_matrices)
            if psl2.compose(p, c) != psl2.compose(c, q):
                valid = False
                break
        if valid:
            yield tuple(candidate)

def recover_alpha(
    beta: Sequence[Sequence[int]],
    couplings: Sequence[dict],
    relations: Sequence,
    *,
    d: int = 5,
    max_domain: int = 200_000,
    max_arc_work: int = 5_000_000,
    max_candidates: int = 2_000_000,
    require_generation: bool = True,
    stop_after: int | None = 1,
) -> tuple[list[list[list[int]]], RecoveryStats]:
    constraints, coupling_sizes = _coupling_domains(beta, couplings, max_domain)
    if not constraints:
        return [], RecoveryStats(coupling_sizes, [None] * d, None)
    domains = _propagate_short_constraints(
        d, constraints, max_domain, max_arc_work)
    domain_sizes = [None if x is None else len(x) for x in domains]
    if any(x is not None and not x for x in domains):
        return [], RecoveryStats(coupling_sizes, domain_sizes, 0)
    missing = [i for i, domain in enumerate(domains) if domain is None]
    if missing:
        raise CandidateSpaceTooLarge(
            f"couplings leave generator domain(s) {missing} unconstrained; "
            "retain more single- or two-letter couplings")

    cartesian_size = math.prod(len(x) for x in domains if x is not None)
    if cartesian_size > max_candidates:
        raise CandidateSpaceTooLarge(
            f"candidate Cartesian product has {cartesian_size:,} tuples "
            f"(limit {max_candidates:,}); retain more couplings")
    stats = RecoveryStats(coupling_sizes, domain_sizes, cartesian_size)

    order = sorted(range(d), key=lambda i: len(domains[i]))

    ordered_domains = [sorted(domains[i]) for i in order]
    results: list[list[list[int]]] = []
    n = len(beta[0])
    for values in itertools.product(*ordered_domains):
        alpha: list[Perm] = [tuple()] * d
        for i, value in zip(order, values):
            alpha[i] = value
        stats.tuples_checked += 1
        if not _satisfies_couplings(alpha, beta, couplings):
            continue
        if not _satisfies_relations(alpha, relations, n):
            continue
        if require_generation and schreier_sims_order(alpha, n) != math.factorial(n):
            continue
        results.append([list(row) for row in alpha])
        if stop_after is not None and len(results) >= stop_after:
            break
    return results, stats


def recover_alpha_psl(
    beta: Sequence[Sequence[int] | Sequence[Sequence[int]]],
    couplings: Sequence[dict],
    relations: Sequence,
    *,
    d: int = 5,
    max_domain: int = 1000,
    max_candidates: int = 2_000_000,
    require_generation: bool = True,
    stop_after: int | None = 1,
):
    """Recover alpha in PSL(2,343)."""
    import psl2_343 as psl2

    beta_matrices = []
    for value in beta:
        if len(value) == 4:
            matrix = psl2.mcanonical(value)  # type: ignore[arg-type]
            if not psl2.mis_psl(matrix):
                raise ValueError("beta contains a matrix outside PSL(2,343)")
        else:
            matrix = psl2.matrix_from_permutation(value)  # type: ignore[arg-type]
        beta_matrices.append(matrix)

    domains = [None] * d
    coupling_sizes = []
    singleton_couplings = sorted(
        (coupling for coupling in couplings if len(coupling["u"]) == 1),
        key=lambda coupling: len(coupling["V"]) + len(coupling["W"]))
    for coupling in singleton_couplings:
        word = tuple(coupling["u"])
        generator = word[0]
        if domains[generator] is not None and len(domains[generator]) == 1:
            continue
        p = psl2.word_element(coupling["V"], beta_matrices)
        q = psl2.word_element(coupling["W"], beta_matrices)
        if p == psl2.IDENTITY and q == psl2.IDENTITY:
            coupling_sizes.append((word, psl2.GROUP_ORDER))
            continue
        try:
            domain = set(psl2.conjugators(p, q, max_domain=max_domain))
        except ValueError as error:
            raise DomainTooLarge(str(error)) from error
        coupling_sizes.append((word, len(domain)))
        if not domain:
            return [], RecoveryStats(coupling_sizes, [None] * d, 0)
        domains[generator], _ = _intersect(domains[generator], domain)
        if not domains[generator]:
            return [], RecoveryStats(coupling_sizes,
                                     [None if value is None else len(value)
                                      for value in domains], 0)
    domain_sizes = [None if domain is None else len(domain) for domain in domains]
    missing = [i for i, domain in enumerate(domains) if domain is None]
    if missing:
        raise CandidateSpaceTooLarge(
            f"PSL singleton couplings leave generator domain(s) {missing} unconstrained")
    cartesian_size = math.prod(len(domain) for domain in domains if domain is not None)
    if cartesian_size > max_candidates:
        raise CandidateSpaceTooLarge(
            f"PSL candidate product has {cartesian_size:,} tuples "
            f"(limit {max_candidates:,})")
    stats = RecoveryStats(coupling_sizes, domain_sizes, cartesian_size)
    order = sorted(range(d), key=lambda i: len(domains[i]))
    ordered_domains = [sorted(domains[i]) for i in order]
    results = []
    for values in itertools.product(*ordered_domains):
        alpha = [psl2.IDENTITY] * d
        for i, value in zip(order, values):
            alpha[i] = value
        stats.tuples_checked += 1
        valid = True
        for coupling in couplings:
            p = psl2.word_element(coupling["V"], beta_matrices)
            c = psl2.word_element(coupling["u"], alpha)
            q = psl2.word_element(coupling["W"], beta_matrices)
            if psl2.compose(p, c) != psl2.compose(c, q):
                valid = False; break
        if not valid:
            continue
        if any(psl2.word_element(left, alpha) != psl2.word_element(right, alpha)
               for left, right in relations):
            continue
        permutations = [psl2.permutation(matrix) for matrix in alpha]
        if require_generation and schreier_sims_order(
                permutations, psl2.DEGREE) != psl2.GROUP_ORDER:
            continue
        results.append([list(row) for row in permutations])
        if stop_after is not None and len(results) >= stop_after:
            break
    return results, stats
