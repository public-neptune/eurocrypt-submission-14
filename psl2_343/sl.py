"""Exact SL(2,343) lifts of the projective PSL backend.

The relation search only needs the faithful projective action, so it recovers
generators in PSL(2,343).  An SL generator above a recovered projective
generator has exactly two possible lifts, differing by the central matrix
``-I``.  This module normalizes one determinant-one lift per generator and
recovers those remaining sign bits by linear algebra over GF(2).
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Iterator, Mapping, Sequence

from . import (Field, Matrix, IDENTITY, fadd, finv, fmul, fneg, fsqrt,
               mdet, mis_psl)

SLMatrix = tuple[Field, Field, Field, Field]
NEGATIVE_IDENTITY: SLMatrix = (fneg(1), 0, 0, fneg(1))


def scalar_mul(scalar: Field, matrix: Sequence[Field]) -> SLMatrix:
    if len(matrix) != 4:
        raise ValueError("a 2x2 matrix needs four entries")
    return tuple(fmul(scalar, value) for value in matrix)  # type: ignore[return-value]


def determinant_one_lift(matrix: Matrix) -> SLMatrix:
    """Choose a deterministic determinant-one representative of a PSL map."""
    if not mis_psl(matrix):
        raise ValueError("matrix is not an element of PSL(2,343)")
    root = fsqrt(mdet(matrix))
    if root is None or root == 0:
        raise ValueError("PSL matrix determinant has no nonzero square root")
    result = scalar_mul(finv(root), matrix)
    if mdet(result) != 1:
        raise AssertionError("determinant-one normalization failed")
    return result


def negate(matrix: SLMatrix) -> SLMatrix:
    return tuple(fneg(value) for value in matrix)  # type: ignore[return-value]


def multiply(left: SLMatrix, right: SLMatrix) -> SLMatrix:
    """Ordinary, non-projectivized matrix product ``left * right``."""
    a, b, c, d = left
    e, f, g, h = right
    return (
        fadd(fmul(a, e), fmul(b, g)),
        fadd(fmul(a, f), fmul(b, h)),
        fadd(fmul(c, e), fmul(d, g)),
        fadd(fmul(c, f), fmul(d, h)),
    )


def compose(first: SLMatrix, second: SLMatrix) -> SLMatrix:
    """Apply ``first`` then ``second``, matching the solver word convention."""
    return multiply(second, first)


def word_image(word: Iterable[str], generators: Mapping[str, SLMatrix]) -> SLMatrix:
    result: SLMatrix = IDENTITY
    for letter in word:
        result = compose(result, generators[letter])
    return result


def central_bit(matrix: SLMatrix) -> int | None:
    """Return 0 for I, 1 for -I, and None for a noncentral matrix."""
    if matrix == IDENTITY:
        return 0
    if matrix == NEGATIVE_IDENTITY:
        return 1
    return None


class InconsistentLifts(ValueError):
    """The recovered projective tuple has no lift matching the SL evidence."""


class BinarySystem:
    """Small incremental row-echelon system represented by integer bitsets."""

    def __init__(self, variables: Sequence[str]):
        self.variables = tuple(variables)
        self.index = {letter: index for index, letter in enumerate(self.variables)}
        self.rows: dict[int, tuple[int, int]] = {}

    @property
    def rank(self) -> int:
        return len(self.rows)

    def parity_mask(self, left: str, right: str = "") -> int:
        mask = 0
        for letter in left + right:
            try:
                mask ^= 1 << self.index[letter]
            except KeyError as error:
                raise ValueError(f"word uses unknown generator {letter!r}") from error
        return mask

    def add(self, mask: int, value: int) -> bool:
        value &= 1
        while mask:
            pivot = mask.bit_length() - 1
            row = self.rows.get(pivot)
            if row is None:
                self.rows[pivot] = (mask, value)
                return True
            mask ^= row[0]
            value ^= row[1]
        if value:
            raise InconsistentLifts("inconsistent central-sign equations")
        return False

    def solve_unique(self) -> dict[str, int]:
        if self.rank != len(self.variables):
            raise InconsistentLifts(
                f"central signs have rank {self.rank}, need {len(self.variables)}")
        return next(self.solve_all())

    def solve_all(self) -> Iterator[dict[str, int]]:
        """Enumerate the affine solution space."""
        pivots = set(self.rows)
        free = [index for index in range(len(self.variables))
                if index not in pivots]
        for choice in range(1 << len(free)):
            solution = 0
            for bit, index in enumerate(free):
                if (choice >> bit) & 1:
                    solution |= 1 << index
            for pivot in sorted(self.rows):
                mask, value = self.rows[pivot]
                lower = mask & ~(1 << pivot)
                if (lower & solution).bit_count() & 1:
                    value ^= 1
                if value:
                    solution |= 1 << pivot
            yield {letter: (solution >> index) & 1
                   for index, letter in enumerate(self.variables)}


@dataclass(frozen=True)
class LiftRecovery:
    generators: dict[str, SLMatrix]
    base_generators: dict[str, SLMatrix]
    signs: dict[str, int]
    rank: int
    equations: int
    relation_equations: int
    nullity: int
    solution_count: int


def _base_discrepancy(left: str, right: str,
                      generators: Mapping[str, SLMatrix]) -> int:
    lhs = word_image(left, generators)
    rhs = word_image(right, generators)
    if lhs == rhs:
        return 0
    if lhs == negate(rhs):
        return 1
    raise InconsistentLifts(
        "a claimed SL equality does not even hold after projection to PSL")


def recover_lift_candidates(
    projective_generators: Mapping[str, Matrix],
    zero_words: Sequence[str],
    one_words: Sequence[str],
    relations: Iterable[tuple[str, str]] = (),
) -> tuple[LiftRecovery, ...]:
    """Enumerate compatible SL lifts."""
    variables = tuple(sorted(projective_generators))
    if not variables:
        raise ValueError("no projective generators were supplied")
    base = {letter: determinant_one_lift(projective_generators[letter])
            for letter in variables}
    system = BinarySystem(variables)
    equations = 0

    for expected, words in ((0, zero_words), (1, one_words)):
        for word in words:
            bit = central_bit(word_image(word, base))
            if bit is None:
                raise InconsistentLifts(
                    f"labelled word {word!r} is noncentral in the recovered quotient")
            system.add(system.parity_mask(word), expected ^ bit)
            equations += 1

    relation_equations = 0
    if system.rank < len(variables):
        for left, right in relations:
            system.add(system.parity_mask(left, right),
                       _base_discrepancy(left, right, base))
            equations += 1
            relation_equations += 1
            if system.rank == len(variables):
                break

    nullity = len(variables) - system.rank
    solution_count = 1 << nullity
    candidates = []
    for signs in system.solve_all():
        lifted = {letter: negate(base[letter]) if signs[letter] else base[letter]
                  for letter in variables}
        for expected, words in ((0, zero_words), (1, one_words)):
            for word in words:
                if central_bit(word_image(word, lifted)) != expected:
                    raise AssertionError("recovered lift fails a labelled example")
        candidates.append(LiftRecovery(
            lifted, base, signs, system.rank, equations, relation_equations,
            nullity, solution_count))
    if len(candidates) != solution_count:
        raise AssertionError("affine lift enumeration has the wrong size")
    return tuple(candidates)


def recover_lifts(
    projective_generators: Mapping[str, Matrix],
    zero_words: Sequence[str],
    one_words: Sequence[str],
    relations: Iterable[tuple[str, str]] = (),
) -> LiftRecovery:
    """Return the first compatible lift."""
    return recover_lift_candidates(
        projective_generators, zero_words, one_words, relations)[0]


def classify(words: Sequence[str], generators: Mapping[str, SLMatrix]) -> str:
    labels = []
    for index, word in enumerate(words):
        bit = central_bit(word_image(word, generators))
        if bit is None:
            raise InconsistentLifts(
                f"challenge word {index} is neither I nor -I in SL(2,343)")
        labels.append(str(bit))
    return "".join(labels)
