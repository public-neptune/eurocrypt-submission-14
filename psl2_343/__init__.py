#!/usr/bin/env python3
"""Reference arithmetic for PSL(2, 343).

The performance solver uses the same conventions, while this deliberately
small Python implementation remains independent enough to serve as a checker.

Field elements are integers ``a0 + 7*a1 + 49*a2`` representing
``a0 + a1*t + a2*t^2`` in GF(7)[t]/(t^3 - 2).  Projective matrices are
normalized by scaling their first non-zero entry to one.  Permutations and
words use Henbane's right-action convention: ``compose(f, g)`` means "apply f,
then g".
"""
from __future__ import annotations

import random
from typing import Iterable, Iterator, Sequence

P = 7
Q = 343
DEGREE = Q + 1
INF = Q
GROUP_ORDER = Q * (Q * Q - 1) // 2

Field = int
Matrix = tuple[Field, Field, Field, Field]


def _digits(a: Field) -> tuple[int, int, int]:
    return a % P, (a // P) % P, a // (P * P)


def fadd(a: Field, b: Field) -> Field:
    a0, a1, a2 = _digits(a)
    b0, b1, b2 = _digits(b)
    return ((a0 + b0) % P + P * ((a1 + b1) % P)
            + P * P * ((a2 + b2) % P))


def fneg(a: Field) -> Field:
    a0, a1, a2 = _digits(a)
    return (-a0) % P + P * ((-a1) % P) + P * P * ((-a2) % P)


def fsub(a: Field, b: Field) -> Field:
    return fadd(a, fneg(b))


def fmul(a: Field, b: Field) -> Field:
    a0, a1, a2 = _digits(a)
    b0, b1, b2 = _digits(b)
    # t^3 = 2 and t^4 = 2t.
    c0 = a0 * b0 + 2 * (a1 * b2 + a2 * b1)
    c1 = a0 * b1 + a1 * b0 + 2 * a2 * b2
    c2 = a0 * b2 + a1 * b1 + a2 * b0
    return c0 % P + P * (c1 % P) + P * P * (c2 % P)


def fpow(a: Field, exponent: int) -> Field:
    if exponent < 0:
        return fpow(finv(a), -exponent)
    result = 1
    while exponent:
        if exponent & 1:
            result = fmul(result, a)
        a = fmul(a, a)
        exponent >>= 1
    return result


def finv(a: Field) -> Field:
    if a == 0:
        raise ZeroDivisionError("zero has no inverse in GF(343)")
    return fpow(a, Q - 2)


def fdiv(a: Field, b: Field) -> Field:
    return fmul(a, finv(b))


def fis_square(a: Field) -> bool:
    return a == 0 or fpow(a, (Q - 1) // 2) == 1


def fsqrt(a: Field) -> Field | None:
    """Return a square root in GF(343), or None for a nonsquare.

    Q is 3 modulo 4, so the usual one-exponent formula applies.
    """
    if not fis_square(a):
        return None
    return fpow(a, (Q + 1) // 4)


def ffrobenius(a: Field, power: int = 1) -> Field:
    """Apply a Frobenius power."""
    value = a
    for _ in range(power % 3):
        value = fpow(value, P)
    return value


def mcanonical(m: Sequence[Field]) -> Matrix:
    if len(m) != 4 or not any(m):
        raise ValueError("a projective matrix needs four entries, not all zero")
    pivot = next(x for x in m if x)
    scale = finv(pivot)
    return tuple(fmul(scale, x) for x in m)  # type: ignore[return-value]


IDENTITY: Matrix = (1, 0, 0, 1)


def mdet(m: Matrix) -> Field:
    a, b, c, d = m
    return fsub(fmul(a, d), fmul(b, c))


def mis_invertible(m: Matrix) -> bool:
    return mdet(m) != 0


def mis_psl(m: Matrix) -> bool:
    return mis_invertible(m) and fis_square(mdet(m))


def mmul(left: Matrix, right: Matrix) -> Matrix:
    """Ordinary matrix product ``left * right`` (left acts last)."""
    a, b, c, d = left
    e, f, g, h = right
    return mcanonical((
        fadd(fmul(a, e), fmul(b, g)),
        fadd(fmul(a, f), fmul(b, h)),
        fadd(fmul(c, e), fmul(d, g)),
        fadd(fmul(c, f), fmul(d, h)),
    ))


def compose(first: Matrix, second: Matrix) -> Matrix:
    """Apply ``first`` and then ``second``, matching ``verify.compose``."""
    return mmul(second, first)


def minverse(m: Matrix) -> Matrix:
    a, b, c, d = m
    if mdet(m) == 0:
        raise ZeroDivisionError("singular projective matrix")
    return mcanonical((d, fneg(b), fneg(c), a))


def pgl_elements() -> Iterator[Matrix]:
    """Stream PGL(2,343)."""
    for b in range(Q):
        for c in range(Q):
            for d in range(Q):
                matrix = (1, b, c, d)
                if mis_invertible(matrix):
                    yield matrix
    for c in range(Q):
        for d in range(Q):
            matrix = (0, 1, c, d)
            if mis_invertible(matrix):
                yield matrix


def apply_automorphism(matrix: Matrix, conjugator: Matrix,
                       frobenius_power: int = 0) -> Matrix:
    """Apply a PΓL automorphism."""
    twisted = mcanonical(tuple(
        ffrobenius(value, frobenius_power) for value in matrix))
    return mmul(mmul(minverse(conjugator), twisted), conjugator)


def automorphisms() -> Iterator[tuple[Matrix, int]]:
    """Stream PΓL(2,343)."""
    for frobenius_power in range(3):
        for conjugator in pgl_elements():
            yield conjugator, frobenius_power


def mpow(m: Matrix, exponent: int) -> Matrix:
    if exponent < 0:
        return mpow(minverse(m), -exponent)
    result = IDENTITY
    while exponent:
        if exponent & 1:
            result = mmul(result, m)
        m = mmul(m, m)
        exponent >>= 1
    return result


def mapply(m: Matrix, point: int) -> int:
    if point < 0 or point > INF:
        raise ValueError(f"point {point} is outside P^1(GF(343))")
    a, b, c, d = m
    if point == INF:
        return INF if c == 0 else fdiv(a, c)
    den = fadd(fmul(c, point), d)
    if den == 0:
        return INF
    return fdiv(fadd(fmul(a, point), b), den)


def permutation(m: Matrix) -> tuple[int, ...]:
    if not mis_invertible(m):
        raise ValueError("singular matrix does not define a permutation")
    return tuple(mapply(m, point) for point in range(DEGREE))


def word_element(word: Iterable[int], generators: Sequence[Matrix]) -> Matrix:
    result = IDENTITY
    for letter in word:
        result = compose(result, generators[letter])
    return result


def _equation_row(source: int, target: int) -> list[Field]:
    """Linear equation on (a,b,c,d) for M(source)=target."""
    if source == INF and target == INF:
        return [0, 0, 1, 0]
    if source == INF:
        return [1, 0, fneg(target), 0]
    if target == INF:
        return [0, 0, source, 1]
    return [source, 1, fneg(fmul(target, source)), fneg(target)]


def nullspace(rows: Sequence[Sequence[Field]], columns: int) -> list[list[Field]]:
    matrix = [list(row) for row in rows]
    pivots: list[int] = []
    rank = 0
    for column in range(columns):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        scale = finv(matrix[rank][column])
        matrix[rank] = [fmul(scale, value) for value in matrix[rank]]
        for i in range(len(matrix)):
            if i == rank or matrix[i][column] == 0:
                continue
            scale = matrix[i][column]
            matrix[i] = [fsub(x, fmul(scale, y))
                         for x, y in zip(matrix[i], matrix[rank])]
        pivots.append(column)
        rank += 1
        if rank == len(matrix):
            break

    free = [column for column in range(columns) if column not in pivots]
    basis: list[list[Field]] = []
    for free_column in free:
        vector = [0] * columns
        vector[free_column] = 1
        for row_index in range(rank - 1, -1, -1):
            pivot_column = pivots[row_index]
            value = 0
            for column in free:
                value = fadd(value, fmul(matrix[row_index][column], vector[column]))
            vector[pivot_column] = fneg(value)
        basis.append(vector)
    return basis


def from_three_points(sources: Sequence[int], targets: Sequence[int], *,
                      require_psl: bool = False) -> Matrix | None:
    if len(sources) != 3 or len(targets) != 3:
        raise ValueError("exactly three source and target points are required")
    if len(set(sources)) != 3 or len(set(targets)) != 3:
        return None
    basis = nullspace([_equation_row(x, y) for x, y in zip(sources, targets)], 4)
    if len(basis) != 1:
        return None
    m = mcanonical(basis[0])
    if not mis_invertible(m) or any(mapply(m, x) != y
                                   for x, y in zip(sources, targets)):
        return None
    if require_psl and not mis_psl(m):
        return None
    return m


ELEMENT_ORDERS = (1, 2, 3, 4, 7, 9, 19, 43, 57, 86, 171, 172)


def element_order(m: Matrix) -> int:
    if not mis_psl(m):
        raise ValueError("element is not in PSL(2,343)")
    for candidate in ELEMENT_ORDERS:
        if mpow(m, candidate) == IDENTITY:
            return candidate
    raise AssertionError("PSL element has an unexpected order")


def random_element(rng: random.Random | None = None, *,
                   nonidentity: bool = False) -> Matrix:
    rng = rng or random
    while True:
        m = mcanonical(tuple(rng.randrange(Q) for _ in range(4)))
        if mis_psl(m) and (not nonidentity or m != IDENTITY):
            return m


def standard_generators() -> tuple[Matrix, Matrix, Matrix]:
    """A deterministic generating triple for the standard permutation model."""
    translation = mcanonical((1, 1, 0, 1))
    inversion = mcanonical((0, fneg(1), 1, 0))
    # 8 = t+1 has multiplicative order 342; its diagonal image has order 171.
    diagonal = mcanonical((8, 0, 0, finv(8)))
    return translation, inversion, diagonal


def matrix_from_permutation(value: Sequence[int], *, require_psl: bool = True) -> Matrix:
    if len(value) != DEGREE or sorted(value) != list(range(DEGREE)):
        raise ValueError("not a permutation of P^1(GF(343))")
    anchors = (0, 1, INF)
    m = from_three_points(anchors, [value[x] for x in anchors],
                          require_psl=require_psl)
    if m is None or permutation(m) != tuple(value):
        raise ValueError("permutation is not a Mobius transformation"
                         + (" in PSL(2,343)" if require_psl else ""))
    return m


def _linear_conjugator_rows(p: Matrix, q: Matrix, scale: Field) -> list[list[Field]]:
    """Rows for X*P = scale*Q*X in variables X=(a,b,c,d)."""
    p00, p01, p10, p11 = p
    q00, q01, q10, q11 = q
    s = scale
    # XP entries minus s*QX entries.
    return [
        [fsub(p00, fmul(s, q00)), p10, fneg(fmul(s, q01)), 0],
        [p01, fsub(p11, fmul(s, q00)), 0, fneg(fmul(s, q01))],
        [fneg(fmul(s, q10)), 0, fsub(p00, fmul(s, q11)), p10],
        [0, fneg(fmul(s, q10)), p01, fsub(p11, fmul(s, q11))],
    ]


def _projective_span(basis: Sequence[Sequence[Field]]) -> Iterator[Matrix]:
    dimension = len(basis)
    if dimension == 0:
        return
    if dimension == 1:
        yield mcanonical(basis[0])
        return
    if dimension != 2:
        raise ValueError(f"conjugator linear space has dimension {dimension}; "
                         "the constraint is not selective")
    first, second = basis
    for scalar in range(Q):
        yield mcanonical([fadd(x, fmul(scalar, y))
                          for x, y in zip(first, second)])
    yield mcanonical(second)


def conjugators(p: Matrix, q: Matrix, *, max_domain: int = 1000) -> tuple[Matrix, ...]:
    """Enumerate X in PSL satisfying compose(p,X) == compose(X,q).

    For nonidentity elements the result is empty or a coset of a centralizer
    and has at most 344 elements.  Identity/identity is intentionally rejected
    as an unselective 20-million-element constraint.
    """
    if p == IDENTITY or q == IDENTITY:
        if p != q:
            return ()
        raise ValueError("identity-to-identity conjugacy leaves all of PSL unconstrained")
    ratio = fdiv(mdet(p), mdet(q))
    root = fsqrt(ratio)
    if root is None:
        return ()
    scales = {root, fneg(root)}
    result: set[Matrix] = set()
    for scale in scales:
        basis = nullspace(_linear_conjugator_rows(p, q, scale), 4)
        try:
            candidates = _projective_span(basis)
            for x in candidates:
                if mis_psl(x) and compose(p, x) == compose(x, q):
                    result.add(x)
                    if len(result) > max_domain:
                        raise ValueError(f"conjugator domain exceeds {max_domain}")
        except ValueError:
            raise
    return tuple(sorted(result))
