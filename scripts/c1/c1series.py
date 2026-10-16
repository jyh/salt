"""The truncated multivariate power series behind the C1 certificates.

`S = sum_j (wt j)! / prod_m j_m! * x^j` over exponent tuples `j` of length `M`,
where the m-th variable (m = 1..M) carries weight `2m`; `series_pow(M, k, wmax)`
is the coefficient table of `S^k` truncated at weight `wmax`, keyed by the tuple.

Ported from the program's original search script: only `keys_upto`, `weight`
and `series_pow` (the eigen-solve that produced the vector is not ported; the
vector is an input of the emitter). `series_pow` works over exact integers (the
coefficients of `S` are multinomials) by binary exponentiation; it is the
SECOND method the emitter checks the Miller recurrence against. Nothing here
bears on twin primes.
"""
from math import factorial


def keys_upto(M, wmax):
    """Exponent tuples `c` of length `M` with `sum_m 2m c_m <= wmax`, in the
    order of the nested loops c_1 (outermost) .. c_M (innermost) — the same
    order as `SaltC1.Cert54.keysW`."""
    out = []

    def rec(m, rem, cur):
        if m == M:
            out.append(tuple(cur))
            return
        w = 2 * (m + 1)
        for c in range(rem // w + 1):
            rec(m + 1, rem - w * c, cur + [c])

    rec(0, wmax, [])
    return out


def weight(c):
    """`sum_m 2m c_m` (m = 1..M)."""
    return sum(2 * (m + 1) * cm for m, cm in enumerate(c))


def series_pow(M, k, wmax):
    """`[x^C] S^k` for every `C` with `weight(C) <= wmax`, exact integers."""
    ks = keys_upto(M, wmax)
    S = {}
    for j in ks:
        den = 1
        for jm in j:
            den *= factorial(jm)
        S[j] = factorial(weight(j)) // den

    def mul(A, B):
        # bucket B by weight, so each a only meets the b it can multiply with
        byw = {}
        for b, vb in B.items():
            byw.setdefault(weight(b), []).append((b, vb))
        C = {}
        for a, va in A.items():
            wa = weight(a)
            for wb in range(0, wmax - wa + 1):
                for b, vb in byw.get(wb, ()):
                    key = tuple(x + y for x, y in zip(a, b))
                    C[key] = C.get(key, 0) + va * vb
        return C

    result = {tuple([0] * M): 1}
    base = S
    e = k
    while e:
        if e & 1:
            result = mul(result, base)
        e >>= 1
        if e:
            base = mul(base, base)
    return result
