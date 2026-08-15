#!/usr/bin/env python3
"""WALL-L1 positive control: the GF(2) rank check behind `blind_iff_const`.

WHAT THIS INSTRUMENT DOES, AND ON WHAT BYTES
--------------------------------------------
`Salt/Entropy/Chowla/PinDichotomy.lean` proves that inside the slot class
(`PmNormalized` + `PairCollapse`) the only twin-blind weight is the constant
one.  The Lean proof reaches that conclusion through a SPECIFIC set of
pair-correlation instances:

    the route  R(M) = {1, 2, 3, 4}  union  {p - 2 : p prime, 7 <= p <= M+2}

(the four seeds, then the descent step at every prime).  The theorem being
true is one thing; the ROUTE being sufficient is another.  This script checks
the second, computationally, over GF(2).

THE VARIABLE CONVENTION (stated here and printed in every triple below)
-----------------------------------------------------------------------
A slot-satisfying weight is completely multiplicative into {+1, -1}, so it is
determined by its values on primes.  Write

    w(p) = (-1)^(x_p)      for every prime p <= M+3
    c    = (-1)^(gamma)    the common value of the pair correlation

so the VARIABLES ARE gamma TOGETHER WITH x_p FOR EVERY PRIME p <= M+3.
(At M = 2000: pi(2003) = 304 primes, plus gamma, = 305 variables.)  Complete
multiplicativity turns w(n) into (-1)^(sum_p a_p(n) x_p) with a_p(n) = v_p(n)
mod 2, so the constraint  w(n) * w(n+2) = c  at instance n is the GF(2) linear
equation

    sum_p ( a_p(n) + a_p(n+2) ) x_p  +  gamma  =  0.

MAIN ARM: the full route.  If the rank leaves gamma pivotal and no prime
undetermined below the cutoff, the route pins every sign -- the derivation is
sufficient in the stated instances, not merely true.

MUTATION ARM (the negative control): the same computation with the n = 4 seed
DROPPED.  This must make the conclusion FALSE, not merely unreachable: the
script exhibits an explicit alternative solution, verifies it satisfies EVERY
surviving constraint, and verifies it VIOLATES the dropped n = 4 constraint.
An instrument that cannot fail proves nothing.

Usage:  python3 scripts/l1_gf2_control.py [M]        (default M = 2000)
"""

import sys


def sieve_spf(limit):
    """Smallest-prime-factor table on [0, limit]."""
    spf = list(range(limit + 1))
    i = 2
    while i * i <= limit:
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf


def primes_upto(limit, spf):
    return [n for n in range(2, limit + 1) if spf[n] == n]


def parity_mask(n, spf, index_of):
    """Bitmask of the primes dividing n to an ODD power (the GF(2) signature)."""
    mask = 0
    while n > 1:
        p = spf[n]
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e & 1:
            mask ^= 1 << index_of[p]
    return mask


def rref(rows, ncols):
    """Reduced row echelon form over GF(2).  Rows are ints (bit i = column i).

    Columns are scanned left to right; returns (reduced rows, pivot column of
    each reduced row, list of free columns).
    """
    rows = [r for r in rows if r]
    pivots = []          # pivot column per reduced row, in order
    reduced = []
    free = []
    for col in range(ncols):
        bit = 1 << col
        target = None
        for i, r in enumerate(rows):
            if r & bit:
                target = i
                break
        if target is None:
            free.append(col)
            continue
        pr = rows.pop(target)
        rows = [r ^ pr if (r & bit) else r for r in rows]
        rows = [r for r in rows if r]
        reduced = [r ^ pr if (r & bit) else r for r in reduced]
        reduced.append(pr)
        pivots.append(col)
    return reduced, pivots, free


def solve_with(reduced, pivots, free, ncols, assignment):
    """Back-substitute a nullspace vector: `assignment` fixes the free columns."""
    val = [0] * ncols
    for c in free:
        val[c] = assignment.get(c, 0)
    for row, pc in zip(reduced, pivots):
        acc = 0
        r = row ^ (1 << pc)
        c = 0
        while r:
            if r & 1:
                acc ^= val[c]
            r >>= 1
            c += 1
        val[pc] = acc
    return val


def check(vec, rows):
    """Every row must evaluate to 0 over GF(2)."""
    for row in rows:
        acc = 0
        r, c = row, 0
        while r:
            if r & 1:
                acc ^= vec[c]
            r >>= 1
            c += 1
        if acc:
            return False
    return True


def row_value(vec, row):
    acc = 0
    r, c = row, 0
    while r:
        if r & 1:
            acc ^= vec[c]
        r >>= 1
        c += 1
    return acc


def name_of(col, primes, gamma_col):
    return "gamma" if col == gamma_col else "x_%d" % primes[col]


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 2000

    var_cutoff = M + 3
    spf = sieve_spf(var_cutoff)
    primes = primes_upto(var_cutoff, spf)
    index_of = {p: i for i, p in enumerate(primes)}
    gamma_col = len(primes)
    ncols = len(primes) + 1

    seeds = [1, 2, 3, 4]
    descent = [p - 2 for p in primes if 7 <= p <= M + 2]
    route = seeds + descent

    print("=" * 74)
    print("WALL-L1 GF(2) POSITIVE CONTROL  --  scripts/l1_gf2_control.py")
    print("=" * 74)
    print("WHAT WAS READ (no file input; the instrument builds its own data):")
    print("  M (instance cutoff)            : %d" % M)
    print("  variable cutoff M+3            : %d" % var_cutoff)
    print("  VARIABLE CONVENTION            : gamma together with x_p for every")
    print("                                   prime p <= M+3   [w(p)=(-1)^x_p,")
    print("                                   c=(-1)^gamma]")
    print("  %-31s: %d" % ("primes p <= %d (= pi)" % var_cutoff, len(primes)))
    print("  variables (primes + gamma)     : %d" % ncols)
    print("  route seeds                    : %s" % seeds)
    print("  route descent {p-2 : p prime, 7 <= p <= %d}" % (M + 2))
    print("                                 : %d instances, first %s ... last %d"
          % (len(descent), descent[:4], descent[-1]))
    print("  route instances total          : %d" % len(route))
    print("  equation at instance n         : sum_p (a_p(n)+a_p(n+2)) x_p + gamma = 0")
    print("  largest index touched (max n+2): %d" % (max(route) + 2))
    print()

    def build(instances):
        return [parity_mask(n, spf, index_of) ^ parity_mask(n + 2, spf, index_of)
                ^ (1 << gamma_col) for n in instances]

    results = {}

    for arm, instances in (("MAIN", route),
                           ("MUTATION", [n for n in route if n != 4])):
        rows = build(instances)
        reduced, pivots, free = rref(rows, ncols)
        rank = len(reduced)
        gamma_pivotal = gamma_col in pivots
        # undetermined primes below the cutoff: a prime column that is free, or
        # that carries a nonzero component in some nullspace basis vector.
        basis = []
        for f in free:
            basis.append(solve_with(reduced, pivots, free, ncols, {f: 1}))
        undetermined = sorted({primes[c] for v in basis for c in range(len(primes))
                               if v[c]})
        undet_below = [p for p in undetermined if p <= M + 2]

        print("-" * 74)
        print("%s ARM   (%d instances)" % (arm, len(instances)))
        if arm == "MUTATION":
            print("  mutation applied: the n = 4 seed is DROPPED from the route")
        print("-" * 74)
        print("  TRIPLE: vars %d | rank %d | free {%s} | gamma %s | "
              "undetermined primes <= %d: %d"
              % (ncols, rank,
                 ", ".join(name_of(c, primes, gamma_col) for c in free),
                 "PIVOTAL" if gamma_pivotal else "NON-pivotal",
                 M + 2, len(undet_below)))
        if undet_below:
            print("           undetermined primes: %s%s"
                  % (undet_below[:12], " ..." if len(undet_below) > 12 else ""))
        results[arm] = dict(rows=rows, reduced=reduced, pivots=pivots, free=free,
                            rank=rank, gamma_pivotal=gamma_pivotal,
                            undet_below=undet_below)
        print()

    # ---- the exhibited alternative solution for the mutation arm ----
    mut = results["MUTATION"]
    alt = solve_with(mut["reduced"], mut["pivots"], mut["free"], ncols,
                     {gamma_col: 1})
    sign = lambda p: "+1" if alt[index_of[p]] == 0 else "-1"
    print("-" * 74)
    print("MUTATION ARM -- THE EXHIBITED ALTERNATIVE SOLUTION (gamma = 1)")
    print("-" * 74)
    print("  first signs      : w2 = %s, w3 = %s, w5 = %s, w7 = %s, w11 = %s"
          % (sign(2), sign(3), sign(5), sign(7), sign(11)))
    print("  c = (-1)^gamma   : %s" % ("-1" if alt[gamma_col] else "+1"))
    print("  nonzero x_p count: %d" % sum(alt[:len(primes)]))
    ok_mut = check(alt, mut["rows"])
    dropped_row = build([4])[0]
    violates4 = row_value(alt, dropped_row) == 1
    print("  satisfies EVERY surviving mutation constraint : %s" % ok_mut)
    print("  VIOLATES the dropped n = 4 constraint         : %s" % violates4)
    print("  => the mutation makes the conclusion FALSE (a genuine second")
    print("     solution exists), not merely unreachable by one route.")
    print()

    main_arm = results["MAIN"]
    verdict_main = (main_arm["gamma_pivotal"] and not main_arm["undet_below"])
    verdict_mut = ((not mut["gamma_pivotal"]) and ok_mut and violates4)
    print("=" * 74)
    print("VERDICT  main arm: %s   |   mutation arm: %s"
          % ("ROUTE SUFFICIENT" if verdict_main else "ROUTE INSUFFICIENT",
             "CONTROL FIRES" if verdict_mut else "CONTROL DEAD"))
    print("=" * 74)
    return 0 if (verdict_main and verdict_mut) else 1


if __name__ == "__main__":
    sys.exit(main())
