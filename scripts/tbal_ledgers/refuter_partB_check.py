#!/usr/bin/env python3
"""Refuter-independent check of the R7-stone truth (Part B of s0_benli_ledger.py).

Independent method: build the quadratic form matrix A[d,e] = F(lcm(d,e)) over
squarefree d,e <= z, with F multiplicative, F(p) = (1 + chi(p) - chi(p)/p)/p.
  Q_BV    = theta_BV^T A theta_BV          (theta_d = mu(d) log(z/d)/log z)
  Q_min   = 1 / (e1^T A^{-1} e1)           (exact constrained minimum, theta_1 = 1)
No Selberg-diagonalization formula used -- pure linear algebra, so this cross-checks
the ledger's L-sum route independently.
"""
import math
import numpy as np

def spf_sieve(n):
    spf = list(range(n + 1))
    for i in range(2, int(n**0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf

def factor(n, spf):
    fs = []
    while n > 1:
        p = spf[n]
        fs.append(p)
        while n % p == 0:
            n //= p
    return fs

def run(z, chi, name):
    spf = spf_sieve(z * z + 10)
    sq = []
    for d in range(1, z + 1):
        fs = factor(d, spf)
        m = 1
        for p in fs:
            m *= p
        if m == d:  # squarefree
            sq.append(d)
    n = len(sq)
    idx = {d: i for i, d in enumerate(sq)}
    Fp = {}
    def F(m):
        v = 1.0
        for p in factor(m, spf):
            if p not in Fp:
                c = chi(p)
                Fp[p] = (1.0 + c - c / p) / p
            v *= Fp[p]
        return v
    A = np.zeros((n, n))
    for i, d in enumerate(sq):
        for j, e in enumerate(sq):
            if j < i:
                continue
            l = d * e // math.gcd(d, e)
            A[i, j] = A[j, i] = F(l)
    # theta_BV
    th = np.array([math.log(z / d) / math.log(z) * mu_cached(d, spf) for d in sq])
    th[idx[1]] = 1.0
    Q_bv = th @ A @ th
    # exact constrained minimum via A^{-1}
    e1 = np.zeros(n); e1[idx[1]] = 1.0
    sol = np.linalg.solve(A, e1)
    Q_min = 1.0 / sol[idx[1]]
    # positive-definiteness check
    eigmin = np.linalg.eigvalsh(A).min()
    print(f"z={z:5d} {name:18s}: Q_BV={Q_bv:.6f}  Q_min={Q_min:.6f}  "
          f"delta_opt={Q_bv/Q_min-1:+.4f}  eigmin={eigmin:.3e}  1/log^2z={1/math.log(z)**2:.4f}")
    return Q_bv / Q_min - 1

def mu_cached(d, spf):
    if d == 1:
        return 1
    fs = factor(d, spf)
    return (-1) ** len(fs)

chis = [("pretense chi=-1", lambda p: -1.0),
        ("worstcase chi=+1", lambda p: +1.0),
        ("chi mod 3 actual", lambda p: 0.0 if p == 3 else (1.0 if p % 3 == 1 else -1.0))]

for z in (36, 1000):
    for name, chi in chis:
        run(z, chi, name)

# The consuming-need side, recomputed independently (natural logs):
print()
for q, tag in ((3, "q=3"), (10**6, "q=1e6")):
    Q = 2.0 * q
    lQ = math.log(Q)
    u0 = min(1.0 / (4 * (1 + math.log(q))), 1.0 / (20 * lQ))
    lx = 50 * lQ + 2 * math.log(1 / u0)
    need_worst = math.log(1 / 32) - 0.1 * lx            # beta0-sigma <= 0.1 bound (candidate)
    need_deep = math.log(1 / 32) - (0.1 - u0) * lx       # honest at beta0 = 1-u0
    z_val = math.ceil(Q * Q)
    best = 0.65 / (1.645 * math.log(z_val) ** 2)         # candidate's fitted best-case
    print(f"{tag}: u0={u0:.6f} log x={lx:.2f}  need(cand)=e^{need_worst:.1f}  "
          f"need(honest,deep-edge)=e^{need_deep:.1f}  bestBV~{best:.3e}=e^{math.log(best):.1f}  "
          f"deficit(cand)=e^{math.log(best)-need_worst:.1f}  deficit(honest)=e^{math.log(best)-need_deep:.1f}")
