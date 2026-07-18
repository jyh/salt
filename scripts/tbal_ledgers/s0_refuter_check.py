#!/usr/bin/env python3
"""ADVERSARIAL REFUTER LEDGER — independent recomputation for the T-BAL-S0
benli-faithful redesign candidate. Everything recomputed from scratch; the
candidate's s0_benli_ledger.py NOT imported.

C1: smallest-index E-terms at q=3 and q=1e6, vs consuming budgets (1/16 each).
C3: prime-sum honest magnitudes at beta = 1-c0/L2 and beta = 9/10.
C4: x-decay exponents incl. the B=40 anchor.
C5: the (z,z^2] band priced + beyond-z^2 witness.
PartB-redo: delta_opt via EXACT rational arithmetic (z=36) and independent
  linear-algebra minimum (min over theta_1=1 of Q = 1/(F^{-1})_{11} — a
  DIFFERENT formula than the candidate's Selberg-diagonalization sum), plus
  an adversarial MINIMIZATION over chi-patterns to test whether ANY pattern
  reaches delta_opt <= e^{-13.1}.
S2-cap: the x^{1-beta0} <= e*u^{-2u} <= 5.67 claim re-derived.
"""
import math
from math import log, sqrt, exp
from fractions import Fraction
import numpy as np

C0 = 1.0 / 126848  # ZeroFreeReal.lean:604

def sieve(n):
    pr = []
    s = [True] * (n + 1)
    for i in range(2, n + 1):
        if s[i]:
            pr.append(i)
            for j in range(i * i, n + 1, i):
                s[j] = False
    return pr

PR = sieve(2 * 10 ** 6)
PRSET = set(PR)

def mu(n):
    if n == 1:
        return 1
    m, res = n, 1
    for p in PR:
        if p * p > m:
            break
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
    if m > 1:
        res = -res
    return res

def factor(n):
    fs = []
    m = n
    for p in PR:
        if p * p > m:
            break
        if m % p == 0:
            fs.append(p)
            while m % p == 0:
                m //= p
    if m > 1:
        fs.append(m)
    return fs

print("=" * 78)
print("S2-CAP CHECK: x^{1-beta0} at the deep edge, x = Q^B u^{-2}, split u<=1/(20 log Q)")
print("=" * 78)
for q in (3, 10 ** 6):
    T = 2.0
    Q = q * T
    B = 50
    u0 = min(1.0 / (4 * (1 + log(q))), 1.0 / (20 * log(Q)))
    lx = B * log(Q) + 2 * log(1 / u0)
    xu = u0 * lx
    # candidate's claimed form: e * u^{-2u} <= 5.67 ; true form e^{B/20} * u^{-2u}
    claim_form = 1 + 2 * u0 * log(1 / u0)          # log of e*u^{-2u}
    true_form = B / 20 + 2 * u0 * log(1 / u0)       # log of e^{B/20}*u^{-2u}
    print(f"q={q:>7}: u0={u0:.6f}  ACTUAL x^u0 = e^{xu:.3f} = {exp(xu):8.2f}   "
          f"claimed cap 5.67  claimed-form e^{claim_form:.3f}={exp(claim_form):.2f}  "
          f"true-form e^{true_form:.3f}={exp(true_form):.2f}")
    # worst over u in (0,u0]: max of u*lx(u) = u*(B logQ + 2 log(1/u))
    us = [u0 * k / 1000 for k in range(1, 1001)]
    worst = max(u * (B * log(Q) + 2 * log(1 / u)) for u in us)
    print(f"          sup over u<=u0 of x^u = e^{worst:.3f} = {exp(worst):.2f}")

print()
print("=" * 78)
print("C1 — E-term pricing, independent recomputation (streams s1,s2 of E_tot)")
print("E_tot = P(s)(1+||s||)(1+log x)^2 (1+2log z)^16 z^{2+2sig} x^{-sig}")
print("      + M (1+2log z)^16 z^6 (||zeta||+1/||1-s||+2) x^{-sig};  budgets 1/16")
print("=" * 78)
def eprice(q, B, sigma=0.9, T=2.0, Timfac=3.0):
    # P-factor priced at |im|<=1 (worst over T in [2,3]); Q,z,x at T (worst decay T=2)
    Q = q * T
    L2 = log(Q) + 2
    z = math.ceil(Q * Q)
    lz = log(z)
    u0 = min(1.0 / (4 * (1 + log(q))), 1.0 / (20 * log(Q)))
    lx = B * log(Q) + 2 * log(1 / u0)
    lM = 0.5 * log(q) + log(1 + log(q))              # PV: sqrt(q)(1+log q)
    lP_rho = log(3) + lM + log(1 + sqrt(sigma ** 2 + 1) / sigma)  # |im|<=1 edge
    lP_b0 = log(3) + lM + log(2.0)                   # real s: 1+||s||/re = 2
    lmom = 16 * log(1 + 2 * lz)
    lz_rho = log(2 * L2 / C0 + 12)                   # ZFR pole-distance grade
    lz_b0 = log(4.0 / u0 + 12)                       # 1/(1-beta0) <= 1/u at edge... 4/u0+12
    lnsfac_rho = log(1 + sqrt(sigma ** 2 + 1))       # (1+||s||)
    lnsfac_b0 = log(2.0)
    s1r = lP_rho + lnsfac_rho + 2 * log(1 + lx) + lmom + (2 + 2 * sigma) * lz - sigma * lx
    s2r = lM + lmom + 6 * lz + lz_rho - sigma * lx
    s1b = lP_b0 + lnsfac_b0 + 2 * log(1 + lx) + lmom + (2 + 2 * sigma) * lz - sigma * lx
    s2b = lM + lmom + 6 * lz + lz_b0 - sigma * lx
    # the beta0-instance is consumed as 2 x^{beta0-sigma} E_tot(beta0);
    # x^{beta0-sigma} <= x^{0.1} at the edge (largest); log-mult:
    shift = (0.1) * lx + log(2)
    s1b += shift; s2b += shift
    tot_r = max(s1r, s2r) + log(2)   # sum of 2 streams <= 2*max
    tot_b = max(s1b, s2b) + log(2)
    thr = log(1 / 16)
    dust = (0.1 - 1) * lx + log(2)   # 2 x^{beta0-sigma}/x
    lneed = log(1.0 / 32) - 0.1 * lx  # H7 u-free defect requirement
    return dict(u0=u0, lx=lx, s1r=s1r, s2r=s2r, s1b=s1b, s2b=s2b,
                tot_r=tot_r, tot_b=tot_b, thr=thr, dust=dust, lneed=lneed, lz=lz)

for B in (40, 50):
    for q in (3, 10 ** 6):
        r = eprice(q, B)
        ok_r = "OK  " if r["tot_r"] <= r["thr"] else "FAIL"
        ok_b = "OK  " if r["tot_b"] <= r["thr"] else "FAIL"
        print(f"B={B} q={q:>7}: logx={r['lx']:6.1f}  E(rho) streams e^{r['s1r']:+7.1f}/e^{r['s2r']:+7.1f} tot e^{r['tot_r']:+7.1f} {ok_r}"
              f" | 2x^sh*E(b0) e^{r['s1b']:+7.1f}/e^{r['s2b']:+7.1f} tot e^{r['tot_b']:+7.1f} {ok_b}"
              f" | dust e^{r['dust']:+6.1f} | need Delta<=e^{r['lneed']:+.1f}")
    print("-" * 78)

# candidate claims: B=50 q=3: E(rho) ~ e^-16.9; b0-side e^-24.9; q=1e6: e^-398.9/e^-406.4
# B=40 q=3: e^-0.8 FAIL. Compare.

print()
print("sweep q at B=50 (both instances), T=2:")
worst = None
for q in (3, 5, 7, 11, 17, 40, 100, 1000, 10**4, 57000, 10**6):
    r = eprice(q, 50)
    m = max(r["tot_r"], r["tot_b"])
    if worst is None or m > worst[1]:
        worst = (q, m)
    print(f"  q={q:>7}: max-instance log-total {m:+7.1f}  {'OK' if m <= r['thr'] else '** FAIL **'}")
print(f"  worst q = {worst[0]} at e^{worst[1]:+.1f}")

print()
print("=" * 78)
print("C3 — prime-sum honest magnitudes (the ground-map pieces, at design z)")
print("=" * 78)
for q in (3,):
    T = 2.0; Q = q * T; z = math.ceil(Q * Q); L2 = log(Q) + 2
    for tag, beta in (("ZFR-edge 1-c0/L2", 1 - C0 / L2), ("sigma=9/10", 0.9)):
        # P1 worst case: all chi(p)=1 -> dhA(p)=2, weight (log p/log z)^2, kern~1
        P1 = sum(2 * (log(p) / log(z)) ** 2 * p ** (-beta) for p in PR if p <= z)
        # actual chi mod 3: chi(p)=1 iff p%3==1
        P1a = sum((2 if p % 3 == 1 else 0) * (log(p) / log(z)) ** 2 * p ** (-beta)
                  for p in PR if p <= z) + (log(3) / log(z)) ** 2 * 3 ** (-beta)
        print(f"q=3 z={z} beta={tag}: P1_worst={P1:.3f}  P1_actual_chi3={P1a:.3f}")
    # band primes (z, x]: weight 1, dhA up to 2; harmonic tail 2*log(lx/lz) at beta~1
    u0 = 1.0 / (20 * log(Q)); lx = 50 * log(Q) + 2 * log(1 / u0)
    band_near1 = 2 * log(lx / log(z))
    # at beta=0.9 the band is polynomial: ~ 2*x^{0.1}/(0.1*lx) grade
    lband09 = log(2) + 0.1 * lx - log(0.1 * lx)
    print(f"q=3: band(z,x] at beta~1 (worst chi=+1): ~{band_near1:.2f}; at beta=9/10: ~e^{lband09:.1f}")
    print(f"     chi(p)=1 restriction: killing P1/band needs prime-level chi-cancellation = L-info;")
    print(f"     in THIS design bypassed by the shift into D(beta0); re-priced as H7's Delta.")

print()
print("=" * 78)
print("C5 — the (z,z^2] straddling band priced, + beyond-z^2 witness")
print("=" * 78)
q = 3; z = 36
band_zz2 = sum(2 * p ** (-0.9) for p in PR if z < p <= z * z)
band_zz2_b1 = sum(2 / p for p in PR if z < p <= z * z)
print(f"z=36: sum over primes (36,1296], w=1, dhA<=2: at beta=.9: {band_zz2:.2f}; at beta~1: {band_zz2_b1:.2f}")
# beyond z^2: w(105)!=0 at z=10 (ground map witness) — recompute
def w_graham(z, n):
    tot = 0.0
    for d in range(1, n + 1):
        if n % d == 0 and mu(d) != 0 and d <= z:
            tot += mu(d) * log(z / d) / log(z)
    return tot
print(f"witness beyond z^2: w(105) at z=10 = {w_graham(10,105):.4f} (nonzero, n>z^2)")
print(f"prime-power full weight: w(53) at z=50 = {w_graham(50,53):.4f}, w(2809)= {w_graham(50,2809):.4f}")

print()
print("=" * 78)
print("PART-B REDO — delta_opt independent (exact rationals z=36; lin-alg z<=1000)")
print("=" * 78)

def sqfree_list(z):
    return [d for d in range(1, z + 1) if mu(d) != 0]

def build_F_exact(z, chi):  # chi: p -> Fraction
    sq = sqfree_list(z)
    Fv = {}
    for d in sq:
        v = Fraction(1)
        for p in factor(d):
            c = chi(p)
            v *= (1 + c - Fraction(c, p)) / p
        Fv[d] = v
    return sq, Fv

def delta_opt_exact(z, chi):
    sq, Fv = build_F_exact(z, chi)
    n = len(sq)
    idx = {d: i for i, d in enumerate(sq)}
    import math as _m
    # exact BV theta impossible (log); so: Q_BV in floats but Q_min EXACT via
    # rational matrix inverse (theta_1=1 constrained min = 1/(F^{-1})_{11}).
    F = [[Fraction(0)] * n for _ in range(n)]
    for i, d in enumerate(sq):
        for j, e in enumerate(sq):
            l = d * e // _m.gcd(d, e)
            v = Fraction(1)
            for p in factor(l):
                c = chi(p)
                v *= (1 + c - Fraction(c, p)) / p
            F[i][j] = v
    # rational Gaussian elimination to solve F y = e1
    A = [row[:] + [Fraction(1) if i == 0 else Fraction(0)] for i, row in enumerate(F)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col] != 0)
        A[col], A[piv] = A[piv], A[col]
        pv = A[col][col]
        A[col] = [x / pv for x in A[col]]
        for r in range(n):
            if r != col and A[r][col] != 0:
                f = A[r][col]
                A[r] = [a - f * b for a, b in zip(A[r], A[col])]
    y = [A[r][n] for r in range(n)]
    Qmin = 1 / y[0]  # min of theta^T F theta s.t. theta_1 = 1 equals 1/(F^{-1})_{11}
    # Q_BV float
    th = [float(mu(d)) * log(z / d) / log(z) if d > 1 else 1.0 for d in sq]
    QBV = 0.0
    for i in range(n):
        for j in range(n):
            QBV += th[i] * th[j] * float(F[i][j])
    return QBV, float(Qmin)

def delta_opt_np(z, chif):
    sq = sqfree_list(z)
    n = len(sq)
    fac = {d: factor(d) for d in sq}
    Fp = {}
    def Fval(m):
        v = 1.0
        for p in fac.get(m, factor(m)):
            c = chif(p)
            v *= (1.0 + c - c / p) / p
        return v
    F = np.zeros((n, n))
    for i, d in enumerate(sq):
        for j, e in enumerate(sq):
            if j < i:
                F[i, j] = F[j, i]
                continue
            l = d * e // math.gcd(d, e)
            v = 1.0
            for p in factor(l):
                c = chif(p)
                v *= (1.0 + c - c / p) / p
            F[i, j] = v
    e1 = np.zeros(n); e1[0] = 1.0
    y = np.linalg.solve(F, e1)
    Qmin = 1.0 / y[0]
    th = np.array([float(mu(d)) * log(z / d) / log(z) if d > 1 else 1.0 for d in sq])
    QBV = th @ F @ th
    # positive-definiteness sanity
    ev = np.linalg.eigvalsh(F)
    return QBV, Qmin, ev.min()

chi_m1 = lambda p: -1.0
chi_p1 = lambda p: +1.0
chi_3 = lambda p: 0.0 if p == 3 else (1.0 if p % 3 == 1 else -1.0)

print("exact-rational Q_min at z=36 (constrained-min formula, NOT diagonalization):")
for name, chie, chif in (("pretense -1", lambda p: Fraction(-1), chi_m1),
                          ("worst +1  ", lambda p: Fraction(1), chi_p1),
                          ("chi mod 3 ", lambda p: Fraction(0) if p == 3 else (Fraction(1) if p % 3 == 1 else Fraction(-1)), chi_3)):
    QBV, Qmin = delta_opt_exact(36, chie)
    print(f"  z=36 {name}: Q_BV={QBV:.6f} Q_min={Qmin:.6f} delta_opt={QBV/Qmin-1:+.5f}")

print("numpy z-trend (independent constrained-min):")
for z in (36, 200, 1000):
    for name, chif in (("pretense -1", chi_m1), ("worst +1  ", chi_p1), ("chi mod 3 ", chi_3)):
        QBV, Qmin, lmin = delta_opt_np(z, chif)
        print(f"  z={z:>5} {name}: Q_BV={QBV:.6f} Q_min={Qmin:.6f} "
              f"delta={QBV/Qmin-1:+.5f}  (min-eig {lmin:.2e})  0.4/log^2z={0.4/log(z)**2:.5f}")

print()
print("ADVERSARIAL: minimize delta_opt over chi-patterns c_p in [-1,1], z=36")
sq36 = sqfree_list(36)
n36 = len(sq36)
p36 = [p for p in PR if p <= 36]
fac36 = {d: factor(d) for d in sq36}
lcm_fac = {}
for i, d in enumerate(sq36):
    for j, e in enumerate(sq36):
        l = d * e // math.gcd(d, e)
        lcm_fac[(i, j)] = factor(l)
th36 = np.array([float(mu(d)) * log(36 / d) / log(36) if d > 1 else 1.0 for d in sq36])

def delta_of(cvec):
    cmap = dict(zip(p36, cvec))
    F = np.zeros((n36, n36))
    for i in range(n36):
        for j in range(i, n36):
            v = 1.0
            for p in lcm_fac[(i, j)]:
                c = cmap[p]
                v *= (1.0 + c - c / p) / p
            F[i, j] = F[j, i] = v
    ev = np.linalg.eigvalsh(F)
    if ev.min() <= 1e-14:
        return None  # degenerate; constrained min ill-posed (skip)
    e1 = np.zeros(n36); e1[0] = 1.0
    y = np.linalg.solve(F, e1)
    Qmin = 1.0 / y[0]
    QBV = th36 @ F @ th36
    return QBV / Qmin - 1.0

rng = np.random.default_rng(0)
best = (None, 1e9)
# start from the three anchors + random + coordinate descent
starts = [np.full(len(p36), -1.0), np.full(len(p36), 1.0),
          np.array([0.0 if p == 3 else (1.0 if p % 3 == 1 else -1.0) for p in p36])]
for _ in range(40):
    starts.append(rng.uniform(-1, 1, len(p36)))
for s in starts:
    c = s.copy()
    d0 = delta_of(c)
    if d0 is None:
        continue
    for sweep in range(60):
        improved = False
        for k in range(len(p36)):
            for step in (0.4, 0.1, 0.02, 0.004):
                for sgn in (+1, -1):
                    c2 = c.copy()
                    c2[k] = min(1.0, max(-1.0, c2[k] + sgn * step))
                    d2 = delta_of(c2)
                    if d2 is not None and d2 < d0 - 1e-12:
                        c, d0 = c2, d2
                        improved = True
        if not improved:
            break
    if d0 < best[1]:
        best = (c.copy(), d0)
print(f"  minimum found over patterns: delta_opt = {best[1]:.6f}  (need <= e^-13.1 = {exp(-13.1):.2e})")
print(f"  at c = {np.round(best[0],3)}")

print()
print("=" * 78)
print("C4 — decay exponents table (log-Q coefficients), sigma=0.9")
print("=" * 78)
for B in (40, 50):
    print(f"B={B}: stream1 z^{{2+2s}}x^{{-s}}: Q-coef {2*(2+2*0.9)-0.9*B:+.1f}; "
          f"stream2 z^6 x^{{-s}}: {12-0.9*B:+.1f}; "
          f"beta0-instance adds +0.1B: s1 {2*(2+2*0.9)-0.8*B:+.1f}, s2 {12-0.8*B:+.1f}")
print("(all negative => decay; but the FAIL at B=40 q=3 is the polylog mass, see C1)")

print()
print("deficit summary (independent):")
for q in (3, 10 ** 6):
    r = eprice(q, 50)
    dbest = 0.4 / r["lz"] ** 2  # candidate's fitted pretense scaling
    print(f"  q={q:>7}: need Delta <= e^{r['lneed']:.1f}; pretense-truth ~{dbest:.3e} "
          f"=> deficit e^{log(dbest)-r['lneed']:.1f}")
