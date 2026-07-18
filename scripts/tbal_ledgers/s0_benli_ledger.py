#!/usr/bin/env python3
"""T-BAL S0 redesign (benli-faithful): the smallest-index ledger, priced FIRST.

Part A: E_tot smallest-index pricing at q=3 and q=1e6, B in {40,50}, sigma=9/10 worst.
Part B: the R7-stone truth value: EXACT computation of the twisted BV quadratic form
        V ~ Q(theta_BV) vs Selberg minimum Q_min for the chi(p)=-1 pretense extreme
        (best case for BV) and the chi(p)=+1 extreme (worst case), at z=36 and z=4e3.
Part C: the deficit lines + SEL re-route window arithmetic.
"""
import math
from math import log, sqrt, exp

def _sieve(n):
    pr = []
    s = [True] * (n + 1)
    for i in range(2, n + 1):
        if s[i]:
            pr.append(i)
            for j in range(i * i, n + 1, i):
                s[j] = False
    return pr

_PR = _sieve(10 ** 6)

def primerange(a, b):
    for p in _PR:
        if p >= b:
            return
        if p >= a:
            yield p

def mu(n):
    if n == 1:
        return 1
    m, res = n, 1
    for p in _PR:
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

# ---------- Part B: the twisted quadratic form, EXACT ----------
# G_chi(z) = sum_{d,e<=z sqfree} theta_d theta_e * F([d,e]),  F(m)=h_chi(m)/m,
# h_chi(p) = 1 + chi(p) - chi(p)/p  (multiplicative on squarefree).
# BV: theta_d = mu(d) log(z/d)/log z.
# Selberg min over theta_1=1: Q_min = 1/L_z, L_z = sum_{k<=z sqfree} mu(k)^2/G(k),
#   G(p) = 1/F(p) - 1  (standard diagonalization, F multiplicative, F([d,e])=F(d)F(e)/F((d,e))).

def form_value_and_min(z, chi):
    zs = int(z)
    sq = [d for d in range(1, zs + 1) if mu(d) != 0]
    def F(m):
        v = 1.0
        mm = m
        for p in primerange(2, m + 1):
            if mm % p == 0:
                c = chi(p)
                v *= (1.0 + c - c / p) / p
                mm //= p
        return v
    def lcm(a, b):
        return a * b // math.gcd(a, b)
    th = {d: mu(d) * log(zs / d) / log(zs) if d > 1 else 1.0 for d in sq}
    # careful: theta_1 = mu(1)*log(z)/log(z) = 1 exactly
    th[1] = 1.0
    Q = 0.0
    for d in sq:
        for e in sq:
            Q += th[d] * th[e] * F(lcm(d, e))
    # Selberg minimum
    L = 0.0
    for k in sq:
        Fk = F(k)
        if Fk <= 0:
            continue
        Gk = 1.0
        kk = k
        for p in primerange(2, k + 1):
            if kk % p == 0:
                Fp = (1.0 + chi(p) - chi(p) / p) / p
                Gk *= (1.0 / Fp - 1.0)
                kk //= p
        L += 1.0 / Gk
    return Q, 1.0 / L, L

print("=" * 72)
print("PART B — the R7-stone truth: Q(theta_BV) vs Q_min (delta_opt = Q/Qmin - 1)")
print("=" * 72)
for z in (36, 1000):
    for name, chi in (("pretense chi=-1", lambda p: -1.0),
                      ("worstcase chi=+1", lambda p: +1.0),
                      ("chi mod 3 actual", lambda p: 0.0 if p == 3 else (1.0 if p % 3 == 1 else -1.0))):
        Q, Qmin, L = form_value_and_min(z, chi)
        print(f"z={z:5d} {name:18s}: Q_BV={Q:.6f}  Q_min={Qmin:.6f}  "
              f"delta_opt={Q/Qmin-1:+.4f}   (1/log^2 z = {1/log(z)**2:.4f})")

# ---------- Part A: E_tot smallest-index pricing ----------
print()
print("=" * 72)
print("PART A — E_tot pricing (faithful-R6 form, refuter-amended zeta factor)")
print("=" * 72)
c0 = 1.0 / 126848

def price(q, B, sigma=0.9, T=2.0):
    # all in natural-log space
    Q = q * T
    L2 = log(Q) + 2
    z = math.ceil(Q * Q)
    lz = log(z)
    u0 = min(1.0 / (4 * (1 + log(q))), 1.0 / (20 * log(Q)))
    lx = B * log(Q) + 2 * log(1 / u0)
    lM = 0.5 * log(q) + log(1 + log(q))
    lPrho = log(3) + lM + log(1 + sqrt(sigma ** 2 + 1) / sigma)
    lPb0 = log(3) + lM + log(2.0)
    lmom = 16 * log(1 + 2 * lz)
    lzeta_rho = log(2 * L2 / c0 + 12)
    lzeta_b0 = log(4.0 / u0 + 12)
    def lE(lP, res, lzfac):
        s1 = lP + log(2.5) + 2 * log(1 + lx) + lmom + (2 + 2 * res) * lz - res * lx
        s2 = lM + lmom + 6 * lz + lzfac - res * lx
        return s1, s2
    e1r, e2r = lE(lPrho, sigma, lzeta_rho)
    e1b, e2b = lE(lPb0, sigma, lzeta_b0)
    e1b += log(2); e2b += log(2)
    thr = log(1.0 / 16)
    def fmt(l):
        return f"e^{l:+.1f}"
    print(f"q={q:>7} B={B} sigma={sigma}: u0={u0:.6f} log x={lx:.1f}")
    print(f"   E(rho)  streams: {fmt(e1r)}, {fmt(e2r)}   vs 1/16=e^-2.77  "
          f"{'OK' if max(e1r, e2r) + log(2) <= thr else '** FAIL **'}")
    print(f"   2x^shift*E(b0):  {fmt(e1b)}, {fmt(e2b)}   vs 1/16  "
          f"{'OK' if max(e1b, e2b) + log(2) <= thr else '** FAIL **'}")
    lneed = log(1.0 / 32) - (1 - sigma) * lx
    best_bv = 0.65 / (1.645 * lz ** 2)
    print(f"   R7-stone: need delta_ufree <= e^{lneed:.1f}; BV best-case delta_opt ~ "
          f"{best_bv:.3e}  deficit e^{log(best_bv)-lneed:.1f}")

for B in (40, 50):
    for q in (3, 10 ** 6):
        price(q, B)
    print("-" * 72)

# small-q sweep at B=50: worst Q for the rho-side
print("sweep B=50 (rho-side log-total vs 1/16), q in small set, log-space:")
for q in (3, 5, 7, 11, 40, 100, 1000, 10**4, 57000, 10**6):
    Q = q * 2.0
    L2 = log(Q) + 2
    z = math.ceil(Q * Q); lz = log(z)
    u0 = min(1.0 / (4 * (1 + log(q))), 1.0 / (20 * log(Q)))
    lx = 50 * log(Q) + 2 * log(1 / u0)
    lM = 0.5 * log(q) + log(1 + log(q))
    lPrho = log(3) + lM + log(1 + sqrt(0.81 + 1) / 0.9)
    lmom = 16 * log(1 + 2 * lz)
    lzeta = log(2 * L2 / c0 + 12)
    s1 = lPrho + log(2.5) + 2 * log(1 + lx) + lmom + 3.8 * lz - 0.9 * lx
    s2 = lM + lmom + 6 * lz + lzeta - 0.9 * lx
    tot = max(s1, s2) + log(2)
    print(f"  q={q:>7}: log-total<={tot:+.1f}  {'OK' if tot <= log(1/16) else '** FAIL **'}")

# ---------- Part C: SEL re-route window ----------
print()
print("=" * 72)
print("PART C — SEL re-route (delta_opt=0) far-sigma window arithmetic")
print("=" * 72)
# window: z >= 1024*q*(1+log q)^4 * x^{2(1-sigma)}   (delta_dens ~ C sqrt(q) polylog /sqrt z)
#         z <= x^{1/6} (frozen z^6 extraction)  or  x^{1/4.4} (sharpened)
for q in (3, 10**6):
    for expo, tag in ((1/6, "z^6 frozen"), (1/4.4, "z^4.4 sharpened")):
        # need x^{expo - 0.2} >= 1024 q (1+log q)^4  => B log Q (expo-0.2) >= log RHS (u-part cancels if tuned)
        rhs = log(1024 * q * (1 + log(q)) ** 4)
        margin = expo - 0.2
        if margin <= 0:
            print(f"  q={q:>7} {tag}: WINDOW EMPTY (margin {margin:+.3f})")
        else:
            Bmin = rhs / (margin * log(2 * q))
            print(f"  q={q:>7} {tag}: need B >= {Bmin:.0f}")
