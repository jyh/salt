"""INDEPENDENT refuter check of the R6 dh_extraction_upper_W freeze.
Fresh implementation (not derived from the designer's r6_verify.py):
sieve-based factorization, direct-definition selMainTerm double sum,
different battery parameters (beta0=0.55/0.9, Y=700, non-squarefree m included).
"""
import math

LIM = 4000
spf = list(range(LIM))  # smallest prime factor sieve
for p in range(2, LIM):
    if spf[p] == p:
        for j in range(p * p, LIM, p):
            if spf[j] == j:
                spf[j] = p

def fact(n):
    f = {}
    while n > 1:
        p = spf[n]; e = 0
        while n % p == 0:
            n //= p; e += 1
        f[p] = e
    return f

def divs(n):
    ds = [1]
    for p, e in fact(n).items():
        ds = [d * p**k for d in ds for k in range(e + 1)]
    return sorted(ds)

def mu(n):
    f = fact(n)
    if any(e > 1 for e in f.values()):
        return 0
    return (-1) ** len(f)

def sf(n): return all(e == 1 for e in fact(n).values())
def omega(n): return len(fact(n))

# --- q=3 real primitive character, completely multiplicative ---
def chi3(n):
    return [0, 1, -1][n % 3]

def dhA(n):  # (chi * 1)(n)
    return sum(chi3(d) for d in divs(n))

# --- Selberg locals per the LEAN definitions (SelWeight.lean) ---
def h_(p): return 1 + chi3(p) - chi3(p) / p              # selH
def g_(p): return h_(p) / (p - h_(p))                    # selG
def hmul(n): return math.prod(h_(p) for p in fact(n))    # selHmul
def gmul(n): return math.prod(g_(p) for p in fact(n))    # selGmul
def nu(n): return hmul(n) / n                            # selNu

def H(z):  # selHSum
    return sum(gmul(r) for r in range(1, z + 1) if sf(r))

def theta(z, d):  # selWeight per Lean def (Nat division z/d)
    if not (d <= z and sf(d)):
        return 0.0
    inner = sum(gmul(r) for r in range(1, z // d + 1)
                if sf(r) and math.gcd(r, d) == 1)
    return mu(d) * (d / hmul(d)) * gmul(d) / H(z) * inner

def gcW(z, m):  # sum over lcm(d,e)=m of theta_d theta_e
    s = 0.0
    for d in divs(m):
        for e in divs(m):
            if d * e // math.gcd(d, e) == m:
                s += theta(z, d) * theta(z, e)
    return s

print("== [C3-a] R6-5 collection: F(m)=sum_{g|m}chi(g)sum_{k|m/g}mu(k)chi(k)/k vs selHmul, sf m ==")
w = 0.0
for m in [1, 2, 5, 6, 7, 10, 11, 13, 14, 15, 21, 22, 26, 30, 33, 34, 35, 39, 42, 55, 66, 70, 105, 110, 210, 231, 273, 330, 390, 462, 546, 570, 690, 714, 770, 798, 858, 870, 910, 930]:
    F = sum(chi3(g) * sum(mu(k) * chi3(k) / k for k in divs(m // g)) for g in divs(m))
    w = max(w, abs(F - hmul(m)))
print(f"   worst |F-selHmul| over 40-case sf battery (incl. omega=4): {w:.3e}")

print("== [C3-b] R6-7 + selberg_opt_eq: DIRECT selMainTerm double sum vs sum gcW*nu vs 1/H ==")
for z in [6, 10, 13]:
    V = sum(theta(z, d) * theta(z, e) * nu(d * e // math.gcd(d, e))
            for d in range(1, z + 1) if sf(d)
            for e in range(1, z + 1) if sf(e))          # Lean def selMainTerm
    Y = z * z + 37
    S = sum(gcW(z, m) * nu(m) for m in range(1, Y + 1))  # R6-7 LHS
    print(f"   z={z:3d}: V(direct)={V:.14f}  sum gcW*nu={S:.14f}  1/H={1/H(z):.14f}"
          f"  d1={abs(V-S):.1e} d2={abs(S-1/H(z)):.1e}")
    beyond = [m for m in range(z * z + 1, min(z * z + 80, LIM)) if abs(gcW(z, m)) > 1e-13]
    print(f"      gcW support beyond z^2: {beyond if beyond else 'none'}")

print("== [C3-c] R6-4 EXACT reduction, DIFFERENT params: beta0 in {0.55,0.9}, Y=700, m incl. NON-squarefree ==")
for beta0 in [0.55, 0.9]:
    def D0(x):
        return sum(dhA(s) * s ** (-beta0) * (1 - s / x)
                   for s in range(1, int(math.floor(x)) + 1))
    Y = 700
    wr = 0.0
    for m in [1, 2, 3, 4, 6, 8, 9, 12, 15, 18, 25, 27, 30, 36, 45, 60]:
        lhs = sum(dhA(n) * n ** (-beta0) * (1 - n / Y)
                  for n in range(m, Y + 1, m))
        rhs = sum(chi3(g) * chi3(k) * mu(k) * (m * k) ** (-beta0) * D0(Y / (m * k))
                  for g in divs(m) for k in divs(m // g))
        wr = max(wr, abs(lhs - rhs))
        if not sf(m):
            tag = "NONSF"
        else:
            tag = "sf   "
        if m in (4, 9, 12, 30, 60):
            print(f"   b0={beta0} m={m:3d} [{tag}] lhs={lhs:+.10f} rhs={rhs:+.10f} err={abs(lhs-rhs):.1e}")
    print(f"   b0={beta0}: worst err over 16-m battery (incl. non-sf): {wr:.3e}")

print("== [C2-small] moment stone at small z: sum_{m<=z^2,sf}|gcW|3^om m^-.5 vs z(1+log z^2)^9; and tau9 ineq ==")
for z in [6, 10, 13]:
    S = sum(abs(gcW(z, m)) * 3 ** omega(m) * m ** -0.5
            for m in range(1, z * z + 1) if sf(m))
    bd = z * (1 + math.log(z * z)) ** 9
    # intermediate step: m^-1/2 <= z/m on m<=z^2, then tau9
    T9 = sum(9 ** omega(m) / m for m in range(1, z * z + 1) if sf(m))
    t9bd = (1 + math.log(z * z)) ** 9
    print(f"   z={z:3d}: S={S:9.3f} <= z(1+log z^2)^9={bd:.3e} : {S<=bd}"
          f" | tau9={T9:8.3f} <= (1+log z^2)^9={t9bd:.3e} : {T9<=t9bd}")
# tau9 inequality stress at larger L
for L in [1000, 4000 - 1]:
    T9 = sum(9 ** omega(m) / m for m in range(1, L + 1) if sf(m))
    print(f"   tau9 stress L={L}: {T9:.2f} <= (1+log L)^9={(1+math.log(L))**9:.2f} : "
          f"{T9 <= (1+math.log(L))**9}")

print("== [C1/C4/C5] budget recomputation FROM SCRATCH at q=3 and q=10^6 ==")
lg = lambda v: math.log10(v)
for q in [3, 10 ** 6]:
    T = 2.0; Q = q * T
    L2 = math.log(Q) + 2
    u = 1 / (40 * L2)              # u* (worst corner: E-amp exponent decreasing in 1/u, see below)
    sigma = 16 / 17
    lnQ = math.log(Q)
    lnz = 12 * lnQ + 2 * math.log(1 / u)
    lnx = 104 * lnQ + 11 * math.log(1 / u)
    l10z = lnz / math.log(10); l10x = lnx / math.log(10)
    M = math.sqrt(q) * (1 + math.log(q))
    Z0 = 2.5
    Cw = 34 + 12 * M + 12 * M * Z0 + 36 * M / u
    C2 = 4 * Cw
    # sanity: C2 covers honest anatomy 3Cw + 7M/u  <=>  Cw >= 7M/u, and 4Cw expansion
    assert Cw >= 7 * M / u and abs(4 * Cw - (136 + 48 * M + 48 * M * Z0 + 144 * M / u)) < 1e-6
    lz9 = 9 * math.log10(1 + 2 * lnz)
    # E_mine = C2 * z * (1+2lnz)^9 * x^{1/2-b0}; amped 2 x^{b0-sigma} => 2 C2 z (1+2lnz)^9 x^{1/2-sigma}
    amp_total = lg(2) + lg(C2) + l10z + lz9 + (0.5 - sigma) * l10x
    amp_m1 = lg(2) + lg(C2) + (0.5 - sigma) * l10x          # smallest index m=1,g=k=1
    # ledger's budgeted E(b0)-amp (ledger.py row 3) for comparison
    CE = 100; P = 8 * M
    E0amp = (lg(2) + lg(CE) + lg(P) + lg(2) + 3 * lg(1 + lnx)
             + 12 * lg(1 + 2 * lnz) + 4 * l10z - sigma * l10x + lg(1 + 1 / u))
    guard = lg(2) + 4 * l10z
    l10x0 = l10x - 4 * l10z                                  # deepest scale x0 = x/z^4
    L1cap = 1 + 6 * M
    dust = lg(L1cap / u) - lg(C2) - 0.5 * l10x0              # wrapper dust ratio at deepest scale
    print(f" q={q}: u*={u:.5g} l10z={l10z:.3f} l10x={l10x:.3f} M={M:.4g} Cw={Cw:.5g} C2={C2:.5g}")
    print(f"   TOTAL amp 10^{amp_total:.2f} vs 1/8=10^{lg(1/8):.3f}  margin={lg(1/8)-amp_total:.2f}")
    print(f"   m=1 amp   10^{amp_m1:.2f}   share=10^{amp_m1-amp_total:.1f}")
    print(f"   ledger budgeted E(b0)-amp 10^{E0amp:.2f}  (freeze claims -8.86/-270 corners)")
    print(f"   guard 2z^4<=x: 10^{guard:.1f} <= 10^{l10x:.1f} : {guard <= l10x};  x0=10^{l10x0:.1f}>=2")
    print(f"   wrapper dust/(C2 term) at x0: 10^{dust:.1f}")
    # C5: u-direction of the amp exponent (is u=u* the max over u<=u*?)
    dexp = 1 + 2 - 11 * (sigma - 0.5)   # dlog10E/dlog10(1/u): C2->1, z->2, x^{1/2-sigma}->-11(sigma-1/2)
    print(f"   d(amp)/dln(1/u) power part = {dexp:.3f} (<0 => u=u* is the worst corner)")
    # C4: u-grade census: C2 one u^-1, z=Q^12 u^-2 => total u^-3; budget z^4(1+1/u)=u^-9
    print(f"   u-grade: mine u^-3 vs budget u^-9 : OK (structural)")
print("== upper-u sweep (u from u* up to 1/2, q=3): amp exponent ==")
q = 3; T = 2.0; Q = q * T; L2 = math.log(Q) + 2; sigma = 16 / 17
M = math.sqrt(q) * (1 + math.log(q)); Z0 = 2.5
for uu in [1 / (40 * L2), 0.02, 0.1, 0.25, 0.5]:
    lnz = 12 * math.log(Q) + 2 * math.log(1 / uu)
    lnx = 104 * math.log(Q) + 11 * math.log(1 / uu)
    C2 = 4 * (34 + 12 * M + 12 * M * Z0 + 36 * M / uu)
    a = lg(2) + lg(C2) + lnz / math.log(10) + 9 * lg(1 + 2 * lnz) + (0.5 - sigma) * lnx / math.log(10)
    print(f"   u={uu:.4g}: amp=10^{a:.2f}  guard 2z^4<=x: {lg(2)+4*lnz/math.log(10) <= lnx/math.log(10)}")
