import math
from math import gcd
from functools import lru_cache

# ---------- arithmetic helpers ----------
def divisors(n):
    return [d for d in range(1, n+1) if n % d == 0]

def mobius(n):
    if n == 1: return 1
    m, cnt = n, 0
    p = 2
    while p*p <= m:
        if m % p == 0:
            m //= p; cnt += 1
            if m % p == 0: return 0
        p += 1
    if m > 1: cnt += 1
    return (-1)**cnt

def squarefree(n): return mobius(n) != 0

def primefactors(n):
    ps, m, p = [], n, 2
    while p*p <= m:
        if m % p == 0:
            ps.append(p)
            while m % p == 0: m //= p
        p += 1
    if m > 1: ps.append(m)
    return ps

# q=3 real primitive character
def chi(n):
    r = n % 3
    return 0 if r == 0 else (1 if r == 1 else -1)

def dhA(n):  # (chi * 1)(n)
    return sum(chi(d) for d in divisors(n))

def selH(p): return 1 + chi(p) - chi(p)/p
def selHmul(d): return math.prod(selH(p) for p in primefactors(d))
def selG(p):
    h = selH(p); return h/(p-h)
def selGmul(d): return math.prod(selG(p) for p in primefactors(d))
def selNu(n): return selHmul(n)/n

def selHSum(z):
    return sum(selGmul(r) for r in range(1, z+1) if squarefree(r))

def selWeight(z, d):
    if not (d <= z and squarefree(d)): return 0.0
    H = selHSum(z)
    inner = sum(selGmul(r) for r in range(1, z//d + 1)
                if squarefree(r) and gcd(r, d) == 1)
    return mobius(d) * (d/selHmul(d)) * selGmul(d) / H * inner

def gcW(lam, m):
    tot = 0.0
    for d1 in divisors(m):
        for d2 in divisors(m):
            if (d1*d2)//gcd(d1,d2) == m:
                tot += lam(d1)*lam(d2)
    return tot

print("=== (a) RUNG C collection identity: F(m) = sum_{g|m} chi(g) sum_{k|m/g} mu(k)chi(k)/k == selHmul(m), sf m, q=3 ===")
worst = 0.0
for m in [1,2,3,5,6,7,10,11,13,14,15,21,22,26,30,33,35]:
    F = sum(chi(g) * sum(mobius(k)*chi(k)/k for k in divisors(m//g)) for g in divisors(m))
    err = abs(F - selHmul(m)); worst = max(worst, err)
    if m <= 15: print(f"  m={m:3d}  F={F:+.12f}  selHmul={selHmul(m):+.12f}  err={err:.2e}")
print(f"  worst |F - selHmul| over battery: {worst:.2e}")

print("\n=== (b) RUNG D: sum_{m<=Y} gcW(selWeight)(m)*selNu(m) == selMainTerm == 1/H(z), z=6, q=3 ===")
for z in [6, 10, 20]:
    lam = lambda d: selWeight(z, d)
    H = selHSum(z)
    for Y in [z*z, z*z + 50]:
        S = sum(gcW(lam, m) * selNu(m) for m in range(1, Y+1))
        print(f"  z={z:3d} Y={Y:4d}  sum gcW*nu = {S:.14f}   1/H = {1/H:.14f}   err={abs(S-1/H):.2e}")
    # support check
    bad = [m for m in range(z*z+1, z*z+60) if abs(gcW(lam, m)) > 1e-14]
    print(f"    gcW support beyond z^2: {bad if bad else 'NONE (confirmed)'}")

print("\n=== (c) RUNG B exact reduction identity, q=3, beta0=0.7, Y=500 ===")
beta0 = 0.7
def D0(x):  # real-scale template
    T = int(math.floor(x))
    return sum(dhA(s) * s**(-beta0) * (1 - s/x) for s in range(1, T+1))
Y = 500
for m in [1, 2, 5, 6, 10, 15, 30]:
    lhs = sum(dhA(n) * n**(-beta0) * (1 - n/Y)
              for n in range(1, Y+1) if n % m == 0)
    rhs = 0.0
    for g in divisors(m):
        for k in divisors(m//g):
            rhs += chi(g)*chi(k)*mobius(k) * (m*k)**(-beta0) * D0(Y/(m*k))
    print(f"  m={m:3d}  LHS={lhs:+.12f}  RHS={rhs:+.12f}  err={abs(lhs-rhs):.2e}")

print("\n=== (c2) pair count = 3^omega, |gcW|<=3^omega, sf m ===")
z = 6; lam = lambda d: selWeight(z, d)
ok = True
for m in [1,2,3,5,6,10,15,30]:
    cnt = sum(1 for g in divisors(m) for k in divisors(m//g))
    om = len(primefactors(m))
    okg = abs(gcW(lam, m)) <= 3**om + 1e-12
    ok = ok and (cnt == 3**om) and okg
    print(f"  m={m:3d}  pairs={cnt}  3^om={3**om}  |gcW|={abs(gcW(lam,m)):.4f}  ok={okg}")
print(f"  all pass: {ok}")

print("\n=== (d) BUDGET: mine vs ledger E(b0) shape, C2 = 4*C_w ===")
L10 = lambda v: math.log10(v)
def budget(q):
    T = 2.0; Q = q*T
    L2 = math.log(Q) + 2
    u = 1/(40*L2)
    sigma = 16/17
    lnQ = math.log(Q)
    lnz = 12*lnQ + 2*math.log(1/u)
    lnx = 104*lnQ + 11*math.log(1/u)
    log10x = lnx/math.log(10); log10z = lnz/math.log(10)
    M = math.sqrt(q)*(1+math.log(q))
    P = 8*M; CE = 100; Z0 = 2.5
    Cw = 34 + 12*M + 12*M*Z0 + 36*M/u
    C2 = 4*Cw
    # ledger budgeted E(b0)-amp (ledger.py line 27):
    lf3 = (1+lnx)**3; lz12 = (1+2*lnz)**12
    E0amp = L10(2)+L10(CE)+L10(P)+L10(2)+L10(lf3)+L10(lz12)+4*log10z+(-sigma*log10x)+L10(1+1/u)
    # my error, amped the same way: 2*x^{b0-s}*E_mine, E_mine = C2*z*(1+2lnz)^9*x^{1/2-b0}
    # -> amp form: 2*C2*z*(1+2lnz)^9*x^{1/2}*x^{-sigma}
    lz9 = (1+2*lnz)**9
    mine_amp = L10(2)+L10(C2)+log10z+L10(lz9)+0.5*log10x+(-sigma*log10x)
    print(f" q={q}: u*={u:.4g} log10z={log10z:.4g} log10x={log10x:.4g} Cw={Cw:.3g} C2={C2:.3g}")
    print(f"   ledger E(b0)-amp = 10^{E0amp:.2f}   (vs 1/8 = 10^-0.90)")
    print(f"   MINE   E(b0)-amp = 10^{mine_amp:.2f}   (vs 1/8)  margin = {(-0.903)-mine_amp:.2f} orders")
    # regime guard 2z^4 <= x
    print(f"   guard 2z^4<=Y=x: log10(2z^4)={L10(2)+4*log10z:.1f} <= log10x={log10x:.1f} : {L10(2)+4*log10z <= log10x}")
    # smallest-index dust at q: real-scale wrapper + Riemann deficit, at deepest scale x0 = x/z^4
    log10x0 = log10x - 4*log10z
    L1cap = 1 + 6*M
    dust_over_C2term = L10(L1cap/u) - L10(C2) - 0.5*log10x0   # (L1/u)x0^{-b0} vs C2 x0^{1/2-b0}
    print(f"   deepest scale log10(x0)={log10x0:.1f}; wrapper dust/(C2-term) = 10^{dust_over_C2term:.1f}")
    # m=1 term of the collection error vs total moment bound (sanity: <= 1)
    print(f"   m=1 error share: C2*x^(1/2-b0) vs C2*z*(1+2lnz)^9*x^(1/2-b0): ratio 10^{-(log10z+L10(lz9)):.1f}")
budget(3)
budget(10**6)

print("\n=== (e) moment stone: sum_{m<=z^2,sf} |gcW|*3^om*m^(-1/2) <= z*(1+log z^2)^9, small-z sanity ===")
for z in [6, 10, 20]:
    lam = lambda d: selWeight(z, d)
    S = sum(abs(gcW(lam, m))*3**len(primefactors(m))*m**-0.5
            for m in range(1, z*z+1) if squarefree(m))
    bound = z*(1+math.log(z*z))**9
    print(f"  z={z:3d}  S={S:10.4f}  z*(1+log z^2)^9={bound:12.1f}  pass={S<=bound}")
