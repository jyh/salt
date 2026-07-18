#!/usr/bin/env python3
"""REFUTER 1 — independent re-ledger of the R5 judge retune.
Written FROM THE FREEZE (docs/exploration/tbal-s0-freeze.md:9-15), not from the judge's script.

RETUNE UNDER ATTACK: z=ceil(Q^12 u^-3) (a=3), x=Q^104 u^-14 (W=14), X1=2330,
sigma-floor 13/14, witnesses b=680 k=14 c=2^-250, sigma0=16/17, tau unchanged,
delta_d=delta_b=0 (rows deleted).

MASTER (freeze:11, delta=0):  3/4 <= 2x^{b0-s}[uX1 lnx + 1/x + E(b0)] + 4u x^{1-s} L2/c0 + E(rho)
E-SHAPE (freeze:12): E(s) <= CE*P*(1+|s|)(1+lnx)^3 (1+2lnz)^12 z^{2+2Re s} x^{-Re s} * dust,
  dust = L2/c0 at rho, 1/u at b0.  P <= 8M, M=sqrt(q)(1+lnq), CE=100 (Cw pin), c0=1/126848.
Rows (each vs 1/8; upper-bounded with x^{b0-s} <= x^{1-s}, z^{2+2b0} <= z^4, 1+|b0| <= 2,
1+|rho| <= 1+sqrt2):
  R_E  = 2 * 2*CE*P * (1+lnx)^3 (1+2lnz)^12 * z^4 * x^{-sigma} / u        [E(b0)-amp]
  R_A  = 2 * x^{1-sigma} * u * X1 * lnx                                    [A-row]
  R_x  = 2 * x^{-sigma}                                                    [1/x row]
  R_r  = 4 * u * x^{1-sigma} * L2/c0                                       [rho main]
  R_Er = CE*P*(1+sqrt2)*(1+lnx)^3 (1+2lnz)^12 * z^{2+2sigma} x^{-sigma} * L2/c0
Contradiction ray: u < tau, tau = c Q^{-b(1-sigma)} L2^{-k}. Wrong-corner law: check
u-grade sign AND at-tau value AND monotone certificate on the WHOLE ray.
"""
import math
from fractions import Fraction as Fr
ln = math.log; LN10 = ln(10)
def lg_from_nats(x): return x / LN10

A_EXP = 3          # z = Q^12 u^-a
W_EXP = 14         # x = Q^104 u^-W
X1    = 2330
CE    = 100
C0INV = 126848
B_W, K_W, C_LN = 680, 14, 250*ln(2)   # witnesses; ln(1/c) = 250 ln2
EIGHTH_LG = math.log10(1/8)           # -0.903

def Mpv(q): return math.sqrt(q)*(1+ln(q))

class Corner:
    def __init__(self, q, T=2.0, sigma=Fr(16,17)):
        self.q=q; self.T=T; self.sigma=float(sigma)
        self.Q=q*T; self.lnQ=ln(self.Q); self.L2=self.lnQ+2
        self.M=Mpv(q); self.P=8*self.M
        self.ustar=1/(40*self.L2); self.s_ustar=ln(1/self.ustar)
        self.s_tau = C_LN + B_W*(1-self.sigma)*self.lnQ + K_W*ln(self.L2)
    def lnz(self,s):  return 12*self.lnQ + A_EXP*s
    def lnx(self,s):  return 104*self.lnQ + W_EXP*s
    # ---- master rows, ln-form, s = ln(1/u) ----
    def lnR_E(self,s):
        return (ln(2*2*CE*self.P) + 3*ln(1+self.lnx(s)) + 12*ln(1+2*self.lnz(s))
                + 4*self.lnz(s) - self.sigma*self.lnx(s) + s)
    def lnR_A(self,s):
        return ln(2*X1) + (1-self.sigma)*self.lnx(s) - s + ln(self.lnx(s))
    def lnR_x(self,s):
        return ln(2) - self.sigma*self.lnx(s)
    def lnR_r(self,s):
        return ln(4*self.L2*C0INV) + (1-self.sigma)*self.lnx(s) - s
    def lnR_Er(self,s):
        return (ln(CE*self.P*(1+math.sqrt(2))*self.L2*C0INV) + 3*ln(1+self.lnx(s))
                + 12*ln(1+2*self.lnz(s)) + (2+2*self.sigma)*self.lnz(s) - self.sigma*self.lnx(s))
    # ---- derivatives in s (F' < 0 at s_tau, and F' decreasing => monotone on ray) ----
    def dR_E(self,s):  return (13-W_EXP*self.sigma) + 3*W_EXP/(1+self.lnx(s)) + 24*A_EXP/(1+2*self.lnz(s))
    def dR_A(self,s):  return (W_EXP*(1-self.sigma)-1) + W_EXP/self.lnx(s)
    def dR_r(self,s):  return  W_EXP*(1-self.sigma)-1
    def dR_Er(self,s): return ((2+2*self.sigma)*A_EXP - W_EXP*self.sigma) + 3*W_EXP/(1+self.lnx(s)) + 24*A_EXP/(1+2*self.lnz(s))

# ---------- CLAIM 1+7: symbolic u-grades and the sigma-window law ----------
print("="*100)
print("CLAIM 1 + 7: u-grades (exact fractions) and the sigma-window law, derived from freeze:10/:12")
a=Fr(A_EXP); W=Fr(W_EXP); s0=Fr(16,17)
eta_E  = W*s0 - (4*a+1)          # z^4 (grade -4a) * u^{-1} dust * x^{-sigma} (grade +W sigma)
eta_A  = 1 - W*(1-s0)            # u * x^{1-sigma}
eta_r  = eta_A
eta_Er = W*s0 - a*(2+2*s0)       # z^{2+2sigma} x^{-sigma}
eta_x  = W*s0
print(f"  eta_E  = W*s0-(4a+1) = {eta_E} = {float(eta_E):+.4f}   (claim +0.176)")
print(f"  eta_A  = 1-W(1-s0)   = {eta_A} = {float(eta_A):+.4f}   (claim +0.176)")
print(f"  eta_Er = W*s0-a(2+2s0)= {eta_Er} = {float(eta_Er):+.4f}  (claim +1.529)")
print(f"  eta_x  = W*s0 = {eta_x} = {float(eta_x):+.3f}")
G = 4*a+1
print(f"  window law: E-grade G=4a+1={G}; need W*sig>=G and W(1-sig)<=1 =>"
      f" sig >= G/(G+1) = {G/(G+1)} = {float(G/(G+1)):.4f} (claim 13/14={13/14:.4f})")
print(f"  at s0=16/17: W in [G/s0, 1/(1-s0)] = [{float(G/s0):.4f}, {float(1/(1-s0)):.1f}]"
      f" -> W>=13.8125 forced, W=14 minimal integer (claim W>=13.8125): {float(G/s0)==13.8125}")
print(f"  structural: W=14 equalizes eta_E==eta_A at EVERY sigma: Wsig-13 = 1-W(1-sig) <=> W=14: "
      f"{W*s0-13 == 1-W*(1-s0)}")
print(f"  refuters' W=13 wrong-corner check: eta_E(W=13) = {Fr(13)*s0-13} = {float(Fr(13)*s0-13):+.4f} < 0 (diverges on ray)")

# ---------- CLAIM 2: rows on the ray at u*, tau, and interior points ----------
print("="*100)
print("CLAIM 2: master rows on the ray, q in {3,5,150,1e6}, sigma=16/17, T=2 (all lg10 vs 1/8 = 10^-0.903)")
def ray_report(c, label=""):
    st = c.s_tau
    pts = [("u*", c.s_ustar), ("tau", st), ("2tau", 2*st), ("5tau", 5*st), ("20tau", 20*st)]
    print(f"-- q={c.q:g} T={c.T:g} sigma={c.sigma:.6f}: s_tau={st:.2f} (tau=10^{-st/LN10:.1f}), "
          f"u*={c.ustar:.4g}, tau<u*: {st > c.s_ustar}")
    hdr = "   {:>6s}" + "".join(f" {n:>10s}" for n,_ in pts)
    print(hdr.format("row"))
    rows = [("E-amp",c.lnR_E),("A-row",c.lnR_A),("1/x",c.lnR_x),("rho",c.lnR_r),("E(rho)",c.lnR_Er)]
    at_tau = {}
    for nm,f in rows:
        vals = [lg_from_nats(f(s)) for _,s in pts]
        at_tau[nm]=vals[1]
        flag = "" if all(v < EIGHTH_LG for v in vals[1:]) else "  <-- RAY FAIL"
        print(("   {:>6s}"+"".join(" {:>10.1f}" for _ in pts)).format(nm,*vals)+flag)
    # monotone certificates on the ray (F'(s_tau)<0 and F' decreasing in s)
    ders = [("E-amp",c.dR_E(st)),("A-row",c.dR_A(st)),("rho",c.dR_r(st)),("E(rho)",c.dR_Er(st))]
    mono = all(d<0 for _,d in ders)
    print("   F'(s_tau): " + "  ".join(f"{n}={d:+.4f}" for n,d in ders) +
          ("  -> monotone-decaying on ray" if mono else "  -> NOT MONOTONE: scanning"))
    # independent dense scan of the ray to 100x depth regardless
    worst = -1e18; wname=None; wst=None
    for nm,f in rows:
        for i in range(1201):
            s = st*(1+99*i/1200)
            v = lg_from_nats(f(s))
            if v > worst: worst, wname, wst = v, nm, s
    ok = worst < EIGHTH_LG
    print(f"   ray max over ALL rows (scan to 100x depth): 10^{worst:.2f} ({wname} at s={wst:.0f}) "
          f"vs 1/8: {'PASS' if ok else 'FAIL'}")
    # master total at tau (log-sum-exp)
    ltot = [f(st) for _,f in rows]
    m = max(ltot); tot = m + ln(sum(math.exp(l-m) for l in ltot))
    print(f"   master TOTAL at tau = 10^{lg_from_nats(tot):.2f}  (< lg(3/4)={math.log10(0.75):.3f}: {lg_from_nats(tot)<math.log10(0.75)})")
    return at_tau, ok

claim2 = {}
allok = True
for q in [3,5,150,10**6]:
    at, ok = ray_report(Corner(q)); claim2[q]=at; allok &= ok
print(f"  judge's claimed at-tau values: E-amp -5.7 (q=3) / -98.5 (q=150) / -310.6 (q=1e6); A-row -8.2; rho -9.2 (q=3)")
print(f"  MY values:                     E-amp {claim2[3]['E-amp']:.1f} / {claim2[150]['E-amp']:.1f} / {claim2[10**6]['E-amp']:.1f}; "
      f"A-row {claim2[3]['A-row']:.1f}; rho {claim2[3]['rho']:.1f}")

# T=3 corner (freeze:15 extra-corner convention)
print("-- T=3 extra corners:")
for q in [3,10**6]:
    ray_report(Corner(q,T=3.0))

# ---------- refuters' W=13 (the wrong-corner instance the judge caught) ----------
print("="*100)
print("WRONG-CORNER REPLAY: W=13 at q=3 (judge's catch, my arithmetic)")
W_EXP=13
c13=Corner(3); v13=lg_from_nats(c13.lnR_E(c13.s_tau))
print(f"  E-amp at tau, W=13: 10^{v13:+.1f}  (judge: 10^+102.0)  -> {'DIVERGES, catch CONFIRMED' if v13>0 else 'hm?'}")
W_EXP=14

# ---------- CLAIM 3: crush coverage condition ----------
print("="*100)
print("CLAIM 3: crush coverage  12 b0^2 lnq >= 3(1-b0^2) ln(1/u) + ln(6M) + 4.1  (judge margins 1.76/2.52/5.9/10.7)")
print("  domain: DEEP branch u <= u* (crush is R5's, consumed before the tau-inversion) => b0 >= 1-u*")
def crush_margin(q, s):
    u = math.exp(-s); b0=1-u; M=Mpv(q)
    LHS = 12*b0*b0*ln(q)
    RHS = 3*(1-b0*b0)*s + ln(6*M) + 4.1
    return LHS, RHS
for q in [3,5,150,10**6]:
    c=Corner(q)
    # worst over the whole branch: scan s in [ln(1/u*), 3000]
    worst=None
    for i in range(4001):
        s = c.s_ustar + (3000-c.s_ustar)*i/4000
        L,R = crush_margin(q,s)
        m = L/R
        if worst is None or m < worst[0]: worst=(m,s,L,R)
    Lu,Ru = crush_margin(q, c.s_ustar)
    Ld,Rd = 12*ln(q), ln(6*Mpv(q))+4.1     # deep limit u->0
    print(f"  q={q:>7g}: at u* {Lu:6.2f} vs {Ru:5.2f} -> {Lu/Ru:5.2f}x | deep-limit {Ld:6.2f} vs {Rd:5.2f} -> {Ld/Rd:5.2f}x"
          f" | scan worst {worst[0]:5.2f}x at s={worst[1]:.1f} | u-uniform>1: {worst[0]>1}")
print("  NOTE which corner the judge quoted: q=3 matches the u* corner; q=5/150/1e6 match the DEEP limit,")
print("  while the true u-uniform worst is the u* corner (slightly smaller).")
# the sigma-floor-edge probe demanded by the tasking: b0 near 13/14 => u = 1/14 -- on which branch?
u_edge = 1-13/14
print(f"  b0=13/14 probe: u=1/14={u_edge:.4f} vs u*_max over q,T = {Corner(3).ustar:.4f}"
      f" -> u=1/14 is {'TRIVIAL-branch (crush never runs there); worst in-window b0 = 1-u*' if u_edge> Corner(3).ustar else 'IN WINDOW: MUST CHECK'}")
Lw,Rw = crush_margin(3, Corner(3).s_ustar)
print(f"  worst-b0 evaluation check (q=3): b0=1-u*={1-Corner(3).ustar:.5f}, LHS uses b0^2={(1-Corner(3).ustar)**2:.5f} -> {Lw:.2f} (judge 13.0: consistent)")

# ---------- CLAIM 4: X1 cap ----------
print("="*100)
print("CLAIM 4: X1=2330 caps x^{1-b0} <= e^{2.6} e^{14/e} = 2322")
cap = math.exp(2.6+14/math.e)
print(f"  e^(2.6+14/e) = {cap:.1f} <= 2330: {cap<=2330}")
print(f"  derivation: 104 u lnQ <= 104 lnQ/(40(lnQ+2)) < 104/40 = 2.6 (sup, strict); W u ln(1/u) <= 14/e (global max of u ln(1/u))")
# honest sup on the actual deep branch (u <= u*(Q)), sup over Q:
def g_ulnx(q,T=2.0):
    c=Corner(q,T); u=c.ustar
    return u*(104*c.lnQ + W_EXP*ln(1/u))
sup = max((g_ulnx(q,T),q,T) for q in [3,4,5,7,10,150,10**4,10**6,10**9,10**12] for T in [2.0,3.0])
print(f"  honest sup of u*lnx on deep branch: e^{sup[0]:.3f} = {math.exp(sup[0]):.1f} at q={sup[1]:g},T={sup[2]:g}"
      f" (as Q->inf -> e^2.6={math.exp(2.6):.1f}); X1=2330 conservative by ~{2330/math.exp(sup[0]):.0f}x")
print(f"  R7 floor-cancel needs e^y-1 <= y*X1 with y=u lnx: e^y<=X1 suffices; holds since {cap:.0f}<=2330")

# ---------- CLAIM 5: crush streams, landed constants ----------
print("="*100)
print("CLAIM 5: crush stream margin, landed constants (strip 6Mc/r, kill 6sqrt(q)(1+lnq), EM 17, leg2 12M, corner)")
print("  allowance: z^{-u} E'' <= L1(1-b0)/(u(2-b0)) = L1/(2-b0) >= 0.27u  [L1_lower_siegel]; I use 0.27u(1-u) (conservative)")
def stream_lns(q, s, lnD, a_exp):
    """ln of the five E'' streams at u=e^{-s}, cut D=e^{lnD}; a_exp = z-exponent."""
    c=Corner(q); u=math.exp(-s); b0=1-u
    lnz = 12*c.lnQ + a_exp*s
    Mk = Mpv(q); Mc = min(q/2.0, Mk)      # strip char-scale: trivial q/2 vs PV, best available
    t1 = u*lnz + s + ln(6*Mc) - lnD                   # (z^u/u) 6Mc/D
    zk = s + ln(6*Mk) - b0*lnD                        # (6Mk/u) D^-b0
    co = zk + u*(lnz - lnD)                           # corner A(D)T(z/D): zk * (z/D)^u
    em = ln(17.0) + lnD - b0*lnz                      # 17 D z^-b0
    l2 = ln(12*Mk) + lnD - b0*lnz                     # 12M D z^-b0
    ls = [t1,zk,co,em,l2]
    m = max(ls); tot = m + ln(sum(math.exp(l-m) for l in ls))
    return tot + (-u*lnz), lnz                        # ln(total * z^-u)
def allow_ln(s):
    u=math.exp(-s)
    return ln(0.27) - s + math.log1p(-u)
# (i) reproduce the claimed 20.1x at q=3, u*, D=sqrt(z), a=3
c=Corner(3); s=c.s_ustar
tot,_lnz = stream_lns(3, s, (12*c.lnQ+3*s)/2, 3)
print(f"  q=3, u*, D=sqrt(z), a=3: margin = e^({allow_ln(s):.3f}-({tot:.3f})) = {math.exp(allow_ln(s)-tot):.1f}x  (claim 20.1x)")
tot2,_ = stream_lns(3, s, (12*c.lnQ+2*s)/2, 2)
print(f"  cross-check frozen a=2 same corner: {math.exp(allow_ln(s)-tot2):.2f}x  (refuters' G4 honest reprice said 1.62x)")
# (ii) full deep-branch coverage: min over D, sweep u over (0, u*], for each q
print("  full-branch coverage (min over cut D in [1,z], scan s=ln(1/u) in [ln(1/u*), 3000]):")
for q in [3,5,150,10**6]:
    c=Corner(q)
    worst=None
    for i in range(301):
        s = c.s_ustar + (3000-c.s_ustar)*(i/300)**2   # denser near u*
        lnz = 12*c.lnQ+3*s
        best=None
        for j in range(401):
            lnD = lnz*j/400
            tot,_ = stream_lns(q, s, lnD, 3)
            if best is None or tot<best: best=tot
        marg = allow_ln(s)-best
        if worst is None or marg<worst[0]: worst=(marg,s)
    print(f"    q={q:>7g}: worst margin over branch = {math.exp(worst[0]):8.1f}x at s={worst[1]:7.1f} "
          f"({'PASS' if worst[0]>0 else 'FAIL -- COVERAGE HOLE'})")
print("  (deep-limit analytic: ratio -> 2 sqrt((6Mc+12Mk)(17+12Mk))/(0.27 Q^6) -- e.g. q=3: "
      f"{2*math.sqrt((6*1.5+12*Mpv(3))*(17+12*Mpv(3)))/(0.27*6**6):.4f}, i.e. {0.27*6**6/(2*math.sqrt((6*1.5+12*Mpv(3))*(17+12*Mpv(3)))):.0f}x)")
# delivered-vs-target at the u* corner (claim: 151.62 vs 150.68)
u=c3u=Corner(3).ustar; b0=1-u
tot,_ = stream_lns(3, ln(1/u), (12*Corner(3).lnQ+3*ln(1/u))/2, 3)
deliv = 1/u - math.exp(tot)/(0.27*u*(2-b0))
print(f"  q=3-u* delivered = {deliv:.2f} L1 vs target 1/(u(2-b0)) = {1/(u*(2-b0)):.2f} L1  (claim 151.62 vs 150.68)")

# ---------- CLAIM 6: sigma sweep ----------
print("="*100)
print("CLAIM 6: sigma-sweep, dense [16/17, 1-1e-6], q in {3,5,150,1e6}: max row on each ray (to 20x depth)")
def sweep_sigma(q):
    worst=(-1e18,None,None)
    sigs = [16/17 + (1-1e-6-16/17)*i/60 for i in range(61)]
    for sg in sigs:
        c=Corner(q,sigma=Fr(sg).limit_denominator(10**9)) if False else Corner(q)
        c.sigma=sg; c.s_tau = C_LN + B_W*(1-sg)*c.lnQ + K_W*ln(c.L2)
        st=c.s_tau
        for f in [c.lnR_E,c.lnR_A,c.lnR_x,c.lnR_r,c.lnR_Er]:
            for i in range(0,241):
                s=st*(1+19*i/240)
                v=lg_from_nats(f(s))
                if v>worst[0]: worst=(v,sg,s)
    return worst
for q in [3,5,150,10**6]:
    w=sweep_sigma(q)
    print(f"  q={q:>7g}: max row over (sigma,ray) = 10^{w[0]:7.2f} at sigma={w[1]:.5f}, s={w[2]:.0f} "
          f"-> {'PASS' if w[0]<EIGHTH_LG else 'FAIL'} (vs 1/8=10^-0.90)")
print("  (grades vanish at sigma=13/14 EDGE: eta_E=eta_A=0 -> log-divergent; frozen hypothesis floor stays 16/17,")
print("   so the edge is outside the master's domain; sliver [13/14,16/17) remains UNCOVERED — matches the judge's note.)")

# ---------- extra: trivial split + C_w headroom ----------
print("="*100)
print("EXTRAS: trivial-split boundary, tau<u* globally, C_w headroom at the new tuning")
worst=None
for q in [3,4,5,7,150,10**6,10**9]:
    for T in [2.0,3.0]:
        c=Corner(q,T)
        # max tau over sigma is at sigma->1: s_tau_min = 250ln2 + 14 ln L2
        s_tau_min = C_LN + K_W*ln(c.L2)
        gap = s_tau_min - c.s_ustar
        if worst is None or gap<worst[0]: worst=(gap,q,T)
print(f"  min over (q,T) of [ln(1/tau_max) - ln(1/u*)] = {worst[0]:.1f} nats at q={worst[1]:g},T={worst[2]:g} "
      f"(>0 => tau < u* ALWAYS, trivial split sound): {worst[0]>0}")
cw_head = (EIGHTH_LG - claim2[3]['E-amp'])
print(f"  E-amp q=3 margin at tau = {EIGHTH_LG - claim2[3]['E-amp']:.2f} orders -> C_E headroom factor 10^{cw_head:.1f} "
      f"(~{10**cw_head:.0f}x above CE=100; old freeze pin 1.89e4 = 189x still passes: {cw_head > math.log10(189)})")
print("="*100)
