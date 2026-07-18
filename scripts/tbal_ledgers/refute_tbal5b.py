#!/usr/bin/env python3
# Refuter ledger v2 — pure log10 arithmetic (no underflow), q in {3,7,1e6}, T corners.
import math
L10 = math.log(10)
def lg(x): return math.log10(x)

c0 = 1.0/126848.0
sigma = 16.0/17.0
B, W, Zb, Zw = 104.0, 11.0, 12.0, 2.0
X1 = 770.0
CE = 100.0
b_wit, k_wit = 680.0, 14.0
lg_c = -250.0*lg(2)

def ledger(q, T, CW):
    Q = q*T; L2 = math.log(Q)+2
    ustar = 1/(40*L2)
    lg_tau = lg_c - b_wit*(1-sigma)*lg(Q) - k_wit*lg(L2)
    M = math.sqrt(q)*(1+math.log(q))
    Prho = 3*M*(1+math.sqrt(2)/sigma); Pb0 = 3*M*2
    rows = {}
    for tag,lgu in (("u*",lg(ustar)),("tau",lg_tau)):
        lgz = Zb*lg(Q) - Zw*lgu; lgx = B*lg(Q) - W*lgu
        lnz, lnx = lgz*L10, lgx*L10
        lg_inv_u = -lgu                      # lg(1/u); (1+1/u) ~ 1/u for u<0.01
        beta0_lgxu = lgx*(10**lgu)/1.0       # u*lg x (for x^{-u} discount, ignored)
        lg_lx3, lg_lz12 = 3*lg(1+lnx), 12*lg(1+2*lnz)
        d = {}
        d["Eb0_amp"] = lg(2*CE*Pb0*2) + lg_lx3 + lg_lz12 + 4*lgz - sigma*lgx + lg_inv_u
        d["Erho"]    = lg(CE*Prho*(1+math.sqrt(2))) + lg_lx3 + lg_lz12 + (2+2*sigma)*lgz - sigma*lgx + lg(L2/c0)
        d["dd"]      = lg(9.3*CW*Prho) + 3*lg(1+lnz) + lg_inv_u - lgz
        d["db"]      = lg(300.0) - 0.4*lgz
        lg_amp = lg(2.0) + (1-sigma)*lgx     # >= (beta0-sigma)lg x; conservative
        d["A"]  = lg_amp + lgu + lg(X1) + lg(lnx)
        d["Bd"] = lg_amp + lg(2*X1) + d["dd"]
        d["Bb"] = lg_amp + lg(2*X1) + d["db"]
        d["D"]  = lg_amp - lgx
        d["F"]  = lg(4*L2/c0) + lgu + (1-sigma)*lgx
        if lg_inv_u < 300:                   # R3 err only meaningful at u*
            invu = 10**lg_inv_u
            d["R3"] = lg(CW*Pb0) + 3*lg(1+invu) + lg(1+invu) - ((1-10**lgu)*invu)/L10
        else: d["R3"] = float("-inf")
        d["dust_b0"]  = lg(Pb0) + lg_inv_u - (1-10**lgu)*lgx
        d["dust_rho"] = lg(Prho) + lg(L2/c0) - sigma*lgx
        d["db_first"] = lg(0.75)*(lgz/lg(2))
        rows[tag] = d
    return dict(q=q,Q=Q,L2=L2,ustar=ustar,lg_tau=lg_tau,M=M,rows=rows,
                lg_trivial=lg_c-k_wit*lg(L2))

for (q,T) in ((3,2),(7,2),(10**6,2),(10**6,3)):
    for CW in (100, 4500):
        o = ledger(q,T,CW)
        r=o["rows"]
        print(f"q={q} T={T} CW={CW}: L2={o['L2']:.2f} u*={o['ustar']:.2e} lgtau={o['lg_tau']:.1f} 20M={20*o['M']:.3g}")
        for tag in ("u*","tau"):
            d=r[tag]
            print(f"  [{tag}] Eb0amp={d['Eb0_amp']:.1f} Erho={d['Erho']:.1f} dd={d['dd']:.2f} db={d['db']:.2f} | "
                  f"A={d['A']:.1f} Bd={d['Bd']:.1f} Bb={d['Bb']:.1f} D={d['D']:.1f} F={d['F']:.1f} R3={d['R3']:.1f} | "
                  f"dust_b0={d['dust_b0']:.1f} dust_rho={d['dust_rho']:.1f} dbfirst={d['db_first']:.1f}")
        print(f"  trivial lg(cL2^-14)={o['lg_trivial']:.1f} <= lg(u*)={lg(o['ustar']):.2f}: {o['lg_trivial']<=lg(o['ustar'])}")

# master total at tau, q=3 (sum of all six pieces, log-domain add)
def lgadd(*xs):
    m=max(xs); return m+lg(sum(10**(x-m) for x in xs))
o=ledger(3,2,4500); d=o["rows"]["tau"]
tot=lgadd(d["A"],d["Bd"],d["Bb"],d["D"],d["F"],d["Eb0_amp"],d["Erho"])
print(f"\nMASTER TOTAL at tau (q=3, CW=4500): lg RHS = {tot:.2f}  (need < lg(3/4) = {lg(0.75):.2f})")

# delta_d <= 1/2 headroom: max CW at the q=3 u* corner
o=ledger(3,2,1.0); base=o["rows"]["u*"]["dd"]     # dd with CW=1
CWmax = 10**(lg(0.5)-base)
print(f"delta_d<=1/2 headroom at q=3,u*: CW_max = {CWmax:.3g} (candidate implied CW~100; refuter used 4500)")

# R5 z-form corner probe (claimed z^{1-b0} form vs heuristic-true H/L1) at both q
for (q,T) in ((3,2),(10**6,2)):
    Q=q*T; L2=math.log(Q)+2; u=1/(40*L2); lnz=(12*lg(Q)-2*lg(u))*L10
    zu=math.exp(u*lnz); claimed=zu/(u*(2-(1-u))); true=1/u+lnz+0.5772
    print(f"R5 z-form (q={q},u*): claimed(d=0)/L1={claimed:.1f} vs heuristic-true/L1={true:.1f} ratio={claimed/true:.4f}"
          f" | z-free form={1/(u*(2-(1-u))):.1f} (safe)")

# sigma-sweep for Bb (the binding margin): Q-exponent must stay negative on (0,1/17]
print("\nBb sigma-sweep f(w)=-4.8-440w+7480w^2:",
      [round(-4.8-440*w+7480*w*w,1) for w in (1/17,0.0294,0.02,0.01,0.001)])
# monotone-cap thresholds
print("monotone thresholds lg t* = (1-j/eta)/ln10:",
      [(lab, round((1-j/eta)/L10,1)) for (eta,j,lab) in
       ((0.153,14,"Bb"),(6/17,15,"A/F"),(1.35,15,"Eb0"),(2.588,15,"Erho"))], "vs lg tau=-114.5")
# R7 self-consistency: honest positive mass u log^2 x vs budget at tau (q=3)
Q=6; lnx=(104*lg(Q)+11*114.5)*L10
print(f"R7 probe q=3 at tau: lg(u ln^2 x)={-114.5+2*lg(lnx):.1f} vs lg(2 db X1)={lg(2*X1*300)-0.4*(12*lg(Q)+2*114.5):.1f}")
# X1 cap check: x^{1-b0} <= e^{2.6} e^{11/e} = 770?
print(f"X1 cap: e^2.6*e^(11/e) = {math.exp(2.6)*math.exp(11/math.e):.0f}; sup u(104 lgQ*ln10*... ) check at q=3: "
      f"104*u**{0}: u*logQ<=1/40 -> e^2.6={math.exp(2.6):.1f}, 11*u*ln(1/u)<=11/e -> e^(11/e)={math.exp(11/math.e):.1f}")
