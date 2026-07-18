#!/usr/bin/env python3
"""REFUTER 1 — claim-5 coverage, corrected D-optimization.
ln(total(streams)) is log-sum-exp of AFFINE functions of lnD => convex in lnD.
Ternary-search the exact min instead of a coarse grid (the grid FAIL at s=3000 was
a 22.5-nat spacing artifact vs the analytic deep-limit 112x margin)."""
import math
ln = math.log
def Mpv(q): return math.sqrt(q)*(1+ln(q))
class C:
    def __init__(s_,q,T=2.0):
        s_.q=q; s_.Q=q*T; s_.lnQ=ln(s_.Q); s_.L2=s_.lnQ+2
        s_.ustar=1/(40*s_.L2); s_.s_ustar=ln(1/s_.ustar)
        s_.s_tau = 250*ln(2)+40*s_.lnQ+14*ln(s_.L2)   # sigma=16/17
def tot_ln(q,s,lnD,a=3,lnQ=None):
    c=C(q); u=math.exp(-s); b0=1-u
    lnz=12*c.lnQ+a*s; Mk=Mpv(q); Mc=min(q/2.0,Mk)
    t1 = u*lnz + s + ln(6*Mc) - lnD
    zk = s + ln(6*Mk) - b0*lnD
    co = zk + u*(lnz-lnD)
    em = ln(17.0) + lnD - b0*lnz
    l2 = ln(12*Mk) + lnD - b0*lnz
    ls=[t1,zk,co,em,l2]; m=max(ls)
    return m+ln(sum(math.exp(l-m) for l in ls)) - u*lnz, lnz
def min_tot(q,s,a=3):
    lnz = 12*C(q).lnQ+a*s
    lo,hi=0.0,lnz
    for _ in range(200):
        m1=lo+(hi-lo)/3; m2=hi-(hi-lo)/3
        if tot_ln(q,s,m1,a)[0] < tot_ln(q,s,m2,a)[0]: hi=m2
        else: lo=m1
    d=(lo+hi)/2
    return tot_ln(q,s,d,a)[0], d, lnz
def allow_ln(s):
    u=math.exp(-s); return ln(0.27)-s+math.log1p(-u)

print("Full deep-branch coverage, EXACT min over D (ternary, convex), a=3, landed constants:")
print("  margin(s) = allowance / min_D(total*z^-u); scan s=ln(1/u) from ln(1/u*) to 3000 (past all taus);")
for q in [3,5,150,10**6]:
    c=C(q); worst=None; at_tau=None; at_ustar=None
    for i in range(601):
        s = c.s_ustar + (3000-c.s_ustar)*i/600
        t,d,lnz = min_tot(q,s)
        marg = allow_ln(s)-t
        if worst is None or marg<worst[0]: worst=(marg,s,d,lnz)
        if at_ustar is None: at_ustar=marg
        if at_tau is None and s>=c.s_tau: at_tau=marg
    print(f"  q={q:>7g}: WORST margin e^{worst[0]:7.2f} = {math.exp(min(worst[0],700)):10.4g}x at s={worst[1]:7.1f} "
          f"(lnD*={worst[2]:.0f}/lnz={worst[3]:.0f}) | at u* {math.exp(min(at_ustar,700)):.3g}x | at tau {math.exp(min(at_tau,700)):.3g}x"
          f" -> {'PASS' if worst[0]>0 else 'FAIL'}")
# sanity: deep-limit analytic vs ternary at s=3000, q=3
q=3; t,d,lnz = min_tot(3,3000.0)
Mk=Mpv(3); pred = ln(2*math.sqrt((6*1.5+12*Mk)*(17+12*Mk))/(0.27*6**6))
print(f"  cross-check q=3 s=3000: ternary ratio ln={t-allow_ln(3000.0):.3f} vs analytic deep-limit ln={pred:.3f} (should match ~)")
# also verify the q=3 u* D=sqrt(z) 20.1x is not an artifact of D-choice: min-D at u*
t,d,lnz = min_tot(3,C(3).s_ustar)
print(f"  q=3 at u*: min-D margin {math.exp(allow_ln(C(3).s_ustar)-t):.1f}x (D=sqrt(z) gave 20.1x; lnD*={d:.2f} vs lnz/2={lnz/2:.2f})")
