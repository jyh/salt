#!/usr/bin/env python3
"""
SS2 - concrete super-solution profile: exact-rational certificate generator.

Deterministically reconstructs and EXACT-RATIONAL verifies the piecewise-linear super-solution
(Ebar, Obar) for the twin-prime numeric keystone (see docs/blueprints/flags.md, "SS2", and
Salt/Chen/SuperProfile.lean).  No floats in the certificate; requires only `fractions` + `mpmath`
(mpmath used solely for rigorous rational log lower/upper bounds).

Verifies:  int Ebar <= 43/75,  int_3^inf Obar <= 11/125,  and all 200 hSE + 220 hSO panel
domination inequalities (rational quadratics >= 0), plus the power-tail K/x^3 seam/self-domination.

Run:  python3 scripts/ss2_profile.py
"""

from fractions import Fraction as F
import mpmath as mp
mp.mp.dps=50

h=F(1,20); W=F(12); K=F(1,10000); Ktail=K/(2*W*W)
D=10**7  # rounding denominator for knot values / log bounds
def grid(lo,hi):
    xs=[]; i=int(round(lo*20))
    while F(i,20)<=hi: xs.append(F(i,20)); i+=1
    return xs
gE=grid(F(2),W); gO=grid(F(1),W); nE=len(gE)-1; nO=len(gO)-1
def loglow(x):
    v=mp.log(mp.mpf(x.numerator)/x.denominator); return F(int(mp.floor(v*D)),D)
def loghigh(x):
    v=mp.log(mp.mpf(x.numerator)/x.denominator); return F(int(mp.ceil(v*D)),D)
L3up=loghigh(F(3))
# precompute log-lower knots at each a-1 for a in gE with 2<=a<=4
LL={}
for a in gE:
    if F(2)<=a<=F(4) and a>F(1):
        LL[a]=loglow(a-1)

def ceilD(x): 
    from math import ceil
    n=x.numerator; d=x.denominator
    return F(-((-n*D)//d), D)  # ceil(x*D)/D

# PL integral int_x^inf, exact
def Gint(g,c,x):
    tot=Ktail
    for i in range(len(g)-1):
        l=g[i]; r=g[i+1]
        if r<=x: continue
        L=l if l>=x else x
        # value at L:
        vl=c[l]+(c[r]-c[l])*(L-l)/(r-l); vr=c[r]
        tot+=(vl+vr)/2*(r-L)
    return tot

# fseq2 upper as AFFINE-over-v function on panel [a,ap]; returns (p0,p1) with maj_num(v)=p0+p1*v
def f2maj_num(a,ap):
    ap=min(ap,F(4))
    if a>=F(4): return (F(0),F(0))
    la=LL.get(a, loglow(a-1)); lap=LL.get(ap, loglow(ap-1))
    # chord(v)=la*(ap-v)/(ap-a)+lap*(v-a)/(ap-a) = A + B v
    B=(lap-la)/(ap-a); A=la - B*(a)  # since la*(ap-v)+lap*(v-a) all /(ap-a): = [la*ap-la*v+lap*v-lap*a]/(ap-a)=[la*ap-lap*a +(lap-la)v]/(ap-a)
    A=(la*ap-lap*a)/(ap-a); B=(lap-la)/(ap-a)
    # maj_num(v)=v-3(A+Bv)+3L3up-4 = (-3A+3L3up-4) + (1-3B) v
    return (-3*A+3*L3up-4, 1-3*B)

# ---- rational fixed point with round-up ----
cE={a:F(0) for a in gE}; cO={a:F(0) for a in gO}
for it in range(400):
    changed=False
    for i,a in enumerate(gE):
        if i<nE: p0,p1=f2maj_num(a,gE[i+1])
        else: p0,p1=f2maj_num(a,a)
        f2a=(p0+p1*a)/a if a<F(4) else F(0)
        nv=ceilD(f2a + Gint(gO,cO,a-1)/a)
        if nv>cE[a]: cE[a]=nv; changed=True
    for j,d in enumerate(gO):
        xarg=d-1 if d-1>=F(2) else F(2)
        nv=ceilD(Gint(gE,cE,xarg)/d)
        if nv>cO[d]: cO[d]=nv; changed=True
    if not changed: break
print("fixed point iters",it)

# ---- budgets (exact) ----
def budE():
    tot=Ktail
    for i in range(nE): tot+=(cE[gE[i]]+cE[gE[i+1]])/2*h
    return tot
def budO():
    tot=Ktail
    for j in range(nO):
        l=gO[j]; r=gO[j+1]
        if r<=F(3): continue
        L=l if l>=F(3) else F(3)
        vl=cO[l]+(cO[r]-cO[l])*(L-l)/(r-l); vr=cO[r]
        tot+=(vl+vr)/2*(r-L)
    return tot
bE=budE(); bO=budO()
print("budgetE=",float(bE)," <=43/75=",float(F(43,75)),"  OK" if bE<=F(43,75) else " FAIL","slack",float(F(43,75)-bE))
print("budgetO=",float(bO)," <=11/125=",float(F(11,125)),"  OK" if bO<=F(11,125) else " FAIL","slack",float(F(11,125)-bO))

# ---- verify hSE per-panel quadratic q(v)=L(v)*v - (f2maj_num(v)+GO(v-1)) >=0 on [a,ap] ----
def quad_nonneg(c2,c1,c0,a,ap):
    # q(v)=c2 v^2+c1 v+c0 >=0 on [a,ap]
    qa=c2*a*a+c1*a+c0; qap=c2*ap*ap+c1*ap+c0
    ok=qa>=0 and qap>=0
    if c2>0:  # convex, min at vertex
        vx=-c1/(2*c2)
        if a<=vx<=ap:
            ok=ok and (c2*vx*vx+c1*vx+c0)>=0
    # if c2<0 concave, min at endpoints (already checked)
    return ok,float(qa),float(qap)

failSE=0
for i in range(nE):
    a=gE[i]; ap=gE[i+1]
    s=(cE[ap]-cE[a])/(ap-a)
    # L(v)*v = (cE[a]-s*a)*v + s*v^2
    Lc2=s; Lc1=cE[a]-s*a; Lc0=F(0)
    p0,p1=f2maj_num(a,ap)  # fseq2 maj_num affine
    # GO(v-1) on panel: Obar linear on [a-1,ap-1]; GO(v-1)=GO(ap-1)+int_{v-1}^{ap-1}Obar
    la1=a-1; lap1=ap-1
    # Obar on [la1,lap1]: value pO+qO*u
    if lap1<=W:
        oL=cO[la1]; oR=cO[lap1]; qO=(oR-oL)/(lap1-la1); pO=oL-qO*la1
        GOap=Gint(gO,cO,lap1)
        # int_{v-1}^{lap1}(pO+qO u)du = pO*(lap1-(v-1)) + qO/2*(lap1^2-(v-1)^2)
        # as poly in v: let u0=v-1. = pO*lap1 - pO*u0 + qO/2*lap1^2 - qO/2*u0^2
        # u0=v-1 => u0^2=v^2-2v+1
        # GO(v-1)=GOap + pO*lap1 - pO*(v-1) + qO/2*lap1^2 - qO/2*(v^2-2v+1)
        G2=-qO/2; G1= pO*(-1)*(-1)  # from -pO*(v-1): -pO*v +pO ; and -qO/2*(-2v)=+qO*v
        G1=-pO + qO
        G0=GOap + pO*lap1 + pO*0 + qO/2*lap1*lap1 - qO/2*1 + pO*1  # constants: GOap+pO*lap1 +pO*(+1 from -pO*(v-1)->+pO) + qO/2 lap1^2 - qO/2
        # recompute cleanly:
        G2=-qO/2
        G1=-pO+qO
        G0=GOap + pO*lap1 + pO + qO/2*lap1*lap1 - qO/2
    else:
        # tail region entirely; skip (handled separately) - shouldn't happen for i<nE since ap<=W
        G2=G1=G0=F(0)
    # q(v)=L(v)*v - (p0+p1*v) - GO(v-1) = (Lc2-G2)v^2 + (Lc1-p1-G1)v + (Lc0-p0-G0)
    c2=Lc2-G2; c1=Lc1-p1-G1; c0=Lc0-p0-G0
    ok,qa,qap=quad_nonneg(c2,c1,c0,a,ap)
    if not ok: failSE+=1
    if i<3 or (a>=F(2) and a<=F(2)+2*h): pass
print("hSE panel failures:",failSE,"/",nE)

# ---- verify hSO per-panel ----
failSO=0
for j in range(nO):
    d=gO[j]; dp=gO[j+1]
    s=(cO[dp]-cO[d])/(dp-d)
    Mc2=s; Mc1=cO[d]-s*d  # M(w)*w = s w^2 + (cO[d]-s d) w
    if dp<=F(3):
        # flat: need M(w)*w >= GE(2) (constant C) on [d,dp]
        C=Gint(gE,cE,F(2))
        c2=Mc2; c1=Mc1; c0=-C
    else:
        # d>=3: need M(w)*w >= GE(w-1). GE(w-1)=quadratic (Ebar linear on [d-1,dp-1])
        ld1=d-1; ldp1=dp-1
        eL=cE[ld1]; eR=cE[ldp1]; qE=(eR-eL)/(ldp1-ld1); pE=eL-qE*ld1
        GEdp=Gint(gE,cE,ldp1)
        R2=-qE/2; R1=-pE+qE; R0=GEdp+pE*ldp1+pE+qE/2*ldp1*ldp1-qE/2
        c2=Mc2-R2; c1=Mc1-R1; c0=-R0
    ok,qa,qap=quad_nonneg(c2,c1,c0,d,dp)
    if not ok: failSO+=1
print("hSO panel failures:",failSO,"/",nO)
print("max denom cE:",max(v.denominator for v in cE.values())," cO:",max(v.denominator for v in cO.values()))

print("\n=== TAIL + SEAM verification (v,w >= W=12) ===")
# TOseam = int_{11}^{inf} Obar = int_{11}^{12} Obar_head + Ktail
TOseam=Ktail
for j in range(nO):
    l=gO[j]; r=gO[j+1]
    if r<=F(11): continue
    L=l if l>=F(11) else F(11)
    vl=cO[l]+(cO[r]-cO[l])*(L-l)/(r-l); vr=cO[r]
    TOseam+=(vl+vr)/2*(r-L)
TEseam=Ktail
for i in range(nE):
    l=gE[i]; r=gE[i+1]
    if r<=F(11): continue
    L=l if l>=F(11) else F(11)
    vl=cE[l]+(cE[r]-cE[l])*(L-l)/(r-l); vr=cE[r]
    TEseam+=(vl+vr)/2*(r-L)
# hSE seam [12,13): need K >= 169 * TOseam   (K/v^2 >= TOseam, worst v=13)
print("hSE seam: K=",float(K)," need >= 169*TOseam=",float(169*TOseam), "OK" if K>=169*TOseam else "FAIL")
print("hSO seam: K=",float(K)," need >= 169*TEseam=",float(169*TEseam), "OK" if K>=169*TEseam else "FAIL")
# hSE tail [13,inf): 2(v-1)^2>=v^2 for v>=13 : v^2-4v+2>=0 at v=13 =119>0, increasing -> holds
print("hSE/hSO tail [13,inf): v^2-4v+2 at 13 =",13*13-4*13+2," (>=0, increasing) OK")
# also confirm K/v^3 >= E(v),O(v) for v>=12 (domination of true fixed pt, sanity): tail>>true
print("K/12^3=",float(K/(12**3)))

# ---- verify hSE knot values dominate the true operator (sanity: cE ~ E) ----
print("\nSanity: cE[2]=",float(cE[F(2)]),"(E(2)~0.999)  cE[3]=",float(cE[F(3)]),"(E(3)~0.177)")
print("cO[3]=",float(cO[F(3)]),"(O(3)~0.187)  cO[1]=",float(cO[F(1)]),"(O(1)~0.561)")

# ---- Save the profile knot tables for Lean generation ----
import json
prof={
 'h':[h.numerator,h.denominator],'W':[W.numerator,W.denominator],
 'K':[K.numerator,K.denominator],
 'gE':[[a.numerator,a.denominator] for a in gE],
 'cE':[[cE[a].numerator,cE[a].denominator] for a in gE],
 'gO':[[a.numerator,a.denominator] for a in gO],
 'cO':[[cO[a].numerator,cO[a].denominator] for a in gO],
 'budE':[bE.numerator,bE.denominator],'budO':[bO.numerator,bO.denominator],
}
import os; json.dump(prof, open(os.environ.get('SS2_OUT','/tmp/ss2_profile.json'),'w'))
print("\nSaved profile.json. Panels E=%d O=%d"%(nE,nO))
print("budgetE=%s"%(bE)); print("budgetO=%s"%(bO))
