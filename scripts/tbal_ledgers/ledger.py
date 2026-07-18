import math
L=lambda v: math.log10(v)
def ledger(q, tag):
    print(f"=== {tag}: q={q} ===")
    T=2.0; Q=q*T
    L2=math.log(Q)+2
    ustar=1/(40*L2)
    sigma=16/17
    lnQ=math.log(Q)
    u=ustar
    z=Q**12*u**-2
    lnz=12*lnQ+2*math.log(1/u)
    lnx=104*lnQ+11*math.log(1/u)
    log10x=lnx/math.log(10)
    M=math.sqrt(q)*(1+math.log(q))
    P=8*M  # cap
    X1=math.exp(2.6)*math.exp(11/math.e)
    c0=1/126848
    print(f"Q={Q:.3g} L2={L2:.4g} u*={ustar:.4g} log10(z)={L(z):.4g} log10(x)={log10x:.4g} X1={X1:.4g} M={M:.4g}")
    # ledger (1): old sqrt-error smallest index 20M
    print(f"(1) OLD sqrt-error 20M = {20*M:.3g}  vs <1/4  [ABSENT in new design]")
    # (3) E(beta0)-amplified: 2*x^{b0-s}E(b0) with x^{-b0} folded -> x^{-sigma}
    CE=100
    lf3=(1+lnx)**3
    lz12=(1+2*lnz)**12
    z4=4*L(z)
    E0amp = L(2)+L(CE)+L(P)+L(2)+L(lf3)+L(lz12)+z4+(-sigma*log10x)+L(1+1/u)
    print(f"(3) E(b0)-amp: 10^{E0amp:.2f}   [z^4=10^{z4:.1f} (1+logx)^3=10^{L(lf3):.2f} (1+2logz)^12=10^{L(lz12):.2f} x^-s=10^{-sigma*log10x:.1f} 1+1/u={1+1/u:.3g}]  vs 1/8")
    # (4) E(rho): dust carries L2/c0 instead of 1/u; z^{2+2sigma}
    Erho = L(CE)+L(P)+L(1+math.sqrt(2))+L(lf3)+L(lz12)+(2+2*sigma)*L(z)+(-sigma*log10x)+L(L2/c0)
    print(f"(4) E(rho): 10^{Erho:.2f}  [L2/c0=10^{L(L2/c0):.2f}]  vs 1/8")
    # (5) delta_d
    Cw=100
    dd=9.3*Cw*P*(1+lnz)**3*(1+1/u)/z
    print(f"(5) delta_d = {dd:.3g} = {dd/u:.3g}*u  vs min(1/2,O(u))")
    # (6) delta_b raw + in-master at tau
    db=300*z**-0.4
    print(f"(6) delta_b raw = {db:.3g}")
    b_,k_,c_=680,14,2**-250
    log10tau = L(c_) - (b_*(1-sigma))*L(Q) - k_*L(L2)
    print(f"    tau = 10^{log10tau:.2f}  [c=10^{L(c_):.2f}, Q^-40=10^{-(b_*(1-sigma))*L(Q):.2f}, L2^-14=10^{-k_*L(L2):.2f}]")
    # in-master delta_b fold at u=tau: 4*X1*x^{1/17}*300*z^{-0.4}, z,x at u=tau
    ut=10**log10tau
    lnz_t=12*lnQ+2*math.log(1/ut); lnx_t=104*lnQ+11*math.log(1/ut)
    fold = L(4*X1*300) + (1/17)*lnx_t/math.log(10) - 0.4*lnz_t/math.log(10)
    print(f"    in-master at tau: 10^{fold:.2f}  vs 1/8 ; margin exp 0.8-11/17 = {0.8-11/17:.4f}")
    # (7) L2.8 residual: err at R=e^{1/u}
    lnR=1/u
    err7 = L(9.3*Cw*P) + 3*L(1+lnR) + (-sigma*lnR/math.log(10)) + L(1+1/u)
    print(f"(7) R3 err@R=e^(1/u): 10^{err7:.2f}  vs 1/8 ; (3/4)/e = {0.75/math.e:.4f} >= 0.27")
    # (8) master u-side at tau: u*x^{1-sigma}*(2*X1*logx + 4*L2/c0)
    K = 2*X1*lnx_t + 4*L2/c0
    us = log10tau + (1/17)*lnx_t/math.log(10) + L(K)
    print(f"(8) master u-side at tau: 10^{us:.2f}  [K={K:.3g}]  vs 1/8")
    # (9) trivial branch
    triv = L(c_) - k_*L(L2)
    print(f"(9) trivial: c*L2^-k = 10^{triv:.2f}  <= u* = {ustar:.3g} : {10**triv <= ustar}")
    # window algebra
    mu1 = 11*sigma-9; mu2 = 1-11*(1-sigma)
    print(f"window: 11s-9={mu1:.3f} (>0 ok), 1-11(1-s)={mu2:.3f} (>0 ok); sigma floor (9+m1)/(10+m1-m2)... at m=0: 9/10")
    print()
ledger(3,"binding corner")
ledger(10**6,"large-q")
# structural: b-tail exponent
print("log2(4/3) =", math.log(4/3,2), " (>0.4 claimed exponent, margin", math.log(4/3,2)-0.4,")")
# b(p^2) identity check numeric, chi=+1, p=2: b(p2)=(1-1/p)^2 ; formula chi*(1-h/p), h=3/2 -> 1-3/4=1/4=(1-1/2)^2 ok
print("b(4) chi=1 p=2: formula", 1*(1-1.5/2), "direct", (1-0.5)**2)
# Rankin factor at exponent 0.6 for p=2 block: sum_k>=2 (1/4)(4/9)(3/2)^k 2^{-0.6k}
s=sum((1/9)*(1.5**k)*(2**(-0.6*k)) for k in range(2,2000))
print("2-adic Rankin block at 0.6:", s)
