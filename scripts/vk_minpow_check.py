#!/usr/bin/env python3
"""Numeric refuter for the VMVT-VK minimal-power freeze.

Shipped with the first Salt/Vk commit (freeze VK-MINPOW v2, synthesis-judged).
Applied repairs relative to the original candidate script:
  * W2b bound 1/4 -> 1/6  (orbit spread (3/2)(1/6)=1/4 matches R3's length-1/4 window)
  * hW1 radius P -> P+Y    (Taylor block uses the enlarged radius P+Y; the
    (1+Y/P)^{k+1} <= 2 degradation is derivable from hD since sqrt(P) >> k)

Frozen parameters:
  k(t)  = max(19, ceil(L^{1/4})),  L = ln t
  r(k)  = ceil(k * ln(4 k^2))          [eta(k,r) <= 1/8]
  b     = k*r,  rho = 1/(16 k r)       [block saving]
  Theta(t) = 1e-3 / (L^{3/4} (ln L)^2) [growth half-width]
  Lq(T) = L^{3/4} (ln L)^3, dd = 1e-7, C_chain = 5e6, c6 = 1e-8
  j_cut = 96 L^{3/4} (ln L)^2          [trivial/VK boundary]
  Block: P = N^{1-beta}, beta = r0/(k+1), r0 = ceil(L/j), Y = P^{1/2}
  delta_j = P^{-j-rho}/(16k) box sides; good coord j* = r0+2
"""
import math
ln = math.log

def params(L):
    k = max(19, math.ceil(L**0.25))
    r = math.ceil(k * ln(4*k*k))
    b = k*r
    rho = 1.0/(16*k*r)
    lnL = ln(L)
    Theta = 1e-3/(L**0.75 * lnL**2)
    jcut = 96*L**0.75*lnL**2
    return k, r, b, rho, Theta, jcut

def check(name, cond, detail):
    print(f"  [{'OK' if cond else 'FAIL'}] {name}: {detail}")
    return cond

allok = True
print("== eta budget: eta(k,r) = 0.5 k^2 (1-1/k)^r <= 1/8 for r = ceil(k ln 4k^2), k in {19..2000, 5.6e6} ==")
for k in [19, 20, 50, 100, 562, 2000, 5623414]:
    r = math.ceil(k*ln(4*k*k))
    eta = 0.5*k*k*math.exp(r*ln(1-1.0/k))  # (1-1/k)^r via exp
    allok &= check(f"k={k}", eta <= 0.125, f"r={r}, eta={eta:.4f}")

print("\n== block budget ledger: 2b*rho + k*rho + eta + lnD_term <= 1/2  (need lnP >= 8*ln((16k)^k D)) ==")
for k in [19, 562, 5623414]:
    r = math.ceil(k*ln(4*k*k)); b = k*r; rho = 1.0/(16*k*r)
    lnD_full = k*ln(16*k) + 24*k*k*r*ln(k)      # ln((16k)^k * k^{24 k^2 r})
    lnP_floor = 8*lnD_full
    eta = 0.5*k*k*math.exp(r*ln(1-1.0/k))
    total = 2*b*rho + k*rho + eta + lnD_full/lnP_floor
    allok &= check(f"k={k}", total <= 0.5 + 1e-12,
                   f"2b*rho={2*b*rho:.4f}, k*rho={k*rho:.6f}, eta={eta:.4f}, D-term={lnD_full/lnP_floor:.4f}, total={total:.4f}, lnP_floor={lnP_floor:.3e}")

print("\n== j_cut vs D-floor margin: lnP at j_cut >= 8*ln((16k)^k D), with lnP = j - L/(k+1) ==")
for L in [1.3e26, 1e27, 1e30]:
    k, r, b, rho, Theta, jcut = params(L)
    lnD_full = k*ln(16*k) + 24*k*k*r*ln(k)
    lnP_at_jcut = jcut - L/(k+1)
    allok &= check(f"L={L:.1e}", lnP_at_jcut >= 8*lnD_full,
                   f"k={k}, r={r}, lnP(j_cut)={lnP_at_jcut:.3e}, 8lnD={8*lnD_full:.3e}, margin={lnP_at_jcut/(8*lnD_full):.2f}x")

print("\n== trivial regime: Theta * j_cut = 96e-3 = O(1); Theta*2L when trivial-only ==")
for L in [18.0, 18.42, 69.1, 1e10, 5e21, 1e25]:
    k, r, b, rho, Theta, jcut = params(L)
    tj = Theta*jcut; t2L = Theta*2*L
    # trivial covers ALL scales iff 2L <= jcut (then no VK/vdC needed at all)
    allok &= check(f"L={L:.3g}", tj <= 0.097 and (2*L > jcut or t2L <= 0.2),
                   f"Theta={Theta:.3e}, Theta*j_cut={tj:.3f}, 2L={2*L:.3g} vs j_cut={jcut:.3g}, Theta*2L={t2L:.3e}, trivial-only={2*L<=jcut}")

print("\n== vdC top-scale constraint (r0<=10 scales, worst landed saving 1/(2^12-2)) Theta <= half of it ==")
worst_vdc = 1.0/(2**12-2)
for L in [18.0, 69.1, 1e22, 1e27]:
    k, r, b, rho, Theta, jcut = params(L)
    allok &= check(f"L={L:.3g}", Theta <= worst_vdc/2, f"Theta={Theta:.3e} vs {worst_vdc/2:.3e}")

print("\n== VK window at deep anchor L = 1e27 (t = e^{1e27}); sample scale j = 3e26 ==")
L = 1e27
k, r, b, rho, Theta, jcut = params(L)
# VK range: r0 in [11, k-8]  <-> j in [L/(k-8), L/10]; j must also be >= j_cut
jlo, jhi = max(jcut, L/(k-8)), L/10
print(f"  k={k}, r={r}, b={b:.3e}, rho={rho:.3e}, j_cut={jcut:.3e}, VK j-range=[{jlo:.3e},{jhi:.3e}]")
allok &= check("VK range nonempty", jlo < jhi, f"[{jlo:.3e}, {jhi:.3e}]")
for j in [jlo*1.01, 1e26, 5e25]:
    if j > jhi: continue
    r0 = math.ceil(L/j); beta = (r0+1)/(k+1); lnN = j; lnP = (1-beta)*j
    jstar = r0+2
    # (W1') Taylor with slack power at RADIUS P+Y:  t*((P+Y)/N)^{k+1} <= N^{-1} <= P^{-rho}(margin)
    #   ln((P+Y)) = lnP + ln(1 + Y/P), Y = sqrt(P) so Y/P = P^{-1/2} = exp(-lnP/2).
    #   hW1 log form: L + (k+1)*(ln(P+Y) - lnN) + lnN <= 0, then still leaves rho*lnP saving.
    slackPY = (k+1)*ln(1.0 + math.exp(-0.5*lnP))     # (1+Y/P)^{k+1} degradation, ~ (k+1)/sqrt(P)
    w1 = L - (r0+1)*j + rho*lnP + slackPY
    # (W2a) spacing: ln s_lower >= ln(4 delta_js);  t > N^{r0-1} (worst t on this scale)
    lhs_a = (r0-1)*lnN - ln(2*math.pi) - (jstar+1)*(lnN+ln(2))
    rhs_a = -(jstar+rho)*lnP - ln(4*k)
    w2a = lhs_a - rhs_a
    # (W2b, REPAIRED 1/4 -> 1/6): s_max*Y <= 1/6; s_max = t/(2pi N^{js+1}) with t <= N^{r0}
    lnY = 0.5*lnP
    w2b = (r0*lnN - ln(2*math.pi) - (jstar+1)*lnN) + lnY + ln(6.0)
    # (W2c) 4 k^2 Y <= N
    w2c = ln(4) + 2*ln(k) + lnY - lnN
    # scale saving beats width: rho*lnP >= 2*Theta*j (factor-2 margin)
    sav = rho*lnP - 2*Theta*j
    allok &= check(f"j={j:.3e} (r0={r0}, j*={jstar})",
                   w1 <= 0 and w2a >= 0 and w2b <= 0 and w2c <= 0 and sav >= 0,
                   f"W1'(P+Y)={w1:.3e}<=0, W2a-slack={w2a:.3e}>=0, W2b(1/6)={w2b:.3e}<=0, W2c={w2c:.3e}<=0, rho*lnP-2Th*j={sav:.3e}>=0")

print("\n== Stage-3 cost ledger at region anchors (T0 = 1e30-grade upward) ==")
for L in [69.1, 100.0, 1e10, 1e27]:
    lnL = ln(L)
    k, r, b, rho, Theta, jcut = params(L)
    K = 30.0
    ln4M0p = ln(8*K*L/Theta)         # ln(4 M0') <= ln(8 K L / Theta)
    allok &= check(f"L={L:.3g}: ln(4M0') <= 7 lnL", ln4M0p <= 7*lnL, f"{ln4M0p:.2f} vs {7*lnL:.2f}")
    Lq = L**0.75*lnL**3
    CL = (7.0/(6*Theta))*120*ln4M0p + 2
    C4 = CL/Lq
    allok &= check(f"L={L:.3g}: C4 = CL/Lq <= 1e6", C4 <= 1e6, f"C4={C4:.3e}")
    allok &= check(f"L={L:.3g}: 5*C4+8 <= 5e6", 5*C4+8 <= 5e6, f"{5*C4+8:.3e}")
    dd = 1e-7
    allok &= check(f"L={L:.3g}: dd/Lq <= 0.486*Theta", dd/Lq <= 0.486*Theta, f"dd/Lq={dd/Lq:.3e}, 0.486Th={0.486*Theta:.3e}")
    allok &= check(f"L={L:.3g}: dd/7 >= c6=1e-8", dd/7 >= 1e-8, f"{dd/7:.3e}")

print("\n== approx-formula error terms at prescribed anchors (N = t^2 truncation) ==")
for L in [18.42, 69.1]:   # t = 1e8, 1e30
    k, r, b, rho, Theta, jcut = params(L)
    lnerr = ln(2) + L - (1-Theta)*2*L                # |s| N^{-sigma}/sigma, N=e^{2L}
    lntail = 2*Theta*L - 0                            # N^{1-s}/(s-1) tail
    allok &= check(f"L={L}: approx error e^{{{lnerr:.2f}}} = O(1)", lnerr < 0, f"lnerr={lnerr:.2f}")
    allok &= check(f"L={L}: pole tail exp={lntail:.3e} = O(1)", lntail < 0.01, f"")
    nb = 2*L/ln(2)+1
    tot = nb*math.exp(Theta*2*L)
    allok &= check(f"L={L}: trivial-routing growth sum {tot:.1f} <= 30*L = {30*L:.0f}", tot <= 30*L, "")

print("\n== r0<=10 landed-window floors at deep anchor: N >= (12!)^6 for VK-era top scales ==")
L=1e27
allok &= check("N at r0=10 scale", L/11 * 1 >= ln(math.factorial(12)**6),
               f"ln N = {L/11:.3e} >= ln((12!)^6) = {ln(math.factorial(12)**6):.1f}")

print("\n== width comparison vs landed c3/log t (informational) ==")
for L in [69.1, 1e10, 1e37, 1e40]:
    lnL=ln(L); w_new = 1e-8/(L**0.75*lnL**3); w_old = 1/(75712*L)
    print(f"  L={L:.2g}: new={w_new:.3e}, landed={w_old:.3e}, new/old={w_new/w_old:.3e}")

print("\nALL:", "PASS" if allok else "FAIL")
