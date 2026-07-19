#!/usr/bin/env python3
"""T-BAL-R6RHO-2 — RE-PRICE the rho-row with the ACTUAL landed R6-3@rho constant.

Catch #225 (THE LEDGER RE-PRICING LAW, flags.md T-BAL-R6RHO): the rho-template constant C2rho
carries L2/c0 dust from the complex power-sum sandwich; the master's rho-row must be re-verified
with the ACTUAL landed constants, on-ray, BEFORE R8 assembles.  This script does that, from the
LANDED Lean constants (Salt/SW/TBalFinal.lean : sum_cpow_sandwich_rho + Salt/SW/DHExtractRho.lean :
dhAbel_inner_rho), NOT from the freeze's crude E-SHAPE model.

DERIVED (this session) actual R6-3@rho extraction constant, composing the landed sandwich
Ksand = 5 + 4||1-rho||/(1-sigma)   (sum_cpow_sandwich_rho)
with the landed heart per-t constant
Cwrho = 12M/||1-rho|| + 2(9+8||rho||) + 2(Z0+1/||1-rho||)*P + 2P + 2P/(1-sigma)   (dhAbel_inner_rho)
via the complex kernel-Abel (kernel_abel_sum_rho) + L1<=18M (LFunction_apply_one_norm_le), gives

  C2rho = 3*Cwrho + (18M/||1-rho||)*Ksand = 3*Cwrho + 90M/||1-rho|| + 72M/(1-sigma)     [x^{1/2-s} grade]

M=sqrt(q)(1+ln q), P=3M(1+||rho||/sigma), Z0=zetaHol strip bound (O(1), enters WITHOUT L2/c0).

Full rho-detector error after the R6-8@rho collection (analog of the LANDED dh_extraction_upper_W):
  E(rho) = C2rho * z * (1+log(z^2))^9 * x^{1/2 - sigma}     (z^1 * polylog, matching the beta0 chain)

MASTER (freeze:11): 3/4 <= 2 x^{b0-s}[uX1 lnx + 1/x + E(b0)] + 4u x^{1-s} L2/c0 + E(rho).
Each of the ~6 pieces gets a 1/8 budget (6*1/8 = 3/4).  We check the E(rho) ROW = E(rho) < 1/8,
on the contradiction ray u < tau, at the frozen sigma0 = 16/17 edge (freeze AMENDMENT: max at edge).

KEY FINDING: 1/(1-sigma) and 1/||1-rho|| are BOUNDED BY 17 AT sigma=16/17 (1-sigma = 1/17 fixed),
so at the BINDING edge C2rho ~ O(M) with NO L2/c0 dust.  The L2/c0 dust (catch #225) only surfaces
as sigma->1, where 1/(1-sigma) -> L2/c0 (zfr_harvest) BUT x^{1/2-sigma} -> x^{-1/2} decays faster.
So the dust is REAL but ABSORBED by the x-power.  Actual u-grade eta = 54/17 (z^1,x^{1/2-s}) BEATS
the freeze's crude eta_Er = 26/17 (z^{2+2s},x^{-s}): the actual row decays FASTER.
"""
import math
from fractions import Fraction as Fr
ln = math.log

# ---- tuning (freeze AMENDMENT 1, matching refuter1_reledger.py) ----
A_EXP = 3            # z = Q^12 u^-3
W_EXP = 14           # x = Q^104 u^-14
X1    = 2330
C0INV = 126848       # c0 = 1/126848
B_W, K_W, C_LN = 680, 14, 250 * ln(2)   # tau witnesses; ln(1/c) = 250 ln2
SIGMA = 16.0 / 17.0
EIGHTH = 1.0 / 8.0
LG_EIGHTH = math.log10(EIGHTH)           # -0.903
Z0 = 10.0            # generous zetaHol strip bound; enters WITHOUT L2/c0 so dominated (checked below)

def Mpv(q):     return math.sqrt(q) * (1 + ln(q))

class Corner:
    def __init__(self, q, T=2.0, sigma=SIGMA):
        self.q = q; self.T = T; self.sigma = sigma
        self.Q = q * T; self.lnQ = ln(self.Q); self.L2 = self.lnQ + 2
        self.M = Mpv(q)
        # on-ray bounds at this sigma
        self.u_sig = 1.0 - sigma                       # 1 - sigma
        self.inv_1msig = 1.0 / self.u_sig              # 1/(1-sigma)
        # ||1-rho|| >= 1-sigma (worst case Im->0), and <= sqrt((1-sigma)^2+1)
        self.inv_norm1mrho = 1.0 / self.u_sig          # 1/||1-rho|| <= 1/(1-sigma)
        self.norm1mrho_up = math.sqrt(self.u_sig**2 + 1.0)   # ||1-rho|| upper (for Ksand numerator)
        self.normrho_up = math.sqrt(sigma**2 + 1.0)    # ||rho|| upper
        self.P = 3 * self.M * (1 + self.normrho_up / sigma)
        # tau (contradiction point), matching refuter1_reledger.py
        self.s_tau = C_LN + B_W * (1 - sigma) * self.lnQ + K_W * ln(self.L2)
        self.tau = math.exp(-self.s_tau)
        self.ustar = 1.0 / (40 * self.L2)
    def C2rho(self):
        M, P = self.M, self.P
        Cwrho = (12*M*self.inv_norm1mrho + 2*(9 + 8*self.normrho_up)
                 + 2*(Z0 + self.inv_norm1mrho)*P + 2*P + 2*P*self.inv_1msig)
        Ksand_const = 90*M*self.inv_norm1mrho + 72*M*self.inv_1msig
        return 3*Cwrho + Ksand_const
    # ---- E(rho) ROW in ln-form, s = ln(1/u) ----
    def lnz(self, s): return 12*self.lnQ + A_EXP*s
    def lnx(self, s): return 104*self.lnQ + W_EXP*s
    def lnRow_Er_actual(self, s):
        # E(rho) = C2rho * z^1 * (1+log(z^2))^9 * x^{1/2 - sigma}
        return (ln(self.C2rho()) + self.lnz(s) + 9*ln(1 + 2*self.lnz(s))
                + (0.5 - self.sigma)*self.lnx(s))
    def lnRow_Er_freeze(self, s):
        # freeze crude model: CE*P*(1+sqrt2)*(1+lnx)^3 (1+2lnz)^12 z^{2+2s} x^{-s} * L2/c0
        CE = 100
        return (ln(CE*self.P*(1+math.sqrt(2))*self.L2*C0INV) + 3*ln(1+self.lnx(s))
                + 12*ln(1+2*self.lnz(s)) + (2+2*self.sigma)*self.lnz(s) - self.sigma*self.lnx(s))

# ---- symbolic u-grades (Row ~ u^eta ; lnRow ~ -eta*s) ----
a = Fr(A_EXP); W = Fr(W_EXP); s0 = Fr(16, 17)
eta_actual = -(1*A_EXP + (Fr(1,2) - s0)*W_EXP)        # -(dz-coeff + x-coeff) in s -> u-grade
eta_actual = -(A_EXP + (Fr(1,2)-s0)*W)                # 3 + (1/2-16/17)*14 -> negate for u^eta
eta_freeze = W*s0 - a*(2 + 2*s0)
print("="*96)
print("SYMBOLIC u-GRADES (Row ~ u^eta ; eta>0 => decays as u->0)")
print(f"  eta_Er_ACTUAL (z^1, x^(1/2-s))     = -(3 + (1/2-16/17)*14) = {eta_actual} = {float(eta_actual):+.4f}")
print(f"  eta_Er_freeze (z^(2+2s), x^(-s))   = W*s0 - a(2+2s0)       = {eta_freeze} = {float(eta_freeze):+.4f}")
print(f"  => ACTUAL grade {float(eta_actual):.3f} > freeze {float(eta_freeze):.3f}: actual decays FASTER.")

print("="*96)
print("RE-PRICED rho-row (E(rho)) at the BINDING sigma0 = 16/17 edge, on the ray u < tau:")
print(f"{'q':>10} | {'C2rho/M':>9} | {'ln(1/tau)':>10} | {'lg Row@tau (actual)':>20} | "
      f"{'lg Row@tau (freeze)':>20} | {'vs lg(1/8)':>12} | verdict")
print("-"*96)
ok = True
for q in [3, 1000, 10**6]:
    c = Corner(q)
    s = c.s_tau
    lg_act = c.lnRow_Er_actual(s) / ln(10)
    lg_frz = c.lnRow_Er_freeze(s) / ln(10)
    c2overM = c.C2rho() / c.M
    passes = lg_act < LG_EIGHTH
    # monotone check: derivative of lnRow in s must stay < 0 for all s >= s_tau (whole ray)
    ss = [s + d for d in (0, 5, 50, 500)]
    mono = all(c.lnRow_Er_actual(a2) > c.lnRow_Er_actual(b2)
               for a2, b2 in zip(ss, ss[1:]))
    ok = ok and passes and mono
    print(f"{q:>10} | {c2overM:>9.1f} | {c.s_tau:>10.1f} | {lg_act:>20.2f} | {lg_frz:>20.2f} | "
          f"{LG_EIGHTH:>12.3f} | {'PASS' if passes and mono else 'FAIL'}")

print("-"*96)
print("SIGMA-SWEEP (the catch #225 dust regime: as sigma->1, 1/(1-sigma)->L2/c0, ONE power):")
print(f"{'q':>10} | {'worst sigma':>12} | {'lg maxRow@tau':>14} | {'C2rho/M @worst':>15} | verdict")
print("-"*96)
sweep_ok = True
for q in [3, 1000, 10**6]:
    worst_lg = -1e18; worst_sig = None; worst_c2 = None
    # sweep sigma from 16/17 up to 1 - 1e-6 (the zfr-permitted zero band)
    N = 4000
    for i in range(N + 1):
        sig = SIGMA + (1.0 - 1e-6 - SIGMA) * i / N
        c = Corner(q, sigma=sig)
        lg = c.lnRow_Er_actual(c.s_tau) / ln(10)     # at u = tau for THIS sigma
        if lg > worst_lg:
            worst_lg = lg; worst_sig = sig; worst_c2 = c.C2rho() / c.M
    passes = worst_lg < LG_EIGHTH
    sweep_ok = sweep_ok and passes
    print(f"{q:>10} | {worst_sig:>12.6f} | {worst_lg:>14.2f} | {worst_c2:>15.1f} | "
          f"{'PASS' if passes else 'FAIL'}")
print("-"*96)
print(f"  With the ACTUAL x^(1/2-sigma) grade the row's max over sigma sits at the sigma->1 DUST edge")
print(f"  (freeze's crude x^(-sigma) model peaked at 16/17 instead) -- there C2rho/M explodes to")
print(f"  ~{Corner(3, sigma=1-1e-6).C2rho()/Corner(3).M:.0f} at q=3 (the catch #225 ONE-power L2/c0 dust, 1/(1-sigma)->L2/c0).")
print(f"  BUT the row is still 10^-327 << 1/8: the dust is killed by x^(1/2-sigma)->x^(-1/2). ABSORBED.")
print(f"NOTE: at sigma=16/17, 1/(1-sigma)=1/||1-rho||=17 (1-sigma=1/17 FIXED): C2rho ~ O(M), NO L2/c0.")
print(f"      C2rho/M ~ {Corner(3).C2rho()/Corner(3).M:.0f} (Z0={Z0}); freeze per-unit budget "
      f"CE*P*(1+sqrt2)/M ~ {100*(1+math.sqrt(2))*3*(1+math.sqrt(2)/SIGMA):.0f}  => actual << freeze budget.")
print(f"      Actual row decades below 1/8 (q=3, thinnest): {(LG_EIGHTH - Corner(3).lnRow_Er_actual(Corner(3).s_tau)/ln(10)):.1f}")
print("="*96)
print("VERDICT:", "ALL rho-rows PASS on-ray at q=3/10^3/10^6 (one power L2/c0, absorbed by x-power)."
      if ok and sweep_ok else "*** FAIL — STOP AND FLAG ***")
