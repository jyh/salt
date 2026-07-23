/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Salt.MR.HalaszRepAsm
import Salt.MR.PrimeSigmaShift
import Salt.MR.Dist

/-!
# THE POINTWISE EULER LAYER — the route-independent SF-0/SF-1/SF-2 shelf (`SupF`)

Route-independent shelf stones for the smooth-leg / large-leg Euler-product bound.
These are the repaired SF-0/SF-1/SF-2 of the SUPF design block (`docs/exploration/
supf-design.md`); the *assembly* that consumed them (`prop21RHS_le_head`) is on HOLD
(BALL-REF confirmed-fatal), but the pointwise layer survives and serves ANY future
head bound, so it lands here as free-standing stones.

* **SF-1** (`ellLin_euler_product`, `euler_log_bound`): the twist adapter.  For
  `Re s > 1`, `LSeries (ellLin g) s = ∏'_p (1 + g(p)·p^{-s})` — the squarefree
  support of `ellLin` (`ellLin_prime_pow_ge_two = 0`) collapses each local Euler
  factor `∑'_e ℓ(p^e)p^{-es}` to `1 + g(p)p^{-s}`, and mathlib's
  `IsMultiplicative.eulerProduct_tprod` (the *general* multiplicative version — NOT
  the completely-multiplicative drop-in, which `ellLin` is not) assembles the
  product.  `euler_log_bound` bounds `‖L‖ ≤ exp(cpeel)·exp(Re ∑'_p g(p)p^{-s})` via
  the elementary per-factor `log‖1+z‖ ≤ Re z + ‖z‖²` and the `‖z‖²`-tail `≤ cpeel`.
* **SF-0** (`smooth_ratio_bound`): the repaired smooth-leg ratio, `C_S` ABSOLUTE via
  `mertens_first_upper`'s cancellation (the leading `(α+2β)·log y` term cancels the
  `log y` from Mertens, leaving an absolute constant).
* **SF-2** (`dist_identification`): the distance identification at the PINNED scale
  `σ = 1/L` only (the `σ = 2η` scale-mismatch is flagged and unresolved — the landed
  `sigma_shift`/`euler_osc_truncation` are `1/log x`-pinned for exactly this reason).

No object is ever evaluated below its abscissa (the ratio move keeps the Euler
product at `Re > 1`).  `⍟`/`δ` unused here; the layer is pure Euler-product analysis.
-/

noncomputable section

namespace Salt.MR

open Complex
open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-! ## Shared helper: the `n^{-s}` factorization across a product -/

/-- `((m·n)^{-s}) = m^{-s}·n^{-s}` for natural `m, n` (the completely-multiplicative
half of the twisted-summand factorization). -/
lemma natCast_mul_cpow (m n : ℕ) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
  rw [Nat.cast_mul, ← Complex.ofReal_natCast m, ← Complex.ofReal_natCast n,
    mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n),
    Complex.ofReal_natCast, Complex.ofReal_natCast]

/-- Elementary: `exp u - 1 ≤ u·exp u` for every real `u` (from `1 - u ≤ exp(-u)`). -/
lemma exp_sub_one_le (u : ℝ) : Real.exp u - 1 ≤ u * Real.exp u := by
  have h : 1 - u ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
  have hmul : Real.exp u * (1 - u) ≤ Real.exp u * Real.exp (-u) :=
    mul_le_mul_of_nonneg_left h (Real.exp_nonneg u)
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
  nlinarith [hmul]

/-- The mean-value-type bound `q^x - 1 ≤ x·(log q)·q^x` for `1 ≤ q` (any real `x`). -/
lemma rpow_sub_one_le {q x : ℝ} (hq : 1 ≤ q) :
    q ^ x - 1 ≤ x * Real.log q * q ^ x := by
  have hqpos : (0 : ℝ) < q := by linarith
  rw [Real.rpow_def_of_pos hqpos x]
  nlinarith [exp_sub_one_le (Real.log q * x)]

/-! ## SF-1, stone 1 — the twisted summand and its Euler product

`ellLinTwist g s` is the arithmetic function `n ↦ ellLin g n · n^{-s}`, the Dirichlet
summand of `LSeries (ellLin g)`.  It is multiplicative (pointwise product of the
coprime-multiplicative `ellLin g` and the completely-multiplicative `n ↦ n^{-s}`) and
norm-summable at `Re s > 1`; its Euler local factor collapses to `1 + g(p)·p^{-s}`. -/

/-- The twisted Dirichlet summand of `ellLin g`: `n ↦ ellLin g n · n^{-s}`, as an
`ArithmeticFunction ℂ` (vanishing at `0` since `ellLin g 0 = 0`). -/
def ellLinTwist (g : ℕ → ℂ) (s : ℂ) : ArithmeticFunction ℂ where
  toFun n := ellLin g n * (n : ℂ) ^ (-s)
  map_zero' := by simp [ellLin]

@[simp] lemma ellLinTwist_apply (g : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    ellLinTwist g s n = ellLin g n * (n : ℂ) ^ (-s) := rfl

/-- `ellLinTwist g s` is multiplicative on coprime arguments. -/
lemma isMult_ellLinTwist (g : ℕ → ℂ) (s : ℂ) :
    (ellLinTwist g s).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [ellLin_one], fun {m n} hm hn hco => ?_⟩
  simp only [ellLinTwist_apply]
  rw [ellLin_mul_coprime g hm hn hco, natCast_mul_cpow m n (-s)]
  ring

/-- At `Re s > 1`, the twisted summand is norm-summable (dominated by `n ↦ ‖n^{-s}‖`,
the ζ-summand, since `‖ellLin g n‖ ≤ 1`). -/
lemma summable_ellLinTwist (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : Summable (fun n => ‖ellLinTwist g s n‖) := by
  have hz : Summable (fun n : ℕ => ‖(n : ℂ) ^ (-s)‖) := by
    simpa only [riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      using summable_riemannZetaSummand hs
  refine hz.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  simp only [ellLinTwist_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ellLin_norm_le_one g hg n)

/-- The total sum of the twisted summand IS the L-series: `∑' n, ℓ(n)·n^{-s} =
LSeries (ellLin g) s`. -/
lemma tsum_ellLinTwist (g : ℕ → ℂ) (s : ℂ) :
    ∑' n, ellLinTwist g s n = LSeries (ellLin g) s := by
  rw [LSeries]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ellLinTwist_apply]
    rw [show ellLin g 0 = 0 by simp [ellLin], zero_mul, LSeries.term_zero]
  · rw [ellLinTwist_apply, LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

/-- The Euler local factor of the twisted summand: `∑'_e ℓ(p^e)·(p^e)^{-s} =
1 + g(p)·p^{-s}` — the `e ≥ 2` terms vanish (squarefree support), `e = 0` gives `1`,
`e = 1` gives `g(p)·p^{-s}`. -/
lemma ellLinTwist_local_factor (g : ℕ → ℂ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, ellLinTwist g s (p ^ e) = 1 + g p * (p : ℂ) ^ (-s) := by
  have hsupp : ∀ e ∉ ({0, 1} : Finset ℕ), ellLinTwist g s (p ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨he0, he1⟩ := he
    rw [ellLinTwist_apply, ellLin_prime_pow_ge_two g hp (by omega : 2 ≤ e), zero_mul]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp only [ellLinTwist_apply, pow_zero, pow_one, ellLin_one, ellLin_apply_prime g hp,
    Nat.cast_one, one_cpow, one_mul]

/-- **SF-1, stone 1 — the twist adapter** (`ellLin_euler_product`).  For `Re s > 1`,
the L-series of the squarefree-linearized twist `ℓ = ellLin g` is the Euler product
with LINEAR local factors `1 + g(p)·p^{-s}`.  This is the repaired SF-1 reorder
(EULER-REF): the general multiplicative Euler product `IsMultiplicative.eulerProduct_
tprod` (NOT the completely-multiplicative `(1 - f p)⁻¹` drop-in, which `ellLin` is not)
applied to `ellLinTwist`, with each local factor collapsed by squarefree support. -/
theorem ellLin_euler_product (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (ellLin g) s = ∏' p : Nat.Primes, (1 + g p * (p : ℂ) ^ (-s)) := by
  rw [← tsum_ellLinTwist g s,
    ← IsMultiplicative.eulerProduct_tprod (isMult_ellLinTwist g s)
        (summable_ellLinTwist g hg hs)]
  exact tprod_congr (fun p => ellLinTwist_local_factor g s p.2)

/-! ## SF-1, stone 2 — the Euler log bound (`euler_log_bound`)

The elementary per-factor bound `|1 + z| ≤ exp(Re z + ‖z‖²)` (proved by squaring:
`|1+z|² = 1 + 2Re z + ‖z‖² ≤ exp(2Re z + 2‖z‖²)`) lifts through the multipliable Euler
product to `‖L‖ ≤ exp(cpeel)·exp(∑'_p Re z_p)`, the `‖z‖²`-tail absorbed into the
ABSOLUTE constant `exp(cpeel) = exp(∑'_p 1/p²)`. -/

/-- **The per-Euler-factor log bound.**  For `‖z‖ < 1` (so `1 + z ≠ 0`),
`log‖1 + z‖ ≤ Re z + ‖z‖²`.  Route: `‖1+z‖² = 1 + 2Re z + ‖z‖² ≤ exp(2(Re z + ‖z‖²))`
(via `1 + w ≤ exp w` and `‖z‖² ≥ 0`), take square roots, then `log`. -/
lemma log_norm_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    Real.log ‖1 + z‖ ≤ z.re + ‖z‖ ^ 2 := by
  have h1z : (1 : ℂ) + z ≠ 0 := by
    intro h
    have hzp : z = -1 := by linear_combination h
    rw [hzp, norm_neg, norm_one] at hz
    exact absurd hz (lt_irrefl 1)
  have hpos : 0 < ‖1 + z‖ := norm_pos_iff.mpr h1z
  have hsq : ‖1 + z‖ ^ 2 = 1 + (2 * z.re + ‖z‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  have hlog2 : Real.log (‖1 + z‖ ^ 2) = 2 * Real.log ‖1 + z‖ := by
    rw [Real.log_pow]; norm_num
  have hp' : (0 : ℝ) < 1 + (2 * z.re + ‖z‖ ^ 2) := by rw [← hsq]; positivity
  have hkey : Real.log (‖1 + z‖ ^ 2) ≤ 2 * z.re + ‖z‖ ^ 2 := by
    rw [hsq]; linarith [Real.log_le_sub_one_of_pos hp']
  have hnn : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
  linarith [hlog2, hkey, hnn]

/-- **SF-1, stone 2 — the Euler log bound** (`euler_log_bound`, the BRIDGE stone).
For `Re s > 1` and a 1-bounded prime datum `g`,
`‖LSeries (ellLin g) s‖ ≤ exp(cpeel)·exp(∑'_p Re(g(p)·p^{-s}))`, with the `k≥2`/`‖z‖²`
tail absorbed into the ABSOLUTE constant `exp(cpeel) = exp(∑'_p 1/p²)`.  Route: the
Euler product `ellLin_euler_product`, `Multipliable.norm_tprod`, the per-factor
`log_norm_one_add_le`, and the `‖z‖²`-tail bound `∑'_p ‖z_p‖² ≤ cpeel`.  (The design's
`Re Σ` is realized as the equal `Σ Re`, the form the corpus's distance sums use.) -/
theorem euler_log_bound (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (ellLin g) s‖
      ≤ Real.exp cpeel * Real.exp (∑' p : Nat.Primes, (g p * (p : ℂ) ^ (-s)).re) := by
  set z : Nat.Primes → ℂ := fun p => g p * (p : ℂ) ^ (-s) with hzdef
  have hsre0 : (-s).re ≠ 0 := by rw [Complex.neg_re]; linarith
  -- per-prime norm bound
  have hnormz : ∀ p : Nat.Primes, ‖z p‖ ≤ (p : ℝ) ^ (-s.re) := by
    intro p
    have h1 : ‖z p‖ = ‖g p.1‖ * (p : ℝ) ^ (-s.re) := by
      rw [hzdef]
      simp only [norm_mul, Complex.norm_natCast_cpow_of_re_ne_zero _ hsre0, Complex.neg_re]
    rw [h1]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hg p.1 p.2)
  have hb : ∀ p : Nat.Primes, ‖z p‖ ≤ 1 / (p : ℝ) := by
    intro p
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.one_lt.le
    refine le_trans (hnormz p) ?_
    calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
  have hnormz_lt : ∀ p : Nat.Primes, ‖z p‖ < 1 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.2.two_le
    have h12 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith [hb p]
  -- summabilities
  have hrpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-s.re)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hznorm : Summable (fun p : Nat.Primes => ‖z p‖) :=
    hrpow.of_nonneg_of_le (fun _ => norm_nonneg _) hnormz
  have hz : Summable z := hznorm.of_norm
  have hzre : Summable (fun p : Nat.Primes => (z p).re) := by
    simpa only [Complex.reCLM_apply] using Complex.reCLM.summable hz
  have hzsq_le : ∀ p : Nat.Primes, ‖z p‖ ^ 2 ≤ 1 / (p : ℝ) ^ 2 := by
    intro p
    calc ‖z p‖ ^ 2 ≤ (1 / (p : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb p) 2
      _ = 1 / (p : ℝ) ^ 2 := by rw [div_pow, one_pow]
  have hzsq : Summable (fun p : Nat.Primes => ‖z p‖ ^ 2) :=
    cpeel_summable.of_nonneg_of_le (fun _ => by positivity) hzsq_le
  have hzsq_sum : (∑' p : Nat.Primes, ‖z p‖ ^ 2) ≤ cpeel :=
    hzsq.tsum_le_tsum hzsq_le cpeel_summable
  -- the multipliable Euler product and its norm
  have hmul : Multipliable (fun p : Nat.Primes => 1 + z p) :=
    multipliable_one_add_of_summable hznorm
  have hkey : ‖LSeries (ellLin g) s‖ = ∏' p : Nat.Primes, ‖1 + z p‖ := by
    rw [ellLin_euler_product g hg hs, ← hmul.norm_tprod]
  rw [hkey, ← Real.rexp_tsum_eq_tprod (fun p => norm_pos_iff.mpr (by
        intro h
        have hzp : z p = -1 := by linear_combination h
        have := hnormz_lt p; rw [hzp, norm_neg, norm_one] at this
        exact absurd this (lt_irrefl 1)))
      hznorm.summable_log_norm_one_add,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog_le : (∑' p : Nat.Primes, Real.log ‖1 + z p‖)
      ≤ ∑' p : Nat.Primes, ((z p).re + ‖z p‖ ^ 2) :=
    (hznorm.summable_log_norm_one_add).tsum_le_tsum
      (fun p => log_norm_one_add_le (hnormz_lt p)) (hzre.add hzsq)
  rw [hzre.tsum_add hzsq] at hlog_le
  linarith [hlog_le, hzsq_sum]

/-! ## SF-0 — the finite smooth Euler product, its nonvanishing, and the repaired ratio

`smoothEuler y g s` is the FINITE Euler product over primes `p ≤ y` — the analytic
continuation of `smoothSeries y g` (which equals it at `Re > 1`, but here is used as the
route-independent object that stays defined even where the L-series diverges: SF-0's
ratio numerator `s − α − β` has `Re` possibly `< 1`, and this is exactly the "no object
below its abscissa" corner — the ratio move keeps everything finite-product).

**DEVIATION (iron rule 1, recorded loudly).**  The SF-0 brief writes the ratio on
`smoothSeries` (the L-series).  At the corpus argument pattern the numerator's real part
`Re(s − α − β) = c₀ − α − β` can be `< 1` (whenever `log y < log X`, the usual
smoothness regime), where `smoothSeries` (a `tsum`) is non-summable and returns junk `0`
— making the stated inequality VACUOUS.  Per the design's binding corner ledger ("No
object below its abscissa, ever"), SF-0 is stated on the FINITE Euler product
`smoothEuler`, which is entire and equals `smoothSeries` at `Re > 1` (`smooth_euler_
product` when landed).  The mathematics — the `mertens_first_upper` cancellation giving
an ABSOLUTE `C_S` — is exactly as designed. -/

/-- **SF-0 object — the finite smooth Euler product.**  `∏_{p ≤ y} (1 + g(p)·p^{-s})`,
the entire analytic continuation of `smoothSeries y g` (equal at `Re > 1`). -/
def smoothEuler (y : ℝ) (g : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 + g p * (p : ℂ) ^ (-s))

/-- Each Euler factor `1 + g(p)·p^{-s}` is nonzero for `Re s > 0` (its second summand has
norm `‖g p‖·p^{-Re s} ≤ 2^{-Re s} < 1`). -/
lemma smooth_factor_ne_zero {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) + g p * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hne : (-s).re ≠ 0 := by rw [Complex.neg_re]; linarith
  have hlt : ‖g p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_re_ne_zero _ hne, Complex.neg_re]
    have h1 : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    calc ‖g p‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hg p hp) (Real.rpow_nonneg (by linarith) _)
      _ = (p : ℝ) ^ (-s.re) := one_mul _
      _ < 1 := h1
  intro h
  have hval : g p * (p : ℂ) ^ (-s) = -1 := by linear_combination h
  rw [hval, norm_neg, norm_one] at hlt
  exact absurd hlt (lt_irrefl 1)

/-- **SF-0 — nonvanishing** (`smooth_ne_zero`).  For `Re s > 0` and a 1-bounded datum,
the finite smooth Euler product is nonzero (every factor is). -/
theorem smooth_ne_zero (y : ℝ) {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : smoothEuler y g s ≠ 0 := by
  rw [smoothEuler, Finset.prod_ne_zero_iff]
  intro p hp
  exact smooth_factor_ne_zero hg (Finset.mem_filter.mp hp).2 hs

/-- **SF-0 — the per-factor ratio bound.**  For `p ≤ y` (with `e ≤ y`, `α,β ∈ [0,1/log y]`,
`Re s > 1`): the numerator factor is bounded by the denominator factor times
`exp(2·e³·(α+2β)·(log p)/p)`.  The `p^{α+2β} ≤ e³` cap and the `1/2`-floor `1 − |b_p| ≥ 1/2`
give the per-factor exponent; summing realizes the `log y` cancellation. -/
lemma smooth_ratio_factor {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) {α β y : ℝ} (hy : Real.exp 1 ≤ y)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαη : α ≤ 1 / Real.log y) (hβη : β ≤ 1 / Real.log y)
    {p : ℕ} (hp : p.Prime) (hpy : (p : ℝ) ≤ y) :
    ‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s - (α : ℂ) - (β : ℂ)))‖
      ≤ ‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s + (β : ℂ)))‖
        * Real.exp (2 * Real.exp 3 * (α + 2 * β) * (Real.log p / (p : ℝ))) := by
  set a : ℂ := g p * (p : ℂ) ^ (-(s - (α : ℂ) - (β : ℂ))) with hadef
  set b : ℂ := g p * (p : ℂ) ^ (-(s + (β : ℂ))) with hbdef
  set d : ℝ := 2 * Real.exp 3 * (α + 2 * β) * (Real.log p / (p : ℝ)) with hddef
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpℂ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
  have hlogp_nn : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlogp_le : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
  have hL1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hy
  have hL_pos : (0 : ℝ) < Real.log y := by linarith
  -- P := p^(α+2β): between 1 and e³
  have hαβsum : α + 2 * β ≤ 3 / Real.log y := by
    have h3 : (3 : ℝ) / Real.log y = 1 / Real.log y + 2 * (1 / Real.log y) := by ring
    rw [h3]; linarith
  have hP1 : (1 : ℝ) ≤ (p : ℝ) ^ (α + 2 * β) := by
    rw [show (1 : ℝ) = (p : ℝ) ^ (0 : ℝ) from (Real.rpow_zero _).symm]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by positivity)
  have hexp3arg : Real.log p * (α + 2 * β) ≤ 3 := by
    calc Real.log p * (α + 2 * β) ≤ Real.log y * (3 / Real.log y) :=
          mul_le_mul hlogp_le hαβsum (by positivity) hL_pos.le
      _ = 3 := by field_simp
  have hPle : (p : ℝ) ^ (α + 2 * β) ≤ Real.exp 3 := by
    rw [Real.rpow_def_of_pos hp0]; exact Real.exp_le_exp.mpr hexp3arg
  have hP1bound : (p : ℝ) ^ (α + 2 * β) - 1 ≤ (α + 2 * β) * Real.log p * Real.exp 3 := by
    have h1 := rpow_sub_one_le (q := (p : ℝ)) (x := α + 2 * β) hp1
    have h2 : (α + 2 * β) * Real.log p * (p : ℝ) ^ (α + 2 * β)
        ≤ (α + 2 * β) * Real.log p * Real.exp 3 :=
      mul_le_mul_of_nonneg_left hPle (by positivity)
    linarith
  -- b-norm bounds
  have hbne : (-(s + (β : ℂ))).re ≠ 0 := by
    rw [Complex.neg_re, Complex.add_re, Complex.ofReal_re]; linarith
  have hb_le_invp : ‖b‖ ≤ 1 / (p : ℝ) := by
    rw [hbdef, norm_mul, Complex.norm_natCast_cpow_of_re_ne_zero _ hbne, Complex.neg_re,
      Complex.add_re, Complex.ofReal_re]
    calc ‖g p‖ * (p : ℝ) ^ (-(s.re + β)) ≤ 1 * (p : ℝ) ^ (-(s.re + β)) :=
          mul_le_mul_of_nonneg_right (hg p hp) (Real.rpow_nonneg hp0.le _)
      _ = (p : ℝ) ^ (-(s.re + β)) := one_mul _
      _ ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
  have hb_le_half : ‖b‖ ≤ 1 / 2 := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith [hb_le_invp]
  have hlow : 1 - ‖b‖ ≤ ‖(1 : ℂ) + b‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-b)
    rw [norm_neg, sub_neg_eq_add] at this
    simpa using this
  -- a = b * ↑(p^(α+2β))
  have hab : a = b * (((p : ℝ) ^ (α + 2 * β) : ℝ) : ℂ) := by
    rw [hadef, hbdef, mul_assoc]
    congr 1
    rw [show -(s - (α : ℂ) - (β : ℂ)) = -(s + (β : ℂ)) + ((α + 2 * β : ℝ) : ℂ) from by
        push_cast; ring, Complex.cpow_add _ _ hpℂ]
    congr 1
    rw [← Complex.ofReal_natCast p, ← Complex.ofReal_cpow hp0.le]
  have hsub : a - b = b * (((p : ℝ) ^ (α + 2 * β) - 1 : ℝ) : ℂ) := by
    rw [hab]; push_cast; ring
  have hnormsub : ‖a - b‖ = ‖b‖ * ((p : ℝ) ^ (α + 2 * β) - 1) := by
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hP1])]
  have htri : ‖(1 : ℂ) + a‖ ≤ ‖(1 : ℂ) + b‖ + ‖b‖ * ((p : ℝ) ^ (α + 2 * β) - 1) := by
    have heq : (1 : ℂ) + a = (1 + b) + (a - b) := by ring
    rw [heq]
    exact le_trans (norm_add_le _ _) (by rw [hnormsub])
  -- assemble
  have hd_nn : 0 ≤ d := by rw [hddef]; positivity
  have hexpd : d + 1 ≤ Real.exp d := Real.add_one_le_exp d
  have hN_half : (1 : ℝ) / 2 ≤ ‖(1 : ℂ) + b‖ := by linarith [hlow, hb_le_half]
  have hMP : ‖b‖ * ((p : ℝ) ^ (α + 2 * β) - 1) ≤ (1 / 2) * d := by
    have h1 : ‖b‖ * ((p : ℝ) ^ (α + 2 * β) - 1)
        ≤ (1 / (p : ℝ)) * ((α + 2 * β) * Real.log p * Real.exp 3) :=
      mul_le_mul hb_le_invp hP1bound (by linarith [hP1]) (by positivity)
    calc ‖b‖ * ((p : ℝ) ^ (α + 2 * β) - 1)
        ≤ (1 / (p : ℝ)) * ((α + 2 * β) * Real.log p * Real.exp 3) := h1
      _ = (1 / 2) * d := by rw [hddef]; ring
  have hND : (1 / 2) * d ≤ ‖(1 : ℂ) + b‖ * (Real.exp d - 1) := by
    calc (1 / 2) * d ≤ ‖(1 : ℂ) + b‖ * d := by nlinarith [hN_half, hd_nn]
      _ ≤ ‖(1 : ℂ) + b‖ * (Real.exp d - 1) :=
          mul_le_mul_of_nonneg_left (by linarith [hexpd]) (norm_nonneg _)
  calc ‖(1 : ℂ) + a‖ ≤ ‖(1 : ℂ) + b‖ + ‖b‖ * ((p : ℝ) ^ (α + 2 * β) - 1) := htri
    _ ≤ ‖(1 : ℂ) + b‖ + ‖(1 : ℂ) + b‖ * (Real.exp d - 1) := by linarith [hMP, hND]
    _ = ‖(1 : ℂ) + b‖ * Real.exp d := by ring

/-- **SF-0 — the repaired smooth-leg ratio bound** (`smooth_ratio_bound`).  For `e ≤ y`,
`α, β ∈ [0, 1/log y]`, and `Re s > 1`, the smooth Euler product at the shifted argument
`s − α − β` is bounded by an ABSOLUTE constant times its value at `s + β`:
`‖smoothEuler y g (s−α−β)‖ ≤ exp(6·e³·(5 + log 4))·‖smoothEuler y g (s+β)‖`.

This is the design's key move: the product-of-ratios `∑_{p≤y} 2e³(α+2β)(log p)/p` is
bounded by `2e³·(α+2β)·(log y + (log 4 + 4))` (`mertens_first_upper`), and `(α+2β) ≤
3/log y` makes the leading `(α+2β)·log y ≤ 3` CANCEL the `log y`, leaving the absolute
`C_S = exp(6·e³·(1 + (log 4 + 4)))`.  No additive fallback (proven illusory). -/
theorem smooth_ratio_bound {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) {α β y : ℝ} (hy : Real.exp 1 ≤ y)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαη : α ≤ 1 / Real.log y) (hβη : β ≤ 1 / Real.log y) :
    ‖smoothEuler y g (s - (α : ℂ) - (β : ℂ))‖
      ≤ Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
        * ‖smoothEuler y g (s + (β : ℂ))‖ := by
  have hy1 : (1 : ℝ) ≤ y := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hy
  have hL_pos : (0 : ℝ) < Real.log y := by linarith
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hpy : ∀ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (p : ℝ) ≤ y := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    calc (p : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast (by omega : p ≤ ⌊y⌋₊)
      _ ≤ y := Nat.floor_le hy0
  have hprim : ∀ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, p.Prime :=
    fun p hp => (Finset.mem_filter.mp hp).2
  rw [smoothEuler, smoothEuler, norm_prod, norm_prod]
  calc ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
          ‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s - (α : ℂ) - (β : ℂ)))‖
      ≤ ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
          (‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s + (β : ℂ)))‖
            * Real.exp (2 * Real.exp 3 * (α + 2 * β) * (Real.log p / (p : ℝ)))) := by
        refine Finset.prod_le_prod (fun p _ => norm_nonneg _) (fun p hp => ?_)
        exact smooth_ratio_factor hg hs hy hα hβ hαη hβη (hprim p hp) (hpy p hp)
    _ = (∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
            ‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s + (β : ℂ)))‖)
          * ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
            Real.exp (2 * Real.exp 3 * (α + 2 * β) * (Real.log p / (p : ℝ))) :=
        Finset.prod_mul_distrib
    _ = (∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
            ‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s + (β : ℂ)))‖)
          * Real.exp (∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
              2 * Real.exp 3 * (α + 2 * β) * (Real.log p / (p : ℝ))) := by
        rw [Real.exp_sum]
    _ ≤ Real.exp (6 * Real.exp 3 * (1 + (Real.log 4 + 4)))
          * ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime,
            ‖(1 : ℂ) + g p * (p : ℂ) ^ (-(s + (β : ℂ)))‖ := by
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_right ?_
          (Finset.prod_nonneg (fun p _ => norm_nonneg _))
        apply Real.exp_le_exp.mpr
        rw [← Finset.mul_sum]
        -- 2e³(α+2β)·∑(log p/p) ≤ 6e³(1+(log4+4))
        have hmert : ∑ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.log p / (p : ℝ)
            ≤ Real.log y + (Real.log 4 + 4) := mertens_first_upper hy1
        have hcoef : (0 : ℝ) ≤ 2 * Real.exp 3 * (α + 2 * β) := by positivity
        have hstep1 := mul_le_mul_of_nonneg_left hmert hcoef
        have hLab : (α + 2 * β) * Real.log y ≤ 3 := by
          have hmul : (α + 2 * β) * Real.log y ≤ (3 / Real.log y) * Real.log y := by
            have hαβsum : α + 2 * β ≤ 3 / Real.log y := by
              have h3 : (3 : ℝ) / Real.log y = 1 / Real.log y + 2 * (1 / Real.log y) := by ring
              rw [h3]; linarith
            exact mul_le_mul_of_nonneg_right hαβsum hL_pos.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hL_pos)] at hmul
        have hαβ3 : α + 2 * β ≤ 3 := by
          have h3L : (3 : ℝ) / Real.log y ≤ 3 := by
            rw [div_le_iff₀ hL_pos]; nlinarith [hL1]
          have hαβsum : α + 2 * β ≤ 3 / Real.log y := by
            have h3 : (3 : ℝ) / Real.log y = 1 / Real.log y + 2 * (1 / Real.log y) := by ring
            rw [h3]; linarith
          linarith
        have hlog4 : (0 : ℝ) ≤ Real.log 4 + 4 := by
          have : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          linarith
        have m1 : 2 * Real.exp 3 * ((α + 2 * β) * Real.log y) ≤ 2 * Real.exp 3 * 3 :=
          mul_le_mul_of_nonneg_left hLab (by positivity)
        have m2 : 2 * Real.exp 3 * ((α + 2 * β) * (Real.log 4 + 4))
            ≤ 2 * Real.exp 3 * (3 * (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαβ3 hlog4) (by positivity)
        nlinarith [hstep1, m1, m2]

/-! ## SF-2 — the distance identification at the PINNED scale `σ = 1/L`

The exponent of `euler_log_bound` at the pinned line `s = (1 + 1/L) + it` (`L = log X`)
decomposes as `Re(g(p)·p^{-s}) = Re((g·p^{-it})(p))·p^{-1-1/L}`, and `euler_osc_
truncation` (the landed `1/log X`-pinned shift bridge) then identifies the full prime
tsum with the truncated head sum up to `O(1)`.

**PIN + SCOPE (recorded, per the design's flag).**  This is stated at `σ = 1/L` ONLY.
The landed `sigma_shift`/`euler_osc_truncation` are `1/log X`-pinned; the `σ = 2η`
scale-mismatch is flagged and unresolved — the full `[1/L, 2η]` range is future work, not
claimed here.  The `−pretDistSq`-form (the general-`g` distance evaluation) is the
corpus's flagged MR-W1 residual (needs a log-of-`L` Euler bridge, absent in mathlib); the
truncated head `∑_{p≤X} Re(g·p^{-it})(p)/p` IS the distance content, but its conversion to
`loglog X − M(t)` is available only at the principal (Liouville) datum
(`pretDistSq_principal_eval`) — not folded in here to avoid a datum misassignment. -/

/-- The pin decomposition: on the line `s = (1 + 1/L) + it` (`L = log X`), the real part
of the twisted summand factors as `Re((g·p^{-it})(p))·p^{-1-1/L}` — the shape
`euler_osc_truncation` consumes (`g·p^{-it} = g·costwist(-t)`). -/
lemma exponent_pin_eq {g : ℕ → ℂ} (X : ℝ) (t : ℝ) (p : Nat.Primes) :
    (g p * (p : ℂ) ^ (-(((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I))).re
      = (g p * costwist (-t) p).re * (p : ℝ) ^ (-1 - 1 / Real.log X : ℝ) := by
  have hpℂ : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.pos.ne'
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hdecomp : ((p : ℕ) : ℂ) ^ (-(((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I))
      = (((((p : ℕ) : ℝ) ^ (-1 - 1 / Real.log X : ℝ)) : ℝ) : ℂ) * costwist (-t) (p : ℕ) := by
    rw [show -(((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I)
          = ((-1 - 1 / Real.log X : ℝ) : ℂ) + (((-t : ℝ)) : ℂ) * Complex.I from by
        push_cast; ring, Complex.cpow_add _ _ hpℂ]
    congr 1
    · rw [← Complex.ofReal_natCast (p : ℕ), ← Complex.ofReal_cpow hp0.le]
    · rw [costwist, Complex.cpow_def_of_ne_zero hpℂ, ← Complex.natCast_log]
      congr 1
      push_cast; ring
  rw [hdecomp, mul_left_comm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- **SF-2 — the distance identification at the pin** (`dist_identification`).  For a
globally 1-bounded datum `g`, `e ≤ X`, and the prime-tail bound at `σ = 1/log X`: the full
twisted prime tsum on the pinned line `(1 + 1/log X) + it` equals the truncated head sum
`∑_{p≤X} Re((g·p^{-it})(p))/p` up to the absolute `O(1)` error `Ctail + (1 + (log4 + 4))`.
A direct consequence of the pin decomposition (`exponent_pin_eq`) and the landed
`euler_osc_truncation` (`sigma_shift` + `prime_tail_shift`), specialized to the twisted
datum `g·costwist(-t)` (1-bounded since `‖costwist‖ = 1`). -/
theorem dist_identification {g : ℕ → ℂ} (hg : ∀ p, ‖g p‖ ≤ 1) {X : ℝ}
    (hX : Real.exp 1 ≤ X) (t : ℝ) {Ctail : ℝ}
    (htail : primeTailShift (1 / Real.log X) (⌊X⌋₊ + 1) ≤ Ctail) :
    |(∑' p : Nat.Primes,
          (g p * (p : ℂ) ^ (-(((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I))).re)
        - ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime, (g p * costwist (-t) p).re / p|
      ≤ Ctail + (1 + (Real.log 4 + 4)) := by
  have hrw : (∑' p : Nat.Primes,
        (g p * (p : ℂ) ^ (-(((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I))).re)
      = ∑' p : Nat.Primes,
          (g p * costwist (-t) p).re * (p : ℝ) ^ (-1 - 1 / Real.log X : ℝ) :=
    tsum_congr (fun p => exponent_pin_eq X t p)
  rw [hrw]
  exact euler_osc_truncation hX htail (fun n => g n * costwist (-t) n)
    (fun n => by rw [norm_mul, costwist_norm, mul_one]; exact hg n)

/-- **SF-2 exit — the pointwise head bound at the pin.**  Composing `euler_log_bound`
(SF-1) with `dist_identification`: for a globally 1-bounded `g`, `e ≤ X`, the L-series of
`ellLin g` on the pinned line is bounded by `exp(cpeel)` times the exponential of the
truncated head sum, up to the `O(1)` shift.  This is the honest `‖F(c₀+it)‖`-bound at the
pin; the `C·L·e^{−M(t)}` form (and the trivial `≤ C·L`) require the distance evaluation
(`loglog X − M(t)`), available at the principal datum only — see the SF-2 scope note. -/
theorem head_pin_bound {g : ℕ → ℂ} (hg : ∀ p, ‖g p‖ ≤ 1) {X : ℝ}
    (hX : Real.exp 1 ≤ X) (t : ℝ) {Ctail : ℝ}
    (htail : primeTailShift (1 / Real.log X) (⌊X⌋₊ + 1) ≤ Ctail) :
    ‖LSeries (ellLin g) (((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ Real.exp cpeel
        * Real.exp ((∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime,
            (g p * costwist (-t) p).re / p) + (Ctail + (1 + (Real.log 4 + 4)))) := by
  have hX1 : (1 : ℝ) < X := by nlinarith [Real.add_one_le_exp (1 : ℝ), hX]
  have hLpos : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hs : 1 < (((1 + 1 / Real.log X : ℝ) : ℂ) + (t : ℝ) * Complex.I).re := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    have : (0 : ℝ) < 1 / Real.log X := by positivity
    simp; linarith
  refine le_trans (euler_log_bound g (fun p _ => hg p) hs) ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply Real.exp_le_exp.mpr
  have hid := dist_identification hg hX t htail
  linarith [(abs_le.mp hid).1, (abs_le.mp hid).2]

end Salt.MR

/-! # THE B-LADDER — the σ-uniform pretentious machinery (route B, HPRET-SCOPE 09:40)

The append-only extension carrying the general-`σ` head bound that feeds the `c = 1/e`
grade re-freeze (terminal-assembly-freeze ⟦A — B4⟧, JYH-ratified 2026-07-23).  Where the
landed SF-2 (`dist_identification`/`head_pin_bound`) is PINNED at `σ = 1/L`, the B-ladder
makes the identification `σ`-UNIFORM on `[1/L, 2η]` and produces the honest majorant
`‖F(1+σ+it)‖ ≤ C·(1/σ)·exp(−(1/e)·𝔻²(scale e^{1/σ}))` (B1), the crude scale-monotone
distance floor `𝔻²(e^{1/σ}) ≥ 𝔻²(X) − 2 log(σL) − C` (B2), and the flat-regime σ-integral
`∫ (1/σ²) exp(−(1/e)(M − 2 log(σL) − C)) ≤ C′ e^{−M/e} L` whose `2/e < 1` convergence is the
whole point (B3).  The grade interface consumed downstream carries `c = 1/e` literally.

**B1 — the identification.**  For a 1-bounded prime datum `g` and `σ ∈ (0, 1]`:
`∑'_p Re(g p)·p^{−1−σ} ≤ (log(1/σ) + C₁) − (1/e)·∑_{p ≤ e^{1/σ}} (1 − Re g p)/p`.
Route: (i) the NEW general-`σ` prime sum `prime_sum_sigma`
`∑'_p p^{−1−σ} ≤ log(1/σ) + (log 4 + cpeel)` — proved elementarily from the LANDED
log-Euler product (`log_norm_zeta_eq_re_tsum`) + the `k≥2` peel (`peel_sum_bound`) + the
closed-form `ζ(1+σ) ≤ 4/σ` (`Salt.SW.norm_riemannZeta_le` at the real point `s = 1+σ`), NO
Abel summation / Chebyshev density needed; (ii) the `p^{−σ} ≥ e^{−1}` cut on `p ≤ e^{1/σ}`
(rpow monotonicity), dropping the nonneg tail. -/

noncomputable section

namespace Salt.MR

open Complex
open scoped BigOperators

/-- **B1 linchpin — the general-`σ` prime sum** (`prime_sum_sigma`).  For `σ ∈ (0, 1]`,
`∑'_p p^{−1−σ} ≤ log(1/σ) + (log 4 + cpeel)`.  The genuinely-new general-`σ` Mertens input,
proved WITHOUT prime-density/Abel machinery: at the real point `s = 1+σ` the target sum is
`∑'_p Re(p^{−s})`, which the `k≥2` peel (`peel_sum_bound`) and the log-Euler product
(`log_norm_zeta_eq_re_tsum`) bound by `log‖ζ(1+σ)‖ + cpeel`, and the corpus closed form
`Salt.SW.norm_riemannZeta_le` gives `‖ζ(1+σ)‖ ≤ 1/σ + 2 + σ ≤ 4/σ` (for `σ ≤ 1`), whence
`log‖ζ(1+σ)‖ ≤ log(1/σ) + log 4`. -/
theorem prime_sum_sigma {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    ∑' p : Nat.Primes, (p : ℝ) ^ (-1 - σ : ℝ)
      ≤ Real.log (1 / σ) + (Real.log 4 + cpeel) := by
  set s : ℂ := ((1 + σ : ℝ) : ℂ) with hsdef
  have hsre : s.re = 1 + σ := by rw [hsdef, Complex.ofReal_re]
  have hs1 : 1 < s.re := by rw [hsre]; linarith
  have hσ0' : (0 : ℝ) < s.re := by rw [hsre]; linarith
  have hsne : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, Complex.one_re] at this; linarith
  -- Re(p^{-s}) = p^{-1-σ} pointwise
  have hre : ∀ p : Nat.Primes, ((p : ℂ) ^ (-s)).re = (p : ℝ) ^ (-1 - σ : ℝ) := by
    intro p
    have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hsdef, ← Complex.ofReal_natCast (p : ℕ),
      show -(((1 + σ : ℝ) : ℂ)) = (((-1 - σ : ℝ)) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_cpow hp0, Complex.ofReal_re]
  have hsum_eq : (∑' p : Nat.Primes, (p : ℝ) ^ (-1 - σ : ℝ))
      = ∑' p : Nat.Primes, ((p : ℂ) ^ (-s)).re :=
    tsum_congr (fun p => (hre p).symm)
  rw [hsum_eq]
  -- peel + log-Euler: Σ Re(p^{-s}) ≤ log‖ζ s‖ + cpeel
  have hpeel := abs_le.mp (peel_sum_bound hs1)
  have hzeta := log_norm_zeta_eq_re_tsum hs1
  have hB : (∑' p : Nat.Primes, ((p : ℂ) ^ (-s)).re)
      ≤ Real.log ‖riemannZeta s‖ + cpeel := by
    rw [hzeta]; linarith [hpeel.1]
  -- log‖ζ s‖ ≤ log(1/σ) + log 4
  have hsub : s - 1 = ((σ : ℝ) : ℂ) := by rw [hsdef]; push_cast; ring
  have hnormsub : ‖s - 1‖ = σ := by
    rw [hsub, Complex.norm_real, Real.norm_of_nonneg hσ0.le]
  have hnorms : ‖s‖ = 1 + σ := by
    rw [hsdef, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hζpos : (0 : ℝ) < ‖riemannZeta s‖ := by
    rw [norm_pos_iff]; exact riemannZeta_ne_zero_of_one_lt_re hs1
  have hζbound := Salt.SW.norm_riemannZeta_le hσ0' hsne
  rw [hnormsub, hnorms, hsre] at hζbound
  -- simplify the closed form to 1/σ + 2 + σ, then ≤ 4/σ
  have hval : (1 + σ * ((1 + σ) * (1 + 1 / (1 + σ)))) / σ = 1 / σ + 2 + σ := by
    have h1σ : (1 : ℝ) + σ ≠ 0 := by positivity
    field_simp
    ring
  rw [hval] at hζbound
  have hζ4 : ‖riemannZeta s‖ ≤ 4 / σ := by
    have h4 : 1 / σ + 2 + σ ≤ 4 / σ := by
      rw [div_add' _ _ _ hσ0.ne', div_add' _ _ _ hσ0.ne', div_le_div_iff_of_pos_right hσ0]
      nlinarith [hσ0, hσ1]
    linarith [hζbound, h4]
  have hlogζ : Real.log ‖riemannZeta s‖ ≤ Real.log (1 / σ) + Real.log 4 := by
    have hstep := Real.log_le_log hζpos hζ4
    rwa [show (4 : ℝ) / σ = 4 * (1 / σ) from by ring,
      Real.log_mul (by norm_num) (by positivity), add_comm] at hstep
  linarith [hB, hlogζ]

/-- **B1 cut (ii) — the `p^{−σ} ≥ e^{−1}` distance lower bound** (`sigma_cut_lower`).  For a
1-bounded `g` and `σ > 0`, the full shifted defect sum dominates `(1/e)` times the truncated
distance at scale `e^{1/σ}`:
`(1/e)·𝔻²(1, g; e^{1/σ}) ≤ ∑'_p (1 − Re g p)·p^{−1−σ}`.  Route: drop the nonneg tail of the
prime tsum past `⌊e^{1/σ}⌋` (the corpus indicator-split idiom), then the pointwise
`p^{−σ} ≥ (e^{1/σ})^{−σ} = e^{−1}` cut (rpow monotonicity) on the retained head. -/
theorem sigma_cut_lower {g : ℕ → ℂ} (hg : ∀ p, ‖g p‖ ≤ 1) {σ : ℝ} (hσ0 : 0 < σ) :
    (1 / Real.exp 1) * pretDistSq (fun _ => 1) g (Real.exp (1 / σ))
      ≤ ∑' p : Nat.Primes, (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := by
  have hσ1 : (-1 - σ : ℝ) < -1 := by linarith
  set Y : ℝ := Real.exp (1 / σ) with hYdef
  set N : ℕ := ⌊Y⌋₊ with hNdef
  have hYpos : (0 : ℝ) < Y := Real.exp_pos _
  -- per-prime facts about `g`
  have hre1 : ∀ n : ℕ, -1 ≤ (g n).re ∧ (g n).re ≤ 1 := fun n =>
    abs_le.mp (le_trans (Complex.abs_re_le_norm (g n)) (hg n))
  -- nonnegativity of the ℕ-lifted summand on primes
  have hFnn : ∀ p : ℕ, 0 ≤ (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := fun p =>
    mul_nonneg (by linarith [(hre1 p).2]) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- Summable indicator of the lifted summand (majorised by 2·prime-rpow-indicator)
  have hindF : Summable (Set.indicator {p : ℕ | Nat.Prime p}
      (fun p => (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ))) := by
    refine Summable.of_nonneg_of_le
      (fun n => Set.indicator_nonneg (fun p _ => hFnn p) n) (fun n => ?_)
      ((summable_indicator_prime_rpow hσ0).mul_left 2)
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hn : n ∈ {p : ℕ | Nat.Prime p}
    · simp only [if_pos hn]
      calc (1 - (g n).re) * (n : ℝ) ^ (-1 - σ : ℝ)
          ≤ 2 * (n : ℝ) ^ (-1 - σ : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith [(hre1 n).1])
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = 2 * (n : ℝ) ^ (-1 - σ : ℝ) := rfl
    · simp only [if_neg hn, mul_zero, le_refl]
  -- the full prime tsum equals the ℕ-indicator tsum, split at N+1, tail nonneg
  have hfull : (∑' p : Nat.Primes, (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ))
      = ∑' n, Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ)) n := by
    rw [← tsum_subtype {p : ℕ | Nat.Prime p}
      (fun n : ℕ => (1 - (g n).re) * (n : ℝ) ^ (-1 - σ : ℝ))]; rfl
  have hsplit := (Summable.sum_add_tsum_nat_add (N + 1) hindF).symm
  have hhead : (∑ n ∈ Finset.range (N + 1), Set.indicator {p : ℕ | Nat.Prime p}
          (fun p => (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ)) n)
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
          (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by
      rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq])
  have htail_nn : (0 : ℝ) ≤ ∑' i, Set.indicator {p : ℕ | Nat.Prime p}
      (fun p => (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ)) (i + (N + 1)) :=
    tsum_nonneg (fun i => Set.indicator_nonneg (fun p _ => hFnn p) _)
  have hge : (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ))
      ≤ ∑' p : Nat.Primes, (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := by
    rw [hfull, hsplit, hhead]; linarith [htail_nn]
  -- pretDistSq unfolds to the truncated (1 − Re)/p sum at scale Y
  have hPD : pretDistSq (fun _ => 1) g Y
      = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (1 - (g p).re) / (p : ℝ) := by
    unfold pretDistSq
    refine Finset.sum_congr (by rw [hNdef]) (fun p _ => ?_)
    rw [one_mul, Complex.conj_re]
  -- the termwise `p^{−σ} ≥ e^{−1}` cut on the retained head
  have htermcut : ∀ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
      (1 / Real.exp 1) * ((1 - (g p).re) / (p : ℝ))
        ≤ (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpp : p.Prime := hp.2
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hpN : p ≤ N := by omega
    have hpY : (p : ℝ) ≤ Y := by
      calc (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
        _ ≤ Y := Nat.floor_le hYpos.le
    -- p^{-σ} ≥ 1/e
    have hYσ : Y ^ σ = Real.exp 1 := by
      rw [hYdef, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, one_div_mul_cancel hσ0.ne']
    have hpσpos : (0 : ℝ) < (p : ℝ) ^ σ := Real.rpow_pos_of_pos hp0 σ
    have hpσ_le : (p : ℝ) ^ σ ≤ Real.exp 1 := by
      rw [← hYσ]; exact Real.rpow_le_rpow hp0.le hpY hσ0.le
    have hcut_p : 1 / Real.exp 1 ≤ (p : ℝ) ^ (-σ : ℝ) := by
      rw [Real.rpow_neg hp0.le, ← one_div]
      exact one_div_le_one_div_of_le hpσpos hpσ_le
    -- split the rpow and compare
    have hsplitrpow : (p : ℝ) ^ (-1 - σ : ℝ) = (p : ℝ)⁻¹ * (p : ℝ) ^ (-σ : ℝ) := by
      rw [show (-1 - σ : ℝ) = (-1 : ℝ) + (-σ) from by ring, Real.rpow_add hp0,
        Real.rpow_neg_one]
    have hfac_nn : 0 ≤ (1 - (g p).re) * (p : ℝ)⁻¹ :=
      mul_nonneg (by linarith [(hre1 p).2]) (by positivity)
    calc (1 / Real.exp 1) * ((1 - (g p).re) / (p : ℝ))
        = (1 - (g p).re) * (p : ℝ)⁻¹ * (1 / Real.exp 1) := by rw [div_eq_mul_inv]; ring
      _ ≤ (1 - (g p).re) * (p : ℝ)⁻¹ * (p : ℝ) ^ (-σ : ℝ) :=
          mul_le_mul_of_nonneg_left hcut_p hfac_nn
      _ = (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := by rw [hsplitrpow]; ring
  -- assemble
  rw [hPD, Finset.mul_sum]
  refine le_trans (Finset.sum_le_sum htermcut) hge

/-- **B1 — the general-`σ` distance identification** (`dist_identification_sigma`).  For a
1-bounded prime datum `g` and `σ ∈ (0, 1]`:
`∑'_p Re(g p)·p^{−1−σ} ≤ (log(1/σ) + (log 4 + cpeel)) − (1/e)·𝔻²(1, g; e^{1/σ})`.
The general-`σ` analog of the pinned SF-2 `dist_identification`: the full defect sum splits as
`∑'_p p^{−1−σ} − ∑'_p (1 − Re g p)·p^{−1−σ}`, the first bounded by `prime_sum_sigma`, the
second dominating `(1/e)·𝔻²` by `sigma_cut_lower`. -/
theorem dist_identification_sigma {g : ℕ → ℂ} (hg : ∀ p, ‖g p‖ ≤ 1)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    (∑' p : Nat.Primes, (g p).re * (p : ℝ) ^ (-1 - σ : ℝ))
      ≤ (Real.log (1 / σ) + (Real.log 4 + cpeel))
        - (1 / Real.exp 1) * pretDistSq (fun _ => 1) g (Real.exp (1 / σ)) := by
  have hσ1' : (-1 - σ : ℝ) < -1 := by linarith
  have hre1 : ∀ n : ℕ, -1 ≤ (g n).re ∧ (g n).re ≤ 1 := fun n =>
    abs_le.mp (le_trans (Complex.abs_re_le_norm (g n)) (hg n))
  -- summabilities
  have hP : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-1 - σ : ℝ)) :=
    Nat.Primes.summable_rpow.mpr hσ1'
  have hR : Summable (fun p : Nat.Primes => (g p).re * (p : ℝ) ^ (-1 - σ : ℝ)) := by
    refine Summable.of_norm_bounded hP (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (abs_le.mpr (hre1 (p : ℕ)))
  have hQ : Summable (fun p : Nat.Primes => (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ)) := by
    refine Summable.of_nonneg_of_le
      (fun p => mul_nonneg (by linarith [(hre1 (p : ℕ)).2])
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (fun p => ?_) (hP.mul_left 2)
    exact mul_le_mul_of_nonneg_right (by linarith [(hre1 (p : ℕ)).1])
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  -- the defect split
  have hsplit_id : (∑' p : Nat.Primes, (g p).re * (p : ℝ) ^ (-1 - σ : ℝ))
      = (∑' p : Nat.Primes, (p : ℝ) ^ (-1 - σ : ℝ))
        - ∑' p : Nat.Primes, (1 - (g p).re) * (p : ℝ) ^ (-1 - σ : ℝ) := by
    rw [← Summable.tsum_sub hP hQ]
    exact tsum_congr (fun p => by ring)
  rw [hsplit_id]
  linarith [prime_sum_sigma hσ0 hσ1, sigma_cut_lower hg hσ0]

/-- **B1 pin (general `σ`)** (`exponent_shift_eq`).  The general-`σ` analog of the pinned
`exponent_pin_eq`: on the line `s = (1 + σ) + it`, the real part of the twisted summand
factors as `Re((g·p^{−it})(p))·p^{−1−σ}` (with `g·p^{−it} = g·costwist(−t)`).  Proof is the
pin decomposition with `1/log X` replaced by the free `σ`. -/
lemma exponent_shift_eq {g : ℕ → ℂ} (σ : ℝ) (t : ℝ) (p : Nat.Primes) :
    (g p * (p : ℂ) ^ (-(((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I))).re
      = (g p * costwist (-t) p).re * (p : ℝ) ^ (-1 - σ : ℝ) := by
  have hpℂ : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.pos.ne'
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
  have hdecomp : ((p : ℕ) : ℂ) ^ (-(((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I))
      = (((((p : ℕ) : ℝ) ^ (-1 - σ : ℝ)) : ℝ) : ℂ) * costwist (-t) (p : ℕ) := by
    rw [show -(((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)
          = ((-1 - σ : ℝ) : ℂ) + (((-t : ℝ)) : ℂ) * Complex.I from by
        push_cast; ring, Complex.cpow_add _ _ hpℂ]
    congr 1
    · rw [← Complex.ofReal_natCast (p : ℕ), ← Complex.ofReal_cpow hp0.le]
    · rw [costwist, Complex.cpow_def_of_ne_zero hpℂ, ← Complex.natCast_log]
      congr 1
      push_cast; ring
  rw [hdecomp, mul_left_comm, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- **B1 exit — the σ-uniform head bound** (`head_sigma_bound`).  For a globally 1-bounded
`g`, `σ ∈ (0, 1]`, and any `t`, the L-series of `ellLin g` on the line `(1 + σ) + it` obeys
the honest `σ`-uniform majorant
`‖F(1+σ+it)‖ ≤ C·(1/σ)·exp(−(1/e)·𝔻²(1, g·p^{−it}; e^{1/σ}))`,
with `C = exp(cpeel + (log 4 + cpeel))`.  Composing `euler_log_bound` (SF-1) with the pin
`exponent_shift_eq` and the identification `dist_identification_sigma` at the twisted datum
`g·costwist(−t)`.  This is the pretentious majorant B3's flat-regime integral consumes. -/
theorem head_sigma_bound {g : ℕ → ℂ} (hg : ∀ p, ‖g p‖ ≤ 1)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (t : ℝ) :
    ‖LSeries (ellLin g) (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
        * Real.exp (-(1 / Real.exp 1)
            * pretDistSq (fun _ => 1) (fun n => g n * costwist (-t) n) (Real.exp (1 / σ))) := by
  set g' : ℕ → ℂ := fun n => g n * costwist (-t) n with hg'def
  have hg' : ∀ p, ‖g' p‖ ≤ 1 := by
    intro p
    have hgp : g' p = g p * costwist (-t) p := by rw [hg'def]
    rw [hgp, norm_mul, costwist_norm, mul_one]; exact hg p
  have hs : 1 < (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I).re := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp; linarith
  have hterm : ∀ p : Nat.Primes,
      (g p * (p : ℂ) ^ (-(((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I))).re
        = (g' p).re * (p : ℝ) ^ (-1 - σ : ℝ) := by
    intro p
    rw [hg'def]; exact exponent_shift_eq σ t p
  have hexp : (∑' p : Nat.Primes,
        (g p * (p : ℂ) ^ (-(((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I))).re)
      = ∑' p : Nat.Primes, (g' p).re * (p : ℝ) ^ (-1 - σ : ℝ) := tsum_congr hterm
  refine le_trans (euler_log_bound g (fun p _ => hg p) hs) ?_
  rw [hexp]
  have hid := dist_identification_sigma hg' hσ0 hσ1
  refine le_trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hid) (Real.exp_nonneg cpeel)) (le_of_eq ?_)
  rw [← Real.exp_add,
    show cpeel + ((Real.log (1 / σ) + (Real.log 4 + cpeel))
          - (1 / Real.exp 1) * pretDistSq (fun _ => 1) g' (Real.exp (1 / σ)))
        = ((cpeel + (Real.log 4 + cpeel)) + Real.log (1 / σ))
          + (-(1 / Real.exp 1) * pretDistSq (fun _ => 1) g' (Real.exp (1 / σ))) from by ring,
    Real.exp_add, Real.exp_add, Real.exp_log (show (0 : ℝ) < 1 / σ from by positivity),
    mul_assoc]

/-! ## B2 — the crude scale-monotone distance floor (`scale_floor`)

The pretentious distance is monotone in the scale; the crude comparison quantifies the
deficit incurred by shrinking the cutoff from `X` to `e^{1/σ}` as the reciprocal mass of the
primes in the gap `(e^{1/σ}, X]`, `≤ Σ 2/p = 2(loglog X − loglog e^{1/σ}) + O(1) =
2 log(σ·log X) + O(1)` (sharp Mertens at both scales).  This lets B3 replace the frozen
`𝔻²(e^{1/σ})` by `M − 2 log(σL) − C` for the flat-regime integrand. -/

/-- **B2 — the crude scale floor** (`scale_floor`).  For 1-bounded data `f, g`, `σ ∈ (0, 1]`,
and `e^{1/σ} ≤ X`:
`𝔻²(f, g; X) − 2·log(σ·log X) − 48 ≤ 𝔻²(f, g; e^{1/σ})`.
The gap `𝔻²(X) − 𝔻²(e^{1/σ}) = Σ_{e^{1/σ}<p≤X}(1 − Re(f·conj g))/p ≤ Σ 2/p =
2(S(X) − S(e^{1/σ}))`, bounded via `mertens_second_sharp_real` at both scales
(`loglog e^{1/σ} = log(1/σ)`, `12/log e^{1/σ} = 12σ`), the honest residual `24/log X + 24σ`
absorbed into the uniform `48` (using `log X ≥ 1`, `σ ≤ 1`). -/
theorem scale_floor {f g : ℕ → ℂ} (hf : ∀ p, ‖f p‖ ≤ 1) (hg : ∀ p, ‖g p‖ ≤ 1)
    {σ X : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X) :
    pretDistSq f g X - 2 * Real.log (σ * Real.log X) - 48
      ≤ pretDistSq f g (Real.exp (1 / σ)) := by
  -- scale facts
  have h1invσ : (1 : ℝ) ≤ 1 / σ := by rw [le_div_iff₀ hσ0]; linarith
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hY2 : (2 : ℝ) ≤ Real.exp (1 / σ) :=
    le_trans h2e (Real.exp_le_exp.mpr h1invσ)
  have hX2 : (2 : ℝ) ≤ X := le_trans hY2 hYX
  have hlogYX : Real.log (Real.exp (1 / σ)) ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hYX
  rw [Real.log_exp] at hlogYX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by linarith
  -- the subset of prime cutoffs
  have hfl : ⌊Real.exp (1 / σ)⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor hYX
  have hsub : (Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime
      ⊆ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime := by
    refine Finset.filter_subset_filter _ ?_
    intro n hn
    rw [Finset.mem_range] at hn ⊢
    omega
  -- the defect decomposition D²(X) = gap + D²(e^{1/σ})
  have hdecomp : pretDistSq f g X
      = (∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime)
            \ ((Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime),
          (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
        + pretDistSq f g (Real.exp (1 / σ)) := by
    simp only [pretDistSq]
    exact (Finset.sum_sdiff hsub).symm
  -- gap mass ≤ 2·(S(X) − S(e^{1/σ}))
  have hgap : (∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime)
        \ ((Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime),
        (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
      ≤ 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial (Real.exp (1 / σ))) := by
    have h1mass : (∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime)
          \ ((Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime), (1 : ℝ) / (p : ℝ))
        = Salt.Mertens.SPartial X - Salt.Mertens.SPartial (Real.exp (1 / σ)) := by
      have hss : (∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime)
            \ ((Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime), (1 : ℝ) / (p : ℝ))
          + (∑ p ∈ (Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
          = ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        Finset.sum_sdiff hsub
      have hSPX : Salt.Mertens.SPartial X
          = ∑ p ∈ (Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := rfl
      have hSPY : Salt.Mertens.SPartial (Real.exp (1 / σ))
          = ∑ p ∈ (Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ) :=
        rfl
      rw [hSPX, hSPY]; linarith [hss]
    calc (∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime)
            \ ((Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime),
            (1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime)
            \ ((Finset.range (⌊Real.exp (1 / σ)⌋₊ + 1)).filter Nat.Prime), (2 : ℝ) / (p : ℝ) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hprime : p.Prime := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
          have hnorm : ‖f p * (starRingEnd ℂ) (g p)‖ ≤ 1 := by
            rw [norm_mul, Complex.norm_conj]
            nlinarith [hf p, hg p, norm_nonneg (f p), norm_nonneg (g p)]
          have hre : -1 ≤ (f p * (starRingEnd ℂ) (g p)).re := by
            have h := (abs_le.mp (Complex.abs_re_le_norm (f p * (starRingEnd ℂ) (g p)))).1
            linarith [h, hnorm]
          gcongr
          linarith
      _ = 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial (Real.exp (1 / σ))) := by
          rw [← h1mass, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by rw [mul_one_div])
  -- Mertens at both scales
  have hmX := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hX2)
  have hmY := abs_le.mp (Salt.Mertens.mertens_second_sharp_real hY2)
  have hlogY : Real.log (Real.exp (1 / σ)) = 1 / σ := Real.log_exp _
  have hloglogY : Real.log (Real.log (Real.exp (1 / σ))) = Real.log (1 / σ) := by rw [hlogY]
  have h12Y : (12 : ℝ) / Real.log (Real.exp (1 / σ)) = 12 * σ := by
    rw [hlogY, div_div_eq_mul_div, div_one]
  have hlogeq : Real.log (Real.log X) - Real.log (1 / σ) = Real.log (σ * Real.log X) := by
    rw [one_div, Real.log_inv, Real.log_mul hσ0.ne' hlogXpos.ne']; ring
  have h12X : (12 : ℝ) / Real.log X ≤ 12 := by rw [div_le_iff₀ hlogXpos]; nlinarith [hlogX1]
  have h12σ : 12 * σ ≤ 12 := by nlinarith [hσ1, hσ0]
  rw [hdecomp]
  have hmertfinal : 2 * (Salt.Mertens.SPartial X - Salt.Mertens.SPartial (Real.exp (1 / σ)))
      ≤ 2 * Real.log (σ * Real.log X) + 48 := by
    linarith [hmX.2, hmY.1, hlogeq, hloglogY, h12Y, h12X, h12σ]
  linarith [hgap, hmertfinal]

/-- **B2 — the `M_range` corollary** (`scale_floor_Mrange`).  For a frequency `t` in the
`M_range` window (the membership side-condition per `M_range`'s definition) and `σ ∈ (0, 1]`
with `e^{1/σ} ≤ X`:
`M_range(1; X, T) − 2·log(σ·log X) − 48 ≤ 𝔻²(1, n^{it}; e^{1/σ})`.
The distance at scale `X` dominates its window infimum `M_range` (`csInf_le`; the image is
bounded below by `0` via `pretDistSq_nonneg`), and `scale_floor` transports it to the shrunk
scale `e^{1/σ}` at the crude `2 log(σL)` cost.  This is the flat-regime `M` that B3 consumes. -/
theorem scale_floor_Mrange {t X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hYX : Real.exp (1 / σ) ≤ X)
    (hmem : (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X) :
    M_range (fun _ => 1) X T - 2 * Real.log (σ * Real.log X) - 48
      ≤ pretDistSq (fun _ => 1) (costwist t) (Real.exp (1 / σ)) := by
  have hf1 : ∀ p : ℕ, ‖(fun _ => (1 : ℂ)) p‖ ≤ 1 := fun _ => by simp
  have hg1 : ∀ p : ℕ, ‖costwist t p‖ ≤ 1 := fun n => le_of_eq (costwist_norm t n)
  have hsf := scale_floor hf1 hg1 hσ0 hσ1 hYX
  have hbdd : BddBelow ((fun t' : ℝ => pretDistSq (fun _ => 1) (costwist t') X) ''
      {t' : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t'|
        ∧ |t'| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t'| ≤ X}) := by
    refine ⟨0, ?_⟩
    rintro v ⟨t', _, rfl⟩
    exact pretDistSq_nonneg (fun _ => 1) (costwist t') X hf1
      (fun n => le_of_eq (costwist_norm t' n))
  have hinf : M_range (fun _ => 1) X T ≤ pretDistSq (fun _ => 1) (costwist t) X := by
    apply csInf_le hbdd
    exact ⟨t, hmem, rfl⟩
  linarith [hsf, hinf]

/-! ## B3 — the flat-regime σ-integral of the pretentious majorant (`sigma_cutoff_pretentious`)

The REPLACEMENT arm for `HExit.sigma_cutoff`'s flat regime under the `c = 1/e` re-freeze
(⟦A — B4⟧).  With the B1 pointwise majorant `‖F(1+σ+it)‖ ≤ C(1/σ)e^{−(1/e)𝔻²(e^{1/σ})}` and the
B2 floor `𝔻²(e^{1/σ}) ≥ M − 2 log(σL) − C`, the weighted-integrand `Fbound σ/σ` is dominated
by `(1/σ²)·e^{−(1/e)(M − 2 log(σL) − C)}`.  The KEY is the `2c = 2/e < 1` convergence: the
integrand is `K·σ^{2/e−2}` and `∫ σ^{2/e−2}` converges at the top (exponent `2/e−2 > −2`; the
antiderivative `σ^{2/e−1}/(2/e−1)` is explicit, `integral_rpow`), so the whole integral is
`≤ C′·e^{−M/e}·L` for ANY upper limit `b ≥ 1/L` (the `min(σ*, 2η)` corner is subsumed: the
flat bound holds regardless of the top).  Contrast the OLD `(1+M)e^{−M}` arm whose flat piece
paid `e^{−M}L·log(σ*L) = e^{−M}L·M` — the linear-in-`M` factor that B4 dissolves.

**Tail-arm compatibility (docstring target, NOT built here).**  The trivial arm `htriv`
(`Fbound σ ≤ 1/σ`, `∫ σ^{−2}` on `[σ*, 2η]`) is UNCHANGED by the re-freeze; the combined
`sigma_cutoff_c : ∫_{1/L}^{2η} Fbound σ/σ ≤ C″·e^{−M/e}·L` (flat via this stone + tail via the
landed `HExit.sigma_cutoff` pattern) is the pinned-assembly target — it wants `HExit`'s socket
and is left to that file (do NOT reopen `HExit` from here). -/

/-- **B3 — the flat-regime pretentious σ-cutoff** (`sigma_cutoff_pretentious`).  For `L ≥ 3`,
`M ≥ 0`, `C ≥ 0`, and any upper limit `b ≥ 1/L`:
`∫_{1/L}^{b} (1/σ²)·exp(−(1/e)(M − 2 log(σL) − C)) dσ ≤ (exp(C/e)/(1 − 2/e))·exp(−M/e)·L`.
The integrand is `K·σ^{2/e−2}` with `K = exp(−M/e)·exp(C/e)·L^{2/e}`; `integral_rpow` gives the
closed antiderivative, and `2/e − 1 < 0` (since `e > 2`) makes `L^{2/e}·(1/L)^{2/e−1} = L` and
the top-endpoint term drop, yielding the honest `c = 1/e` grade with fixed constant. -/
theorem sigma_cutoff_pretentious {L M C b : ℝ} (hL : 3 ≤ L) (_hM : 0 ≤ M) (_hC : 0 ≤ C)
    (hb : 1 / L ≤ b) :
    (∫ σ in (1 / L)..b,
        (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1) * (M - 2 * Real.log (σ * L) - C)))
      ≤ (Real.exp (C / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(M / Real.exp 1)) * L := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le hLinv0 hb
  have he1 : (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have he1pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h2e : 2 / Real.exp 1 < 1 := by rw [div_lt_one he1pos]; exact he1
  have hsneg : (2 / Real.exp 1 - 1 : ℝ) < 0 := by linarith
  have hσsq : ∀ σ : ℝ, σ ^ (2 : ℝ) = σ ^ 2 := fun σ => by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  set K : ℝ := Real.exp (-(M / Real.exp 1)) * Real.exp (C / Real.exp 1)
      * L ^ (2 / Real.exp 1 : ℝ) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  -- pointwise integrand identity for σ > 0
  have hpoint0 : ∀ σ : ℝ, 0 < σ →
      (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1) * (M - 2 * Real.log (σ * L) - C))
        = K * σ ^ (2 / Real.exp 1 - 2 : ℝ) := by
    intro σ hσpos
    have hσL : 0 < σ * L := mul_pos hσpos hLpos
    rw [show -(1 / Real.exp 1) * (M - 2 * Real.log (σ * L) - C)
          = -(M / Real.exp 1) + Real.log (σ * L) * (2 / Real.exp 1) + C / Real.exp 1 from by ring,
      Real.exp_add, Real.exp_add, ← Real.rpow_def_of_pos hσL,
      Real.mul_rpow hσpos.le hLpos.le, hKdef,
      show σ ^ (2 / Real.exp 1 - 2 : ℝ) = σ ^ (2 / Real.exp 1 : ℝ) * (1 / σ ^ 2) from by
        rw [Real.rpow_sub hσpos, hσsq σ, div_eq_mul_one_div]]
    ring
  have hpoint : Set.EqOn
      (fun σ => (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1) * (M - 2 * Real.log (σ * L) - C)))
      (fun σ => K * σ ^ (2 / Real.exp 1 - 2 : ℝ)) (Set.uIcc (1 / L) b) := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact hpoint0 σ (lt_of_lt_of_le hLinv0 hσ.1)
  -- integrate the rpow monomial
  rw [intervalIntegral.integral_congr hpoint, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by intro h; linarith, by
      rw [Set.uIcc_of_le hb, Set.mem_Icc]; rintro ⟨h1, _⟩; linarith⟩),
    show (2 / Real.exp 1 - 2 : ℝ) + 1 = 2 / Real.exp 1 - 1 from by ring]
  -- the closed-form bound
  have hbs : (0 : ℝ) < b ^ (2 / Real.exp 1 - 1 : ℝ) := Real.rpow_pos_of_pos hbpos _
  have hLL : L ^ (2 / Real.exp 1 : ℝ) * (1 / L) ^ (2 / Real.exp 1 - 1 : ℝ) = L := by
    rw [one_div, Real.inv_rpow hLpos.le, ← Real.rpow_neg hLpos.le, ← Real.rpow_add hLpos,
      show (2 / Real.exp 1 : ℝ) + -(2 / Real.exp 1 - 1) = 1 from by ring, Real.rpow_one]
  have hKL : K * (1 / L) ^ (2 / Real.exp 1 - 1 : ℝ)
      = Real.exp (-(M / Real.exp 1)) * Real.exp (C / Real.exp 1) * L := by
    rw [hKdef, mul_assoc, hLL]
  have hstep : (b ^ (2 / Real.exp 1 - 1 : ℝ) - (1 / L) ^ (2 / Real.exp 1 - 1 : ℝ))
        / (2 / Real.exp 1 - 1)
      ≤ (1 / L) ^ (2 / Real.exp 1 - 1 : ℝ) / (1 - 2 / Real.exp 1) := by
    rw [show (1 : ℝ) - 2 / Real.exp 1 = -(2 / Real.exp 1 - 1) from by ring, div_neg, sub_div]
    have hAs : b ^ (2 / Real.exp 1 - 1 : ℝ) / (2 / Real.exp 1 - 1) ≤ 0 :=
      le_of_lt (div_neg_of_pos_of_neg hbs hsneg)
    linarith [hAs]
  calc K * ((b ^ (2 / Real.exp 1 - 1 : ℝ) - (1 / L) ^ (2 / Real.exp 1 - 1 : ℝ))
          / (2 / Real.exp 1 - 1))
      ≤ K * ((1 / L) ^ (2 / Real.exp 1 - 1 : ℝ) / (1 - 2 / Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hstep hKnn
    _ = (K * (1 / L) ^ (2 / Real.exp 1 - 1 : ℝ)) / (1 - 2 / Real.exp 1) := by rw [mul_div_assoc]
    _ = (Real.exp (-(M / Real.exp 1)) * Real.exp (C / Real.exp 1) * L)
          / (1 - 2 / Real.exp 1) := by rw [hKL]
    _ = (Real.exp (C / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(M / Real.exp 1)) * L := by ring

/-! ## B2′ — the g-datum `M_range` seam clone (`scale_floor_Mrange_seam`)

The BINDER-REF repair (⟦A — 2026-07-23 11:06⟧).  `scale_floor_Mrange` (:960) floors the
*g-free* datum `M_range(1; X, T)`, but the joint head (`T1_head_wire`'s J0 amendment,
`hRHS_discharged_joint`, `T1_head_supplied_joint`) instantiates `M` at the *seam datum*
`M := M_range (seamCoeff (ellLin g) 1 t₀) X T` — the twisted `ℓ`-coefficient sequence whose
L-series *is* the σ-live joint head.  Flooring `M_range(1)` in the strong-cancellation regime
undershoots (it discards the g-dependence entirely: exactly the wrong `M` when the datum
cancels well against the twist).  This clone floors the seam datum instead, and the exact
trivial-seam identity `𝔻(seamCoeff f 1 t₀, costwist t; X)² = 𝔻(f, costwist(t+t₀); X)²` translates
the shrunk-scale RHS into the bare `ℓ`-datum shifted-center form
`𝔻(ellLin g, costwist(t+t₀); e^{1/σ})²` that `head_sigma_bound`'s g-datum decay consumes.

`seamCoeff_trivial_dist_eq` (`HalaszHead:375`) is the landed keystone; `HalaszHead` is not in
`SupF`'s import closure, so the identity and the two `costwist`-algebra facts it needs
(`costwist_add`/`costwist_conj`, `DistSplit`) are re-derived locally below as `private` copies —
byte-for-byte the landed proofs, no statement change (Iron rule 1). -/

/-- Local re-derivation of `head_natCpow_neg_costwist` (`HalaszHead`, `private`, unreachable
here): the seam twist `n ↦ n^{−it₀}` is the character `costwist (−t₀)` for `n ≥ 1`. -/
private lemma seam_twist_costwist (t₀ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℂ) ^ (-(t₀ : ℂ) * Complex.I) = costwist (-t₀) n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
  unfold costwist
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- Local copy of `costwist_add` (`DistSplit`, unreachable here): phase additivity. -/
private lemma costwist_add_local (a b : ℝ) (n : ℕ) :
    costwist a n * costwist b n = costwist (a + b) n := by
  unfold costwist
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Local copy of `costwist_conj` (`DistSplit`, unreachable here): conjugation flips phase. -/
private lemma costwist_conj_local (a : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (costwist a n) = costwist (-a) n := by
  unfold costwist
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Local re-derivation of `seamCoeff_trivial_dist_eq` (`HalaszHead:375`, unreachable here):
the EXACT trivial-seam distance identity
`𝔻(seamCoeff f 1 t₀, costwist t; X)² = 𝔻(f, costwist(t+t₀); X)²`.  The trivial indicator puts
every prime in window (no out-of-window deficit), and the seam twist `n^{−it₀}` folds into the
character, shifting the center frequency by `t₀`. -/
private lemma seamCoeff_trivial_dist_eq_local {f : ℕ → ℂ} (t₀ t X : ℝ) :
    pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t) X
      = pretDistSq f (costwist (t + t₀)) X := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
  have hp1 : 1 ≤ p := hpp.one_lt.le
  have hpne : p ≠ 0 := Nat.one_le_iff_ne_zero.mp hp1
  have hsc : seamCoeff f (fun _ => 1) t₀ p = f p * costwist (-t₀) p := by
    unfold seamCoeff
    rw [if_neg hpne]
    simp only [seam_twist_costwist t₀ hp1, mul_one]
  have heq : seamCoeff f (fun _ => 1) t₀ p * (starRingEnd ℂ) (costwist t p)
      = f p * (starRingEnd ℂ) (costwist (t + t₀) p) := by
    rw [hsc, costwist_conj_local t p, costwist_conj_local (t + t₀) p, mul_assoc,
      costwist_add_local (-t₀) (-t) p, show -t₀ + -t = -(t + t₀) from by ring]
  rw [heq]

/-- **B2′ — the seam-datum `M_range` floor** (`scale_floor_Mrange_seam`).  The g-datum clone of
`scale_floor_Mrange`: for a globally 1-bounded `g` at primes, a frequency `t` in the `M_range`
window, and `σ ∈ (0, 1]` with `e^{1/σ} ≤ X`,
`M_range(seamCoeff (ellLin g) 1 t₀; X, T) − 2·log(σ·log X) − 48
  ≤ 𝔻(ellLin g, costwist(t+t₀); e^{1/σ})²`.
Proof mirrors the g-free corollary: the scale-`X` distance dominates its window infimum
`M_range` (`csInf_le`; the image is `≥ 0` via `pretDistSq_nonneg`, the seam datum 1-bounded via
`norm_seamCoeff_le`∘`ellLin_norm_le_one`), and `scale_floor` transports it to `e^{1/σ}` at the
crude `2 log(σL)` cost; the trivial-seam identity then translates the seam datum on the shrunk
scale into the bare `ℓ`-datum shifted-center form.  This is the `M` `head_sigma_bound`'s g-datum
decay and `T1_head_wire`'s J0 `M_range` instantiation both consume (the strong-cancellation
regime: flooring the g-free `M_range(1)` here discards the cancellation and undershoots). -/
theorem scale_floor_Mrange_seam {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (hmem : (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X) :
    M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T - 2 * Real.log (σ * Real.log X) - 48
      ≤ pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ)) := by
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hf1 : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  have hg1 : ∀ n : ℕ, ‖costwist t n‖ ≤ 1 := fun n => le_of_eq (costwist_norm t n)
  have hsf := scale_floor hf1 hg1 hσ0 hσ1 hYX
  have hbdd : BddBelow ((fun t' : ℝ =>
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t') X) ''
      {t' : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t'|
        ∧ |t'| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t'| ≤ X}) := by
    refine ⟨0, ?_⟩
    rintro v ⟨t', _, rfl⟩
    exact pretDistSq_nonneg (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t') X hf1
      (fun n => le_of_eq (costwist_norm t' n))
  have hinf : M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
      ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X := by
    apply csInf_le hbdd
    exact ⟨t, hmem, rfl⟩
  rw [seamCoeff_trivial_dist_eq_local t₀ t (Real.exp (1 / σ))] at hsf
  linarith [hsf, hinf]

end Salt.MR
