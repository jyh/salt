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
