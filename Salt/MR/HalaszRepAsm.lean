/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszRep
import Salt.MR.HalaszSeam

/-!
# HALASZ-INFRA — the S1' representation ASSEMBLY (`HalaszRepAsm`)

The concrete C-assembly of the S1' representation (`prop21_analog`, the frozen
statement in `Salt/MR/HalaszSeam.lean`'s module docstring), consuming the ladder
`Salt.MR.HalaszRep` (the FTC leg `shifted_dirichlet_ftc` and the four
single-interchange Fubini rungs) and the seam `Salt.MR.HalaszSeam`.

This file lands the three assembly tasks the HAL-REP scoper (catch #255) named:

* **(T1) the object defs** — `restrictBelow` (the small-prime datum, the exact
  complement of `restrictAbove`), the split product law
  `ellLin g = ellLin (restrictBelow y g) ⍟ ellLin (restrictAbove y g)`
  (GHS `f = s ⋆ ℓ`, p.7), and the four Dirichlet objects `smoothSeries` (`𝒮`),
  `largeSeries` (`𝓛`), `windowSum` (`P_β`) with their summability/analytic API;
* **(T2) the domination discharges** — the concrete dominating functions for the
  three hypothesis-carrying Fubini rungs at the seam integrands (the hat kernel's
  `1/‖s‖²` decay `hat_mellin_bound`, the finite window `windowSum`, and the
  compact-square continuity);
* **(T3) the window algebra** — gluing `shifted_dirichlet_ftc`'s endpoint
  differences back to the coefficient sums via `lambdaLin_convolution`, and the
  honest assembly of the S1' representation.

## DEVIATION RECORDED LOUDLY (iron rule 1 — never silent)

The dispatch brief describes `restrictBelow y g` as "primes `< y`".  The
mathematically-correct object — the one making the product law
`ellLin g = ellLin (restrictBelow y g) ⍟ ellLin (restrictAbove y g)` hold
UNCONDITIONALLY (for every `n`, every `y`, whether or not `y` is a prime value) —
is the **exact complement of `restrictAbove` (`y < p`), i.e. `p ≤ y`**.  This
matches GHS (`docs/sources/1706.03749v1.pdf`, §2 p.7): the small-prime datum `s`
is supported on `p ≤ y` and the large-prime datum `ℓ` on `p > y`, so that
`f = s ⋆ ℓ` is a genuine partition of the Euler factors.  With a strict `p < y`
cutoff a prime exactly equal to `y` would fall in NEITHER part and the product
law would fail at that Euler factor.  The complement `p ≤ y` is adopted; see
`restrictBelow_add_restrictAbove` (partition) and `restrictBelow_mul_restrictAbove`
(disjointness), the two facts that carry the split.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators LSeries.notation
open ArithmeticFunction

/-! ## T1 — the small-prime datum `restrictBelow` and the split algebra -/

/-- The prime datum restricted to primes at or below the smoothness cutoff `y`
(the `g·1_{p≤y}` of GHS §2, the exact complement of `restrictAbove y g`'s `p>y`). -/
def restrictBelow (y : ℝ) (g : ℕ → ℂ) : ℕ → ℂ :=
  fun p => if (p : ℝ) ≤ y then g p else 0

/-- **Partition of the Euler factors.**  At every `p`, the below/above data sum to
`g p` (exactly one of the disjoint cutoffs `p ≤ y`, `y < p` fires). -/
lemma restrictBelow_add_restrictAbove (y : ℝ) (g : ℕ → ℂ) (p : ℕ) :
    restrictBelow y g p + restrictAbove y g p = g p := by
  unfold restrictBelow restrictAbove
  by_cases h : (p : ℝ) ≤ y
  · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg h, if_pos (not_le.mp h), zero_add]

/-- **Disjointness of the cutoffs.**  The below/above data never overlap:
their product is `0` at every `p` (the `p ≤ y` and `y < p` indicators are
disjoint).  This is the fact that kills the cross term at the squarefull
(`k = 2`) Euler factor in the split product law. -/
lemma restrictBelow_mul_restrictAbove (y : ℝ) (g : ℕ → ℂ) (p : ℕ) :
    restrictBelow y g p * restrictAbove y g p = 0 := by
  unfold restrictBelow restrictAbove
  by_cases h : (p : ℝ) ≤ y
  · rw [if_neg (not_lt.mpr h), mul_zero]
  · rw [if_neg h, zero_mul]

/-- `restrictBelow` preserves the unit bound at primes. -/
lemma restrictBelow_norm_le {g : ℕ → ℂ} {y : ℝ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (p : ℕ) (hp : p.Prime) : ‖restrictBelow y g p‖ ≤ 1 := by
  unfold restrictBelow; split_ifs with h
  · exact hg p hp
  · simp

/-- `restrictAbove` preserves the unit bound at primes. -/
lemma restrictAbove_norm_le {g : ℕ → ℂ} {y : ℝ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (p : ℕ) (hp : p.Prime) : ‖restrictAbove y g p‖ ≤ 1 := by
  unfold restrictAbove; split_ifs with h
  · exact hg p hp
  · simp

/-! ### The split product law `ellLin g = ellLin (below) ⍟ ellLin (above)` -/

/-- **The split, `ArithmeticFunction`-ring form.**  `toAF (ellLin g)` factors as the
Dirichlet product of the below/above linearized twists.  Both sides are multiplicative
(`isMult_ellLin`); on a prime power `p^i` the local convolution telescopes to the single
matching term (`i = 0 → 1`, `i = 1 → g p` by the partition, `i ≥ 2 → 0` by squarefree
support and, at `i = 2`, the cutoff disjointness). -/
lemma ellLin_split_toAF (y : ℝ) (g : ℕ → ℂ) :
    toArithmeticFunction (ellLin g)
      = toArithmeticFunction (ellLin (restrictBelow y g))
        * toArithmeticFunction (ellLin (restrictAbove y g)) := by
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMult_ellLin g)
      _ ((isMult_ellLin (restrictBelow y g)).mul (isMult_ellLin (restrictAbove y g)))]
  intro p i hp
  rw [convAF_prime_pow _ _ hp, toAF_apply, if_neg (pow_ne_zero i hp.pos.ne')]
  rcases i with _ | i'
  · simp [ellLin_one]
  rcases i' with _ | i''
  · -- i = 1
    simp only [zero_add, pow_one, ellLin_apply_prime g hp, Finset.sum_range_succ,
      Finset.sum_range_zero, Nat.sub_zero, Nat.sub_self, pow_zero, ellLin_one,
      ellLin_apply_prime (restrictBelow y g) hp, ellLin_apply_prime (restrictAbove y g) hp,
      one_mul, mul_one]
    rw [← restrictBelow_add_restrictAbove y g p]; ring
  · -- i = i'' + 2 ≥ 2
    rw [ellLin_prime_pow_ge_two g hp (by omega : 2 ≤ i'' + 1 + 1)]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j 2 with h2 | h2
    · interval_cases j
      · rw [Nat.sub_zero,
          ellLin_prime_pow_ge_two (restrictAbove y g) hp (by omega : 2 ≤ i'' + 1 + 1), mul_zero]
      · rcases Nat.eq_zero_or_pos i'' with rfl | hpos
        · simp only [show 0 + 1 + 1 - 1 = 1 by omega, pow_one,
            ellLin_apply_prime (restrictBelow y g) hp, ellLin_apply_prime (restrictAbove y g) hp]
          exact restrictBelow_mul_restrictAbove y g p
        · rw [ellLin_prime_pow_ge_two (restrictAbove y g) hp
            (by omega : 2 ≤ i'' + 1 + 1 - 1), mul_zero]
    · rw [ellLin_prime_pow_ge_two (restrictBelow y g) hp h2, zero_mul]

/-- **T1 — the split product law** (GHS `f = s ⋆ ℓ`, p.7, the linearized analog).
The squarefree-linearized twist `ℓ = ellLin g` factors as the Dirichlet convolution of
its below-cutoff and above-cutoff parts.  Transported from `ellLin_split_toAF`. -/
theorem ellLin_split (y : ℝ) (g : ℕ → ℂ) :
    ellLin (restrictBelow y g) ⍟ ellLin (restrictAbove y g) = ellLin g := by
  change ⇑(toArithmeticFunction (ellLin (restrictBelow y g))
      * toArithmeticFunction (ellLin (restrictAbove y g))) = ellLin g
  rw [← ellLin_split_toAF y g]
  funext n
  rw [toAF_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [ellLin]
  · rw [if_neg hn]

/-! ## T1 — the four Dirichlet objects `𝒮`, `𝓛`, `P_β`

The frozen S1' integrand `𝒮(s-α-β)·𝓛(s+β)·P₋(s-β)·P₊(s+β)·hatKernel` (Seam
docstring, GHS Prop 2.1 (2.1)) is built from three functions of `s`: the smooth
and large L-series and the window Dirichlet polynomial.  `P₋` and `P₊` are the
same `windowSum` evaluated at `s-β` and `s+β`. -/

/-- **T1 — the smooth (small-prime) Dirichlet series `𝒮`** (GHS `𝒮(s)=∑ s(n)/n^s`,
p.7): the L-series of the below-cutoff linearized twist.  Bounded coefficients
(`‖·‖ ≤ 1`), so its abscissa of absolute convergence is `≤ 1`. -/
def smoothSeries (y : ℝ) (g : ℕ → ℂ) : ℂ → ℂ := LSeries (ellLin (restrictBelow y g))

/-- **T1 — the large (big-prime) Dirichlet series `𝓛`** (GHS `𝓛(s)=∑ ℓ(n)/n^s`, p.7):
the L-series of the above-cutoff linearized twist.  Abscissa `≤ 1`. -/
def largeSeries (y : ℝ) (g : ℕ → ℂ) : ℂ → ℂ := LSeries (ellLin (restrictAbove y g))

/-- **T1 — the window Dirichlet polynomial `P_β`** (GHS `∑_{y<n<x/y} Λ_ℓ(n)/n^s`,
(2.1), the linearized analog with `Λ_ℓ = lambdaLin (restrictAbove y g)`): a FINITE
sum over the open window `(y, X/y)`.  For `0 ≤ y` the index set `Ioo ⌊y⌋₊ ⌈X/y⌉₊` is
exactly `{n : y < n < X/y}` (`mem_window_iff`).

**AMENDMENT S1-B (catch #256, maestro ruling 2026-07-20).**  The coefficient is the
GHS-faithful large-part von Mangoldt analog `lambdaLin (restrictAbove y g)` — the
`Λ_ℓ` whose derivative `ellLin_lseries_deriv` is exact at the LARGE datum `𝓛`.  The
naive `lambdaLin g` overcounts small-base powers `p^k` with `p ≤ y < p^k` that GHS
routes into the smooth part; those extras are NOT in `𝓛`'s derivative.  Exactness
requires the restricted form; the restricted coefficient has strictly smaller mass
(`‖lambdaLin (restrictAbove y g) n‖ ≤ Λ n` a fortiori), so every downstream bound
survives.  See `docs/exploration/halasz-infra-freeze.md` AMENDMENT S1-B. -/
def windowSum (g : ℕ → ℂ) (X y : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, lambdaLin (restrictAbove y g) n / (n : ℂ) ^ s

/-- The window index set is exactly `{n : y < n < X/y}` (for `0 ≤ y`). -/
lemma mem_window_iff {X y : ℝ} (hy : 0 ≤ y) (n : ℕ) :
    n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ ↔ y < (n : ℝ) ∧ (n : ℝ) < X / y := by
  rw [Finset.mem_Ioo, Nat.floor_lt hy, Nat.lt_ceil]

/-! ### Abscissa / summability of `𝒮` and `𝓛` -/

/-- `𝒮`'s coefficient series has abscissa of absolute convergence `≤ 1`. -/
lemma abscissa_smoothSeries_le_one {g : ℕ → ℂ} {y : ℝ}
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (ellLin (restrictBelow y g)) ≤ 1 :=
  abscissa_ellLin_le_one (restrictBelow y g) (restrictBelow_norm_le hg)

/-- `𝓛`'s coefficient series has abscissa of absolute convergence `≤ 1`. -/
lemma abscissa_largeSeries_le_one {g : ℕ → ℂ} {y : ℝ}
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (ellLin (restrictAbove y g)) ≤ 1 :=
  abscissa_ellLin_le_one (restrictAbove y g) (restrictAbove_norm_le hg)

/-- `𝒮` is `L`-summable on `1 < re s`. -/
lemma smoothSeries_summable {g : ℕ → ℂ} {y : ℝ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (ellLin (restrictBelow y g)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => ellLin_norm_le_one (restrictBelow y g) (restrictBelow_norm_le hg) n) hs

/-- `𝓛` is `L`-summable on `1 < re s`. -/
lemma largeSeries_summable {g : ℕ → ℂ} {y : ℝ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (ellLin (restrictAbove y g)) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => ellLin_norm_le_one (restrictAbove y g) (restrictAbove_norm_le hg) n) hs

/-! ### `P_β` is an entire finite Dirichlet polynomial (continuity of the window) -/

/-- The window polynomial is continuous in `s` (a finite sum of `n^{-s}`, `n ≥ 1`). -/
lemma continuous_windowSum (g : ℕ → ℂ) (X y : ℝ) : Continuous (windowSum g X y) := by
  refine continuous_finsetSum _ (fun n hn => ?_)
  rw [Finset.mem_Ioo] at hn
  have hn0 : n ≠ 0 := by have := hn.1; omega
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  have hne : ∀ s : ℂ, (n : ℂ) ^ s ≠ 0 := by
    intro s; rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨h0, _⟩
    exact (Nat.cast_ne_zero.mpr hn0) h0
  simp_rw [div_eq_mul_inv]
  exact continuous_const.mul ((continuous_const_cpow (n : ℂ)).inv₀ hne)

/-! ## T2 — the concrete dominating functions for the Fubini rungs

The three hypothesis-carrying rungs of `HalaszRep` (`interval_integral_tsum_swap`
[β↔n], `interval_integral_line_swap` [β↔t], `line_integral_tsum_swap` [t↔n]) each
carry an explicit domination hypothesis.  At the seam integrands these reduce to
two landed ingredients: the hat kernel's `1/‖s‖² ~ 1/t²` decay (`hat_mellin_bound`
+ the SW workhorse `integrable_inv_c_sq_add_sq`), giving the `t`-integral its `L¹`
dominating function; and the finiteness of the smooth series `𝒮` and window `P_β`
(finite Dirichlet polynomials, so bounded on the vertical line). -/

/-- The per-`t` hat kernel is continuous (a ratio of entire `cpow`s over a
nowhere-vanishing denominator `h·s·(s+1)`). -/
lemma continuous_hatKernel {X h c : ℝ} (hX : 0 < X) (hh : 0 < h) (hc : 0 < c) :
    Continuous (fun t : ℝ => hatKernel X h c t) := by
  have hXh : (0 : ℝ) < X + h := by linarith
  haveI : NeZero ((X + h : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hXh.ne'⟩
  haveI : NeZero ((X : ℝ) : ℂ) := ⟨Complex.ofReal_ne_zero.mpr hX.ne'⟩
  have hexp : Continuous (fun t : ℝ => ((c : ℂ) + (t : ℂ) * I) + 1) := by
    fun_prop
  have hnum : Continuous (fun t : ℝ =>
      ((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
        - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)) :=
    ((continuous_const_cpow _).comp hexp).sub ((continuous_const_cpow _).comp hexp)
  have hden : Continuous (fun t : ℝ =>
      (h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1))) := by
    fun_prop
  have hdenne : ∀ t : ℝ,
      (h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)) ≠ 0 :=
    fun t =>
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne')
      (mul_ne_zero (Salt.SW.s_ne_zero hc t) (Salt.SW.s1_ne_zero hc t))
  exact hnum.div hden hdenne

/-- **T2 core — the hat kernel is `L¹`** (the `1/t²` decay of the seam kernel).
`‖hatKernel X h c t‖ ≤ (X+h)^c·2(X+h)/(h·(c²+t²))` by the dominant branch of
`hat_mellin_bound`, and `∫ (c²+t²)⁻¹ < ∞` by `integrable_inv_c_sq_add_sq`; hence the
per-`t` hat kernel is integrable on the full line.  This is the concrete dominating
function underneath every `t`-integral in the S1' representation. -/
theorem integrable_hatKernel {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) :
    Integrable (fun t : ℝ => hatKernel X h c t) := by
  have hcont := continuous_hatKernel (by linarith : (0:ℝ) < X) hh hc
  set A : ℝ := (X + h) ^ c * (2 * (X + h) / h) with hA
  have hg : Integrable (fun t : ℝ => A * (c ^ 2 + t ^ 2)⁻¹) :=
    (Salt.SW.integrable_inv_c_sq_add_sq hc).const_mul A
  refine hg.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => ?_))
  have hnorm : ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hb := hat_mellin_bound hX hh hc t
  have hXhc : (0 : ℝ) ≤ (X + h) ^ c := Real.rpow_nonneg (by linarith) _
  calc ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * min (2 / ‖(c : ℂ) + (t : ℂ) * I‖)
          (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := hb
    _ ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := by
        gcongr; exact min_le_right _ _
    _ = A * (c ^ 2 + t ^ 2)⁻¹ := by
        rw [hnorm, hA]
        have hct : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
        field_simp

/-- **T2 — the line-integral domination.**  For any BOUNDED continuous coefficient
`D` (the seam's `𝒮·𝓛·P·P` restricted to the vertical line is such — `𝒮` and each
`P` are finite Dirichlet polynomials, `𝓛` converges on `re > 1`), the product
`D·hatKernel` is integrable on the full line: `‖D‖ ≤ M` and `hatKernel ∈ L¹`.  This
discharges the `t`-integral existence in the `β↔t` (`interval_integral_line_swap`)
and `t↔n` (`line_integral_tsum_swap`) rungs at the concrete seam integrand. -/
theorem integrable_bddCoeff_mul_hatKernel {D : ℝ → ℂ} (hD : Continuous D) {M : ℝ}
    (hDb : ∀ t, ‖D t‖ ≤ M) {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) :
    Integrable (fun t : ℝ => D t * hatKernel X h c t) :=
  (integrable_hatKernel hX hh hc).bdd_mul hD.aestronglyMeasurable
    (Filter.Eventually.of_forall hDb)

/-! ## T3 — the window algebra: gluing the FTC leg to the split objects

The FTC leg `shifted_dirichlet_ftc` produces the endpoint difference of
`LSeries (ellLin g)`; the split product law lifts it to the `𝒮·𝓛` product form
(GHS `F = 𝒮·𝓛`, p.7), which is the shape the S1' integrand consumes. -/

/-- On `1 < re z` the full L-series factors as the smooth × large product
(`F = 𝒮·𝓛`), by the split product law `ellLin_split` and `LSeries_convolution'`. -/
lemma lseries_ellLin_eq_smooth_mul_large (y : ℝ) (g : ℕ → ℂ)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {z : ℂ} (hz : 1 < z.re) :
    LSeries (ellLin g) z = smoothSeries y g z * largeSeries y g z := by
  simp only [smoothSeries, largeSeries]
  conv_lhs => rw [← ellLin_split y g]
  exact LSeries_convolution' (smoothSeries_summable hg hz) (largeSeries_summable hg hz)

/-- **T3 window glue — the split-form FTC.**  Along the vertical segment `[0,η]`
the product-form log-derivative integrates to the `𝒮·𝓛` endpoint difference:
`∫₀^η L(λ_lin g)(w+β)·(𝒮·𝓛)(w+β) dβ = (𝒮·𝓛)(w) - (𝒮·𝓛)(w+η)`.
This is `shifted_dirichlet_ftc` (GHS Lemma 2.1's `∫₀^η F'(w+β)dβ = F(w)-F(w+η)`)
lifted through the split product law — the exact shape the S1' `α,β` integrand
consumes (`F = 𝒮·𝓛`). -/
theorem shifted_dirichlet_ftc_split (y : ℝ) (g : ℕ → ℂ)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {w : ℂ} (hw : 1 < w.re) {η : ℝ}
    (hη : 0 ≤ η) :
    ∫ β in (0 : ℝ)..η, LSeries (lambdaLin g) (w + (β : ℂ))
        * (smoothSeries y g (w + (β : ℂ)) * largeSeries y g (w + (β : ℂ)))
      = smoothSeries y g w * largeSeries y g w
        - smoothSeries y g (w + (η : ℂ)) * largeSeries y g (w + (η : ℂ)) := by
  have hwη : 1 < (w + (η : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have key := shifted_dirichlet_ftc g hg hw hη
  have hint : ∀ β ∈ Set.uIcc (0 : ℝ) η,
      LSeries (lambdaLin g) (w + (β : ℂ)) * LSeries (ellLin g) (w + (β : ℂ))
      = LSeries (lambdaLin g) (w + (β : ℂ))
        * (smoothSeries y g (w + (β : ℂ)) * largeSeries y g (w + (β : ℂ))) := by
    intro β hβ
    have hβ0 : 0 ≤ β := by
      rcases Set.mem_uIcc.mp hβ with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    have hre : 1 < (w + (β : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith
    rw [lseries_ellLin_eq_smooth_mul_large y g hg hre]
  rw [intervalIntegral.integral_congr hint,
    lseries_ellLin_eq_smooth_mul_large y g hg hw,
    lseries_ellLin_eq_smooth_mul_large y g hg hwη] at key
  exact key

/-! ## T2 — the `‖aₙ‖(X/n)^c` summability shape (the `hat_contour_rep` gate)

`hat_contour_rep` (the LHS→contour leg of S1') is gated on the summability of the
weighted coefficient sum `∑ ‖aₙ‖((X+h)/n)^c`.  For a 1-bounded coefficient
(`‖aₙ‖ ≤ 1`, which the seam's `seamCoeff`/`fgJ` satisfies) and any `c > 1` (the
seam's `c₀ = 1+1/log X > 1`) this is a convergent `p`-series, discharged concretely
here.  This is the "`‖aₙ‖(X/n)^c` summability shape" of the resistance map. -/

/-- **T2 — the weighted-coefficient summability** for a 1-bounded coefficient at
`c > 1`: `∑ ‖aₙ‖((X+h)/n)^c` converges, dominated by the `p`-series
`(X+h)^c·∑ n^{-c}`.  Discharges the `hat_contour_rep` summability hypothesis. -/
theorem summable_bounded_weight {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {X h c : ℝ}
    (hXh : 0 < X + h) (hc : 1 < c) :
    Summable (fun n => ‖a n‖ * ((X + h) / (n : ℝ)) ^ c) := by
  have hcne : c ≠ 0 := by linarith
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((Real.summable_nat_rpow.mpr (by linarith : -c < -1)).mul_left ((X + h) ^ c))
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, div_zero, Real.zero_rpow hcne, mul_zero]
    positivity
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hrw : ((X + h) / (n : ℝ)) ^ c = (X + h) ^ c * (n : ℝ) ^ (-c) := by
      rw [Real.div_rpow (by linarith) (le_of_lt hn0), Real.rpow_neg (le_of_lt hn0),
        div_eq_mul_inv]
    rw [hrw]
    exact mul_le_of_le_one_left (by positivity) (ha n)

/-! ## T3 — the S1' representation assembly

The frozen S1' statement (`Salt/MR/HalaszSeam.lean` docstring) equates the twisted,
windowed, hat-smoothed sum `∑' n, f·g_J·n^{-it₀}·hatK` with the `α,β` double integral
of the four-series product `𝒮·𝓛·P·P` against `hatKernel`, up to the desmooth error
(`O((h+1)·2^J)`) and the secondary error (`O(X/log X·(log y)^κ)`).

Two legs are DISCHARGED concretely below; the third is named.

* **LHS → contour** (`prop21_contour_leg`, FULLY DISCHARGED): the hat-smoothed sum
  equals `(1/2π)·∫_t 𝒟(c+it)·hatKernel`, where `𝒟` is the seam Dirichlet series.
  A direct instance of `hat_contour_rep` with the summability gate discharged by
  `summable_bounded_weight` and `a 0 = 0` by `seamCoeff_zero`.
* **desmooth** (`prop21_desmooth_reduction`, LANDED in `HalaszSeam`): the sharp
  partial sum and the hat-smoothed sum differ by `≤ h+1`.
* **the inner `α,β` factorization** — the RESIDUAL: `𝒟(c+it)` re-expressed as the
  `(α,β)`-double integral of `𝒮(s-α-β)𝓛(s+β)P(s-β)P(s+β)` (GHS Lemma 2.1/2.2 →
  Prop 2.1, the multivariable-Perron coefficient identity + the Shiu/Lemma-2.4
  secondary term).  This is the multi-thousand-line multivariable core with no
  mathlib apparatus; it is carried as the explicit hypothesis `hfactor`. -/

/-- The **seam Dirichlet series** `𝒟(s) = ∑' n, f·g_J·n^{-it₀}/n^s` (the coefficient
side integrated by `hat_contour_rep`). -/
def seamDirichlet (f gJ : ℕ → ℂ) (t₀ : ℝ) (s : ℂ) : ℂ :=
  ∑' n, seamCoeff f gJ t₀ n / (n : ℂ) ^ s

/-- **T3 — the LHS→contour leg of S1'** (FULLY DISCHARGED, residual-free).  The
twisted-windowed hat-smoothed sum equals the exact full-line contour integral of the
seam Dirichlet series against the hat kernel.  A direct instance of `hat_contour_rep`
(the summability gate discharged by `summable_bounded_weight`, `a 0 = 0` by
`seamCoeff_zero`).  This is the concrete half of the S1' representation. -/
theorem prop21_contour_leg {f gJ : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hgJ : ∀ n, ‖gJ n‖ ≤ 1)
    (t₀ : ℝ) {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 1 < c) :
    ∑' n, seamCoeff f gJ t₀ n * (hatK X h n : ℂ)
      = (1 / (2 * Real.pi)) •
          ∫ t : ℝ, seamDirichlet f gJ t₀ ((c : ℂ) + (t : ℂ) * I) * hatKernel X h c t := by
  have hsum := summable_bounded_weight (norm_seamCoeff_le hf hgJ t₀)
    (by linarith : (0 : ℝ) < X + h) hc
  have hrep := hat_contour_rep (seamCoeff f gJ t₀) (seamCoeff_zero f gJ t₀) hX hh
    (by linarith : (0 : ℝ) < c) hsum
  rw [hrep]
  simp only [seamDirichlet, hatKernel]

/-- The **frozen S1' main integral** — the `α,β` double integral of the four-series
product `𝒮(s-α-β)·𝓛(s+β)·P(s-β)·P(s+β)` against the centered hat kernel, with
`s = c₀ + (t-t₀)·I` on the exact vertical line (Seam docstring, GHS Prop 2.1).

**AMENDMENT P21-2X (2026-07-22, maestro-ruled from HID-ALPHA's confirmed
factor-2 verdict):** the leading factor `2` is the β→2β Jacobian of GHS's
Prop 2.1 proof (p.11 "finally replace β by 2β": `∫₀^{2η} G(β/2) dβ =
2·∫₀^η G(β′) dβ′`, the Lean witness `beta_double_jacobian` in
`HalaszIdentity`). GHS's *printed* (2.1) omits the 2 — harmless for their
one-sided `≪`, fatal for the two-sided `hfactor` identity: without it,
`prop21RHS ≈ ½·(Σf(n) − secondary)` and the defect is main-term-sized.
The original transcription was faithful to the printed display; the
amendment restores fidelity to the *derivation*. -/
def prop21RHS (g : ℕ → ℂ) (t₀ X h c₀ y η : ℝ) : ℂ :=
  (2 : ℝ) • ∫ α in (0 : ℝ)..η, ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi)) •
    ∫ t : ℝ,
      smoothSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y g (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
        * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))
        * windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))
        * hatKernel X h c₀ (t - t₀)

/-- **T3 CAPSTONE — the S1' representation** (`prop21_analog`, the campaign's last
named residual, in the sanctioned conditional-assembly form).  For a 1-bounded `f`,
its prime datum `g` (`‖g p‖ ≤ 1`), the GHS window `g_J = windowIndicator y (X/y)`,
and the seam parameters (`c₀ > 1`), the twisted–windowed hat-smoothed sum equals the
frozen `α,β` double integral `prop21RHS` up to the error `E`.

The LHS→contour leg is DISCHARGED (`prop21_contour_leg`); the sole hypothesis
`hfactor` is the genuine residual — the inner factorization of the seam Dirichlet
series into the four-series product integrated over `(α,β)` against the CENTERED
kernel, up to `E` (GHS Lemma 2.1/2.2 → Prop 2.1: the multivariable-Perron
coefficient identity, the `n^{-it₀}` centering change-of-variables, and the
Shiu/Lemma-2.4 secondary term `O(X/log X·(log y)^κ)` plus the desmooth
`O((h+1)·2^J)` — the multi-thousand-line core with no mathlib apparatus).  This is
the SAME conditional landing form as `contour_A13_A14_head`/`halasz_ball_decay`.

DEVIATIONS RECORDED (iron rule 1): (1) `restrictBelow = p ≤ y` (module docstring);
(2) RESOLVED by AMENDMENT S1-B (catch #256, T0 of the hfactor campaign): the window
`P_β` now uses the GHS-faithful large-part coefficient `lambdaLin (restrictAbove y g)`
(see `windowSum`'s docstring) — exactness at `𝓛`'s derivative, restricted-form mass
`≤ Λ` a fortiori so all downstream bounds survive. -/
theorem prop21_analog {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (t₀ : ℝ) {X h c₀ y η E : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc₀ : 1 < c₀)
    (hfactor :
      ‖(1 / (2 * Real.pi)) • (∫ t : ℝ,
          seamDirichlet f (windowIndicator y (X / y)) t₀ ((c₀ : ℂ) + (t : ℂ) * I)
            * hatKernel X h c₀ t)
        - prop21RHS g t₀ X h c₀ y η‖ ≤ E) :
    ‖(∑' n, seamCoeff f (windowIndicator y (X / y)) t₀ n * (hatK X h n : ℂ))
        - prop21RHS g t₀ X h c₀ y η‖ ≤ E := by
  rw [prop21_contour_leg hf (norm_windowIndicator_le y (X / y)) t₀ hX hh hc₀]
  exact hfactor

end Salt.MR
