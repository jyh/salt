/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.Kernel
import Salt.SW.ContourShift

/-!
# HALASZ-INFRA wave I-1, FILE A — the hat-kernel Perron infrastructure

The reusable analytic core of the minimal-seam Halász route
(`docs/exploration/halasz-infra-freeze.md`, FILE A, rungs K1'–K4').  We replace
the sharp truncated Perron step by an *exact* representation against a trapezoid
("hat") kernel `hatK X h`, built from two instances of the landed smoothed
Mellin identity `Salt.SW.kernel_identity` (`Salt/SW/Kernel.lean`).

`s` abbreviates `(c : ℂ) + (t : ℂ) * I` throughout (matching the `SW.Kernel`
convention so the landed identities unify).

## Rungs

* `hatK` (K1') — the trapezoid kernel `(max (X+h-n) 0 − max (X-n) 0)/h`, an
  exact indicator of `[1, X]` off the ramp `(X, X+h]`.
* `hat_desmooth` (K1') — the desmoothing bound `‖∑_{1≤n≤⌊X⌋} aₙ − ∑ₙ aₙ hatK‖ ≤ h+1`.
* `hat_contour_rep` (K2') — the EXACT full-line vertical representation of
  `∑ₙ aₙ hatK X h n` (no truncation), via two `kernel_identity` instances.
* `hat_mellin_bound` / `hat_tail` (K3') — the kernel modulus bound and its tail,
  with the `Tsplit := (log X)^4` split ledger.
* K4' (`cos_int_pair` / `dirichlet_plancherel`) — the Poisson-kernel cosine
  integral and the Dirichlet Plancherel bilinear form — is the NAMED RESIDUAL of
  this wave (HAL-I1a NOTES): `cos_int_pair` (`∫ cos(θt)/(c²+t²) = (π/c)e^{-c|θ|}`)
  is mathlib-absent and requires the full contour/arc-limit apparatus (rectangle
  CIF `SW.ContourShift.rectBI_cif_eq` + pole at `t = ci` + edge bounds + `R→∞`);
  `dirichlet_plancherel` is its Finset-bilinear consumer (norm-sq expansion +
  finite Fubini + per-pair `Re`-linear split via `cos_int_pair` and sin-oddness).
  Both are deferred, not built here; see the wave report.
-/

open MeasureTheory Complex Set
open scoped BigOperators

noncomputable section
namespace Salt.MR

/-! ## K1' — the hat (trapezoid) kernel -/

/-- **The hat / trapezoid kernel** (K1').  `hatK X h n` smooths the sharp
indicator of the interval `[1, X]`: it equals `1` for `n ≤ X`, ramps down
linearly on `(X, X+h]`, and vanishes for `n > X+h`. -/
noncomputable def hatK (X h : ℝ) (n : ℕ) : ℝ :=
  (max (X + h - n) 0 - max (X - n) 0) / h

/-! ### Pointwise facts about `hatK`. -/

/-- `hatK` is nonnegative (the numerator is a difference of `max`'s in the right order). -/
lemma hatK_nonneg {X h : ℝ} (hh : 0 < h) (n : ℕ) : 0 ≤ hatK X h n := by
  refine div_nonneg ?_ hh.le
  have : max (X - n) 0 ≤ max (X + h - n) 0 := by apply max_le_max _ le_rfl; linarith
  linarith

/-- `hatK ≤ 1` (the numerator is at most `h`). -/
lemma hatK_le_one {X h : ℝ} (hh : 0 < h) (n : ℕ) : hatK X h n ≤ 1 := by
  rw [hatK, div_le_one hh]
  by_cases hc : X - (n : ℝ) ≤ 0
  · rw [max_eq_right hc]
    by_cases hd : X + h - (n : ℝ) ≤ 0
    · rw [max_eq_right hd]; linarith
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ X + h - n)]; linarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ X - n),
        max_eq_left (by linarith : (0 : ℝ) ≤ X + h - n)]; linarith

/-- On `[0, X]` the hat kernel is exactly `1` (`n ≤ X`). -/
lemma hatK_eq_one {X h : ℝ} (hh : 0 < h) {n : ℕ} (hn : (n : ℝ) ≤ X) : hatK X h n = 1 := by
  rw [hatK, max_eq_left (by linarith : (0 : ℝ) ≤ X + h - n),
    max_eq_left (by linarith : (0 : ℝ) ≤ X - n),
    show X + h - (n : ℝ) - (X - n) = h by ring, div_self hh.ne']

/-- Past the ramp the hat kernel vanishes (`X + h < n`). -/
lemma hatK_eq_zero {X h : ℝ} (hh : 0 < h) {n : ℕ} (hn : X + h < n) : hatK X h n = 0 := by
  rw [hatK, max_eq_right (by linarith : X + h - (n : ℝ) ≤ 0),
    max_eq_right (by linarith : X - (n : ℝ) ≤ 0)]; simp

/-! ### K1' — the desmoothing bound `hat_desmooth`.

CATCH (HAL-I1a, house ratification requested): the frozen statement in
`halasz-infra-freeze.md` line 13 omits the hypothesis `a 0 = 0` and is FALSE as
literally written — e.g. `X = 1.9, h = 0.5, a 0 = a 2 = 1` gives error `1.8 >
h + 1 = 1.5`.  The freeze's own COVER/DEGEN section (line 35) lists "n = 0 (ha0)"
and the downstream consumer K2' (`hat_contour_rep`) carries `ha0` explicitly, so
`ha0` is restored here. -/

/-- **The desmoothing bound** (K1').  Replacing the sharp partial sum
`∑_{1 ≤ n ≤ ⌊X⌋} aₙ` by the hat-smoothed sum `∑ₙ aₙ · hatK X h n` costs at most
`h + 1`: the difference is exactly the ramp contribution `∑_{X < n ≤ X+h}`, whose
`⌊X+h⌋ − ⌊X⌋ ≤ h + 1` terms each have modulus `≤ 1`.  (Requires `a 0 = 0`; see
the CATCH above.) -/
theorem hat_desmooth (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (ha0 : a 0 = 0)
    {X h : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hhX : h ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, a n) - ∑' n, a n * (hatK X h n : ℂ)‖ ≤ h + 1 := by
  have _ := hhX  -- `h ≤ X` is a frozen hypothesis; the bound holds without it
  set M := ⌊X⌋₊ with hM
  set N := ⌊X + h⌋₊ with hN
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hXh0 : (0 : ℝ) ≤ X + h := by linarith
  have hMN : M ≤ N := Nat.floor_mono (by linarith)
  -- the tsum collapses to a finite sum over `range (N+1)`
  have htsum : ∑' n, a n * (hatK X h n : ℂ)
      = ∑ n ∈ Finset.range (N + 1), a n * (hatK X h n : ℂ) := by
    apply tsum_eq_sum
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hgt : X + h < n := by
      have h1 := Nat.lt_floor_add_one (X + h)
      have hle : (N : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    rw [hatK_eq_zero hh hgt]; simp
  -- the sharp sum equals `∑_{Icc 1 M} aₙ · hatK` (kernel is `1` there)
  have hS : (∑ n ∈ Finset.Icc 1 M, a n)
      = ∑ n ∈ Finset.Icc 1 M, a n * (hatK X h n : ℂ) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    have hnX : (n : ℝ) ≤ X := by
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn.2
      have hMX : (M : ℝ) ≤ X := Nat.floor_le hX0
      linarith
    rw [hatK_eq_one hh hnX, Complex.ofReal_one, mul_one]
  have hsub : Finset.Icc 1 M ⊆ Finset.range (N + 1) := by
    intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_range]; omega
  rw [hS, htsum]
  -- the difference is (minus) the sum over the complement `D := range(N+1) \ Icc 1 M`
  have hdiff : (∑ n ∈ Finset.Icc 1 M, a n * (hatK X h n : ℂ))
        - (∑ n ∈ Finset.range (N + 1), a n * (hatK X h n : ℂ))
      = -(∑ n ∈ Finset.range (N + 1) \ Finset.Icc 1 M, a n * (hatK X h n : ℂ)) := by
    rw [Finset.sum_sdiff_eq_sub hsub]; ring
  rw [hdiff, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  -- `0 ∈ D`; its term vanishes by `ha0`, the rest are each `≤ 1`
  have h0D : (0 : ℕ) ∈ Finset.range (N + 1) \ Finset.Icc 1 M := by
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]; omega
  rw [← Finset.insert_erase h0D, Finset.sum_insert (by simp),
    ha0, zero_mul, norm_zero, zero_add]
  refine (Finset.sum_le_card_nsmul _ _ 1 (fun n _ => ?_)).trans ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hatK_nonneg hh n)]
    exact (mul_le_mul (ha n) (hatK_le_one hh n) (hatK_nonneg hh n) (by norm_num)).trans_eq
      (by ring)
  · rw [nsmul_eq_mul, mul_one]
    have hcardD : (Finset.range (N + 1) \ Finset.Icc 1 M).card = N + 1 - M := by
      rw [Finset.card_sdiff, Finset.card_range, Finset.inter_eq_left.mpr hsub, Nat.card_Icc]
      omega
    have hcarderase : ((Finset.range (N + 1) \ Finset.Icc 1 M).erase 0).card = N - M := by
      rw [Finset.card_erase_of_mem h0D, hcardD]; omega
    rw [hcarderase, Nat.cast_sub hMN]
    have hNle : (N : ℝ) ≤ X + h := Nat.floor_le hXh0
    have hMgt : X - 1 < (M : ℝ) := by have h1 := Nat.lt_floor_add_one X; linarith
    linarith

/-! ## K2' — the exact vertical (contour) representation `hat_contour_rep`.

Two cpow helpers first. -/

/-- `((x/n)^s = x^s / n^s)` for a real `x ≥ 0` and `n ≥ 1` (positive real bases,
so no branch subtlety). -/
lemma ofReal_div_cpow {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    ((x / (n : ℝ) : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (n : ℂ) ^ s := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have harg : (((n : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hnn]; exact Real.pi_pos.ne
  rw [show (x / (n : ℝ) : ℝ) = x * (n : ℝ)⁻¹ by rw [div_eq_mul_inv], Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hx (by positivity), Complex.ofReal_inv,
    Complex.inv_cpow _ _ harg, Complex.ofReal_natCast, div_eq_mul_inv]

/-- The value of `kernel_identity` at `y = x/n`, scaled by `x`, is exactly `max (x-n) 0`:
`x·(1 - n/x)₊ = (x-n)₊`.  (For `n ≥ 1`, so `x/n` is a genuine positive real.) -/
lemma kival_max {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    (x : ℂ) * (if 1 ≤ x / (n : ℝ) then (1 - 1 / ((x / (n : ℝ) : ℝ) : ℂ)) else 0)
      = ((max (x - n) 0 : ℝ) : ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hnC : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn0.ne'
  split_ifs with hcond
  · have hxn : (n : ℝ) ≤ x := by rwa [le_div_iff₀ hn0, one_mul] at hcond
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ x - n), Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_natCast]
    field_simp
  · rw [not_le, div_lt_one hn0] at hcond
    rw [max_eq_right (by linarith : x - (n : ℝ) ≤ 0)]; simp

/-- Closed form for the integral of the norm of a single kernel term. -/
private lemma kterm_norm_integral (w : ℂ) {b : ℝ} (hb : 0 ≤ b) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ, ‖w * (b : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))‖
      = (‖w‖ * b ^ c) * ∫ t : ℝ,
          ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [norm_div, norm_mul, Salt.SW.norm_ofReal_cpow_vert hb hc, norm_inv]; ring

theorem hat_contour_rep (a : ℕ → ℂ) (ha0 : a 0 = 0) {X h c : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c)
    (hsum : Summable fun n => ‖a n‖ * ((X + h) / n) ^ c) :
    ∑' n, a n * (hatK X h n : ℂ)
      = (1 / (2 * Real.pi)) •
          ∫ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
            * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
                - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
              / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)))) := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hXh : (0 : ℝ) < X + h := by linarith
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  -- second real summability (base X ≤ X+h)
  have hsum2 : Summable (fun n => ‖a n‖ * (X / (n : ℝ)) ^ c) := by
    refine hsum.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    apply Real.rpow_le_rpow (by positivity) _ hc.le
    gcongr; linarith
  -- the shared denominator-norm integral (a finite nonnegative constant)
  set Cden : ℝ := ∫ t : ℝ, ‖(((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))⁻¹‖
    with hCden
  -- per-n integrals (a included)
  set M1 : ℕ → ℂ := fun n => ∫ t : ℝ, a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) with hM1
  set M2 : ℕ → ℂ := fun n => ∫ t : ℝ, a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
      / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) with hM2
  -- summability of the per-n integrals
  have hM1sum : Summable M1 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hsum.mul_right Cden))
    rw [hM1]
    exact (norm_integral_le_integral_norm _).trans_eq (kterm_norm_integral (a n) (by positivity) hc)
  have hM2sum : Summable M2 := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hsum2.mul_right Cden))
    rw [hM2]
    exact (norm_integral_le_integral_norm _).trans_eq (kterm_norm_integral (a n) (by positivity) hc)
  -- the frozen per-n summand `W n`
  set W : ℕ → ℝ → ℂ := fun n t => a n
      * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
          - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)))
        / (((n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) * (h : ℂ)
            * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1))) with hW
  set rc : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) with hrc
  -- Part A per-n bridges via `kernel_identity`.
  have hM1n : ∀ n : ℕ, 1 ≤ n → a n * ((max (X + h - (n : ℝ)) 0 : ℝ) : ℂ)
      = ((X + h : ℝ) : ℂ) * (rc * M1 n) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hy : (0 : ℝ) < (X + h) / (n : ℝ) := by positivity
    have hki := Salt.SW.kernel_identity hy hc
    rw [Complex.real_smul, ← hrc] at hki
    have hMJ : M1 n = a n * ∫ t : ℝ, (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
      rw [hM1, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun t => by dsimp only; rw [mul_div_assoc]))
    rw [hMJ, ← kival_max (show (0 : ℝ) < X + h by linarith) hn, ← hki]; ring
  have hM2n : ∀ n : ℕ, 1 ≤ n → a n * ((max (X - (n : ℝ)) 0 : ℝ) : ℂ)
      = ((X : ℝ) : ℂ) * (rc * M2 n) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hy : (0 : ℝ) < X / (n : ℝ) := by positivity
    have hki := Salt.SW.kernel_identity hy hc
    rw [Complex.real_smul, ← hrc] at hki
    have hMJ : M2 n = a n * ∫ t : ℝ, ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)) := by
      rw [hM2, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun t => by dsimp only; rw [mul_div_assoc]))
    rw [hMJ, ← kival_max hXpos hn, ← hki]; ring
  -- Part A: the LHS equals the common value.
  have key : ∑' n, a n * (hatK X h n : ℂ)
      = (h : ℂ)⁻¹ * (((X + h : ℝ) : ℂ) * (rc * ∑' n, M1 n)
          - ((X : ℝ) : ℂ) * (rc * ∑' n, M2 n)) := by
    have hAn : ∀ n, a n * (hatK X h n : ℂ)
        = (h : ℂ)⁻¹ * (((X + h : ℝ) : ℂ) * (rc * M1 n) - ((X : ℝ) : ℂ) * (rc * M2 n)) := by
      intro n
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        have hM10 : M1 0 = 0 := by
          rw [hM1]; simp only [ha0, zero_mul, zero_div]; exact integral_zero _ _
        have hM20 : M2 0 = 0 := by
          rw [hM2]; simp only [ha0, zero_mul, zero_div]; exact integral_zero _ _
        rw [ha0, hM10, hM20]; simp
      · rw [hatK, Complex.ofReal_div, Complex.ofReal_sub, ← mul_div_assoc, mul_sub,
          hM1n n hpos, hM2n n hpos, div_eq_inv_mul]
    rw [tsum_congr hAn, tsum_mul_left,
      Summable.tsum_sub ((hM1sum.mul_left _).mul_left _) ((hM2sum.mul_left _).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  -- Part B: the frozen summand `W n` and the integral swap.
  set c1 : ℂ := ((X + h : ℝ) : ℂ) / (h : ℂ) with hc1
  set c2 : ℂ := ((X : ℝ) : ℂ) / (h : ℂ) with hc2
  have hWeq : ∀ n, W n = fun (t : ℝ) =>
      c1 * (a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))
      - c2 * (a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
        / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
    intro n; funext t; rw [hW]; dsimp only
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ha0]
    · have hns : ((n : ℂ)) ^ ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
        rw [Ne, Complex.cpow_eq_zero_iff]; rintro ⟨hc0, _⟩
        exact (Nat.cast_ne_zero.mpr (by omega)) hc0
      have hs0 := Salt.SW.s_ne_zero hc t
      have hs1 := Salt.SW.s1_ne_zero hc t
      rw [hc1, hc2, ofReal_div_cpow (by linarith) hpos ((c : ℂ) + (t : ℂ) * I),
        ofReal_div_cpow (by linarith) hpos ((c : ℂ) + (t : ℂ) * I),
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hXh.ne'),
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hXpos.ne'),
        Complex.cpow_one, Complex.cpow_one]
      field_simp
  have hWint : ∀ n, Integrable (W n) := by
    intro n; rw [hWeq n]
    exact ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1).sub
      ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2)
  have hI1 : ∀ n, (∫ t : ℝ, ‖c1 * (a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖)
      = ‖c1‖ * (‖a n‖ * ((X + h) / (n : ℝ)) ^ c * Cden) := by
    intro n; simp_rw [norm_mul]
    rw [integral_const_mul, kterm_norm_integral (a n) (b := (X + h) / (n : ℝ)) (by positivity) hc]
  have hI2 : ∀ n, (∫ t : ℝ, ‖c2 * (a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
          / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖)
      = ‖c2‖ * (‖a n‖ * (X / (n : ℝ)) ^ c * Cden) := by
    intro n; simp_rw [norm_mul]
    rw [integral_const_mul, kterm_norm_integral (a n) (b := X / (n : ℝ)) (by positivity) hc]
  have hWsum : Summable (fun n => ∫ t : ℝ, ‖W n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_)
      (((hsum.mul_right Cden).mul_left ‖c1‖).add ((hsum2.mul_right Cden).mul_left ‖c2‖))
    calc (∫ t, ‖W n t‖)
        ≤ ∫ (t : ℝ), (‖c1 * (a n * (((X + h) / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
            / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖
          + ‖c2 * (a n * ((X / (n : ℝ) : ℝ) : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)
            / (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1)))‖) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            ((((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1).norm).add
              (((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2).norm))
            (Filter.Eventually.of_forall fun t => ?_)
          rw [hWeq n]; exact norm_sub_le _ _
      _ = ‖c1‖ * (‖a n‖ * ((X + h) / (n : ℝ)) ^ c * Cden)
            + ‖c2‖ * (‖a n‖ * (X / (n : ℝ)) ^ c * Cden) := by
          rw [integral_add (((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1).norm)
            (((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2).norm), hI1, hI2]
  have hWval : ∀ n, (∫ t, W n t)
      = (h : ℂ)⁻¹ * (((X + h : ℝ) : ℂ) * M1 n - ((X : ℝ) : ℂ) * M2 n) := by
    intro n
    rw [hWeq n, integral_sub ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c1)
      ((Salt.SW.integrable_Fterm (a n) (by positivity) hc).const_mul c2),
      integral_const_mul, integral_const_mul]
    simp only [hM1, hM2]
    rw [hc1, hc2]; ring
  have hSGsum : ∀ t : ℝ, (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
            - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
          / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1))))
      = ∑' n, W n t := by
    intro t; rw [← tsum_mul_right]; refine tsum_congr (fun n => ?_)
    rw [hW]; dsimp only; rw [div_mul_div_comm]; ring
  rw [key]
  rw [Complex.real_smul, ← hrc,
    show (fun t : ℝ => (∑' n, a n / (n : ℂ) ^ ((c : ℂ) + (t : ℂ) * I))
        * ((((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
            - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
          / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)))))
      = (fun t => ∑' n, W n t) from funext hSGsum,
    (integral_tsum_of_summable_integral_norm hWint hWsum).symm,
    tsum_congr hWval, tsum_mul_left,
    Summable.tsum_sub (hM1sum.mul_left _) (hM2sum.mul_left _), tsum_mul_left, tsum_mul_left]
  ring

/-- The per-`t` kernel factor of the contour representation (`K3'`). -/
def hatKernel (X h c t : ℝ) : ℂ :=
  (((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
      - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1))
    / ((h : ℂ) * (((c : ℂ) + (t : ℂ) * I) * (((c : ℂ) + (t : ℂ) * I) + 1)))


-- segment (MVT) bound on the numerator
lemma cpow_seg_bound {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖((X + h : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)
        - ((X : ℝ) : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) + 1)‖
      ≤ ‖((c : ℂ) + (t : ℂ) * I) + 1‖ * (X + h) ^ c * h := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hr : s + 1 ≠ 0 := by
    rw [hs]; intro he
    have := congrArg Complex.re he; simp at this; linarith
  have hderiv : ∀ u ∈ Icc X (X + h),
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ (s + 1)) ((s + 1) * (u : ℂ) ^ s)
        (Icc X (X + h)) u := by
    intro u hu
    have hu0 : u ≠ 0 := by rw [mem_Icc] at hu; nlinarith [hu.1]
    have h1 := (hasDerivAt_ofReal_cpow_const hu0 hr).hasDerivWithinAt (s := Icc X (X + h))
    have hpow : (s + 1) * (u : ℂ) ^ (s + 1 - 1) = (s + 1) * (u : ℂ) ^ s := by ring_nf
    rwa [hpow] at h1
  have hbound : ∀ u ∈ Icc X (X + h), ‖(s + 1) * (u : ℂ) ^ s‖ ≤ ‖s + 1‖ * (X + h) ^ c := by
    intro u hu
    rw [mem_Icc] at hu
    have hu0 : 0 < u := by linarith [hu.1]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : s.re = c := by rw [hs]; simp
    rw [hre]
    gcongr
    exact hu.2
  have hmvt := (convex_Icc X (X + h)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  calc ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖
      ≤ ‖s + 1‖ * (X + h) ^ c * ‖(X + h) - X‖ := hmvt
    _ = ‖s + 1‖ * (X + h) ^ c * h := by rw [show (X + h) - X = h by ring, Real.norm_of_nonneg hh.le]

theorem hat_mellin_bound {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * min (2 / ‖(c : ℂ) + (t : ℂ) * I‖)
          (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := by
  set s : ℂ := (c : ℂ) + (t : ℂ) * I with hs
  have hXh : (0 : ℝ) < X + h := by linarith
  have hsn : (0 : ℝ) < ‖s‖ := norm_pos_iff.mpr (by rw [hs]; exact Salt.SW.s_ne_zero hc t)
  have hs1n : (0 : ℝ) < ‖s + 1‖ := norm_pos_iff.mpr (by rw [hs]; exact Salt.SW.s1_ne_zero hc t)
  have hss1 : ‖s‖ ≤ ‖s + 1‖ := by
    rw [hs, Complex.norm_add_mul_I,
      show (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I by push_cast; ring,
      Complex.norm_add_mul_I]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hseg := cpow_seg_bound hX hh hc t
  rw [← hs] at hseg
  have htri : ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ ≤ 2 * (X + h) ^ (c + 1) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXh,
      Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < X),
      show (s + 1).re = c + 1 by rw [hs]; simp]
    have : X ^ (c + 1) ≤ (X + h) ^ (c + 1) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    linarith
  have hHK : ‖hatKernel X h c t‖
      = ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ / (h * ‖s‖ * ‖s + 1‖) := by
    rw [hatKernel, ← hs, norm_div, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hh.le]; ring_nf
  rw [hHK]
  have hbranch1 : ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ / (h * ‖s‖ * ‖s + 1‖)
      ≤ (X + h) ^ c * (2 / ‖s‖) := by
    rw [div_le_iff₀ (by positivity)]
    refine hseg.trans ?_
    rw [show (X + h) ^ c * (2 / ‖s‖) * (h * ‖s‖ * ‖s + 1‖) = 2 * (‖s + 1‖ * (X + h) ^ c * h) by
      field_simp]
    have hp : (0 : ℝ) ≤ ‖s + 1‖ * (X + h) ^ c * h := by positivity
    linarith
  have hbranch2 : ‖((X + h : ℝ) : ℂ) ^ (s + 1) - ((X : ℝ) : ℂ) ^ (s + 1)‖ / (h * ‖s‖ * ‖s + 1‖)
      ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖s‖ ^ 2)) := by
    rw [div_le_iff₀ (by positivity)]
    refine htri.trans ?_
    rw [show (X + h) ^ c * (2 * (X + h) / (h * ‖s‖ ^ 2)) * (h * ‖s‖ * ‖s + 1‖)
      = 2 * ((X + h) ^ c * (X + h)) * (‖s + 1‖ / ‖s‖) by field_simp,
      show (X + h) ^ (c + 1) = (X + h) ^ c * (X + h) by rw [Real.rpow_add hXh, Real.rpow_one]]
    have hratio : 1 ≤ ‖s + 1‖ / ‖s‖ := by rw [le_div_iff₀ hsn]; linarith
    have hp : (0 : ℝ) ≤ 2 * ((X + h) ^ c * (X + h)) := by positivity
    nlinarith [hratio, hp]
  exact (le_min hbranch1 hbranch2).trans_eq (mul_min_of_nonneg _ _ (by positivity)).symm

/-- **The branch-2 tail bound** (`hat_tail`).  Beyond height `T`, the (dominant,
`1/‖s‖²`-decaying) branch of the kernel has one-sided tail mass `≤ 2(X+h)^{c+1}/(hT)`;
by evenness the full `|t| ≥ T` mass is `≤ 4(X+h)^{c+1}/(hT)`. -/
theorem hat_tail {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    ∫ t in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2))
      ≤ 2 * (X + h) ^ (c + 1) / (h * T) := by
  have hAnn : (0 : ℝ) ≤ 2 * (X + h) ^ (c + 1) / h := by positivity
  have hInt1 : IntegrableOn (fun t : ℝ => (c ^ 2 + t ^ 2)⁻¹) (Set.Ioi T) :=
    (Salt.SW.integrable_inv_c_sq_add_sq hc).integrableOn
  have hInt2 : IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ)) (Set.Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  calc ∫ t in Set.Ioi T, 2 * (X + h) ^ (c + 1) / (h * (c ^ 2 + t ^ 2))
      = (2 * (X + h) ^ (c + 1) / h) * ∫ t in Set.Ioi T, (c ^ 2 + t ^ 2)⁻¹ := by
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        have hne : c ^ 2 + t ^ 2 ≠ 0 := by positivity
        field_simp
    _ ≤ (2 * (X + h) ^ (c + 1) / h) * ∫ t in Set.Ioi T, t ^ (-2 : ℝ) := by
        refine mul_le_mul_of_nonneg_left ?_ hAnn
        refine setIntegral_mono_on hInt1 hInt2 measurableSet_Ioi (fun t ht => ?_)
        rw [Set.mem_Ioi] at ht
        have ht0 : (0 : ℝ) < t := by linarith
        rw [Real.rpow_neg ht0.le, Real.rpow_two]
        exact inv_anti₀ (pow_pos ht0 2) (by nlinarith [sq_nonneg c])
    _ = 2 * (X + h) ^ (c + 1) / (h * T) := by
        rw [integral_Ioi_rpow_of_lt (show (-2 : ℝ) < -1 by norm_num) hT,
          show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-! ### The `Tsplit` split ledger (K3', REF-B R1 — binding).

The Perron integral is split at the kernel height `Tsplit := (log X)^4`.  Ledger
(numbers from `halasz-infra-freeze.md`, `L := log X`):

* **main part** `|t| ≤ Tsplit`: the sup of the integrand is `≤ C·L^3`
  (`S_𝒥·L ≤ C·L` times the `Λ`-window double-sum `≤ (log (x/y))^2`);
* **tail part** `|t| > Tsplit`: by `hat_tail`, the branch-2 tail mass is
  `≤ 4(X+h)^{c+1}/(h·Tsplit)`, which — with the frozen `h = X·L^{-1/2}` (#253)
  and `c₀ = 1 + 1/L` — lands `X·L^{-1/2}`, **at grade, zero ε borrowing**.

The REF-B R1 repair: the parent height `T0 = L^2` overruns the grade by a full
`L` (net log-power `L^{+1}`); raising it to `Tsplit = L^4` turns the net log-power
into `L^{-1}` (a genuine gain).  This is `tsplit_ledger` below.  `Tsplit` is the
**kernel-split height** — DISTINCT from the parent freeze's ball radius
`T0 = (log X)^{1/46}`; never conflate the two. -/

/-- The `Tsplit = (log X)^4` kernel-split height (K3'). -/
def Tsplit (X : ℝ) : ℝ := (Real.log X) ^ 4

/-- **The split ledger arithmetic** (REF-B R1, verified).  With sup-integrand
budget `C·L^3` and a branch-2 tail decaying as `1/T`, the net log-power of the tail
contribution is `L^3/Tsplit = L^{-1}` at `Tsplit = L^4` (a genuine gain, at grade),
whereas at the parent height `T0 = L^2` it is `L^3/T0 = L^{+1} > 1` (the overrun
REF-B R1 caught). -/
lemma tsplit_ledger {L : ℝ} (hL : 1 < L) :
    L ^ 3 * (L ^ 4)⁻¹ ≤ L⁻¹ ∧ 1 < L ^ 3 * (L ^ 2)⁻¹ := by
  have hL0 : (0 : ℝ) < L := by linarith
  refine ⟨le_of_eq ?_, ?_⟩
  · field_simp
  · rw [show L ^ 3 * (L ^ 2)⁻¹ = L by field_simp]; exact hL

end Salt.MR
