/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.SW.Siegel

/-!
# The SW rung, node S4b′ — Estermann's positivity lemma (the Landau truncation core)

Design: `docs/blueprints/sw.md`, wave S4; the flag `SW S4b` / `SW S4b′` in
`docs/blueprints/flags.md`. This module discharges the genuine mathematical heart of
Montgomery–Vaughan *Multiplicative Number Theory I*, Lemma 11.13 (the quantitative Landau
positivity lemma abstracted as `Salt.SW.EstermannPositivity` in `Siegel.lean`):

> For an entire `f` bounded by `M ≥ 1` on `|s − 2| < 3/2`, whose product with `ζ` has
> nonnegative Dirichlet coefficients `r` (`r 1 = 1`), if `f σ ≥ 0` at some `σ ∈ [19/20, 1)`
> then `(1 − σ)/4 · M^{−3(1−σ)} ≤ (f 1).re`.

## What is FULLY PROVEN here (sorry-free, axiom-clean)

* `landau_truncation` — **the arithmetic heart**: the pure real-analysis Landau truncation.
  Given the pole-subtracted Taylor data of `F = ζ·f` at `s = 2` — nonnegative coefficients
  `a k ≥ 0` with `a 0 ≥ 1`, the Cauchy bound `|a k − L| ≤ B·(2/3)^k` with `B ≤ (29/2)·M`, and
  the truncated inequality `∑ (a k − L) y^k ≤ L/(y−1)` at `y = 2 − σ ∈ (1, 21/20]` — it derives
  the frozen bound `(y−1)/4 · M^{−3(y−1)} ≤ L`. The truncation index is
  `K = ⌈log(40B/3)/log(10/7)⌉`; the tail is controlled to `≤ 1/4` and the head to `≥ 1 − L·∑y^k`,
  and the closing `y^K ≤ 3·M^{3(y−1)}` uses `log y ≤ y−1` with the numeric slack
  `1/log(10/7) < 3`. All constants close with ~28% margin (the `M^{−3}` and `¼` were tuned for
  the crude circle bound `sup_{|s−2|=3/2} ‖ζ‖ ≤ 25/2`, giving `B ≤ (29/2)·M`).

* `estermannPositivity_core` — the frozen conclusion `(1−σ)/4 · M^{−3(1−σ)} ≤ (f 1).re`, proven
  from the Taylor/Cauchy data (`a`, `B`) + the ψ-series identity + `ζ(σ) ≤ 0`, via
  `landau_truncation`. (The `ζ(σ)·f(σ) ≤ 0` step — negative `ζ` times nonnegative `f` — is proven
  here from `ζ(σ) ≤ 0` and `f σ ≥ 0`.)

* `estermannPositivity_of_interface` — the **exact reduction**: `EstermannPositivity` (the frozen
  `Prop` from `Siegel.lean`) holds provided the analytic interface `EstermannInterface` — the
  per-input construction of `(a, B)` with the Cauchy bound and the ψ-series identity — is
  discharged. The compiler enforces the conclusion shape.

## What is ABSTRACTED (`EstermannInterface`, the deferred analytic plumbing)

The one deferred input is the construction, for each admissible `f`, of the pole-subtracted Taylor
data: the coefficients `a k = ∑ r(n)(log n)^k/(k! n²)` and their nonnegativity/`a 0 ≥ 1` (mathlib's
`ArithmeticFunction.iteratedDeriv_LSeries_alternating`, gated on `abscissaOfAbsConv r < 2`); the
Cauchy bound `B` on `ψ = ζf − f(1)/(s−1)` about `s = 2` (removable singularity à la `BadChar` /
`Zc`, then Cauchy estimates on the circle `|s−2| = 3/2` with the `Zc`-growth ζ bound); the entire
ψ-series identity `∑ (a k − L)(2−σ)^k = (ζ(σ)f(σ)).re + L/(1−σ)`
(`Complex.taylorSeries_eq_of_entire'`); and `ζ(σ) ≤ 0` on `[19/20, 1)` (the Dirichlet-eta /
`Zc`-positivity route). See `docs/blueprints/flags.md` (SW S4b′) — this is the PB-floor.
-/

open scoped BigOperators ComplexOrder

namespace Salt.SW

set_option maxHeartbeats 1200000 in
-- The tail geometric estimate, head bound, `⌈log⌉`-index choice and the closing `rpow`/`log`
-- numeric chain (incl. `norm_num` on `(10/7)^19` and several `nlinarith`s) exceed the default budget.
/-- **Landau truncation (the arithmetic heart of Estermann's lemma).**
Given nonnegative Taylor coefficients `a` with `a 0 ≥ 1`, a Cauchy bound `|a k − L| ≤ B·(2/3)^k`
(with `2 ≤ B ≤ (29/2)·M`, `M ≥ 1`), and the pole-subtracted inequality `∑ (a k − L) y^k ≤ L/(y−1)`
at `y = 2 − σ ∈ (1, 21/20]`, we get the frozen lower bound `(y−1)/4 · M^{−3(y−1)} ≤ L`. -/
theorem landau_truncation {a : ℕ → ℝ} {L B M y : ℝ}
    (ha : ∀ k, 0 ≤ a k) (ha0 : 1 ≤ a 0)
    (hy1 : 1 < y) (hy2 : y ≤ 21 / 20)
    (hM : 1 ≤ M) (hBlo : 2 ≤ B) (hBM : B ≤ 29 / 2 * M)
    (hcauchy : ∀ k, |a k - L| ≤ B * (2 / 3) ^ k)
    (hle : ∑' k, (a k - L) * y ^ k ≤ L / (y - 1)) :
    (y - 1) / 4 * M ^ (-(3 * (y - 1))) ≤ L := by
  set q : ℝ := 2 * y / 3 with hq
  have hy0 : (0:ℝ) < y := by linarith
  have hδ : (0:ℝ) ≤ y - 1 := by linarith
  have hδ2 : y - 1 ≤ 1 / 20 := by linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hqle : q ≤ 7 / 10 := by rw [hq]; linarith
  have hq1 : q < 1 := by linarith
  have hBpos : 0 < B := by linarith
  have hMpos : (0:ℝ) < M := by linarith
  set term : ℕ → ℝ := fun k => (a k - L) * y ^ k with hterm
  have hcomp : ∀ k, |term k| ≤ B * q ^ k := by
    intro k
    simp only [hterm]
    have hyk : (0:ℝ) ≤ y ^ k := by positivity
    calc |(a k - L) * y ^ k| = |a k - L| * y ^ k := by rw [abs_mul, abs_of_nonneg hyk]
      _ ≤ B * (2/3) ^ k * y ^ k := mul_le_mul_of_nonneg_right (hcauchy k) hyk
      _ = B * q ^ k := by rw [hq, show (2*y/3:ℝ) = 2/3*y from by ring, mul_pow]; ring
  have hgeom : Summable (fun k => B * q ^ k) := (summable_geometric_of_lt_one hq0 hq1).mul_left B
  have hsummable : Summable term :=
    Summable.of_norm_bounded hgeom (fun k => by rw [Real.norm_eq_abs]; exact hcomp k)
  -- choose truncation index K = ⌈log(40B/3)/log(10/7)⌉₊
  set c7 : ℝ := Real.log (10 / 7) with hc7def
  have hc7 : 0 < c7 := by rw [hc7def]; exact Real.log_pos (by norm_num)
  set L₀ : ℝ := Real.log (40 * B / 3) / c7 with hL₀
  have h40Bpos : (0:ℝ) < 40 * B / 3 := by positivity
  have hL₀0 : 0 ≤ L₀ := by
    rw [hL₀]; apply div_nonneg _ hc7.le
    apply Real.log_nonneg; rw [le_div_iff₀ (by norm_num : (0:ℝ) < 3)]; nlinarith [hBlo]
  set K : ℕ := ⌈L₀⌉₊ with hK
  have hK_ge : L₀ ≤ (K : ℝ) := Nat.le_ceil L₀
  have hK_lt : (K : ℝ) < L₀ + 1 := Nat.ceil_lt_add_one hL₀0
  have hK1 : 1 ≤ K := by
    rw [hK]; apply Nat.one_le_ceil_iff.mpr
    rw [hL₀]; apply div_pos _ hc7
    apply Real.log_pos; rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]; nlinarith [hBlo]
  -- numeric facts
  have ha_fact : 1 ≤ 3 * c7 := by
    have h3 : (3:ℝ) * c7 = Real.log ((10/7:ℝ)^3) := by rw [hc7def, Real.log_pow]; push_cast; ring
    rw [h3, Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      _ ≤ (10/7:ℝ)^3 := by norm_num
  have hc_fact : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    calc Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
      _ ≤ 3 := by norm_num
  have hb_fact : Real.log (580 / 3) ≤ 19 * c7 := by
    have h19 : (19:ℝ) * c7 = Real.log ((10/7:ℝ)^19) := by
      rw [hc7def, Real.log_pow]; push_cast; ring
    rw [h19]; apply Real.log_le_log (by norm_num); norm_num
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hy0
  have hlog40 : Real.log (40 * B / 3) ≤ Real.log (580 / 3) + Real.log M := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    apply Real.log_le_log h40Bpos
    rw [show (580 / 3 * M : ℝ) = 580 * M / 3 from by ring,
        div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
    nlinarith [hBM]
  have hE : L₀ ≤ 19 + 3 * Real.log M := by
    have hnum : Real.log (40 * B / 3) ≤ 19 * c7 + Real.log M := by linarith [hlog40, hb_fact]
    have hmm : Real.log M ≤ 3 * (Real.log M * c7) := by
      nlinarith [mul_nonneg hlogM (by linarith [ha_fact] : (0:ℝ) ≤ 3 * c7 - 1)]
    rw [hL₀, div_le_iff₀ hc7,
        show (19 + 3 * Real.log M) * c7 = 19 * c7 + 3 * (Real.log M * c7) from by ring]
    linarith [hnum, hmm]
  -- crux : log y · K ≤ log 3 + 3(y−1) log M
  have hcrux : Real.log y * (K : ℝ) ≤ Real.log 3 + 3 * (y - 1) * Real.log M := by
    have hK0 : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    have h1 : Real.log y * (K : ℝ) ≤ (y - 1) * (K : ℝ) := mul_le_mul_of_nonneg_right hlogy hK0
    have h2 : (y - 1) * (K : ℝ) ≤ (y - 1) * (L₀ + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hK_lt) hδ
    have h3 : (y - 1) * (L₀ + 1) ≤ (y - 1) * (20 + 3 * Real.log M) :=
      mul_le_mul_of_nonneg_left (by linarith [hE]) hδ
    have h5 : 20 * (y - 1) ≤ Real.log 3 := by nlinarith [hδ2, hc_fact]
    calc Real.log y * (K:ℝ) ≤ (y - 1) * (20 + 3 * Real.log M) := le_trans h1 (le_trans h2 h3)
      _ = 20 * (y - 1) + 3 * (y - 1) * Real.log M := by ring
      _ ≤ Real.log 3 + 3 * (y - 1) * Real.log M := by linarith [h5]
  have hyK_le : y ^ K ≤ 3 * M ^ (3 * (y - 1)) := by
    have e1 : (y:ℝ) ^ K = Real.exp (Real.log y * (K:ℝ)) := by
      rw [← Real.rpow_natCast y K, Real.rpow_def_of_pos hy0]
    have e2 : Real.exp (Real.log 3 + 3 * (y - 1) * Real.log M) = (3:ℝ) * M ^ (3 * (y - 1)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 3), Real.rpow_def_of_pos hMpos,
          show 3 * (y - 1) * Real.log M = Real.log M * (3 * (y - 1)) from by ring]
    rw [e1, ← e2]; exact Real.exp_le_exp.mpr hcrux
  -- tail : |∑' i, term (i+K)| ≤ 1/4
  have hsummable_shift : Summable (fun i => term (i + K)) := (summable_nat_add_iff K).mpr hsummable
  have hgeom_shift : Summable (fun i => B * q ^ (i + K)) := (summable_nat_add_iff K).mpr hgeom
  have hbnd_shift : ∀ i, |term (i + K)| ≤ B * q ^ (i + K) := fun i => hcomp (i + K)
  have htail_abs : |∑' i, term (i + K)| ≤ B * q ^ K / (1 - q) := by
    have hnormbnd : |∑' i, term (i + K)| ≤ ∑' i, |term (i + K)| := by
      have h := norm_tsum_le_tsum_norm (f := fun i => term (i+K))
                  (by simpa only [Real.norm_eq_abs] using hsummable_shift.abs)
      simpa only [Real.norm_eq_abs] using h
    calc |∑' i, term (i + K)| ≤ ∑' i, |term (i + K)| := hnormbnd
      _ ≤ ∑' i, B * q ^ (i + K) := hsummable_shift.abs.tsum_le_tsum hbnd_shift hgeom_shift
      _ = B * q ^ K * ∑' i, q ^ i := by
          rw [← tsum_mul_left]; apply tsum_congr; intro i; rw [pow_add]; ring
      _ = B * q ^ K / (1 - q) := by rw [tsum_geometric_of_lt_one hq0 hq1]; ring
  have htail_le : B * q ^ K / (1 - q) ≤ 1 / 4 := by
    have hqK : q ^ K ≤ (7/10:ℝ) ^ K := pow_le_pow_left₀ hq0 hqle K
    have hkey : 40 * B / 3 ≤ (10/7:ℝ) ^ K := by
      have h1 : (10/7:ℝ) ^ (L₀:ℝ) ≤ (10/7:ℝ) ^ (K:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hK_ge
      have h2 : (10/7:ℝ) ^ (L₀:ℝ) = 40 * B / 3 := by
        rw [Real.rpow_def_of_pos (by norm_num),
            show Real.log (10/7) * L₀ = Real.log (40*B/3) from by rw [hL₀, hc7def]; field_simp]
        exact Real.exp_log h40Bpos
      rw [Real.rpow_natCast] at h1; linarith [h1, h2.le, h2.ge]
    have h710K : (7/10:ℝ) ^ K ≤ 3/(40*B) := by
      rw [show (7/10:ℝ)^K = ((10/7:ℝ)^K)⁻¹ from by rw [← inv_pow]; norm_num,
          show (3/(40*B):ℝ) = (40*B/3)⁻¹ from by rw [inv_div]]
      exact inv_anti₀ (by positivity) hkey
    have hinv : (1-q)⁻¹ ≤ 10/3 := by
      rw [show (10/3:ℝ) = (3/10)⁻¹ from by norm_num]
      exact inv_anti₀ (by norm_num) (by linarith [hqle])
    have hBqK : (0:ℝ) ≤ B * q^K := by positivity
    have hB0 : B ≠ 0 := ne_of_gt hBpos
    calc B * q ^ K / (1 - q)
        = B * q^K * (1-q)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ B * q^K * (10/3) := mul_le_mul_of_nonneg_left hinv hBqK
      _ ≤ B * (7/10:ℝ)^K * (10/3) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hqK hBpos.le
      _ ≤ B * (3/(40*B)) * (10/3) := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left h710K hBpos.le
      _ = 1/4 := by field_simp; ring
  have htail_ge : -(1/4:ℝ) ≤ ∑' i, term (i + K) := (abs_le.mp (htail_abs.trans htail_le)).1
  -- head : ∑_{k<K} term k ≥ 1 − L·∑_{k<K} y^k
  set G : ℝ := ∑ k ∈ Finset.range K, y ^ k with hG
  have hhead_eq : ∑ k ∈ Finset.range K, term k
      = (∑ k ∈ Finset.range K, a k * y ^ k) - L * G := by
    rw [hG, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; simp only [hterm]; ring
  have hayk_ge : 1 ≤ ∑ k ∈ Finset.range K, a k * y ^ k := by
    have hmem : (0:ℕ) ∈ Finset.range K := Finset.mem_range.mpr hK1
    have hnn : ∀ k ∈ Finset.range K, 0 ≤ a k * y ^ k := fun k _ => mul_nonneg (ha k) (by positivity)
    have hsingle := Finset.single_le_sum hnn hmem
    simp only [pow_zero, mul_one] at hsingle; linarith [ha0, hsingle]
  have hhead_ge : 1 - L * G ≤ ∑ k ∈ Finset.range K, term k := by
    rw [hhead_eq]; linarith [hayk_ge]
  have hsplit := hsummable.sum_add_tsum_nat_add K
  have hden' : (0:ℝ) < y - 1 := by linarith
  have hGval : G + 1/(y-1) = y^K/(y-1) := by
    rw [hG, geom_sum_eq (by linarith : y ≠ 1) K]; ring
  have hSle : (∑ k ∈ Finset.range K, term k) + (∑' i, term (i + K)) ≤ L/(y-1) := by
    rw [hsplit]; exact hle
  have hcombine : (3:ℝ)/4 ≤ L * G + L / (y - 1) := by
    linarith [hhead_ge, htail_ge, hSle]
  have hcombine2 : (3:ℝ)/4 ≤ L * (y^K/(y-1)) := by
    have heq : L * (y^K/(y-1)) = L * G + L/(y-1) := by rw [← hGval]; ring
    rw [heq]; exact hcombine
  have hyKpos : (0:ℝ) < y^K := by positivity
  have hLyK : (3/4)*(y-1) ≤ L * y^K := by
    have h := hcombine2
    rw [show L * (y^K/(y-1)) = (L*y^K)/(y-1) from by ring] at h
    rwa [le_div_iff₀ hden'] at h
  have hLlb : (3/4)*(y-1)/y^K ≤ L := by rw [div_le_iff₀ hyKpos]; linarith [hLyK]
  have hL0 : 0 ≤ L := le_trans (div_nonneg (mul_nonneg (by norm_num) hδ) hyKpos.le) hLlb
  rw [Real.rpow_neg hMpos.le]
  have hPpos : (0:ℝ) < M^(3*(y-1)) := Real.rpow_pos_of_pos hMpos _
  rw [show (y-1)/4 * (M^(3*(y-1)))⁻¹ = ((y-1)/4)/(M^(3*(y-1))) from by ring,
      div_le_iff₀ hPpos]
  have hprod : 0 ≤ L * (3 * M^(3*(y-1)) - y^K) := mul_nonneg hL0 (by linarith [hyK_le])
  nlinarith [hLyK, hprod]

/-- **Estermann's positivity lemma (the frozen conclusion) from the pole-subtracted Taylor data.**
For entire-`f`-shaped data with `M ≥ 1`, at `σ ∈ [19/20, 1)` with `f σ ≥ 0`, given the Taylor
coefficients `a` of `F = ζ·f` at `s = 2` (`a k ≥ 0`, `a 0 ≥ 1`), the Cauchy bound
`|a k − (f 1).re| ≤ B·(2/3)^k` with `2 ≤ B ≤ (29/2)·M`, the sign fact `ζ(σ) ≤ 0`, and the
ψ-series identity `∑ (a k − (f 1).re)(2−σ)^k = (ζ(σ)·f(σ)).re + (f 1).re/(1−σ)`, we obtain the
frozen bound `(1−σ)/4 · M^{−3(1−σ)} ≤ (f 1).re`. -/
theorem estermannPositivity_core (f : ℂ → ℂ) {M : ℝ} (hM : 1 ≤ M) {σ : ℝ}
    (hσlo : (19 / 20 : ℝ) ≤ σ) (hσhi : σ < 1) (hfσ : (0 : ℂ) ≤ f (σ : ℂ))
    (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) (ha0 : 1 ≤ a 0)
    (B : ℝ) (hBlo : 2 ≤ B) (hBM : B ≤ 29 / 2 * M)
    (hcauchy : ∀ k, |a k - (f 1).re| ≤ B * (2 / 3) ^ k)
    (hζneg : riemannZeta (σ : ℂ) ≤ 0)
    (hseries : ∑' k, (a k - (f 1).re) * (2 - σ) ^ k
        = (riemannZeta (σ : ℂ) * f (σ : ℂ)).re + (f 1).re / (1 - σ)) :
    (1 - σ) / 4 * M ^ (-(3 * (1 - σ))) ≤ (f 1).re := by
  set L : ℝ := (f 1).re with hLdef
  -- `ζ(σ) ≤ 0` (negative real) times `f σ ≥ 0` (nonnegative real) gives `(ζ(σ)·f(σ)).re ≤ 0`
  have hFnonpos : (riemannZeta (σ : ℂ) * f (σ : ℂ)).re ≤ 0 := by
    obtain ⟨hζre, hζim⟩ := Complex.le_def.mp hζneg
    obtain ⟨hfre, _⟩ := Complex.le_def.mp hfσ
    simp only [Complex.zero_re, Complex.zero_im] at hζre hζim hfre
    rw [Complex.mul_re, hζim]
    nlinarith [mul_nonneg hfre (neg_nonneg.mpr hζre)]
  -- the truncated inequality `∑ (a k − L)(2−σ)^k ≤ L/((2−σ)−1)`
  have hle : ∑' k, (a k - L) * ((2 : ℝ) - σ) ^ k ≤ L / (((2 : ℝ) - σ) - 1) := by
    rw [show ((2 : ℝ) - σ) - 1 = 1 - σ from by ring, hseries]
    linarith [hFnonpos]
  have hmain := landau_truncation (a := a) (L := L) (B := B) (M := M) (y := 2 - σ)
    ha ha0 (by linarith : (1 : ℝ) < 2 - σ) (by linarith : (2 : ℝ) - σ ≤ 21 / 20)
    hM hBlo hBM hcauchy hle
  rwa [show (2 : ℝ) - σ - 1 = 1 - σ from by ring] at hmain

/-- **The analytic interface** deferred to the later Estermann wave: for each admissible input,
the pole-subtracted Taylor data (`a`, `B`) of `F = ζ·f` at `s = 2` together with its Cauchy bound,
the sign `ζ(σ) ≤ 0`, and the ψ-series identity. Discharging this is the remaining formalization
work (see the module docstring and `docs/blueprints/flags.md`, SW S4b′). -/
def EstermannInterface : Prop :=
  ∀ (f : ℂ → ℂ) (r : ℕ → ℂ) (M : ℝ), 1 ≤ M → Differentiable ℂ f →
    (∀ z ∈ Metric.ball (2 : ℂ) (3 / 2), ‖f z‖ ≤ M) →
    (0 ≤ r) → r 1 = 1 → LSeries.abscissaOfAbsConv r < 2 →
    (∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries r s) →
    ∀ {σ : ℝ}, (19 / 20 : ℝ) ≤ σ → σ < 1 → (0 : ℂ) ≤ f (σ : ℂ) →
      ∃ (a : ℕ → ℝ) (B : ℝ), (∀ k, 0 ≤ a k) ∧ 1 ≤ a 0 ∧ 2 ≤ B ∧ B ≤ 29 / 2 * M ∧
        (∀ k, |a k - (f 1).re| ≤ B * (2 / 3) ^ k) ∧ riemannZeta (σ : ℂ) ≤ 0 ∧
        ∑' k, (a k - (f 1).re) * (2 - σ) ^ k
          = (riemannZeta (σ : ℂ) * f (σ : ℂ)).re + (f 1).re / (1 - σ)

/-- **The exact reduction.** `EstermannPositivity` (the frozen `Prop` from `Siegel.lean`) holds
whenever the analytic interface `EstermannInterface` can be discharged. Everything downstream of
the interface — the Landau truncation and the frozen constants — is proven
(`estermannPositivity_core`). -/
theorem estermannPositivity_of_interface (H : EstermannInterface) : EstermannPositivity := by
  intro f r M hM hf hfM hr0 hr1 habsc hζf σ hσlo hσhi hfσ
  obtain ⟨a, B, ha, ha0, hBlo, hBM, hcauchy, hζneg, hseries⟩ :=
    H f r M hM hf hfM hr0 hr1 habsc hζf (σ := σ) hσlo hσhi hfσ
  exact estermannPositivity_core f hM hσlo hσhi hfσ a ha ha0 B hBlo hBM hcauchy hζneg hseries

end Salt.SW
