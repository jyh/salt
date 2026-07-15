/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.Lemma11
import Salt.BrunLower.MertensWindow
import Salt.BrunLower.MertensDischarge

/-!
# C1d — the hypothesis-(4) discharge at the Chen sequence (BJS Lemmas 15–18)

Chen's linear sieve runs at **dimension 1**: the `A₁` carrier sifts the shifted singles
`n + 2 ≡ 0`, so the sifting density is `ν(p) = 1/(p−1)`-shape (the `{−2 mod p}` residue on
`Λ`-weighted integers has density `1/φ(p) = 1/(p−1)`).  Hypothesis (4) of the explicit linear
sieve (BJS Theorem 6) is the V-ratio product bound

  `V(u)/V(z) = ∏_{u ≤ p < z} (1 − ν(p))⁻¹ ≤ (1 + ε)·log z / log u`.

**Catch #22 (corrected):** (4) is FALSE for the twin `g(p) = 1/(p−1)` at `ℚ = ∅` (the small-`u`
excess `∏(1 − 1/(p−1)²)⁻¹` is a genuine constant that no Mertens error term absorbs).  BJS verify
(4) only on `u₀ ≤ u < z` with `ℚ = {p < u₀}` excluded.  The freeze here: `ℚ = {p < w₀}`, `w₀`
explicit per `w0R ε = exp(40 / log(1+ε))` (half-share budget split), the constant `Q = ∏_{p<w₀} p`
paid into the `d < QD` remainder range (threaded by C2a).

## What is proved (sorry-free, axiom-clean)

* **The pointwise helper** `neg_log_nu_le` (`p ≥ 3`): `−log(1 − ν p) ≤ 1/p + 4/p²` whenever
  `ν p ≤ 1/(p−1)`.  Route: `−log(1−x) ≤ x/(1−x)` (PM2's `log t ≤ t−1` at `t = (1−x)⁻¹`),
  monotone reduction to `1/(p−1)`, then `1/(p−2) ≤ 1/p + 4/p²` for `p ≥ 4` (and the `p = 3`
  panel `log 2 ≤ 7/9` directly).  Does NOT consume `BrunLower.neg_log_one_sub_nu_le` (the `2/p`
  BoundingSieve-typed density — wrong dimension).

* **The main theorem** `vratio_prod_le` (parametric ε, abstract threshold `u`): for any finite
  prime set `T ⊆ [u, z)` with `ν p ≤ 1/(p−1)` and the guard `19/log u + 4/(u−1) ≤ log(1+ε)`,
  `(∏_{p∈T} (1 − ν p))⁻¹ ≤ (1+ε)·log z / log u`.  Route (catch-#22 mathematics): sum the pointwise
  helper, PM1 (`sum_inv_le_of_prime_window`, `C₃ = 19`) on the `Σ 1/p` main term, the telescope
  (`sum_one_div_sq_le`) on the `Σ 4/p²` tail, then exponentiate against the threshold guard.

* **The explicit threshold** `w0R ε = exp(40/log(1+ε))` with `w0R_threshold` proving the guard
  `19/log w₀ + 4/(w₀−1) ≤ log(1+ε)` for `ε > 0`, and `thresh_mono` (monotone in `u ≥ w₀`).  At
  the frozen `ε = 1/10000` this is `w₀ ≈ exp(4·10⁵)` — astronomical and fine (the Infinite-form
  headline).  `w0N`/`Qval` export the `ℕ`-valued `w₀` and `Q = ∏_{p<w₀} p` for the level threading.

* **The consumer corollaries.**  `h4_base` produces Lemma11's exact `h4` slot
  `Vlow s D ≤ (3·(1+ε)/sparam)·W s` (at `u = D^{1/3}`, `sparam = log D/log z`); `vratio_window_le`
  is the windowed V-ratio over `[u, z)` (StepBound2's future `hstep'` cites this shape).
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the pointwise helper `−log(1 − ν p) ≤ 1/p + 4/p²` (`p ≥ 3`) -/

/-- `−log(1 − y) ≤ y/(1 − y)` for `y < 1` (PM2's `log t ≤ t−1` at `t = (1−y)⁻¹`). -/
theorem neg_log_one_sub_le_div {y : ℝ} (hy : y < 1) :
    -Real.log (1 - y) ≤ y / (1 - y) := by
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 - y)⁻¹ by positivity)
  rw [Real.log_inv] at h
  have he : (1 - y)⁻¹ - 1 = y / (1 - y) := by
    rw [← one_div, div_sub_one (ne_of_gt h1y), show (1 : ℝ) - (1 - y) = y by ring]
  linarith [he ▸ h]

/-- **The C1d pointwise helper** (`p ≥ 3`): `−log(1 − x) ≤ 1/p + 4/p²` when `x ≤ 1/(p−1)`.
The dimension-1 analogue of PM2's `−log(1−ν) ≤ 2/p + 12/p²`. -/
theorem neg_log_nu_le {x : ℝ} {p : ℕ} (hp3 : 3 ≤ p) (hxle : x ≤ 1 / ((p : ℝ) - 1)) :
    -Real.log (1 - x) ≤ 1 / (p : ℝ) + 4 / (p : ℝ) ^ 2 := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hinvle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith
  have hbpos : (0 : ℝ) < 1 - 1 / ((p : ℝ) - 1) := by linarith
  -- `hB`: the bound at the extreme density `x = 1/(p−1)`.
  have hB : -Real.log (1 - 1 / ((p : ℝ) - 1)) ≤ 1 / (p : ℝ) + 4 / (p : ℝ) ^ 2 := by
    rcases eq_or_lt_of_le hp3 with hp3eq | hp4
    · -- p = 3 : `log 2 ≤ 7/9` (the `1/(p−2)` route overshoots here)
      have hpn : p = 3 := hp3eq.symm
      have hpe : (p : ℝ) = 3 := by rw [hpn]; norm_num
      rw [hpe]
      have he : (1 : ℝ) - 1 / ((3 : ℝ) - 1) = 2⁻¹ := by norm_num
      rw [he, Real.log_inv, neg_neg]
      have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have hrhs : (1 : ℝ) / (3 : ℝ) + 4 / (3 : ℝ) ^ 2 = 7 / 9 := by norm_num
      rw [hrhs]; linarith
    · -- p ≥ 4 : `−log(1−1/(p−1)) ≤ 1/(p−2) ≤ 1/p + 4/p²`
      have hp4n : 4 ≤ p := by omega
      have hp4R : (4 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp4n
      have hpm2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      have hne1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1
      have hne2 : (p : ℝ) - 2 ≠ 0 := ne_of_gt hpm2
      -- `−log(1−1/(p−1)) ≤ (1−1/(p−1))⁻¹ − 1 = 1/(p−2)` (PM2's `log t ≤ t−1`)
      have hq : -Real.log (1 - 1 / ((p : ℝ) - 1)) ≤ 1 / ((p : ℝ) - 2) := by
        have h := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < (1 - 1 / ((p : ℝ) - 1))⁻¹ by positivity)
        rw [Real.log_inv] at h
        have he : (1 - 1 / ((p : ℝ) - 1))⁻¹ - 1 = 1 / ((p : ℝ) - 2) := by
          rw [show (1 : ℝ) - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) by field_simp; ring,
            inv_div, div_sub_one hne2, show ((p : ℝ) - 1) - ((p : ℝ) - 2) = 1 by ring]
        linarith [he ▸ h]
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hfin : 1 / ((p : ℝ) - 2) ≤ 1 / (p : ℝ) + 4 / (p : ℝ) ^ 2 := by
        rw [div_add_div _ _ (ne_of_gt hp0) (pow_ne_zero 2 (ne_of_gt hp0)),
          div_le_div_iff₀ hpm2 (by positivity)]
        nlinarith [hp4R, hp0, mul_nonneg hp0.le (by linarith : (0 : ℝ) ≤ (p : ℝ) - 4)]
      linarith [hq, hfin]
  -- monotone reduction from `x` up to `1/(p−1)`
  have h1x : (0 : ℝ) < 1 - x := by
    have : x ≤ 1 / 2 := le_trans hxle hinvle; linarith
  have hmono : -Real.log (1 - x) ≤ -Real.log (1 - 1 / ((p : ℝ) - 1)) := by
    have hle : 1 - 1 / ((p : ℝ) - 1) ≤ 1 - x := by linarith [hxle]
    have := Real.log_le_log hbpos hle
    linarith
  exact hmono.trans hB

/-! ## Part B — the main V-ratio product bound (parametric ε, abstract threshold `u`) -/

/-- **Hypothesis (4), abstract form** (BJS Lemma 18 at the dimension-1 density).  For a finite
prime set `T` all lying in `[u, z)` with `ν p ≤ 1/(p−1)`, and the threshold guard
`19/log u + 4/(u−1) ≤ log(1+ε)` (`u ≥ 3`), the V-ratio product obeys
`(∏_{p∈T} (1 − ν p))⁻¹ ≤ (1+ε)·log z / log u`. -/
theorem vratio_prod_le (s : BoundingSieve) {u z ε : ℝ} (T : Finset ℕ)
    (hε : 0 ≤ ε) (hu3 : 3 ≤ u) (huz : u ≤ z)
    (hthresh : 19 / Real.log u + 4 / (u - 1) ≤ Real.log (1 + ε))
    (hT : ∀ p ∈ T, p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ s.nu p ≤ 1 / ((p : ℝ) - 1)) :
    (∏ p ∈ T, (1 - s.nu p))⁻¹ ≤ (1 + ε) * Real.log z / Real.log u := by
  have hu1 : (1 : ℝ) < u := by linarith
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos hu1
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hlogratio_pos : 0 < Real.log z / Real.log u := by positivity
  have hεpos : (0 : ℝ) < 1 + ε := by linarith
  -- each window factor is positive
  have hfacpos : ∀ p ∈ T, 0 < 1 - s.nu p := by
    intro p hp
    obtain ⟨hpp, hup, _, hnu⟩ := hT p hp
    have hpR : (3 : ℝ) ≤ (p : ℝ) := le_trans hu3 hup
    have hle : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    linarith [hnu, hle]
  have hProd_pos : 0 < ∏ p ∈ T, (1 - s.nu p) := Finset.prod_pos hfacpos
  -- log of the inverse product = Σ (−log)
  have hloginv : Real.log ((∏ p ∈ T, (1 - s.nu p))⁻¹) = ∑ p ∈ T, -Real.log (1 - s.nu p) := by
    rw [Real.log_inv, Real.log_prod (fun p hp => ne_of_gt (hfacpos p hp)),
      ← Finset.sum_neg_distrib]
  -- pointwise
  have hpoint : ∑ p ∈ T, -Real.log (1 - s.nu p) ≤ ∑ p ∈ T, (1 / (p : ℝ) + 4 / (p : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpp, hup, _, hnu⟩ := hT p hp
    have hp3 : 3 ≤ p := by
      have : (3 : ℝ) ≤ (p : ℝ) := le_trans hu3 hup
      exact_mod_cast this
    exact neg_log_nu_le hp3 hnu
  have hsplit : ∑ p ∈ T, (1 / (p : ℝ) + 4 / (p : ℝ) ^ 2)
      = (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ T, 4 / (p : ℝ) ^ 2 := Finset.sum_add_distrib
  -- MAIN TERM via PM1
  have hmain : ∑ p ∈ T, (1 : ℝ) / (p : ℝ)
      ≤ Real.log (Real.log z / Real.log u) + 19 / Real.log u := by
    apply Salt.BrunLower.sum_inv_le_of_prime_window (by linarith : (2 : ℝ) ≤ u) huz
    intro p hp
    obtain ⟨hpp, hup, hpz, _⟩ := hT p hp
    exact ⟨hpp, hup, hpz⟩
  -- TAIL via the telescope `Σ 1/p² ≤ 1/(u−1)`
  have htail : ∑ p ∈ T, 4 / (p : ℝ) ^ 2 ≤ 4 / (u - 1) := by
    have hMge : 2 ≤ ⌈u⌉₊ := by
      have h := Nat.le_ceil u
      have : (2 : ℝ) ≤ (⌈u⌉₊ : ℝ) := le_trans (by linarith) h
      exact_mod_cast this
    have hsub : T ⊆ Finset.Icc ⌈u⌉₊ ⌊z⌋₊ := by
      intro p hp
      obtain ⟨hpp, hup, hpz, _⟩ := hT p hp
      rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr hup, Nat.le_floor hpz.le⟩
    have hfactor : ∑ p ∈ T, 4 / (p : ℝ) ^ 2 = 4 * ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    have hsteple : ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2
        ≤ ∑ p ∈ Finset.Icc ⌈u⌉₊ ⌊z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _; positivity
    have htel := Salt.BrunLower.sum_one_div_sq_le (M := ⌈u⌉₊) (K := ⌊z⌋₊) hMge
    have hMreal : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
    have hM1 : (0 : ℝ) < (⌈u⌉₊ : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (⌈u⌉₊ : ℝ) := by exact_mod_cast hMge
      linarith
    have hu1' : (0 : ℝ) < u - 1 := by linarith
    have hinv : 1 / ((⌈u⌉₊ : ℝ) - 1) ≤ 1 / (u - 1) := by
      apply one_div_le_one_div_of_le hu1'; linarith
    calc ∑ p ∈ T, 4 / (p : ℝ) ^ 2 = 4 * ∑ p ∈ T, (1 : ℝ) / (p : ℝ) ^ 2 := hfactor
      _ ≤ 4 * ∑ p ∈ Finset.Icc ⌈u⌉₊ ⌊z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hsteple (by norm_num)
      _ ≤ 4 * (1 / ((⌈u⌉₊ : ℝ) - 1)) := by apply mul_le_mul_of_nonneg_left htel (by norm_num)
      _ ≤ 4 * (1 / (u - 1)) := by apply mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 4 / (u - 1) := by ring
  -- combine to `log(inv) ≤ log(logz/logu) + (19/logu + 4/(u−1))`
  have hcomb : Real.log ((∏ p ∈ T, (1 - s.nu p))⁻¹)
      ≤ Real.log (Real.log z / Real.log u) + (19 / Real.log u + 4 / (u - 1)) := by
    rw [hloginv]
    calc ∑ p ∈ T, -Real.log (1 - s.nu p)
        ≤ ∑ p ∈ T, (1 / (p : ℝ) + 4 / (p : ℝ) ^ 2) := hpoint
      _ = (∑ p ∈ T, (1 : ℝ) / (p : ℝ)) + ∑ p ∈ T, 4 / (p : ℝ) ^ 2 := hsplit
      _ ≤ (Real.log (Real.log z / Real.log u) + 19 / Real.log u) + 4 / (u - 1) :=
          add_le_add hmain htail
      _ = Real.log (Real.log z / Real.log u) + (19 / Real.log u + 4 / (u - 1)) := by ring
  -- fold in the threshold guard
  have hcomb2 : Real.log ((∏ p ∈ T, (1 - s.nu p))⁻¹)
      ≤ Real.log ((Real.log z / Real.log u) * (1 + ε)) := by
    rw [Real.log_mul (ne_of_gt hlogratio_pos) (ne_of_gt hεpos)]
    linarith [hcomb, hthresh]
  -- exponentiate
  have hinvpos : 0 < (∏ p ∈ T, (1 - s.nu p))⁻¹ := inv_pos.mpr hProd_pos
  have hfinal : (∏ p ∈ T, (1 - s.nu p))⁻¹ ≤ (Real.log z / Real.log u) * (1 + ε) := by
    have h := Real.exp_le_exp.mpr hcomb2
    rwa [Real.exp_log hinvpos, Real.exp_log (mul_pos hlogratio_pos hεpos)] at h
  calc (∏ p ∈ T, (1 - s.nu p))⁻¹ ≤ (Real.log z / Real.log u) * (1 + ε) := hfinal
    _ = (1 + ε) * Real.log z / Real.log u := by ring

/-! ## Part C — the explicit threshold `w₀(ε) = exp(40/log(1+ε))` -/

/-- The explicit hypothesis-(4) threshold `w₀(ε) = exp(40/log(1+ε))` (half-share budget split).
At the frozen `ε = 1/10000` this is `≈ exp(4·10⁵)` — astronomical by design (catch #22). -/
noncomputable def w0R (ε : ℝ) : ℝ := Real.exp (40 / Real.log (1 + ε))

/-- **The threshold guard holds at `w₀(ε)`** for `ε > 0`:
`19/log w₀ + 4/(w₀−1) ≤ log(1+ε)`.  The `40 = 2·(19 + 1)`-shape splits the budget:
`19/log w₀ = 19·log(1+ε)/40` and `4/(w₀−1) ≤ log(1+ε)/10`, summing to
`23·log(1+ε)/40 ≤ log(1+ε)`. -/
theorem w0R_threshold {ε : ℝ} (hε : 0 < ε) :
    19 / Real.log (w0R ε) + 4 / (w0R ε - 1) ≤ Real.log (1 + ε) := by
  have hL : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  have hLpos : 0 < 40 / Real.log (1 + ε) := by positivity
  have hlogw : Real.log (w0R ε) = 40 / Real.log (1 + ε) := by rw [w0R, Real.log_exp]
  have hexp : 40 / Real.log (1 + ε) + 1 ≤ w0R ε := by
    have := Real.add_one_le_exp (40 / Real.log (1 + ε)); rw [w0R]; linarith
  have hwm1 : 40 / Real.log (1 + ε) ≤ w0R ε - 1 := by linarith
  have hterm1 : 19 / Real.log (w0R ε) = 19 * Real.log (1 + ε) / 40 := by
    rw [hlogw, div_div_eq_mul_div]
  have hterm2 : 4 / (w0R ε - 1) ≤ Real.log (1 + ε) / 10 := by
    have h1 : 4 / (w0R ε - 1) ≤ 4 / (40 / Real.log (1 + ε)) :=
      div_le_div_of_nonneg_left (by norm_num) hLpos hwm1
    have h2 : 4 / (40 / Real.log (1 + ε)) = Real.log (1 + ε) / 10 := by
      rw [div_div_eq_mul_div]; ring
    linarith [h1, h2]
  rw [hterm1]
  have hbudget : 19 * Real.log (1 + ε) / 40 + Real.log (1 + ε) / 10 ≤ Real.log (1 + ε) := by
    nlinarith [hL]
  linarith [hterm2, hbudget]

/-- **Threshold monotonicity**: the guard at `w ≥ 3` transports up to any `u ≥ w`.  Lets a caller
discharge the `hthresh` of `vratio_prod_le` from `w0R ε ≤ u` and `w0R_threshold`. -/
theorem thresh_mono {u w ε : ℝ} (hw3 : 3 ≤ w) (hwu : w ≤ u)
    (hthresh_w : 19 / Real.log w + 4 / (w - 1) ≤ Real.log (1 + ε)) :
    19 / Real.log u + 4 / (u - 1) ≤ Real.log (1 + ε) := by
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogwu : Real.log w ≤ Real.log u := Real.log_le_log (by linarith) hwu
  have h1 : 19 / Real.log u ≤ 19 / Real.log w :=
    div_le_div_of_nonneg_left (by norm_num) hlogw hlogwu
  have hwm1 : (0 : ℝ) < w - 1 := by linarith
  have h2 : 4 / (u - 1) ≤ 4 / (w - 1) :=
    div_le_div_of_nonneg_left (by norm_num) hwm1 (by linarith)
  linarith [h1, h2, hthresh_w]

/-- The `ℕ`-valued freeze threshold `w₀(ε) = ⌈exp(40/log(1+ε))⌉`.  Its excluded-prime product
`Qval` is the constant paid into the `d < QD` remainder range (C2a threads it). -/
noncomputable def w0N (ε : ℝ) : ℕ := ⌈w0R ε⌉₊

/-- `Q = ∏_{p < w₀} p`, the C1d level constant (BJS's `Q`; asymptotically free since it is a
constant, but it must be threaded into the BV input at level `QD`). -/
noncomputable def Qval (ε : ℝ) : ℕ := ∏ p ∈ (Finset.range (w0N ε)).filter Nat.Prime, p

/-- `w0R ε ≤ w0N ε`: the real threshold is dominated by its ceiling, so `w0R ε ≤ u` follows from
`(w0N ε : ℝ) ≤ u` — the shape a caller works with once `w₀` is a `ℕ`. -/
theorem w0R_le_w0N (ε : ℝ) : w0R ε ≤ (w0N ε : ℝ) := Nat.le_ceil _

/-! ## Part D — the consumer corollaries (Lemma11's `h4` slot + the windowed form) -/

/-- **The windowed V-ratio** over `[u, z)` (StepBound2's future `hstep'` cites this shape).
For a sieve whose sifting primes are `< z` and obey `ν p ≤ 1/(p−1)`, and a threshold `u ≥ 3`
meeting the guard, `∏_{p ≥ u} (1 − ν p)⁻¹ ≤ (1+ε)·log z / log u`. -/
theorem vratio_window_le (s : BoundingSieve) {u z ε : ℝ}
    (hε : 0 ≤ ε) (hu3 : 3 ≤ u) (huz : u ≤ z)
    (hthresh : 19 / Real.log u + 4 / (u - 1) ≤ Real.log (1 + ε))
    (hz : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hnu : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ 1 / ((p : ℝ) - 1)) :
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ => u ≤ (p : ℝ)), (1 - s.nu p))⁻¹
      ≤ (1 + ε) * Real.log z / Real.log u := by
  apply vratio_prod_le s _ hε hu3 huz hthresh
  intro p hp
  rw [Finset.mem_filter] at hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
  exact ⟨hpp, hp.2, hz p hp.1, hnu p hp.1⟩

/-- **The base V-ratio corollary** = Lemma11's exact `h4` slot.  With `u = D^{1/3}` (the first-check
threshold) supplied as the abstract `u` (`hcube : D ≤ p³ → u ≤ p`) and the level relation
`log z/log u = 3/sparam` (`hlogrel`), hypothesis (4) reads `Vlow s D ≤ (3·(1+ε)/sparam)·W s`.
This is the `h4` fed to `StepBound.hbase_of` / `StepBound2.hbase'_of` with `K = 1+ε`. -/
theorem h4_base (s : BoundingSieve) (D : ℕ) {u z ε sparam : ℝ}
    (hε : 0 ≤ ε) (hu3 : 3 ≤ u) (huz : u ≤ z)
    (hthresh : 19 / Real.log u + 4 / (u - 1) ≤ Real.log (1 + ε))
    (hz : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z)
    (hcube : ∀ p ∈ s.prodPrimes.primeFactors, D ≤ p ^ 3 → u ≤ (p : ℝ))
    (hlogrel : Real.log z / Real.log u = 3 / sparam)
    (hnu : ∀ p ∈ s.prodPrimes.primeFactors, s.nu p ≤ 1 / ((p : ℝ) - 1)) :
    Vlow s D ≤ (3 * (1 + ε) / sparam) * Salt.BrunLower.W s := by
  have hW := Salt.BrunLower.W_pos s
  have hP_pos : 0 < ∏ p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3), (1 - s.nu p) := by
    apply Finset.prod_pos
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have hdvd : p ∣ s.prodPrimes := Nat.dvd_of_mem_primeFactors hp.1
    have := s.nu_lt_one_of_prime p hpp hdvd; linarith
  have hVlow_eq : Vlow s D
      = Salt.BrunLower.W s
        * (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3), (1 - s.nu p))⁻¹ := by
    rw [W_eq_Vlow_mul s D, mul_inv_cancel_right₀ (ne_of_gt hP_pos)]
  have hT : ∀ p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3),
      p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z ∧ s.nu p ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    exact ⟨hpp, hcube p hp.1 hp.2, hz p hp.1, hnu p hp.1⟩
  have hmain := vratio_prod_le s _ hε hu3 huz hthresh hT
  have heq : (1 + ε) * Real.log z / Real.log u = 3 * (1 + ε) / sparam := by
    rw [mul_div_assoc, hlogrel, ← mul_div_assoc, mul_comm (1 + ε) 3]
  have hbound : (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3), (1 - s.nu p))⁻¹
      ≤ 3 * (1 + ε) / sparam := heq ▸ hmain
  rw [hVlow_eq]
  calc Salt.BrunLower.W s
        * (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p => D ≤ p ^ 3), (1 - s.nu p))⁻¹
      ≤ Salt.BrunLower.W s * (3 * (1 + ε) / sparam) :=
        mul_le_mul_of_nonneg_left hbound hW.le
    _ = (3 * (1 + ε) / sparam) * Salt.BrunLower.W s := mul_comm _ _

end Salt.Chen
