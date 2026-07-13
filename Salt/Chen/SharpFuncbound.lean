/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.StepBound

/-!
# E₁a — the sharp `hBJS` functional integral bound `κ₃ ≤ 49/50`

The sharp companion of `StepBound.hBJS_funcbound` (which lands the *elementary* `κ₃ = 1`,
tight at `s = 2`).  BJS's τ-recursion contracts only with `κ₃ < 1`, so E₁b needs a fixed
rational `κ₃ < 1`; here we land **`κ₃ = 49/50`** on the operating window `s ≥ 2`.

## What is proved (sorry-free, axiom-clean)

* **The parts-twice tail bound** (`tail_parts_bound`): `∫_3^c 3u⁻¹e⁻ᵘ ≤ (8/9)e⁻³` for `c ≥ 3`.
  The `κ = 1` version of `hBJS_funcbound` threw away the `3/u` factor on `[3,∞)` by the crude
  `3u⁻¹e⁻ᵘ ≤ e⁻ᵘ`; here we keep it.  Route: the single explicit antiderivative
  `Gtail u := 3(u⁻¹ − u⁻² + 2u⁻³)e⁻ᵘ`, which packages BJS's *integrate-by-parts-twice*
  computation (`∫_3^∞ 3u⁻¹e⁻ᵘ = 3a⁻¹e⁻ᵃ − 3∫u⁻²e⁻ᵘ`, `∫_a^∞ u⁻²e⁻ᵘ ≥ a⁻²e⁻ᵃ(1−2/a)`).
  One checks `−Gtail'(u) = 3u⁻¹e⁻ᵘ + 18u⁻⁴e⁻ᵘ ≥ 3u⁻¹e⁻ᵘ` (a majorant with an *elementary*
  antiderivative), `Gtail 3 = (8/9)e⁻³`, and `Gtail c ≥ 0` — so
  `∫_3^c 3u⁻¹e⁻ᵘ ≤ ∫_3^c(−Gtail') = Gtail 3 − Gtail c ≤ (8/9)e⁻³`.

* **The sharp crossing bound** (`hBJS_intbound_cross_sharp`): for `a ≤ 2`,
  `∫_a^c h ≤ e⁻²(3−a) − (1/9)e⁻³` — the `−(1/9)e⁻³` refinement of `hBJS_intbound_cross`,
  coming from `∫_2^∞ h = (e⁻² − e⁻³) + ∫_3^∞ 3u⁻¹e⁻ᵘ ≤ e⁻² − (1/9)e⁻³`.

* **The sharp functional bound** (`hBJS_funcbound_sharp`): for `s ≥ 2` and any `c`,
  `∫_{s−1}^c h ≤ (49/50)·s·h(s)`.  The tail `s ≥ 3` reuses the crude
  `StepBound.hBJS_intbound_hi` (there `e/3 ≈ 0.906 < 49/50` already); the band `2 ≤ s ≤ 3`
  uses the sharp crossing bound and the Padé panel `(4−s)e^{s−2} ≤ s`, closing at `49/50`
  because `e ≤ 25/9` (the constraint is tight at `s = 2`, margin ≈ 2%).

## The `s`-threshold (for E₁b)

The constant `49/50 < 1` holds **exactly on `s ≥ 2`** — the threshold is `s₀ = 2`.  For
`s ∈ [1,2)` the constant e⁻² plateau makes `∫_{s−1}^∞ h / (s·h(s)) → 3` as `s → 1`, so no
`κ₃ < 1` is possible there; E₁b's small-`s`/odd-level cases are served by Lemma 11's landed
`n = 1` treatment (valid on `s ∈ [1,3]`), not by this bound.
-/

open MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-! ## Part A — the parts-twice tail bound `∫_3^c 3u⁻¹e⁻ᵘ ≤ (8/9)e⁻³` -/

/-- The explicit antiderivative packaging BJS's integrate-by-parts-twice: `Gtail` satisfies
`−Gtail'(u) = 3u⁻¹e⁻ᵘ + 18u⁻⁴e⁻ᵘ ≥ 3u⁻¹e⁻ᵘ`, with `Gtail 3 = (8/9)e⁻³` and `Gtail ≥ 0`. -/
noncomputable def Gtail (u : ℝ) : ℝ :=
  3 * ((u⁻¹ - (u⁻¹) ^ 2 + 2 * (u⁻¹) ^ 3) * Real.exp (-u))

/-- `d/du[Gtail] = −(3u⁻¹e⁻ᵘ) − 18u⁻⁴e⁻ᵘ` for `u ≠ 0`. -/
theorem hasDerivAt_Gtail {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt Gtail
      (-(3 * u⁻¹ * Real.exp (-u)) - 18 * (u⁻¹) ^ 4 * Real.exp (-u)) u := by
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u := by
    have h1 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) u := (hasDerivAt_id u).neg
    simpa using h1.exp
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-(u ^ 2)⁻¹) u := hasDerivAt_inv hu
  have hP := (hinv.sub (hinv.pow 2)).add ((hinv.pow 3).const_mul 2)
  have hmul := hP.mul hexp
  have hG : HasDerivAt Gtail
      (3 * ((-(u ^ 2)⁻¹ - (2 : ℝ) * u⁻¹ ^ 1 * -(u ^ 2)⁻¹ + 2 * ((3 : ℝ) * u⁻¹ ^ 2 * -(u ^ 2)⁻¹))
          * Real.exp (-u) + (u⁻¹ - (u⁻¹) ^ 2 + 2 * (u⁻¹) ^ 3) * -Real.exp (-u))) u :=
    hmul.const_mul 3
  have hEq : (3 * ((-(u ^ 2)⁻¹ - (2 : ℝ) * u⁻¹ ^ 1 * -(u ^ 2)⁻¹
          + 2 * ((3 : ℝ) * u⁻¹ ^ 2 * -(u ^ 2)⁻¹)) * Real.exp (-u)
        + (u⁻¹ - (u⁻¹) ^ 2 + 2 * (u⁻¹) ^ 3) * -Real.exp (-u)))
      = -(3 * u⁻¹ * Real.exp (-u)) - 18 * (u⁻¹) ^ 4 * Real.exp (-u) := by
    simp only [← inv_pow]
    ring
  rw [← hEq]
  exact hG

/-- `Gtail 3 = (8/9)e⁻³` (the boundary value at `a = 3`: `3·(1/3 − 1/9 + 2/27) = 8/9`). -/
theorem Gtail_three : Gtail 3 = (8 / 9) * Real.exp (-3) := by
  unfold Gtail
  rw [show ((3 : ℝ)⁻¹ - ((3 : ℝ)⁻¹) ^ 2 + 2 * ((3 : ℝ)⁻¹) ^ 3) = 8 / 27 from by norm_num]
  ring

/-- `Gtail c ≥ 0` for `c ≥ 3` (the discarded far boundary term, `c⁻¹(1 − c⁻¹ + 2c⁻²) > 0`). -/
theorem Gtail_nonneg {c : ℝ} (hc : 3 ≤ c) : 0 ≤ Gtail c := by
  unfold Gtail
  have hc0 : 0 < c := by linarith
  have ht : 0 < c⁻¹ := by positivity
  have hq : 0 < 2 * (c⁻¹) ^ 2 - c⁻¹ + 1 := by nlinarith [sq_nonneg (2 * c⁻¹ - 1), ht]
  have hfac : 0 ≤ c⁻¹ - (c⁻¹) ^ 2 + 2 * (c⁻¹) ^ 3 := by nlinarith [mul_pos ht hq]
  have hexp : 0 < Real.exp (-c) := Real.exp_pos _
  have h3 : 0 ≤ 3 * (c⁻¹ - (c⁻¹) ^ 2 + 2 * (c⁻¹) ^ 3) := by linarith
  positivity

/-- **The parts-twice tail bound** (BJS's `∫_3^∞ 3u⁻¹e⁻ᵘ ≤ (8/9)e⁻³`, finite-`c` form).
The `κ₃ = 1` funcbound used `3u⁻¹e⁻ᵘ ≤ e⁻ᵘ` here (giving `∫ ≤ e⁻³`); keeping the `3/u`
factor via `Gtail` shaves it to `(8/9)e⁻³`, exactly the improvement that closes `49/50`. -/
theorem tail_parts_bound (c : ℝ) (hc : 3 ≤ c) :
    (∫ u in (3 : ℝ)..c, 3 * u⁻¹ * Real.exp (-u)) ≤ (8 / 9) * Real.exp (-3) := by
  have hne0 : ∀ u ∈ Set.uIcc (3 : ℝ) c, u ≠ 0 := by
    intro u hu
    rw [Set.uIcc_of_le hc] at hu
    exact ne_of_gt (by linarith [hu.1])
  have hcinv : ContinuousOn (fun u : ℝ => u⁻¹) (Set.uIcc (3 : ℝ) c) :=
    (continuous_id.continuousOn).inv₀ (fun u hu => hne0 u hu)
  have hcexp : ContinuousOn (fun u : ℝ => Real.exp (-u)) (Set.uIcc (3 : ℝ) c) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn
  have hcontf : ContinuousOn (fun u : ℝ => 3 * u⁻¹ * Real.exp (-u)) (Set.uIcc (3 : ℝ) c) :=
    (continuousOn_const.mul hcinv).mul hcexp
  have hcontM : ContinuousOn
      (fun u : ℝ => 3 * u⁻¹ * Real.exp (-u) + 18 * (u⁻¹) ^ 4 * Real.exp (-u))
      (Set.uIcc (3 : ℝ) c) :=
    hcontf.add ((continuousOn_const.mul (hcinv.pow 4)).mul hcexp)
  have hintf : IntervalIntegrable (fun u => 3 * u⁻¹ * Real.exp (-u)) volume 3 c :=
    hcontf.intervalIntegrable
  have hintM : IntervalIntegrable
      (fun u => 3 * u⁻¹ * Real.exp (-u) + 18 * (u⁻¹) ^ 4 * Real.exp (-u)) volume 3 c :=
    hcontM.intervalIntegrable
  -- majorise the integrand by `−Gtail'`
  have hmono : (∫ u in (3 : ℝ)..c, 3 * u⁻¹ * Real.exp (-u))
      ≤ ∫ u in (3 : ℝ)..c, (3 * u⁻¹ * Real.exp (-u) + 18 * (u⁻¹) ^ 4 * Real.exp (-u)) := by
    apply intervalIntegral.integral_mono_on hc hintf hintM
    intro u _
    have : 0 ≤ 18 * (u⁻¹) ^ 4 * Real.exp (-u) := by positivity
    linarith
  -- evaluate the majorant integral through the antiderivative `−Gtail`
  have hderivF : ∀ u ∈ Set.uIcc (3 : ℝ) c, HasDerivAt (fun x => -(Gtail x))
      (3 * u⁻¹ * Real.exp (-u) + 18 * (u⁻¹) ^ 4 * Real.exp (-u)) u := by
    intro u hu
    have h0 := (hasDerivAt_Gtail (hne0 u hu)).neg
    rw [show (-(-(3 * u⁻¹ * Real.exp (-u)) - 18 * (u⁻¹) ^ 4 * Real.exp (-u)))
        = 3 * u⁻¹ * Real.exp (-u) + 18 * (u⁻¹) ^ 4 * Real.exp (-u) from by ring] at h0
    exact h0
  have hval : (∫ u in (3 : ℝ)..c, (3 * u⁻¹ * Real.exp (-u) + 18 * (u⁻¹) ^ 4 * Real.exp (-u)))
      = -(Gtail c) - -(Gtail 3) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderivF hintM
  rw [hval] at hmono
  have hGc := Gtail_nonneg hc
  have hG3 := Gtail_three
  linarith [hmono, hGc, hG3]

/-! ## Part B — the sharp crossing / functional bounds -/

/-- The sharp bound on `∫_2^c h`: `≤ e⁻² − (1/9)e⁻³` for **all** `c` (the crude bound is
`≤ e⁻²`).  On `[3,∞)` it consumes `tail_parts_bound`. -/
theorem hBJS_intbound_from2_sharp (c : ℝ) :
    (∫ u in (2 : ℝ)..c, hBJS u) ≤ Real.exp (-2) - (1 / 9) * Real.exp (-3) := by
  have hpos : (0 : ℝ) ≤ Real.exp (-2) - (1 / 9) * Real.exp (-3) := by
    have : Real.exp (-3) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by norm_num)
    nlinarith [Real.exp_pos (-3 : ℝ), this]
  rcases le_total c 2 with hc2 | hc2
  · rw [intervalIntegral.integral_symm]
    have h1 : 0 ≤ ∫ u in c..(2 : ℝ), hBJS u :=
      intervalIntegral.integral_nonneg hc2 (fun u _ => (hBJS_pos u).le)
    linarith
  · rcases le_total c 3 with hc3 | hc3
    · -- 2 ≤ c ≤ 3: `∫_2^c h = e⁻² − e⁻ᶜ`
      have hcongr : (∫ u in (2 : ℝ)..c, hBJS u) = ∫ u in (2 : ℝ)..c, Real.exp (-u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hc2] at hu
        exact hBJS_mid hu.1 (le_trans hu.2 hc3)
      rw [hcongr, integral_exp_neg]
      have hce : (1 / 9) * Real.exp (-3) ≤ Real.exp (-c) := by
        have h1 : Real.exp (-3) ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos (-3 : ℝ), h1]
      linarith
    · -- c ≥ 3: split at 3
      have hsplit : (∫ u in (2 : ℝ)..c, hBJS u)
          = (∫ u in (2 : ℝ)..(3 : ℝ), hBJS u) + ∫ u in (3 : ℝ)..c, hBJS u :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hBJS_intervalIntegrable 2 3) (hBJS_intervalIntegrable 3 c)).symm
      rw [hsplit]
      have hmid : (∫ u in (2 : ℝ)..(3 : ℝ), hBJS u) = Real.exp (-2) - Real.exp (-3) := by
        have hcongr : (∫ u in (2 : ℝ)..(3 : ℝ), hBJS u)
            = ∫ u in (2 : ℝ)..(3 : ℝ), Real.exp (-u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le (by norm_num)] at hu
          exact hBJS_mid hu.1 hu.2
        rw [hcongr, integral_exp_neg]
      have htail : (∫ u in (3 : ℝ)..c, hBJS u) ≤ (8 / 9) * Real.exp (-3) := by
        have hcongr : (∫ u in (3 : ℝ)..c, hBJS u) = ∫ u in (3 : ℝ)..c, 3 * u⁻¹ * Real.exp (-u) := by
          apply intervalIntegral.integral_congr
          intro u hu
          rw [uIcc_of_le hc3] at hu
          exact hBJS_ge3 hu.1
        rw [hcongr]
        exact tail_parts_bound c hc3
      rw [hmid]
      linarith [htail]

/-- The sharp crossing bound (BJS's `H`-slack refinement): for `a ≤ 2`,
`∫_a^c h ≤ e⁻²(3−a) − (1/9)e⁻³`.  Sharpens `StepBound.hBJS_intbound_cross`. -/
theorem hBJS_intbound_cross_sharp (a c : ℝ) (ha : a ≤ 2) :
    (∫ u in a..c, hBJS u) ≤ Real.exp (-2) * (3 - a) - (1 / 9) * Real.exp (-3) := by
  have hsplit : (∫ u in a..c, hBJS u)
      = (∫ u in a..(2 : ℝ), hBJS u) + ∫ u in (2 : ℝ)..c, hBJS u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hBJS_intervalIntegrable a 2) (hBJS_intervalIntegrable 2 c)).symm
  rw [hsplit]
  have hflat : (∫ u in a..(2 : ℝ), hBJS u) = Real.exp (-2) * (2 - a) := by
    have hcongr : (∫ u in a..(2 : ℝ), hBJS u) = ∫ _u in a..(2 : ℝ), Real.exp (-2) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le ha] at hu
      exact hBJS_le2 hu.2
    rw [hcongr, intervalIntegral.integral_const]; simp; ring
  rw [hflat]
  have hhi := hBJS_intbound_from2_sharp c
  have key : Real.exp (-2) * (2 - a) + (Real.exp (-2) - (1 / 9) * Real.exp (-3))
      = Real.exp (-2) * (3 - a) - (1 / 9) * Real.exp (-3) := by ring
  linarith [hhi, key]

/-- **E₁a — the sharp `hBJS` functional integral bound** (BJS `H(s) ≤ κ₃·s·h(s)` at
`κ₃ = 49/50`).  For `s ≥ 2` and any upper limit `c`, `∫_{s−1}^c h(u) du ≤ (49/50)·s·h(s)`.
Same statement shape as `StepBound.hBJS_funcbound` (the `κ₃ = 1` version) with `κ₃ < 1`, the
contraction constant E₁b's τ-recursion needs. -/
theorem hBJS_funcbound_sharp (s c : ℝ) (hs : 2 ≤ s) :
    (∫ u in (s - 1)..c, hBJS u) ≤ (49 / 50) * s * hBJS s := by
  rcases le_total s 3 with h3 | h3
  · -- band 2 ≤ s ≤ 3: sharp crossing + Padé, closing at 49/50 since `e ≤ 25/9`
    have hcross := hBJS_intbound_cross_sharp (s - 1) c (by linarith)
    rw [hBJS_mid hs h3]
    have hpade : (4 - s) * Real.exp (s - 2) ≤ s := by
      have h := exp_pade_upper (x := s - 2) (by linarith) (by linarith)
      have e1 : (2 - (s - 2)) = 4 - s := by ring
      have e2 : (2 + (s - 2)) = s := by ring
      rw [e1, e2] at h; exact h
    have hexp_ge : s - 1 ≤ Real.exp (s - 2) := by
      have := Real.add_one_le_exp (s - 2); linarith
    have hEm : (9 : ℝ) / 25 ≤ Real.exp (-1) := by
      have hmul : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
      nlinarith [hmul, Real.exp_one_lt_d9, Real.exp_pos (1 : ℝ), Real.exp_pos (-1 : ℝ)]
    have hprod : (9 / 25) * (s - 1) ≤ Real.exp (-1) * Real.exp (s - 2) :=
      mul_le_mul hEm hexp_ge (by linarith) (Real.exp_pos _).le
    have hreduced : (4 - s) * Real.exp (s - 2) - (1 / 9) * (Real.exp (-1) * Real.exp (s - 2))
        ≤ (49 / 50) * s := by nlinarith [hpade, hprod, hs]
    have e2id : Real.exp (-2) = Real.exp (s - 2) * Real.exp (-s) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3id : Real.exp (-3) = Real.exp (-1) * Real.exp (s - 2) * Real.exp (-s) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hkey : Real.exp (-2) * (4 - s) - (1 / 9) * Real.exp (-3)
        ≤ (49 / 50) * s * Real.exp (-s) := by
      calc Real.exp (-2) * (4 - s) - (1 / 9) * Real.exp (-3)
          = ((4 - s) * Real.exp (s - 2) - (1 / 9) * (Real.exp (-1) * Real.exp (s - 2)))
              * Real.exp (-s) := by rw [e2id, e3id]; ring
        _ ≤ (49 / 50) * s * Real.exp (-s) :=
            mul_le_mul_of_nonneg_right hreduced (Real.exp_pos _).le
    calc (∫ u in (s - 1)..c, hBJS u)
        ≤ Real.exp (-2) * (3 - (s - 1)) - (1 / 9) * Real.exp (-3) := hcross
      _ = Real.exp (-2) * (4 - s) - (1 / 9) * Real.exp (-3) := by ring
      _ ≤ (49 / 50) * s * Real.exp (-s) := hkey
  · -- tail s ≥ 3: the crude decay bound already beats 49/50 (`e/3 ≈ 0.906`)
    have hhi := hBJS_intbound_hi (s - 1) c (by linarith)
    rw [hBJS_ge3 h3]
    have hs0 : s ≠ 0 := (show (0 : ℝ) < s by linarith).ne'
    have hval : (49 / 50) * s * (3 * s⁻¹ * Real.exp (-s)) = (147 / 50) * Real.exp (-s) := by
      rw [show (49 : ℝ) / 50 * s * (3 * s⁻¹ * Real.exp (-s))
          = 147 / 50 * (s * s⁻¹) * Real.exp (-s) from by ring, mul_inv_cancel₀ hs0]
      ring
    rw [hval]
    calc (∫ u in (s - 1)..c, hBJS u) ≤ Real.exp (-(s - 1)) := hhi
      _ = Real.exp 1 * Real.exp (-s) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ (147 / 50) * Real.exp (-s) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          have := Real.exp_one_lt_d9; linarith

end Salt.Chen
