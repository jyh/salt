/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TwinA2
import Salt.Chen.SuperClose
import Salt.Chen.AbelPass2

/-!
# A2W — the F-weighted A₂ aggregation (catch #58b's fix)

Design: `docs/blueprints/flags.md`, `2026-07-14 ★★ THE END-TO-END RE-GATE — catch #58`, the 58b
paragraph.  The landed `TwinA2.A2grid_le_envelope` bounds

  `A2grid = Σ_{p ∈ window} (1/(p−1))·Fchain (Nf p) (s_p)`,   `s_p = logRatio z (cdiv Dtot p)`

by `supF·(crude +2 envelope)` — five times the honest F-weighted value.  This file replaces that
crude sup·mass bound with the **honest** F-weighted aggregation, using the SAME mass identity that
fixed 58a (`MassLedger.Fchain_mass_ledger`).

## The route

1. **The identity substitution.**  On the A₂ grid `s_p ∈ [1,3]` the mass ledger collapses the
   Rosser chain to a scalar: `Fchain (Nf p) s_p = 1 + (3 − s_p)/s_p + M_p/s_p`, and since
   `1 + (3 − s_p)/s_p = 3/s_p`, this is `(3 + M_p)/s_p` with `M_p = A2massSum (Nf p) ∈ [0, 43/75]`
   (`SuperClose.massSum_le_A2_final`; the true value is `≤ 112618127/200000000 + 1/2880000 ≈
   0.56309`, exposed here as `massSum_le_A2_sharp` for the tight razor budget).

2. **The ceiling domination.**  `cdiv Dtot p = ⌈Dtot/p⌉ ≥ Dtot/p`, so `s_p ≥ s̃(p)` with the
   *smooth* operating point `s̃(t) = (log Dtot − log t)/log z`, hence `1/s_p ≤ w(p)` where
   `w(t) = A2weight z Dtot t = log z/(log Dtot − log t)`.  This turns the non-smooth per-prime grid
   into a smooth carrier the Abel machinery can price.

   Combining 1–2 (`A2grid_le_weighted`):
   `A2grid ≤ (3 + Cmass)·Σ_{p ∈ P} (1/(p−1))·w(p)`.

3. **The Abel pass.**  `w` is positive and increasing on `[z, y]`, so `prime_sum_abel_monotone`
   (BJS Lemma 20, increasing carrier) prices `Σ w(p)/p ≤ ∫_z^y w/(t log t) + (21/log z)·w(y)`; the
   `(p−1)`-vs-`p` gap is a `Σ w(p)/(p(p−1))` crumb.

4. **The integral.**  The change of variables `t = z^u` (mirroring
   `AbelPass2.Ifun_integral_eq_cbar`) sends `∫_z^y w/(t log t) dt` to `∫_1^η du/(u(δ − u))` with
   `δ = log Dtot/log z`, `η = log y/log z`; on the A₂ geometry `δ = 4`, `η = 8/3` this is
   `(log 6)/4` (`a2_pf_integral`, the partial-fraction antiderivative
   `(1/δ)(log u − log(δ − u))`).

The honest constant: `A2grid ≤ (3 + Cmass)·(log 6)/4 + o(1)`.  With `Cmass = 43/75`:
`(268/75)·(log 6)/4 = 1.60064` (half `0.80032`); with the sharp `0.56309`: `1.59605` (half
`0.79803`).  Both clear the razor gate (positive margin); the sharp form meets the design's
`½mainA2/X_W ≤ 0.7995` sub-budget.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset MeasureTheory intervalIntegral Set

namespace Salt.Chen

/-! ## Part A — the mass-ledger substitution and the ceiling domination (FLOOR A) -/

/-- The A₂ even-mass partial sum `M_N = Σ_{even k, 2 ≤ k < N} massE k` (the ledger scalar).  The
landed budget `SuperClose.massSum_le_A2_final` gives `M_N ≤ 43/75` for every `N`. -/
noncomputable def A2massSum (N : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range N).filter (fun k => Even k ∧ 2 ≤ k), massE k

theorem A2massSum_nonneg (N : ℕ) : 0 ≤ A2massSum N :=
  Finset.sum_nonneg (fun k _ => massE_nonneg k)

theorem A2massSum_le_final (N : ℕ) : A2massSum N ≤ 43 / 75 := massSum_le_A2_final N

/-- **The sharp A₂ even-mass budget.**  `A2massSum N ≤ 112618127/200000000 + (1/10000)/(2·12²) ≈
0.56309` for every `N` — the *achieved* super-solution value (`SuperProfileDef.Ebar_int_2_12` `=
112618127/200000000` plus the `∫_{12}^∞` cubic tail), tighter than the frozen `43/75 = 0.57333`
that `massSum_le_A2_final` exposes.  Re-derives that reduction with the sharp integral bound
(`Ebar_integral_le_sharp`), used to meet the razor's tight A₂ sub-budget. -/
theorem Ebar_integral_le_sharp : ∀ b, 2 ≤ b →
    (∫ v in (2 : ℝ)..b, Ebar v) ≤ 112618127 / 200000000 + (1 / 10000) / (2 * 12 ^ 2) := by
  intro b hb
  rcases le_or_gt b 12 with hb12 | hb12
  · have hsplit : (∫ v in (2 : ℝ)..12, Ebar v)
        = (∫ v in (2 : ℝ)..b, Ebar v) + ∫ v in b..12, Ebar v :=
      (intervalIntegral.integral_add_adjacent_intervals
        (Ebar_intervalIntegrable 2 b) (Ebar_intervalIntegrable b 12)).symm
    have htail0 : 0 ≤ ∫ v in b..12, Ebar v :=
      intervalIntegral.integral_nonneg hb12 (fun x _ => Ebar_nonneg x)
    have h212 := Ebar_int_2_12
    have hpos : (0 : ℝ) ≤ (1 / 10000) / (2 * 12 ^ 2) := by norm_num
    linarith
  · have hsplit : (∫ v in (2 : ℝ)..b, Ebar v)
        = (∫ v in (2 : ℝ)..12, Ebar v) + ∫ v in (12 : ℝ)..b, Ebar v :=
      (intervalIntegral.integral_add_adjacent_intervals
        (Ebar_intervalIntegrable 2 12) (Ebar_intervalIntegrable 12 b)).symm
    have htaileq : (∫ v in (12 : ℝ)..b, Ebar v) = ∫ v in (12 : ℝ)..b, (1 / 10000) / v ^ 3 := by
      apply intervalIntegral.integral_congr
      intro x hx; rw [Set.uIcc_of_le hb12.le] at hx; exact Ebar_tail_eq x hx.1
    have htailbd : (∫ v in (12 : ℝ)..b, (1 / 10000 : ℝ) / v ^ 3) ≤ (1 / 10000) / (2 * 12 ^ 2) :=
      tail_integral_le (by norm_num) (by norm_num) hb12.le
    have h212 := Ebar_int_2_12
    linarith

theorem massSum_le_A2_sharp (N : ℕ) :
    A2massSum N ≤ 112618127 / 200000000 + (1 / 10000) / (2 * 12 ^ 2) := by
  have hdom := superSol_dominates Ebar Obar Ebar_nonneg Obar_nonneg
    Ebar_intervalIntegrable Obar_intervalIntegrable hSE_holds hSO_holds
  have hkey : ∀ K, A2massSum (K + 1) ≤ 112618127 / 200000000 + (1 / 10000) / (2 * 12 ^ 2) := by
    intro K
    have hle2 : (2 : ℝ) ≤ (K : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) K; linarith
    simp only [A2massSum]
    rw [massE_sum_eq K]
    calc (∫ v in (2 : ℝ)..((K : ℝ) + 2), Xe K v)
        ≤ ∫ v in (2 : ℝ)..((K : ℝ) + 2), Ebar v := by
          apply intervalIntegral.integral_mono_on hle2 (Xe_intervalIntegrable K 2 _)
            (Ebar_intervalIntegrable 2 _)
          intro v hv; exact (hdom K).1 v hv.1
      _ ≤ _ := Ebar_integral_le_sharp ((K : ℝ) + 2) hle2
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp only [A2massSum, Finset.range_zero, Finset.filter_empty, Finset.sum_empty]
    norm_num
  · have hN : N = (N - 1) + 1 := by omega
    rw [hN]; exact hkey (N - 1)

/-- **The mass-ledger collapse.**  On `s ∈ [1,3]` (and `N ≥ 1`), the whole Rosser chain is a
scalar over `s`: `Fchain N s = (3 + A2massSum N)/s`.  Immediate from
`MassLedger.Fchain_mass_ledger` (`= 1 + (3 − s)/s + M/s`) and `1 + (3 − s)/s = 3/s`. -/
theorem Fchain_eq_three_add_mass (N : ℕ) (hN : 1 ≤ N) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    Fchain N s = (3 + A2massSum N) / s := by
  have hs0 : (0 : ℝ) < s := by linarith
  rw [Fchain_mass_ledger N hN hs1 hs3, A2massSum]
  field_simp
  ring

/-- The smooth A₂ carrier `w(t) = log z/(log Dtot − log t) = 1/s̃(t)`, the reciprocal of the smooth
operating point `s̃(t) = (log Dtot − log t)/log z`.  Increasing on `[z, y]` (`t ↑ ⟹ denominator
↓`); dominates `1/s_p` because `cdiv` rounds up. -/
noncomputable def A2weight (z Dtot : ℕ) (t : ℝ) : ℝ :=
  Real.log z / (Real.log Dtot - Real.log t)

/-- `⌈D/p⌉`-monotonicity as reals: `D/p ≤ cdiv D p`.  From `p·cdiv D p ≥ D` in `ℕ`
(`cdiv D p = (D−1)/p + 1`, so `p·cdiv = (D−1) − (D−1)%p + p ≥ D`). -/
theorem cdiv_ge_real {D p : ℕ} (hp : 0 < p) (hD : 1 ≤ D) :
    (D : ℝ) / p ≤ (cdiv D p : ℝ) := by
  have hnat : D ≤ p * cdiv D p := by
    have hdm := Nat.div_add_mod (D - 1) p
    have hmod := Nat.mod_lt (D - 1) hp
    simp only [cdiv]
    -- p * ((D-1)/p + 1) = p*((D-1)/p) + p = (D-1) - (D-1)%p + p
    have : p * ((D - 1) / p + 1) = p * ((D - 1) / p) + p := by ring
    omega
  rw [div_le_iff₀ (by exact_mod_cast hp)]
  calc (D : ℝ) ≤ (p * cdiv D p : ℕ) := by exact_mod_cast hnat
    _ = (cdiv D p : ℝ) * p := by push_cast; ring

/-- **The per-prime domination `1/s_p ≤ w(p)`.**  For `z ≥ 2`, `p ≥ 2`, `p < Dtot` (so
`log(Dtot/p) > 0`), the ceiling rounding gives `s_p = logRatio z (cdiv Dtot p) ≥ s̃(p)`, hence
`1/s_p ≤ w(p)`.  Also `s_p > 0`. -/
theorem inv_sp_le_weight {z Dtot p : ℕ} (hz2 : 2 ≤ z) (hp2 : 2 ≤ p) (hpD : p < Dtot) :
    1 / logRatio z (cdiv Dtot p) ≤ A2weight z Dtot p := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 2 ≤ p)
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hDpos : (0 : ℝ) < (Dtot : ℝ) := by exact_mod_cast (by omega : 0 < Dtot)
  -- log(Dtot/p) = log Dtot - log p > 0
  have hlogDp : Real.log Dtot - Real.log p = Real.log ((Dtot : ℝ) / p) := by
    rw [Real.log_div hDpos.ne' hppos.ne']
  have hDp1 : (1 : ℝ) < (Dtot : ℝ) / p := by
    rw [lt_div_iff₀ hppos, one_mul]; exact_mod_cast hpD
  have hden_pos : 0 < Real.log Dtot - Real.log p := by
    rw [hlogDp]; exact Real.log_pos hDp1
  -- cdiv ≥ Dtot/p ⟹ log(cdiv) ≥ log(Dtot/p) > 0
  have hcdiv : (Dtot : ℝ) / p ≤ (cdiv Dtot p : ℝ) := cdiv_ge_real (by omega) (by omega)
  have hcdiv_pos : (0 : ℝ) < (cdiv Dtot p : ℝ) := lt_of_lt_of_le (by positivity) hcdiv
  have hlogcdiv : Real.log Dtot - Real.log p ≤ Real.log (cdiv Dtot p) := by
    rw [hlogDp]; exact Real.log_le_log (by linarith) hcdiv
  have hlogcdiv_pos : 0 < Real.log (cdiv Dtot p) := lt_of_lt_of_le hden_pos hlogcdiv
  -- 1/s_p = log z/log(cdiv) ≤ log z/(log Dtot - log p) = w(p)
  rw [logRatio, A2weight, one_div_div]
  exact div_le_div_of_nonneg_left hlogz.le hden_pos hlogcdiv

/-- **`A2grid ≤ (3 + Cmass)·Σ (1/(p−1))·w(p)` (FLOOR A).**  The mass-ledger collapse
(`Fchain = (3 + M_p)/s_p`, `M_p ≤ Cmass`) followed by the ceiling domination (`1/s_p ≤ w(p)`).
Requires the caller-supplied window facts: every `p ∈ P` is a prime `≥ z`, `< Dtot`, its operating
point `s_p ∈ [1,3]`, and its truncation depth `Nf p ≥ 1`.  Parametric in the mass bound `Cmass`
(instantiated by `43/75` or the sharp `massSum_le_A2_sharp`). -/
theorem A2grid_le_weighted {Cmass : ℝ} (P : Finset ℕ) (z Dtot : ℕ) (Nf : ℕ → ℕ)
    (hz2 : 2 ≤ z) (hCmass : ∀ N, A2massSum N ≤ Cmass)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < (Dtot : ℝ))
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hsrange : ∀ p ∈ P, 1 ≤ logRatio z (cdiv Dtot p) ∧ logRatio z (cdiv Dtot p) ≤ 3) :
    A2grid P z Dtot Nf ≤ (3 + Cmass) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p := by
  have hCmass_nn : (0 : ℝ) ≤ Cmass := by
    have := hCmass 0; simpa [A2massSum] using this
  have h3C : (0 : ℝ) ≤ 3 + Cmass := by linarith
  rw [A2grid, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpp, hzp, hpD⟩ := hP p hp
  obtain ⟨hs1, hs3⟩ := hsrange p hp
  have hp2 : 2 ≤ p := hpp.two_le
  have hp2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpD' : p < Dtot := by exact_mod_cast hpD
  have hp1pos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hinvp1 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := by positivity
  set s := logRatio z (cdiv Dtot p) with hsdef
  have hs0 : (0 : ℝ) < s := by linarith
  -- Fchain (Nf p) s = (3 + M_p)/s ≤ (3 + Cmass)·w(p)
  have hMle : A2massSum (Nf p) ≤ Cmass := hCmass (Nf p)
  have hMnn : 0 ≤ A2massSum (Nf p) := A2massSum_nonneg (Nf p)
  have hFval : Fchain (Nf p) s = (3 + A2massSum (Nf p)) / s :=
    Fchain_eq_three_add_mass (Nf p) (hN p hp) hs1 hs3
  have hweight : 1 / s ≤ A2weight z Dtot p := inv_sp_le_weight hz2 hp2 hpD'
  have hwnn : 0 ≤ A2weight z Dtot p := le_trans (by positivity) hweight
  -- (3 + M)/s = (3+M)·(1/s) ≤ (3+Cmass)·w(p)
  have hchain : Fchain (Nf p) s ≤ (3 + Cmass) * A2weight z Dtot p := by
    rw [hFval, div_eq_mul_one_div]
    calc (3 + A2massSum (Nf p)) * (1 / s)
        ≤ (3 + Cmass) * (1 / s) := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (3 + Cmass) * A2weight z Dtot p := by
          apply mul_le_mul_of_nonneg_left hweight h3C
  calc (1 / ((p : ℝ) - 1)) * Fchain (Nf p) s
      ≤ (1 / ((p : ℝ) - 1)) * ((3 + Cmass) * A2weight z Dtot p) :=
        mul_le_mul_of_nonneg_left hchain hinvp1
    _ = (3 + Cmass) * (1 / ((p : ℝ) - 1) * A2weight z Dtot p) := by ring

/-! ## Part B — the smooth carrier `w`'s calculus (for the monotone Abel pass) -/

/-- `w'(t) = log z/(t·(log Dtot − log t)²)`, the derivative of the smooth carrier `w`.  Nonnegative
(`w` increasing) since `log z ≥ 0`, `t > 0`. -/
noncomputable def A2weight_deriv (z Dtot : ℕ) (t : ℝ) : ℝ :=
  Real.log z / (t * (Real.log Dtot - Real.log t) ^ 2)

/-- **`w`'s derivative.**  `HasDerivAt (A2weight z Dtot) (A2weight_deriv z Dtot t) t` for `t > 0`
below the level (`log t < log Dtot`).  Elementary `.div`/`.log` computation. -/
theorem A2weight_hasDerivAt {z Dtot : ℕ} {t : ℝ} (ht0 : 0 < t)
    (hden : Real.log t < Real.log Dtot) :
    HasDerivAt (A2weight z Dtot) (A2weight_deriv z Dtot t) t := by
  have hg : HasDerivAt (fun s => Real.log Dtot - Real.log s) (-t⁻¹) t := by
    simpa using (Real.hasDerivAt_log ht0.ne').const_sub (Real.log Dtot)
  have hden0 : Real.log Dtot - Real.log t ≠ 0 := by
    have : 0 < Real.log Dtot - Real.log t := by linarith
    exact this.ne'
  have hc : HasDerivAt (fun _ : ℝ => (Real.log z : ℝ)) 0 t := hasDerivAt_const t (Real.log z)
  have hdiv := hc.div hg hden0
  have hval : (0 * (Real.log Dtot - Real.log t) - Real.log z * -t⁻¹)
      / (Real.log Dtot - Real.log t) ^ 2 = A2weight_deriv z Dtot t := by
    rw [A2weight_deriv]; field_simp; ring
  rw [hval] at hdiv
  exact hdiv

/-- **`w ≥ 0`.**  On `[z, y]` (`log t < log Dtot`, `z ≥ 2`), `w(t) = log z/(log Dtot − log t)`. -/
theorem A2weight_nonneg {z Dtot : ℕ} {t : ℝ} (hz2 : 2 ≤ z) (hden : Real.log t < Real.log Dtot) :
    0 ≤ A2weight z Dtot t := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hlogz : 0 ≤ Real.log z := (Real.log_pos hz1).le
  rw [A2weight]
  apply div_nonneg hlogz
  linarith

/-- **`w' ≥ 0`** (`w` increasing).  `log z ≥ 0`, `t > 0`, square `≥ 0`. -/
theorem A2weight_deriv_nonneg {z Dtot : ℕ} {t : ℝ} (hz1 : 1 ≤ z) (ht0 : 0 < t) :
    0 ≤ A2weight_deriv z Dtot t := by
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1R
  rw [A2weight_deriv]
  positivity

/-- Interval-integrability of `w'` on `[zR, yR]` (denominators bounded away from `0`). -/
theorem A2weight_deriv_intervalIntegrable {z Dtot : ℕ} {zR yR : ℝ}
    (hz0 : 0 < zR) (hzy : zR ≤ yR) (hyD : Real.log yR < Real.log Dtot) :
    IntervalIntegrable (A2weight_deriv z Dtot) MeasureTheory.volume zR yR := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hzy]
  have hmem : ∀ t ∈ Set.Icc zR yR, 0 < t ∧ Real.log t < Real.log Dtot := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact ⟨ht0, lt_of_le_of_lt (Real.log_le_log ht0 ht.2) hyD⟩
  have hlogcont : ContinuousOn Real.log (Set.Icc zR yR) :=
    Real.continuousOn_log.mono (fun t ht => (hmem t ht).1.ne')
  have hden_cont : ContinuousOn (fun t => Real.log Dtot - Real.log t) (Set.Icc zR yR) :=
    continuousOn_const.sub hlogcont
  have hden_ne : ∀ t ∈ Set.Icc zR yR, (Real.log Dtot - Real.log t) ^ 2 ≠ 0 := by
    intro t ht
    obtain ⟨_, hlt⟩ := hmem t ht
    have hp : (0 : ℝ) < Real.log Dtot - Real.log t := by linarith
    exact pow_ne_zero 2 hp.ne'
  change ContinuousOn (fun t => Real.log z / (t * (Real.log Dtot - Real.log t) ^ 2))
    (Set.Icc zR yR)
  apply continuousOn_const.div
  · exact continuousOn_id.mul (hden_cont.pow 2)
  · intro t ht
    obtain ⟨ht0, _⟩ := hmem t ht
    exact mul_ne_zero ht0.ne' (hden_ne t ht)

/-! ## Part C — the partial-fraction integral and the change of variables -/

/-- **The A₂ partial-fraction integral.**  `∫_1^{8/3} (u(4 − u))⁻¹ du = (log 6)/4`.  Antiderivative
`F(u) = (1/4)(log u − log(4 − u))` (the `δ = 4` case of `(1/δ)(log u − log(δ − u))`); the endpoint
values collapse to `(1/4)(log 2 + log 3) = (log 6)/4`.  Mirrors `AbelPass2.inner_pf_integral`. -/
theorem a2_pf_integral :
    ∫ u in (1 : ℝ)..(8 / 3), (u * (4 - u))⁻¹ = Real.log 6 / 4 := by
  have hpos : ∀ u ∈ Set.uIcc (1 : ℝ) (8 / 3), (0 : ℝ) < u ∧ (0 : ℝ) < 4 - u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 8 / 3), Set.mem_Icc] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hderiv : ∀ u ∈ Set.uIcc (1 : ℝ) (8 / 3),
      HasDerivAt (fun s => (4 : ℝ)⁻¹ * (Real.log s - Real.log (4 - s)))
        ((u * (4 - u))⁻¹) u := by
    intro u hu
    obtain ⟨hu0, h4u0⟩ := hpos u hu
    have hd1 : HasDerivAt (fun s : ℝ => Real.log s) u⁻¹ u := Real.hasDerivAt_log hu0.ne'
    have hinner : HasDerivAt (fun s : ℝ => 4 - s) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (4 : ℝ)
    have hd2 : HasDerivAt (fun s : ℝ => Real.log (4 - s)) ((4 - u)⁻¹ * (-1)) u :=
      (Real.hasDerivAt_log h4u0.ne').comp u hinner
    have hF := (hd1.sub hd2).const_mul (4 : ℝ)⁻¹
    have hval : (4 : ℝ)⁻¹ * (u⁻¹ - (4 - u)⁻¹ * (-1)) = (u * (4 - u))⁻¹ := by
      rw [mul_inv]; field_simp; ring
    rwa [hval] at hF
  have hcont : ContinuousOn (fun u : ℝ => (u * (4 - u))⁻¹) (Set.uIcc (1 : ℝ) (8 / 3)) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro u hu; obtain ⟨hu0, h4u0⟩ := hpos u hu; positivity
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [hkey]
  -- endpoint arithmetic: (1/4)[(log(8/3) - log(4/3)) - (log 1 - log 3)] = (log 6)/4
  have e1 : (4 : ℝ) - 8 / 3 = 4 / 3 := by norm_num
  have e2 : (4 : ℝ) - 1 = 3 := by norm_num
  have hl2 : Real.log (8 / 3 : ℝ) - Real.log (4 / 3 : ℝ) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  have hl6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [e1, e2, Real.log_one, hl2, hl6]
  ring

/-- **The A₂ change of variables.**  On the geometry `log Dtot = 4 log z`, `log yR = (8/3) log z`,
the monotone substitution `t = exp(u·log z)` (so `t = z^u`) maps `[z, yR]` to `[1, 8/3]` and
collapses the integrand to `(u(4 − u))⁻¹`; hence

  `∫_z^{yR} w(t)/(t log t) dt = (log 6)/4`.

Mirrors `AbelPass2.Ifun_integral_eq_cbar`.  (The geometry `log Dtot = 4 log z` idealises
`Dtot = z^4`; the realistic Chen instance carries `O(1/log z)` geometry corrections absorbed at the
razor threshold, per the re-gate's ε-slack accounting.) -/
theorem A2weight_integral_eq {z Dtot : ℕ} {yR : ℝ} (hz1 : 1 < (z : ℝ)) (hyR0 : 0 < yR)
    (hLD : Real.log Dtot = 4 * Real.log z) (hLy : Real.log yR = 8 / 3 * Real.log z) :
    (∫ t in (z : ℝ)..yR, A2weight z Dtot t / (t * Real.log t)) = Real.log 6 / 4 := by
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  set φ : ℝ → ℝ := fun u => Real.exp (u * Real.log z) with hφ
  set φ' : ℝ → ℝ := fun u => Real.exp (u * Real.log z) * Real.log z with hφ'
  have hφderiv : ∀ u : ℝ, HasDerivAt φ (φ' u) u := by
    intro u
    have h1 : HasDerivAt (fun s : ℝ => s * Real.log z) (Real.log z) u := by
      simpa using (hasDerivAt_id u).mul_const (Real.log z)
    simpa [hφ, hφ'] using h1.exp
  have hφ1 : φ 1 = (z : ℝ) := by
    rw [hφ]; simp only [one_mul]; exact Real.exp_log hzpos
  have hφ83 : φ (8 / 3) = yR := by
    rw [hφ]; simp only
    rw [show (8 / 3 : ℝ) * Real.log z = Real.log yR by rw [hLy]]
    exact Real.exp_log hyR0
  have hcov := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := φ) (f' := φ') (g := fun t => A2weight z Dtot t / (t * Real.log t))
    (a := 1) (b := 8 / 3)
    (Continuous.continuousOn (by rw [hφ]; fun_prop))
    (fun x _ => hφderiv x)
    (fun x _ => by rw [hφ']; positivity)
  rw [hφ1, hφ83] at hcov
  rw [← hcov]
  rw [intervalIntegral.integral_congr (g := fun u => (u * (4 - u))⁻¹) ?_]
  · exact a2_pf_integral
  · -- the pointwise integrand identity `(g ∘ φ) u · φ' u = (u(4 − u))⁻¹`
    intro u hu
    obtain ⟨hu1, hu83⟩ : (1 : ℝ) ≤ u ∧ u ≤ 8 / 3 := by
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 8 / 3), Set.mem_Icc] at hu; exact hu
    have hu0 : (0 : ℝ) < u := by linarith
    have h4u : (0 : ℝ) < 4 - u := by linarith
    have hEpos : (0 : ℝ) < Real.exp (u * Real.log z) := Real.exp_pos _
    have hlogexp : Real.log (Real.exp (u * Real.log z)) = u * Real.log z := Real.log_exp _
    have hEne : Real.exp (u * Real.log z) ≠ 0 := hEpos.ne'
    simp only [Function.comp, hφ, hφ', A2weight, hlogexp, hLD]
    rw [eq_comm, show (4 : ℝ) * Real.log z - u * Real.log z = (4 - u) * Real.log z by ring]
    field_simp

/-- **Application A₂ — the monotone Abel pass on the smooth carrier `w`.**  On the A₂ geometry, the
increasing carrier `w` is priced by `prime_sum_abel_monotone` (BJS Lemma 20):

  `Σ_{p ∈ [z,yR) prime} w(p)/p ≤ (log 6)/4 + (21/log z)·w(yR)`.

The four calculus hypotheses are Part B's package (`A2weight_hasDerivAt`,
`A2weight_deriv_intervalIntegrable`, `A2weight_nonneg`, `A2weight_deriv_nonneg`); the integral is
`A2weight_integral_eq`. -/
theorem applicationA2 {z Dtot : ℕ} {yR : ℝ} (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR)
    (hyR0 : 0 < yR) (hLD : Real.log Dtot = 4 * Real.log z)
    (hLy : Real.log yR = 8 / 3 * Real.log z) :
    ∑ p ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR, A2weight z Dtot p / p
      ≤ Real.log 6 / 4 + (21 / Real.log z) * A2weight z Dtot yR := by
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hz2R : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  -- on `[z, yR]`: `0 < t` and `log t < log Dtot`
  have hbounds : ∀ t ∈ Set.Icc (z : ℝ) yR, 0 < t ∧ Real.log t < Real.log Dtot := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    refine ⟨ht0, ?_⟩
    calc Real.log t ≤ Real.log yR := Real.log_le_log ht0 ht.2
      _ = 8 / 3 * Real.log z := hLy
      _ < 4 * Real.log z := by linarith
      _ = Real.log Dtot := hLD.symm
  have hyD : Real.log yR < Real.log Dtot := by
    rw [hLy, hLD]; linarith
  have habel := prime_sum_abel_monotone (w := (z : ℝ)) (z := yR) hz2R hzy
    (f := A2weight z Dtot) (f' := A2weight_deriv z Dtot)
    (fun t ht => A2weight_hasDerivAt (hbounds t ht).1 (hbounds t ht).2)
    (A2weight_deriv_intervalIntegrable hzpos hzy hyD)
    (fun t ht => A2weight_nonneg hz2 (hbounds t ht).2)
    (fun t ht => A2weight_deriv_nonneg (by omega : 1 ≤ z) (hbounds t ht).1)
  rw [A2weight_integral_eq hz1 hyR0 hLD hLy] at habel
  exact habel

/-! ## Part D — the aggregation and the sharp A₂ bound (FULL) -/

/-- **`w` monotone (denominator form).**  `log t ≤ log yR < log Dtot ⟹ w(t) ≤ w(yR)` (the
denominator `log Dtot − log t` is `≥ log Dtot − log yR > 0`). -/
theorem A2weight_le_of_log_le {z Dtot : ℕ} {t yR : ℝ} (hz1 : 1 ≤ z)
    (htyR : Real.log t ≤ Real.log yR) (hyD : Real.log yR < Real.log Dtot) :
    A2weight z Dtot t ≤ A2weight z Dtot yR := by
  have hz1R : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz1R
  have hdyR : 0 < Real.log Dtot - Real.log yR := by linarith
  rw [A2weight, A2weight]
  exact div_le_div_of_nonneg_left hlogz hdyR (by linarith)

/-- The value at the top endpoint: on the A₂ geometry `w(yR) = 3/4` (`log Dtot − log yR =
(4/3) log z`).  Not needed for the bound (which keeps `w(yR)` symbolic), but records the honest
top-of-window constant. -/
theorem A2weight_top_eq {z Dtot : ℕ} {yR : ℝ} (hz1 : 1 < (z : ℝ))
    (hLD : Real.log Dtot = 4 * Real.log z) (hLy : Real.log yR = 8 / 3 * Real.log z) :
    A2weight z Dtot yR = 3 / 4 := by
  have hL : 0 < Real.log z := Real.log_pos hz1
  rw [A2weight, hLD, hLy]
  rw [show (4 : ℝ) * Real.log z - 8 / 3 * Real.log z = 4 / 3 * Real.log z by ring]
  field_simp

/-- **The sharp F-weighted A₂ bound** (catch #58b's fix, FULL).  On the A₂ geometry
(`log Dtot = 4 log z`, `log yR = (8/3) log z`) with each `p ∈ P` a prime in `[z, yR)` whose
operating point `s_p = logRatio z (cdiv Dtot p) ∈ [1,3]` and truncation depth `Nf p ≥ 1`,

  `A2grid ≤ (3 + Cmass)·((log 6)/4 + w(yR)·(21/log z + 2/(z − 1)))`.

The honest limit is `(3 + Cmass)·(log 6)/4`; with `Cmass = 43/75` this is `(268/75)·(log 6)/4 =
1.60064` (half `0.80032`), with the sharp `massSum_le_A2_sharp` value `≈ 0.56309` it is `1.59605`
(half `0.79803` ≈ the honest F-weighted value, meeting the razor's `½mainA2/X_W ≤ 0.7995`).  The
error term is `O(1/log z)` (`w(yR) = 3/4`; `A2weight_top_eq`), absorbed at the razor's `x₀`. -/
theorem A2grid_sharp_le {Cmass : ℝ} (P : Finset ℕ) (z Dtot : ℕ) (yR : ℝ) (Nf : ℕ → ℕ)
    (hz2 : 2 ≤ z) (hzy : (z : ℝ) ≤ yR) (hyR0 : 0 < yR) (hCmass : ∀ N, A2massSum N ≤ Cmass)
    (hLD : Real.log Dtot = 4 * Real.log z) (hLy : Real.log yR = 8 / 3 * Real.log z)
    (hP : ∀ p ∈ P, p.Prime ∧ (z : ℝ) ≤ (p : ℝ) ∧ (p : ℝ) < yR)
    (hN : ∀ p ∈ P, 1 ≤ Nf p)
    (hsrange : ∀ p ∈ P, 1 ≤ logRatio z (cdiv Dtot p) ∧ logRatio z (cdiv Dtot p) ≤ 3) :
    A2grid P z Dtot Nf
      ≤ (3 + Cmass) * (Real.log 6 / 4
          + A2weight z Dtot yR * (21 / Real.log z + 2 / ((z : ℝ) - 1))) := by
  have hCmass_nn : (0 : ℝ) ≤ Cmass := by
    have := hCmass 0; simpa [A2massSum] using this
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast hz2
  have hL : 0 < Real.log z := Real.log_pos hz1
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  have hz1m : (0 : ℝ) < (z : ℝ) - 1 := by linarith
  have h3C : (0 : ℝ) ≤ 3 + Cmass := by linarith
  have hyD : Real.log yR < Real.log Dtot := by rw [hLy, hLD]; linarith
  have hDge2 : 2 ≤ Dtot := by
    by_contra h
    rw [not_le] at h
    interval_cases Dtot <;>
      simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one] at hLD <;> linarith
  have hDpos : (0 : ℝ) < (Dtot : ℝ) := by exact_mod_cast (by omega : 0 < Dtot)
  have hyR_lt_D : yR < (Dtot : ℝ) := by
    have h1 := Real.exp_lt_exp.mpr hyD
    rwa [Real.exp_log hyR0, Real.exp_log hDpos] at h1
  -- `w(yR) ≥ 0`
  have hWyR_nn : 0 ≤ A2weight z Dtot yR := A2weight_nonneg hz2 hyD
  -- domination facts per prime, and `p < Dtot`
  have hpDtot : ∀ p ∈ P, (p : ℝ) < (Dtot : ℝ) := by
    intro p hp; obtain ⟨_, _, hpy⟩ := hP p hp; exact lt_trans hpy hyR_lt_D
  -- FLOOR A: A2grid ≤ (3+Cmass)·∑ (1/(p-1))·w(p)
  have hfloorA : A2grid P z Dtot Nf
      ≤ (3 + Cmass) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p := by
    apply A2grid_le_weighted P z Dtot Nf hz2 hCmass
      (fun p hp => ⟨(hP p hp).1, (hP p hp).2.1, hpDtot p hp⟩) hN hsrange
  -- aggregation: ∑ (1/(p-1))·w(p) ≤ (log6)/4 + w(yR)·(21/log z + 2/(z-1))
  have hagg : ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p
      ≤ Real.log 6 / 4 + A2weight z Dtot yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)) := by
    -- split 1/(p-1) = 1/p + 1/(p(p-1))
    have hsplit : ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p
        = (∑ p ∈ P, A2weight z Dtot p / p)
          + ∑ p ∈ P, A2weight z Dtot p / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨hpp, _, _⟩ := hP p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      field_simp
      ring
    rw [hsplit]
    -- main term: ∑ w(p)/p ≤ ∑_{primesInWindow} w(p)/p ≤ (log6)/4 + (21/log z) w(yR)
    have hPsub : P ⊆ Salt.BrunLower.primesInWindow (z : ℝ) yR := by
      intro p hp
      obtain ⟨hpp, hzp, hpy⟩ := hP p hp
      rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_ceil.mpr hpy, hpp, hzp⟩
    have hwinnn : ∀ q ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR,
        q ∉ P → 0 ≤ A2weight z Dtot q / q := by
      intro q hq _
      rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hq
      obtain ⟨hqc, hqp, hzq⟩ := hq
      have hqy : (q : ℝ) < yR := Nat.lt_ceil.mp hqc
      have hqD : Real.log q < Real.log Dtot :=
        lt_of_le_of_lt (Real.log_le_log (by exact_mod_cast hqp.pos) hqy.le) hyD
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqp.pos
      exact div_nonneg (A2weight_nonneg hz2 hqD) hqpos.le
    have hmain : ∑ p ∈ P, A2weight z Dtot p / p
        ≤ Real.log 6 / 4 + 21 / Real.log z * A2weight z Dtot yR := by
      calc ∑ p ∈ P, A2weight z Dtot p / p
          ≤ ∑ p ∈ Salt.BrunLower.primesInWindow (z : ℝ) yR, A2weight z Dtot p / p :=
            Finset.sum_le_sum_of_subset_of_nonneg hPsub hwinnn
        _ ≤ Real.log 6 / 4 + 21 / Real.log z * A2weight z Dtot yR :=
            applicationA2 hz2 hzy hyR0 hLD hLy
    -- crumb: ∑ w(p)/(p(p-1)) ≤ 2 w(yR)/(z-1)
    have hcrumb : ∑ p ∈ P, A2weight z Dtot p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ A2weight z Dtot yR * (2 / ((z : ℝ) - 1)) := by
      have hstep : ∀ p ∈ P, A2weight z Dtot p / ((p : ℝ) * ((p : ℝ) - 1))
          ≤ A2weight z Dtot yR * (2 / (p : ℝ) ^ 2) := by
        intro p hp
        obtain ⟨hpp, _, hpy⟩ := hP p hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have hpprod : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by positivity
        have hwp : A2weight z Dtot p ≤ A2weight z Dtot yR :=
          A2weight_le_of_log_le (by omega : 1 ≤ z)
            (Real.log_le_log hp0 hpy.le) hyD
        have hwpnn : 0 ≤ A2weight z Dtot p := A2weight_nonneg hz2
          (lt_of_le_of_lt (Real.log_le_log hp0 hpy.le) hyD)
        -- w(p)/(p(p-1)) ≤ w(yR)·2/p²
        rw [show A2weight z Dtot yR * (2 / (p : ℝ) ^ 2)
              = (2 * A2weight z Dtot yR) / (p : ℝ) ^ 2 by ring,
          div_le_div_iff₀ hpprod (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hwp (sq_nonneg (p : ℝ)),
          mul_nonneg hWyR_nn (by nlinarith [hp2] : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 2))]
      calc ∑ p ∈ P, A2weight z Dtot p / ((p : ℝ) * ((p : ℝ) - 1))
          ≤ ∑ p ∈ P, A2weight z Dtot yR * (2 / (p : ℝ) ^ 2) := Finset.sum_le_sum hstep
        _ = A2weight z Dtot yR * (2 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro p _; ring
        _ ≤ A2weight z Dtot yR * (2 * (1 / ((z : ℝ) - 1))) := by
            apply mul_le_mul_of_nonneg_left _ hWyR_nn
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            -- ∑_{p∈P} 1/p² ≤ 1/(z-1)
            have hPsub2 : P ⊆ Finset.Icc z ⌊yR⌋₊ := by
              intro p hp
              obtain ⟨hpp, hzp, hpy⟩ := hP p hp
              rw [Finset.mem_Icc]
              refine ⟨by exact_mod_cast hzp, Nat.le_floor hpy.le⟩
            calc ∑ p ∈ P, 1 / (p : ℝ) ^ 2
                ≤ ∑ p ∈ Finset.Icc z ⌊yR⌋₊, 1 / (p : ℝ) ^ 2 :=
                  Finset.sum_le_sum_of_subset_of_nonneg hPsub2 (fun p _ _ => by positivity)
              _ ≤ 1 / ((z : ℝ) - 1) := Salt.BrunLower.sum_one_div_sq_le hz2
        _ = A2weight z Dtot yR * (2 / ((z : ℝ) - 1)) := by ring
    -- combine main + crumb
    have := add_le_add hmain hcrumb
    calc (∑ p ∈ P, A2weight z Dtot p / p)
          + ∑ p ∈ P, A2weight z Dtot p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ (Real.log 6 / 4 + 21 / Real.log z * A2weight z Dtot yR)
          + A2weight z Dtot yR * (2 / ((z : ℝ) - 1)) := this
      _ = Real.log 6 / 4 + A2weight z Dtot yR * (21 / Real.log z + 2 / ((z : ℝ) - 1)) := by
          ring
  calc A2grid P z Dtot Nf
      ≤ (3 + Cmass) * ∑ p ∈ P, (1 / ((p : ℝ) - 1)) * A2weight z Dtot p := hfloorA
    _ ≤ (3 + Cmass) * (Real.log 6 / 4
          + A2weight z Dtot yR * (21 / Real.log z + 2 / ((z : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hagg h3C

end Salt.Chen
