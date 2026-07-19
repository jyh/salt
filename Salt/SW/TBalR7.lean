/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.TBalCompose
import Salt.SW.DHBalance

/-!
# T-BAL THE COMPOSE — R7 : the balance `dh_balance`

The support-native master (`docs/exploration/tbal-s0-freeze.md`:11, AMENDMENT 1) reads
`3/4 ≤ 2·x^{β₀−σ}·[u·X₁·ln x + 1/x + E(β₀)] + 4·u·x^{1−σ}·L₂/c₀ + E(ρ)`. Here we assemble the
**balance** — a lower bound `Λ ≤ L(1,χ).re` — from the two landed detector extractions:

* **the floor** (`dhW_detector_floor_rho`): the `ρ`-detector's `n = 1` term is `1 − 1/Y`; the
  real part of the whole detector is `≥ (1 − 1/Y) − S₀`, `S₀` the shifted `σ`-tail, so
  `1 − 1/Y ≤ ‖D_ρ‖ + S₀`;
* **R1** (`tail_shift_to_beta0`, the T-BAL-UNORDERED `σ ≤ β₀` deviation): `S₀ ≤ Y^{β₀−σ}·(D₀^{β₀}
  − (1 − 1/Y))`;
* **the β₀-side** (`dh_extraction_upper_W` + the `H_lower`/`selberg_opt_eq` cancellation, exactly
  as in `dh_balance_beta0_real`): `D₀^{β₀} ≤ Y^{1−β₀} + E(β₀)`;
* **the ρ-side** (`dh_extraction_upper_rho` + `norm_LFunction_one_eq_re`): `‖D_ρ‖ ≤ ‖main_ρ‖ +
  E(ρ)`, `‖main_ρ‖ = L(1,χ).re·selMainTerm·Y^{1−σ}/(‖1−ρ‖·‖2−ρ‖)`.

Chaining gives the master lower bound `Λ ≤ L(1,χ).re` with
`Λ = (1 − 1/Y − E(ρ) − Y^{β₀−σ}·(Y^{1−β₀} + E(β₀)))·‖1−ρ‖·‖2−ρ‖ / (selMainTerm·Y^{1−σ})`,
the input the Siegel-MVT inverter `dh_repulsion_of_LFunction_one_lower` (M4) consumes for R8.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §1 — the ρ-detector floor -/

/-- **The `selWeight` ρ-detector floor.** The complex mollified detector's `n = 1` term is the
real `1 − 1/Y` (`dhCoeffW(1) = θ₁² = 1`); its real part dominates `(1 − 1/Y) − S₀`, where `S₀` is
the shifted `σ`-tail (`σ = Re ρ`), because `|Re(a·n^{−ρ}·k)| ≤ a·n^{−σ}·k` for `a, k ≥ 0`
(`norm_dhCoeffW_term`, `dhCoeffW_nonneg`). Since `Re D_ρ ≤ ‖D_ρ‖`, `1 − 1/Y ≤ ‖D_ρ‖ + S₀`. -/
theorem dhW_detector_floor_rho [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {ρ : ℂ} (hσ0 : 0 < ρ.re) {z Y : ℕ} (hz : 1 ≤ z) (hY : 1 ≤ Y) :
    1 - 1 / (Y : ℝ)
      ≤ ‖∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
            * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)‖
        + ∑ n ∈ Finset.Icc 2 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-ρ.re)
            * dhKernR ((n : ℝ) / (Y : ℝ)) := by
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  set D : ℂ := ∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
      * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ) with hDdef
  set S0 : ℝ := ∑ n ∈ Finset.Icc 2 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-ρ.re)
      * dhKernR ((n : ℝ) / (Y : ℝ)) with hS0def
  have hins : Finset.Icc 1 Y = insert 1 (Finset.Icc 2 Y) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have h1 : (1 : ℕ) ∉ Finset.Icc 2 Y := by simp only [Finset.mem_Icc]; omega
  have hterm1 : (dhCoeffW χ (selWeight χ z) 1 : ℂ) * ((1 : ℕ) : ℂ) ^ (-ρ)
      * ((dhKernR (((1 : ℕ) : ℝ) / (Y : ℝ)) : ℝ) : ℂ) = ((1 - 1 / (Y : ℝ) : ℝ) : ℂ) := by
    rw [dhCoeffW_one, selWeight_apply_one χ hsq hz, one_pow, Nat.cast_one, Complex.one_cpow,
      dhKernR_eq (by rw [Nat.cast_one, div_le_one hYR]; exact_mod_cast hY)]
    push_cast; ring
  set T : ℂ := ∑ n ∈ Finset.Icc 2 Y, (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
      * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ) with hTdef
  have hDsplit : D = ((1 - 1 / (Y : ℝ) : ℝ) : ℂ) + T := by
    rw [hDdef, hins, Finset.sum_insert h1, hterm1, hTdef]
  have hTnorm : ‖T‖ ≤ S0 := by
    rw [hTdef, hS0def]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n hn => ?_))
    rw [Finset.mem_Icc] at hn
    rw [norm_dhCoeffW_term χ (selWeight χ z) (Y : ℝ) hσ0 (by omega : 1 ≤ n),
      abs_of_nonneg (dhCoeffW_nonneg χ hsq _ (by omega))]
  have hReD : D.re = (1 - 1 / (Y : ℝ)) + T.re := by
    rw [hDsplit, Complex.add_re, Complex.ofReal_re]
  have hReT : -S0 ≤ T.re := by
    have habs := (abs_le.mp (Complex.abs_re_le_norm T)).1
    linarith [hTnorm]
  have hDreS0 : 1 - 1 / (Y : ℝ) - S0 ≤ D.re := by rw [hReD]; linarith [hReT]
  have hDre_norm : D.re ≤ ‖D‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm D)
  linarith [hDreS0, hDre_norm]

/-! ## §2 — R7 : the balance `dh_balance` → `Λ ≤ L(1,χ).re` -/

set_option maxHeartbeats 1600000 in
-- The master lower bound assembles the floor + R1 shift + β₀-cancellation + ρ-norm; the
-- rearrangement over the `(1−ρ)(2−ρ)`/selMainTerm denominators exceeds the default budget.
/-- **R7 (`dh_balance`) — the master lower bound `Λ ≤ L(1,χ).re`.** For a real primitive `χ`
mod `q ≥ 2` at a real zero `β₀` (`1/2 ≤ β₀ < 1`) and a zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`,
`Re ρ ≤ β₀`), under the `H_lower` deep-regime guards (`hN`/`hscale`/`hguard`/`hcov` at the Siegel
scale) and the detector length `2z⁴ ≤ Y`, the balance chain
(`dhW_detector_floor_rho` → `tail_shift_to_beta0` → `dh_extraction_upper_W` + the
`H_lower`/`selberg_opt_eq` cancellation → `dh_extraction_upper_rho` + `norm_LFunction_one_eq_re`)
gives `Λ ≤ (L(1,χ)).re`, where `Λ` is the master bracket `1 − 1/Y − E(ρ) − Y^{β₀−σ}(Y^{1−β₀} +
E(β₀))` scaled by `‖1−ρ‖·‖2−ρ‖ / (selMainTerm·Y^{1−σ})`. The Deuring–Heilbronn residual, ready for
the Siegel-MVT inverter `dh_repulsion_of_LFunction_one_lower` (M4). -/
theorem dh_balance [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzeroβ : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hloβ : 1 / 2 ≤ β₀) (hhiβ : β₀ < 1)
    {ρ : ℂ} (hzeroρ : DirichletCharacter.LFunction χ ρ = 0) (hloρ : 1 / 2 ≤ ρ.re) (hhiρ : ρ.re < 1)
    (himρ : |ρ.im| ≤ 1) (hord : ρ.re ≤ β₀)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {N : ℕ} (hN : 4 ≤ N) (hscale : (N : ℝ) ^ (1 - β₀) ≤ Real.exp 1)
    (hguard : 2 * (34 + 12 * (Real.sqrt q * (1 + Real.log q))
        + 12 * (Real.sqrt q * (1 + Real.log q)) * Z₀
        + 36 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (N : ℝ) ^ (1 / 2 - β₀) ≤ 1 / 64)
    {z Y : ℕ} (hz : 2 ≤ z) (hY : 2 * z ^ 4 ≤ Y)
    (hcov : crushErr q Z₀ β₀ z ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀))) :
    (1 - 1 / (Y : ℝ)
        - C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - ρ.re)
        - (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀)
            + (136 + 48 * (Real.sqrt q * (1 + Real.log q))
                + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
                + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
              * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀)))
      * ‖1 - ρ‖ * ‖2 - ρ‖ / (selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re))
      ≤ (DirichletCharacter.LFunction χ 1).re := by
  set L₁re : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1re
  set Eβ : ℝ := (136 + 48 * (Real.sqrt q * (1 + Real.log q))
      + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
      + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
    * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀) with hEβ
  set Eρ : ℝ := C2Rho q Z₀ ρ * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9
    * (Y : ℝ) ^ (1 / 2 - ρ.re) with hEρ
  have hσ0 : 0 < ρ.re := by linarith
  have hσu : 0 < 1 - ρ.re := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hz1 : 1 ≤ z := by omega
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY1
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhiρ; simp at hhiρ
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have h2npos : 0 < ‖2 - ρ‖ := norm_pos_iff.mpr h2ρne
  have hselM : 0 < selMainTerm χ z := by
    rw [selberg_opt_eq χ hsq hz1]; exact one_div_pos.mpr (selHSum_pos χ hsq hz1)
  have hYσ : (0 : ℝ) < (Y : ℝ) ^ (1 - ρ.re) := Real.rpow_pos_of_pos hYpos _
  -- coefficient facts
  have hcnn : ∀ n, 0 ≤ dhCoeffW χ (selWeight χ z) n := by
    intro n; rcases eq_or_ne n 0 with rfl | hn
    · simp [dhCoeffW, dhWeightSqW, dhA]
    · exact dhCoeffW_nonneg χ hsq _ hn
  have hc1 : dhCoeffW χ (selWeight χ z) 1 = 1 := by
    rw [dhCoeffW_one, selWeight_apply_one χ hsq hz1, one_pow]
  -- the floor : 1 − 1/Y ≤ ‖D_ρ‖ + S₀
  have hfloor := dhW_detector_floor_rho χ hsq hσ0 hz1 hY1
  -- R1 : S₀ ≤ Y^{β₀−σ}·(D₀^{β₀} − (1−1/Y))
  have hshift := tail_shift_to_beta0 (c := dhCoeffW χ (selWeight χ z)) hcnn hc1
    (x := (Y : ℝ)) (by exact_mod_cast hY1) (N := Y) hY1 (σ := ρ.re) (β₀ := β₀) hord
  -- β₀-side : D₀^{β₀} ≤ Y^{1−β₀} + E(β₀)
  have hR6β := dh_extraction_upper_W χ hχ hsq hq hzeroβ hloβ hhiβ hZ hz1 hY
  have hHl := H_lower χ hχ hsq hq hzeroβ hloβ hhiβ hZ hN hscale hguard hz hcov
  have hopt := selberg_opt_eq χ hsq hz1
  have hHpos := selHSum_pos χ hsq hz1
  have hYβrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - β₀) := Real.rpow_nonneg hYpos.le _
  have hcancel : L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
      ≤ (Y : ℝ) ^ (1 - β₀) := by
    rw [hopt]
    have hrw : L₁re * (1 / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
        = (L₁re / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) := by field_simp
    rw [hrw]
    calc (L₁re / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀)
        ≤ 1 * (Y : ℝ) ^ (1 - β₀) :=
          mul_le_mul_of_nonneg_right ((div_le_one hHpos).mpr hHl) hYβrp
      _ = (Y : ℝ) ^ (1 - β₀) := one_mul _
  have hD0β : ∑ n ∈ Finset.Icc 1 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀)
        * dhKernR ((n : ℝ) / (Y : ℝ))
      ≤ (Y : ℝ) ^ (1 - β₀) + Eβ := by
    rw [← hL1re, ← hEβ] at *
    linarith [(abs_le.mp hR6β).2, hcancel]
  -- combine R1 + β₀ : S₀ ≤ Y^{β₀−σ}·(Y^{1−β₀} + E(β₀))
  have hYβσ : (0 : ℝ) ≤ (Y : ℝ) ^ (β₀ - ρ.re) := Real.rpow_nonneg hYpos.le _
  have hYinv : 0 ≤ 1 - 1 / (Y : ℝ) := by
    rw [sub_nonneg, div_le_one hYpos]; exact_mod_cast hY1
  have hSshift : ∑ n ∈ Finset.Icc 2 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-ρ.re)
        * dhKernR ((n : ℝ) / (Y : ℝ))
      ≤ (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) + Eβ) := by
    calc ∑ n ∈ Finset.Icc 2 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-ρ.re)
            * dhKernR ((n : ℝ) / (Y : ℝ))
        ≤ (Y : ℝ) ^ (β₀ - ρ.re)
            * ((∑ n ∈ Finset.Icc 1 Y, dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀)
                * dhKernR ((n : ℝ) / (Y : ℝ))) - (1 - 1 / (Y : ℝ))) := hshift
      _ ≤ (Y : ℝ) ^ (β₀ - ρ.re) * (((Y : ℝ) ^ (1 - β₀) + Eβ) - (1 - 1 / (Y : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith [hD0β]) hYβσ
      _ ≤ (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) + Eβ) :=
          mul_le_mul_of_nonneg_left (by linarith [hYinv]) hYβσ
  -- ρ-side : ‖D_ρ‖ ≤ ‖main_ρ‖ + E(ρ), with ‖main_ρ‖ computed
  have hR6ρ := dh_extraction_upper_rho χ hχ hsq hq hzeroρ hloρ hhiρ himρ hZ hz1 hY
  rw [← hEρ] at hR6ρ
  have hmain_norm : ‖DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ)
        / ((1 - ρ) * (2 - ρ))‖
      = L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_LFunction_one_eq_re χ hne hsq, ← hL1re,
      show ‖(selMainTerm χ z : ℂ)‖ = selMainTerm χ z from by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hselM.le],
      show ‖(Y : ℂ) ^ (1 - ρ)‖ = (Y : ℝ) ^ (1 - ρ.re) from by
        rw [show (Y : ℂ) = ((Y : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
        rw [Complex.sub_re, Complex.one_re]]
  have hDρnorm : ‖∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ) * (n : ℂ) ^ (-ρ)
        * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ)‖
      ≤ L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) + Eρ := by
    have htri := norm_sub_norm_le (∑ n ∈ Finset.Icc 1 Y, (dhCoeffW χ (selWeight χ z) n : ℂ)
        * (n : ℂ) ^ (-ρ) * ((dhKernR ((n : ℝ) / (Y : ℝ)) : ℝ) : ℂ))
      (DirichletCharacter.LFunction χ 1 * (selMainTerm χ z : ℂ) * (Y : ℂ) ^ (1 - ρ)
        / ((1 - ρ) * (2 - ρ)))
    rw [hmain_norm] at htri
    linarith [htri, hR6ρ]
  -- KEY : the master bracket ≤ ‖main_ρ‖
  have hkey : (1 - 1 / (Y : ℝ) - Eρ - (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) + Eβ))
      ≤ L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) / (‖1 - ρ‖ * ‖2 - ρ‖) := by
    linarith [hfloor, hSshift, hDρnorm]
  -- divide out ‖1−ρ‖‖2−ρ‖/(selMainTerm·Y^{1−σ})
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re))]
  have hmul := mul_le_mul_of_nonneg_right hkey
    (by positivity : (0 : ℝ) ≤ ‖1 - ρ‖ * ‖2 - ρ‖)
  rw [div_mul_cancel₀ _ (by positivity : ‖1 - ρ‖ * ‖2 - ρ‖ ≠ 0)] at hmul
  calc (1 - 1 / (Y : ℝ) - Eρ - (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) + Eβ))
          * ‖1 - ρ‖ * ‖2 - ρ‖
      = (1 - 1 / (Y : ℝ) - Eρ - (Y : ℝ) ^ (β₀ - ρ.re) * ((Y : ℝ) ^ (1 - β₀) + Eβ))
          * (‖1 - ρ‖ * ‖2 - ρ‖) := by ring
    _ ≤ L₁re * selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re) := hmul
    _ = L₁re * (selMainTerm χ z * (Y : ℝ) ^ (1 - ρ.re)) := by ring

end Salt.SW

end
