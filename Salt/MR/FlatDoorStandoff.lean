/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatDoorEpsRung2
import Salt.SW.StandoffGate
import Salt.SW.StandoffCert
import Mathlib
import Salt.MR.FlatDesignBound
import Salt.Entropy.Chowla.HeadFloors

/-!
# Theorem 4.25 under the standoff, cut below `Salt.SW.siegel_theorem` (O13)

`logChowla2_epsFamily_flatDoor_floor_holds` (Theorem 4.25) reaches `Salt.SW.siegel_theorem`
through exactly two direct users in its closure (measured, `#cut_walk`, at main `7290d90c`):
`siegel_real_carve` (channels A, the `MmuChiRate` threshold, and B, the twisted rectangle's `Ks`)
and `Salt.SW.psi1AP_main_bound` (channel C, Siegel–Walfisz through `Salt.Chen.lambda_mass_lower`).

This module cuts both.  `standoff_real_carve` is `siegel_real_carve`'s statement under
`NoSiegelZerosAt cS`; channel C takes the landed `Salt.SW.siegelWalfisz_of_standoff` through
`Salt.Chen.lambda_mass_lower_of_SW`.  The 21 declarations between them and the root are re-stated
as `_of_standoff` twins: each landed statement under three leading binders `{cS} (hcS) (hSieg)`,
its landed proof verbatim with each cut child replaced by the child's twin.  No landed proof is
edited; the ledger `Salt/MR/All.lean` gains the import and the audit block.

⚠ LIMIT, beside the verdict: the certificate lines at the foot say the root REACHES NONE OF the
three Siegel names `Salt.SW.siegel_theorem` · `Salt.SW.siegel_L_one_exceptional` ·
`Salt.SW.L1_lower_siegel`, and none of the three cut nodes `Salt.MR.siegel_real_carve` ·
`Salt.SW.siegelWalfisz_holds` · `Salt.SW.psi1AP_main_bound`.  The result is CONDITIONAL on the
open hypothesis `NoSiegelZerosAt cS`, and it is not a claim that the result is effective: the
constants below it are those of the landed proofs.  The `file:line` locators in the twins'
docstrings cite the landed sources at main `56559117` and will move.  Nothing here bears on
twin primes.
-/

open private uniformCap_arc uniformCap_shuffle spine_False_core_xi_sq_uniform from
  Salt.MR.S16Uniform

noncomputable section

namespace Salt.MR

open scoped BigOperators
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

/-- **⟦THE STANDOFF CARVE⟧** `siegel_real_carve`'s statement token for token, under
`NoSiegelZerosAt cS` in place of `Salt.SW.siegel_theorem`.  The non-real arm is the landed one
(`zero_free_region_all'`, Siegel-free).  The real arm takes the standoff on the primitive
character: its conductor `f` satisfies `1 < f ≤ q`, so `β ≤ 1 − cS/log f`, and
`log f ≤ 16·f^{1/16} ≤ 16·q^{1/16}` (`log_le_rpow_div`) turns the gate `q^{1/16}·W ≤ cS/16`
into `W ≤ cS/log f`.  `K = min (min (cS/16) (c₀/32)) (1/2)`: it is explicit in `cS` and in the
landed `c₀`; nothing here claims it is computed. -/
theorem standoff_real_carve {cS : ℝ} (hcS : 0 < cS) (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ W : ℝ, 0 < W → (q : ℝ) ^ ((1 : ℝ) / 16) * W ≤ K →
      ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ.im = 0 → ρ.re ≤ 1 - W := by
  obtain ⟨c₀, hc₀0, hc₀⟩ := Salt.SW.zero_free_region_all'
  refine ⟨min (min (cS / 16) (c₀ / 32)) (1 / 2), by positivity, ?_⟩
  intro q hq χ hχ1 W hW hgate ρ hρ0 hρim
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqe1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) := Real.one_le_rpow hq1 (by norm_num)
  have hqe0 : (0 : ℝ) < (q : ℝ) ^ ((1 : ℝ) / 16) := by linarith
  have hWK : W ≤ min (min (cS / 16) (c₀ / 32)) (1 / 2) := by
    refine le_trans ?_ hgate
    nlinarith only [hW, hqe1]
  have hWhalf : W ≤ 1 / 2 := le_trans hWK (min_le_right _ _)
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
  · have hρeq : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re]
      · rw [Complex.ofReal_im, hρim]
    have hβ1 : ρ.re < 1 := by
      by_contra hge
      exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by linarith [not_lt.mp hge]) hρ0
    by_cases hsq : χ.primitiveCharacter ^ 2 = 1
    · -- REAL character: the standoff, in place of Siegel
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hprim : χ.primitiveCharacter.IsPrimitive := primitiveCharacter_isPrimitive χ
      have hχ1' : χ.primitiveCharacter ≠ 1 := fun h =>
        hχ1 (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])
      have hzero1 : LFunction χ.primitiveCharacter ρ = 0 :=
        (Salt.SW.LFunction_eq_zero_iff_primitive χ (by linarith) (Or.inl hχ1)).mp hρ0
      have hzero1' : LFunction χ.primitiveCharacter ((ρ.re : ℝ) : ℂ) = 0 := by
        rw [← hρeq]; exact hzero1
      have hcondN : 1 < χ.conductor := by
        rcases Nat.lt_or_ge 1 χ.conductor with h | h
        · exact h
        · exfalso
          have h1 : χ.conductor = 1 := by
            have := Nat.pos_of_ne_zero χ.conductor_ne_zero; omega
          exact hχ1 (eq_one_iff_conductor_eq_one.mpr h1)
      have hs := hSieg χ.conductor χ.primitiveCharacter hcondN hprim hsq hχ1' ρ.re hzero1' hβ1
      have hcond1 : (1 : ℝ) < (χ.conductor : ℝ) := by exact_mod_cast hcondN
      have hcondq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (conductor_dvd_level χ)
      have hlogf : (0 : ℝ) < Real.log (χ.conductor : ℝ) := Real.log_pos hcond1
      have hce : (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_le_rpow (by linarith) hcondq (by norm_num)
      have hlogle : Real.log (χ.conductor : ℝ) ≤ 16 * (q : ℝ) ^ ((1 : ℝ) / 16) := by
        have h := log_le_rpow_div (u := (χ.conductor : ℝ)) (ε := (1 : ℝ) / 16)
          (by linarith) (by norm_num)
        have h3 : (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) / ((1 : ℝ) / 16)
            = 16 * (χ.conductor : ℝ) ^ ((1 : ℝ) / 16) := by ring
        rw [h3] at h
        linarith
      have hgate' : (q : ℝ) ^ ((1 : ℝ) / 16) * W ≤ cS / 16 :=
        le_trans hgate (le_trans (min_le_left _ _) (min_le_left _ _))
      have hWc : W ≤ cS / Real.log (χ.conductor : ℝ) := by
        rw [le_div_iff₀ hlogf]
        have h1 : W * Real.log (χ.conductor : ℝ) ≤ W * (16 * (q : ℝ) ^ ((1 : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hlogle hW.le
        linarith only [h1, hgate']
      linarith [hs, hWc]
    · -- NON-REAL character: the effective classical region, as landed
      have hcl : ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * 2) := by
        have h := hc₀ q χ hχ1 hρ0 hre (Or.inl hsq)
        rw [hρim, abs_zero, zero_add] at h
        exact h
      have hlog2q : (0 : ℝ) < Real.log ((q : ℝ) * 2) := by
        apply Real.log_pos; linarith
      have hlogle : Real.log ((q : ℝ) * 2) ≤ 32 * (q : ℝ) ^ ((1 : ℝ) / 16) := by
        have h := log_le_rpow_div (u := (q : ℝ) * 2) (ε := (1 : ℝ) / 16)
          (by linarith) (by norm_num)
        have hsplit : ((q : ℝ) * 2) ^ ((1 : ℝ) / 16)
            = (q : ℝ) ^ ((1 : ℝ) / 16) * (2 : ℝ) ^ ((1 : ℝ) / 16) :=
          Real.mul_rpow (by linarith) (by norm_num)
        have h2 : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ 2 := by
          have hh : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rwa [Real.rpow_one] at hh
        rw [hsplit] at h
        have h3 : ((q : ℝ) ^ ((1 : ℝ) / 16) * (2 : ℝ) ^ ((1 : ℝ) / 16)) / ((1 : ℝ) / 16)
            = 16 * ((q : ℝ) ^ ((1 : ℝ) / 16) * (2 : ℝ) ^ ((1 : ℝ) / 16)) := by ring
        rw [h3] at h
        nlinarith only [hqe1, h2, h]
      have hgate' : (q : ℝ) ^ ((1 : ℝ) / 16) * W ≤ c₀ / 32 :=
        le_trans hgate (le_trans (min_le_left _ _) (min_le_right _ _))
      have hWc : W ≤ c₀ / Real.log ((q : ℝ) * 2) := by
        rw [le_div_iff₀ hlog2q]
        have h1 : W * Real.log ((q : ℝ) * 2) ≤ W * (32 * (q : ℝ) ^ ((1 : ℝ) / 16)) :=
          mul_le_mul_of_nonneg_left hlogle hW.le
        linarith only [h1, hgate']
      linarith [hcl, hWc]
  · linarith

end Salt.MR

namespace Salt.MR

section
open scoped BigOperators
open Complex DirichletCharacter
/-- **⟦STANDOFF TWIN⟧** `xiCarveWidth_of_siegel` (`Salt/MR/PortClose.lean:76`): its statement under
the three standoff binders, its proof verbatim with `siegel_real_carve` replaced by the standoff
form. -/
theorem xiCarveWidth_of_siegel_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ H₀ : ℝ, Real.exp (Real.exp 100) + 3 ≤ H₀ ∧ XiCarveWidth H₀ := by
  obtain ⟨K, hK0, hsg⟩ := (standoff_real_carve hcS hSieg)
  refine ⟨max (Real.exp (Real.exp 100) + 3) (Real.exp (Real.exp (1 / K))),
    le_max_left _ _, ?_⟩
  intro q hq χ hχ1 H hH hqH ρ hρ0 hρim
  have hχinv1 : χ⁻¹ ≠ 1 := fun h => hχ1 (by rw [← inv_inv χ, h, inv_one])
  have hH1 : Real.exp (Real.exp 100) + 3 ≤ H := le_trans (le_max_left _ _) hH
  have hH2 : Real.exp (Real.exp (1 / K)) ≤ H := le_trans (le_max_right _ _) hH
  have hEpos : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hexp100 : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hHpos : (0 : ℝ) < H := by linarith
  have hlogH100 : Real.exp 100 ≤ Real.log H := by
    rw [← Real.log_exp (Real.exp 100)]
    exact Real.log_le_log hEpos (by linarith)
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hll100 : (100 : ℝ) ≤ Real.log (Real.log H) := by
    rw [← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hlogH100
  have hllK : 1 / K ≤ Real.log (Real.log H) := by
    have h1 : Real.exp (1 / K) ≤ Real.log H := by
      rw [← Real.log_exp (Real.exp (1 / K))]
      exact Real.log_le_log (Real.exp_pos _) hH2
    have h2 := Real.log_le_log (Real.exp_pos (1 / K)) h1
    rwa [Real.log_exp] at h2
  have hW0 : 0 < vkShallowWidth (1 / 10 ^ 6) q H :=
    vkShallowWidth_pos (by norm_num) (by linarith)
  refine hsg q χ⁻¹ hχinv1 _ hW0 ?_ ρ hρ0 hρim
  -- ⟦the Siegel gate⟧ `q^{1/16}·W ≤ K`
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log H) := by linarith
  have hR1 : (1 : ℝ) ≤ Real.log H ^ ((3 : ℝ) / 4) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hqR : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ Real.log H ^ ((3 : ℝ) / 4) := by
    have h1 : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ (Real.log H ^ (12 : ℕ)) ^ ((1 : ℝ) / 16) :=
      Real.rpow_le_rpow (by linarith) hqH (by norm_num)
    have h2 : (Real.log H ^ (12 : ℕ)) ^ ((1 : ℝ) / 16) = Real.log H ^ ((3 : ℝ) / 4) := by
      rw [← Real.rpow_natCast (Real.log H) 12, ← Real.rpow_mul hlogH0.le]
      norm_num
    rwa [h2] at h1
  have hℓ3 : Real.log (Real.log H) ≤ Real.log (Real.log H) ^ (3 : ℕ) := by
    have h := pow_le_pow_right₀ hℓ1 (show 1 ≤ 3 by norm_num)
    simpa using h
  have hKℓ : (1 : ℝ) ≤ K * Real.log (Real.log H) := by
    have h1 : K * (1 / K) ≤ K * Real.log (Real.log H) :=
      mul_le_mul_of_nonneg_left hllK hK0.le
    have h0 : K * (1 / K) = 1 := by field_simp
    linarith [h0 ▸ h1]
  have hKℓ3 : (1 : ℝ) ≤ K * Real.log (Real.log H) ^ (3 : ℕ) := by
    nlinarith [hℓ3, hK0.le, hKℓ]
  have hDpos : (0 : ℝ) < (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
      * Real.log (Real.log H) ^ (3 : ℕ) := by
    have h1 : (0 : ℝ) < Real.log (q : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < Real.log H ^ ((3 : ℝ) / 4) := by linarith
    have h3 : (0 : ℝ) < Real.log (Real.log H) ^ (3 : ℕ) := by positivity
    positivity
  rw [vkShallowWidth, mul_div_assoc', div_le_iff₀ hDpos]
  have ha0 : (0 : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / 16) :=
    Real.rpow_nonneg (by linarith) _
  calc (q : ℝ) ^ ((1 : ℝ) / 16) * (1 / 10 ^ 6)
      ≤ Real.log H ^ ((3 : ℝ) / 4) := by nlinarith [hqR, ha0]
    _ ≤ (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
          * (K * Real.log (Real.log H) ^ (3 : ℕ)) := by
        have h1 : Real.log H ^ ((3 : ℝ) / 4)
            ≤ (Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4) := by
          nlinarith [hR1, hlogq]
        nlinarith [h1, hKℓ3, hR1, hlogq]
    _ = K * ((Real.log (q : ℝ) + 1) * Real.log H ^ ((3 : ℝ) / 4)
          * Real.log (Real.log H) ^ (3 : ℕ)) := by ring

end

section
open scoped BigOperators
open Complex DirichletCharacter
/-- **⟦STANDOFF TWIN⟧** `mmuChiRate_holds_gated` (`Salt/MR/PortClose.lean:157`): its statement under
the three standoff binders, its proof verbatim with `xiCarveWidth_of_siegel` replaced by the
standoff form. -/
theorem mmuChiRate_holds_gated_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) : MmuChiRate := by
  obtain ⟨H₀, hH₀, hxi⟩ := (xiCarveWidth_of_siegel_of_standoff hcS hSieg)
  exact mmuChiRate_of_carve hH₀ hxi

end

section
open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `s16_bandLaneWinL_holdsU` (`Salt/MR/S16ComposeV4.lean:100`): its statement
under the three standoff binders, its proof verbatim with `mmuChiRate_holds_gated` replaced by the
standoff form. -/
theorem s16_bandLaneWinL_holdsU_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Awin : ℝ, 162 ≤ Awin ∧ S16BandLaneCBoundedL_winU Awin := by
  obtain ⟨x₀, Cb, hCb0, hsplit⟩ :=
    m4_hband_at_door_slot_split_graded_L_gk_uniform
        (mmuChiRate_holds_gated_of_standoff hcS hSieg) s13Aexp
      (by rw [s13Aexp]; norm_num)
  set E : ℝ := (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) with hEdef
  have hE0 : (0 : ℝ) < E := by
    rw [hEdef]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ (s13Aexp) := Real.rpow_pos_of_pos (by norm_num) _
    have h1 : (0 : ℝ) < (4 : ℝ) ^ (1.05 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set Cband : ℝ := Cb / E with hCbanddef
  have hCband0 : (0 : ℝ) < Cband := div_pos hCb0 hE0
  refine ⟨max 162 ((Real.log Cband + 20) / 0.64), le_max_left _ _,
    x₀, Cband, hCband0, ?_, ?_⟩
  · -- ⟦THE WINDOW, BY CONSTRUCTION⟧
    have h := le_max_right (162 : ℝ) ((Real.log Cband + 20) / 0.64)
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 0.64)] at h
    linarith
  · intro K M hM
    obtain ⟨C', hC'0, hC'le, hbody⟩ := hsplit K M hM
    refine ⟨C', hC'0, ?_, hbody⟩
    have hid : Cband * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) = Cb := by
      rw [hCbanddef, hEdef]; field_simp
    have hMpow : (0 : ℝ) ≤ (M : ℝ) ^ (2.1 : ℝ) :=
      Real.rpow_nonneg (Nat.cast_nonneg M) _
    rw [hid]
    nlinarith [hC'le, hMpow]

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 1200000 in
-- The twin re-elaborates the landed statement with one extra conjunct, so it needs the
-- landed declaration's own heartbeat room.
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter in
open scoped LSeries.notation in
/-- **⟦STANDOFF TWIN⟧** `twisted_rect_zero_free_siegel_bounded` (`Salt/MR/NumeralKq.lean:502`): its
statement under the three standoff binders, its proof verbatim with `siegel_real_carve` replaced by
the standoff form. -/
theorem twisted_rect_zero_free_siegel_bounded_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Kq Ks : ℝ, 0 < Kq ∧ Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ (A T : ℝ), 1 ≤ A →
      Real.exp (Real.exp 100) ≤ T →
      Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 →
      A + 7 ≤ Real.log (Real.log (5 * T + 1)) →
      Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
          ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
      (q : ℝ) ^ ((1 : ℝ) / 16)
          ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ ρ : ℂ, LFunction ψ ρ = 0 → |ρ.im| ≤ 5 * T + 1 →
        ρ.re ≤ 1 - (1 / 10 ^ 8)
          / ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) := by
  obtain ⟨c₀, hc₀0, hc₀b, hc₀⟩ := Salt.SW.zero_free_region_all'_bounded
  obtain ⟨Ks, hKs0, hsg⟩ := (standoff_real_carve hcS hSieg)
  refine ⟨1 / (10 ^ 8 * c₀), 10 ^ 8 * Ks, by positivity, ?_, by positivity, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 10 ^ 8)]
    linarith only [hc₀b]
  intro q hNe ψ hψ1 A T hA1 hTfloor hAq hAabs hKq hSg ρ hρ0 hρim
  -- the `T`-scale quantities
  have hE0 : (0 : ℝ) < Real.exp (Real.exp 100) := Real.exp_pos _
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hE0 hTfloor
  have h5T : Real.exp (Real.exp 100) ≤ 5 * T + 1 := by linarith
  have h5T0 : (0 : ℝ) < 5 * T + 1 := by linarith
  have hLg100 : Real.exp 100 ≤ Real.log (5 * T + 1) := by
    have h := Real.log_le_log hE0 h5T; rwa [Real.log_exp] at h
  have hexp100 : (1 : ℝ) ≤ Real.exp 100 := by
    have := Real.add_one_le_exp (100 : ℝ); linarith
  have hLg1 : (1 : ℝ) ≤ Real.log (5 * T + 1) := by linarith
  have hLg0 : 0 < Real.log (5 * T + 1) := by linarith
  have hℓ100 : (100 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by
    have h := Real.log_le_log (Real.exp_pos 100) hLg100; rwa [Real.log_exp] at h
  have hℓ1 : (1 : ℝ) ≤ Real.log (Real.log (5 * T + 1)) := by linarith
  set Lg : ℝ := Real.log (5 * T + 1) with hLgdef
  set ℓ : ℝ := Real.log (Real.log (5 * T + 1)) with hℓdef
  have hLg34 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) := Real.one_le_rpow hLg1 (by norm_num)
  have hLg34pos : 0 < Lg ^ ((3 : ℝ) / 4) := by linarith
  have hD3pos : 0 < Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ) := by positivity
  have hD4pos : 0 < Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by positivity
  have hD4ge1 : (1 : ℝ) ≤ Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by
    have h1 : (1 : ℝ) ≤ ℓ ^ (4 : ℕ) := one_le_pow₀ hℓ1
    nlinarith only [hLg34, h1]
  -- the target width is tiny
  have hWsmall : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hD4pos (by norm_num : (0:ℝ) < 2)]
    linarith only [hD4ge1, hD4pos]
  by_cases hcase : Real.exp (Real.exp 100) + 1 ≤ |ρ.im|
  · -- ABOVE the floor: stones A+B
    have hβ1 : ρ.re < 1 := by
      by_contra hge
      exact LFunction_ne_zero_of_one_le_re ψ (Or.inl hψ1) (by linarith [not_lt.mp hge]) hρ0
    have hℓγ100 : (100 : ℝ) ≤ Real.log (Real.log |ρ.im|) := loglog_ge_hundred hcase
    have hgate : Real.log (20000 * (vkStripConst q + 8104))
        ≤ A * Real.log (Real.log |ρ.im|) := by
      have : A * 100 ≤ A * Real.log (Real.log |ρ.im|) :=
        mul_le_mul_of_nonneg_left hℓγ100 (by linarith)
      linarith
    -- the two arms deliver the same D₃-shaped width at the zero's own height
    have hstone : ρ.re ≤ 1 - (1 / (10 ^ 8 * (A + 7)))
        * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
            * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      by_cases hsq : ψ ^ 2 = 1
      · refine LFunction_real_zero_free_region_vk hψ1 hsq hA1 hρ0 hβ1 hcase ?_
        exact hgate
      · refine LFunction_zero_free_region_vk hψ1 hsq hA1 hρ0 hβ1 hcase ?_
        have hvk : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
        exact le_trans (Real.log_le_log (by linarith) (by linarith)) hgate
      -- (both arms take the SAME gate: `vkStripConst q ≤ vkStripConst q + 8104`)
    -- compare the two widths
    have hEexp1 : Real.exp 1 ≤ |ρ.im| := by
      have h1 : Real.exp 1 ≤ Real.exp (Real.exp 100) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hmono := logDn_mono 3 hEexp1 hρim
    have hDγpos : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by
      have hL1 : (1 : ℝ) ≤ Real.log |ρ.im| := by
        have h := Real.log_le_log (Real.exp_pos 1) hEexp1; rwa [Real.log_exp] at h
      have h1 : 0 < (Real.log |ρ.im|) ^ ((3 : ℝ) / 4) :=
        Real.rpow_pos_of_pos (by linarith) _
      have h2 : 0 < (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ) := by positivity
      exact mul_pos h1 h2
    have hstep1 : (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
        ≤ (1 / (10 ^ 8 * (A + 7)) : ℝ)
          * (1 / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
              * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact one_div_le_one_div_of_le hDγpos hmono
    have hstep2 : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
        ≤ (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by
      have hA7 : (0 : ℝ) < A + 7 := by linarith
      have hL : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
          = 1 / (10 ^ 8 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))) := by rw [div_div]
      have hR : (1 / (10 ^ 8 * (A + 7)) : ℝ) * (1 / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)))
          = 1 / (10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by
        rw [div_mul_div_comm, one_mul]
      have hden : (0 : ℝ) < 10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) :=
        mul_pos (mul_pos (by norm_num) hA7) hD3pos
      have hkey : (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
          ≤ Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by
        calc (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
            ≤ ℓ * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ)) :=
              mul_le_mul_of_nonneg_right hAabs hD3pos.le
          _ = Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ) := by ring
      rw [hL, hR]
      refine one_div_le_one_div_of_le hden ?_
      calc 10 ^ 8 * (A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))
          = 10 ^ 8 * ((A + 7) * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (3 : ℕ))) := by ring
        _ ≤ 10 ^ 8 * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by linarith [hkey]
    linarith [hstone, hstep1, hstep2]
  · -- BELOW the floor: the classical effective region
    rw [not_le] at hcase
    rcases le_or_gt (1 / 2 : ℝ) ρ.re with hre | hre
    · by_cases him : ρ.im = 0
      · -- THE REAL-ZERO CORNER: §7's Siegel arm gives the conclusion outright
        have hW0 : (0 : ℝ) < (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) :=
          div_pos (by norm_num) hD4pos
        have hgate : (q : ℝ) ^ ((1 : ℝ) / 16)
            * ((1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))) ≤ Ks := by
          have heq : (q : ℝ) ^ ((1 : ℝ) / 16)
              * ((1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)))
              = ((q : ℝ) ^ ((1 : ℝ) / 16) * (1 / 10 ^ 8 : ℝ))
                / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by ring
          rw [heq, div_le_iff₀ hD4pos]
          linarith only [hSg]
        exact hsg q ψ hψ1 _ hW0 hgate ρ hρ0 him
      · have hcv : ψ.primitiveCharacter ^ 2 ≠ 1 ∨ ρ.im ≠ 0 := Or.inr him
        have hcl := hc₀ q ψ hψ1 hρ0 hre hcv
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
          have := Nat.pos_of_ne_zero (NeZero.ne q); exact_mod_cast this
        have hEq : |ρ.im| + 2 ≤ Real.exp (Real.exp 100) + 3 := by linarith
        have hlow0 : 0 < Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
          apply Real.log_pos; nlinarith only [hq1, abs_nonneg ρ.im, (Nat.cast_nonneg _ : 0 ≤ ↑q)]
        have hlowle : Real.log ((q : ℝ) * (|ρ.im| + 2))
            ≤ Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
          apply Real.log_le_log (by nlinarith [abs_nonneg ρ.im])
          exact mul_le_mul_of_nonneg_left hEq (by linarith)
        have hlowE0 : 0 < Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
          linarith
        -- the gate converts the fixed classical width into the VK-shaped one
        have hkey : (1 / 10 ^ 8 : ℝ) / (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ))
            ≤ c₀ / Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3)) := by
          rw [div_le_div_iff₀ hD4pos hlowE0]
          have hgate' : Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
              ≤ 10 ^ 8 * c₀ * (Lg ^ ((3 : ℝ) / 4) * ℓ ^ (4 : ℕ)) := by
            have h := hKq
            rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h
            linarith
          linarith only [hgate']
        have hshrink : c₀ / Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)) := by
          rw [div_le_div_iff₀ hlowE0 hlow0]
          exact mul_le_mul_of_nonneg_left hlowle hc₀0.le
        linarith [hcl, hkey, hshrink]
    · linarith [hWsmall, hre]

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex MeasureTheory Set ArithmeticFunction DirichletCharacter in
open scoped LSeries.notation in
/-- **⟦STANDOFF TWIN⟧** `halasz_primes_chi_pair_of_gates_bounded_cs` (`Salt/MR/V7B.lean:1133`): its
statement under the three standoff binders, its proof verbatim with
`twisted_rect_zero_free_siegel_bounded` replaced by the standoff form. -/
theorem halasz_primes_chi_pair_of_gates_bounded_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) {C₁ C₂ C₃ T₀e : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₃ : 0 < C₃)
    (hT₀e : Real.exp (Real.exp 100) ≤ T₀e)
    (hprice : TwistedWindowPriceGated (1 / 10 ^ 8) C₁ C₂ C₃ T₀e) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C, c, T₀, hC, hc, hcf, hT₀, hgated⟩ :=
    halaszPrimesChiGated_of_price_floored (by norm_num) hC₁ hC₂ hC₃ hT₀e hprice
  obtain ⟨Kq, Ks, hKq, hKqb, hKs, hreg⟩ :=
      (twisted_rect_zero_free_siegel_bounded_of_standoff hcS hSieg)
  refine ⟨C, c, max T₀ T₀e, Kq, Ks, hC, hc, hcf, le_trans hT₀ (le_max_left _ _), hKq, hKqb,
    hKs, ?_⟩
  intro q hq T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTfloor : Real.exp (Real.exp 100) ≤ T := le_trans hT₀e (le_trans (le_max_right _ _) hT)
  -- the `A`-instantiation that makes stone C's own `hAq` free
  set A : ℝ := 1 + Real.log (20000 * (vkStripConst q + 8104)) / 100 with hAdef
  have hCq1 : (1 : ℝ) ≤ vkStripConst q := one_le_vkStripConst
  have hlogA0 : (0 : ℝ) ≤ Real.log (20000 * (vkStripConst q + 8104)) :=
    Real.log_nonneg (by linarith)
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; linarith
  have hAq : Real.log (20000 * (vkStripConst q + 8104)) ≤ A * 100 := by
    rw [hAdef]; linarith
  have hAabs : A + 7 ≤ Real.log (Real.log (5 * T + 1)) := by rw [hAdef]; linarith [hG2]
  exact hgated q T P hTT₀ hP hPT10 hG1
    (fun ψ hψ1 => hreg q ψ hψ1 A T hA1 hTfloor hAq hAabs hG3 hG4) ℰ hws hsub S hS a

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦STANDOFF TWIN⟧** `halaszPrimesChi_holds_gated_bounded_cs` (`Salt/MR/V7B.lean:1187`): its
statement under the three standoff binders, its proof verbatim with
`halasz_primes_chi_pair_of_gates_bounded_cs` replaced by the standoff form. -/
theorem halaszPrimesChi_holds_gated_bounded_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T P : ℝ), T₀ ≤ T → 2 ≤ P → P ≤ T ^ 10 →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      ∀ (ℰ : Finset (DirichletCharacter ℂ q × ℝ)), FibreWellSpaced ℰ →
        (∀ r ∈ ℰ, r.2 ∈ Set.Icc (-T) T) →
      ∀ (S : Finset ℕ), (∀ n ∈ S, n.Prime ∧ P ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * P) →
      ∀ (a : ℕ → ℂ),
        ∑ r ∈ ℰ, ‖∑ n ∈ S, (n : ℂ) ^ (-(r.2 : ℂ) * Complex.I) * chiBarCoeff q r.1 a n‖ ^ 2
          ≤ C * (P + (ℰ.card : ℝ) * P
                  * Real.exp (-c * Real.log P
                      / ((Real.log ((q : ℝ) * T)) ^ ((3 : ℝ) / 4)
                          * (Real.log (Real.log ((q : ℝ) * T))) ^ (4 : ℕ)))
                  * (Real.log ((q : ℝ) * T)) ^ 2)
              / Real.log P * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  obtain ⟨C₁, C₂, C₃, T₀e, hC₁, hC₂, hC₃, hT₀e, hprice⟩ := twisted_window_price_gated_holds
  exact (halasz_primes_chi_pair_of_gates_bounded_cs_of_standoff hcS hSieg) hC₁ hC₂ hC₃ hT₀e hprice

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 1600000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open Complex DirichletCharacter in
/-- **⟦STANDOFF TWIN⟧** `halaszPrimesChi_pointwise_of_gates_bounded_cs` (`Salt/MR/V7B.lean:1221`):
its statement under the three standoff binders, its proof verbatim with
`halaszPrimesChi_holds_gated_bounded_cs` replaced by the standoff form. -/
theorem halaszPrimesChi_pointwise_of_gates_bounded_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ C c T₀ Kq Ks : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (-100) ≤ c ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
      HalaszPrimesChi C c q T := by
  obtain ⟨C, c, T₀, Kq, Ks, hC, hc, hcf, hT₀, hKq, hKqb, hKs, hrow⟩ :=
    (halaszPrimesChi_holds_gated_bounded_cs_of_standoff hcS hSieg)
  refine ⟨C, c, T₀, Kq, Ks, hC, hc, hcf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ T hT hG1 hG2 hG3 hG4 P hP hPT10 ℰ hws hsub S hS a
  exact hrow q T P hT hP hPT10 hG1 hG2 hG3 hG4 ℰ hws hsub S hS a

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 2400000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦STANDOFF TWIN⟧** `usetGChi_window_meansq_gated_family_perBlock_bounded_cs`
(`Salt/MR/V7B.lean:1248`): its statement under the three standoff binders, its proof verbatim with
`halaszPrimesChi_pointwise_of_gates_bounded_cs` replaced by the standoff form. -/
theorem usetGChi_window_meansq_gated_family_perBlock_bounded_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cs cs T₀ Kq Ks : ℝ, 0 < Cs ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (f : ℕ → ℂ), (∀ n : ℕ, ‖f n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (T VJ V L X : ℝ), 1 ≤ T → 1 < (q : ℝ) * T →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * T →
        30 ≤ Real.log ((q : ℝ) * T) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * T)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → T ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        -- ⟦THE PER-`(q,T)` FLOOR — what the socket's discharge costs⟧
        T₀ ≤ T →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * T + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * T + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * T + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * T + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * T) → Real.log ((q : ℝ) * T) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * T) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * T) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * T) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ T ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ 𝔄 : Set (DirichletCharacter ℂ q × ℝ),
        (∀ χ : DirichletCharacter ℂ q, MeasurableSet {t : ℝ | (χ, t) ∈ 𝔄}) →
        (∀ r ∈ 𝔄, r.2 ∈ Set.Icc (-T) T) →
        𝔄 ⊆ UsetGChi q f Pseq Qseq Hseq αseq J →
        (∀ j ∈ ramI H P Q, ∀ r ∈ 𝔄,
          ‖ramR H N Xd P Q j (chiBarCoeff q r.1 b) r.2‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-T)..T,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        (∑ χ : DirichletCharacter ℂ q,
            ∫ t in {t : ℝ | (χ, t) ∈ 𝔄}, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (∑ j ∈ ramI H P Q,
                  (5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ)
                        * (1 + Real.log (2 * T))
                      * (∑ m ∈ Finset.Icc 1 (Ms j),
                          ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
                    + 81 * Cs * Rbd ^ 2 * (H / (j : ℝ)) ^ 2))
            + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, hpt⟩ :=
    (halaszPrimesChi_pointwise_of_gates_bounded_cs_of_standoff hcS hSieg)
  refine ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ f hf1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X hT1 hqT hP3 hPQ
    hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd 𝔄 hAm hAsub hUA hR E herr
  exact usetGChi_window_meansq_of_socket_family_perBlock hCs hcs q f hf1 Pseq Qseq Hseq αseq
    J Jb hJb1 hJbJ hH2seq hα0 T VJ V L X (hpt q T hT₀T hG1 hG2 hG3 hG4) hT1 hqT hP3 hPQ hQT
    hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hlogT1 hTL hLe hlogV
    H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd
    𝔄 hAm hAsub hUA hR E herr

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 2400000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦STANDOFF TWIN⟧** `usetGChi_row_exit_perChi_perBlock_bounded_cs` (`Salt/MR/V7B.lean:1330`):
its statement under the three standoff binders, its proof verbatim with
`usetGChi_window_meansq_gated_family_perBlock_bounded_cs` replaced by the standoff form. -/
theorem usetGChi_row_exit_perChi_perBlock_bounded_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
      ∀ (H : ℝ), 2 ≤ H → ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ),
        (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        (∀ j ∈ ramI H P Q, ramRrange H N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI H P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI H P Q, H ≤ (j : ℝ)) →
        (∀ j ∈ ramI H P Q, 3 ≤ ramQbase H P j) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI H P Q, 30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase H P j)) →
        (∀ j ∈ ramI H P Q, (ramQbase H P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI H P Q, Real.log (ramQbase H P j) ≤ L) →
        (∀ j ∈ ramI H P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase H P j)) ^ 2) →
      ∀ Rbd : ℝ, 0 ≤ Rbd →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI H P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR H N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ E : ℝ, (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr H N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
      ∀ KS : ℝ,
        (∀ j ∈ ramI H P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff H N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        2 ≤ ⌊H * Real.log (P : ℝ)⌋₊ →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
            ∩ UsetG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
            ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 4 * ((ramI H P Q).card : ℝ)
              * (((ramI H P Q).card : ℝ) * KS
                  + 54 * Cq * Rbd ^ 2 * H ^ 2
                      / ((⌊H * Real.log (P : ℝ)⌋₊ : ℝ) - 1)) + 2 * E := by
  obtain ⟨Cs, cs, T₀, Kq, Ks, hCs, hcs, hcsf, hT₀, hKq, hKqb, hKs, hfam⟩ :=
    (usetGChi_window_meansq_gated_family_perBlock_bounded_cs_of_standoff hcS hSieg)
  refine ⟨3 * Cs / 2, cs, T₀, Kq, Ks, by linarith, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3 hBT hκ30 hBT10 hWL
    hgate Rbd hRbd t₁ hR E herr KS hKS hj₀ χ
  -- ⟦the Σ_χ exit at the row's own pair set⟧
  have hsum := hfam q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV H hH2 N Xd P Q Ms a b cf hcf1 hM hbudget hHj hB3
    hBT hκ30 hBT10 hWL hgate Rbd hRbd
    (rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁)
    (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_sub q c Pseq Qseq Hseq αseq J X Tann t₁)
    (rowPairSetG_subset_UsetGChi q c Pseq Qseq Hseq αseq J X Tann t₁)
    (fun j hj r hr => hR r.1 j hj r.2 hr.1) E herr
  -- ⟦the per-χ read: every fibre integral is nonnegative, so one is at most the sum⟧
  have hnn : ∀ χ' ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      (0 : ℝ) ≤ ∫ t in {t : ℝ | (χ', t) ∈ rowPairSetG q c Pseq Qseq Hseq αseq J X Tann t₁},
        ‖spoly N (chiBarCoeff q χ' a) t‖ ^ 2 := by
    intro χ' _
    exact setIntegral_nonneg
      (measurableSet_rowPairSetG_fibre q c Pseq Qseq Hseq αseq J X Tann t₁ χ')
      (fun _ _ => by positivity)
  have hsingle := Finset.single_le_sum hnn (Finset.mem_univ χ)
  -- ⟦the ⟦ii-8⟧ block price, per block⟧
  have hprice := usetGChi_block_price_perBlock H N Xd P Q Ms b X Tann KS Cs Rbd hCs.le hRbd
    hj₀ hKS
  have hcard0 : (0 : ℝ) ≤ 4 * ((ramI H P Q).card : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hprice hcard0
  rw [rowPairSetG_fibre] at hsingle
  linarith

end

section
open scoped BigOperators
open MeasureTheory
set_option maxHeartbeats 3200000 in
-- The twin re-elaborates the `_bounded` statement with one more conjunct, so it needs
-- that declaration's own heartbeat room.
open MeasureTheory in
/-- **⟦STANDOFF TWIN⟧** `m4_rowChi_capstone_perBlock_bounded_cs` (`Salt/MR/V7B.lean:1435`): its
statement under the three standoff binders, its proof verbatim with
`usetGChi_row_exit_perChi_perBlock_bounded_cs` replaced by the standoff form. -/
theorem m4_rowChi_capstone_perBlock_bounded_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
      ∀ (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ) (J Jb : ℕ), 1 ≤ Jb → Jb ≤ J →
        2 ≤ Hseq Jb → 0 ≤ αseq Jb →
      ∀ (Tann VJ V L X : ℝ), 1 ≤ Tann → 1 < (q : ℝ) * Tann →
        3 ≤ Pseq Jb → Pseq Jb ≤ Qseq Jb → ((Qseq Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann →
        30 ≤ Real.log ((q : ℝ) * Tann) / Real.log ((Qseq Jb : ℕ) : ℝ) →
        5 ≤ Real.log (Real.log ((q : ℝ) * Tann)) →
        (∀ v ∈ ramI (Hseq Jb) (Pseq Jb) (Qseq Jb),
          Real.exp (αseq Jb * (v : ℝ) / Hseq Jb) ≤ VJ) →
      ∀ η ε : ℝ, αseq Jb ≤ 1 / 4 - η → 2 * η ≤ 1 → Tann ≤ X → 0 < X →
        (q : ℝ) ^ (2 * αseq Jb) ≤ X ^ ε → 0 < Real.log X →
        (q : ℝ) ≤ (Real.log X) ^ 12 → 1 ≤ V → V⁻¹ ≤ (Real.log X) ^ (-106 : ℝ) →
        T₀ ≤ Tann →
        8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) →
        8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
            ≤ Real.log (Real.log (5 * Tann + 1)) →
        Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
            ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) →
        (q : ℝ) ^ ((1 : ℝ) / 16)
            ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
                * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) →
        1 ≤ Real.log ((q : ℝ) * Tann) → Real.log ((q : ℝ) * Tann) ≤ L → Real.exp 1 ≤ L →
        Real.log V ≤ 100 * Real.log L →
        -- ⟦THE `X`-SIDE FRAME⟧
        2 ≤ H83 X theta293 → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        TannGate X Tann →
      ∀ (N Xd P Q : ℕ) (Ms : ℕ → ℕ) (a b cf : ℕ → ℂ), (∀ n : ℕ, ‖cf n‖ ≤ 1) →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleGChi ((q : ℝ) * Tann) VJ (Hseq Jb) (Pseq Jb) (Qseq Jb)
            * X ^ (1 - 2 * η + ε) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, H83 X theta293 ≤ (j : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 3 ≤ ramQbase (H83 X theta293) P j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ (q : ℝ) * Tann) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          30 ≤ Real.log ((q : ℝ) * Tann) / Real.log (ramQbase (H83 X theta293) P j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          (ramQbase (H83 X theta293) P j : ℝ) ≤ Tann ^ 10) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          Real.log (ramQbase (H83 X theta293) P j) ≤ L) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5
          ≤ cs * (Real.log (ramQbase (H83 X theta293) P j)) ^ 2) →
      ∀ (Rbd CR : ℝ), 0 ≤ Rbd → Rbd ≤ CR * (Real.log X) ^ (-rho293) →
        1728 * Cq * CR ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
      ∀ t₁ : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ j ∈ ramI (H83 X theta293) P Q,
          ∀ t ∈ seamAnn X Tann \ seamBall X (t₁ χ),
            ‖ramR (H83 X theta293) N Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd) →
      ∀ KS : ℝ, 0 ≤ KS →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          5128 * (Real.log X) ^ (-200 : ℝ) * ((Ms j : ℕ) : ℝ) * (1 + Real.log (2 * Tann))
              * (∑ m ∈ Finset.Icc 1 (Ms j),
                  ‖ramRcoeff (H83 X theta293) N Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
            ≤ KS) →
        32 * (Real.log X) ^ (2 + 2 * theta293) * KS ≤ (Real.log X) ^ (-theta293) →
      ∀ (E EP2 εr : ℝ), 0 ≤ εr → 8640 ≤ (Real.log X) ^ εr →
        12 * EP2 ≤ (Real.log X) ^ (-theta293 + εr) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
          ‖ramErr (H83 X theta293) N Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b)
            (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
      ∀ S : DirichletCharacter ℂ q → ℝ,
        (∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann →
          |t - t₁ χ| ≤ seamRad X → ∀ m : ℕ, m ≤ N →
            ‖spolyA (chiBarCoeff q χ a) t m‖ ≤ S χ * m / (1 + |t - t₁ χ|)) →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S χ ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X (t₁ χ))
                ∩ seamTtotG (chiBarCoeff q χ c) Pseq Qseq Hseq αseq J,
                ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + εr)) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hexit⟩ :=
    (usetGChi_row_exit_perChi_perBlock_bounded_cs_of_standoff hcS hSieg)
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro q _ c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X hT1 hqT hP3
    hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T hG1 hG2 hG3 hG4
    hlogT1 hTL hLe hlogV hH2 hLXe hL4 hTgate
    N Xd P Q Ms a b cf hcf1 hPlow hQ0 hQhigh hM hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate
    Rbd CR hRbd hRgrade hCqgate t₁ hR KS hKS0 hKS hKSgate E EP2 εr hεr habs hEP2 hErow herr
    hXN hN2 hsupp S hSup χ
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hH0 : (0 : ℝ) ≤ H83 X theta293 := by linarith
  have hHeq : H83 X theta293 = (Real.log X) ^ theta293 := by rw [H83]
  have hTann0 : (0 : ℝ) ≤ Tann := by linarith
  have hfl := floor_pin X P hL4 hPlow
  -- ⟦the per-χ `𝒰` exit, per block⟧
  have hU := hexit q c hc1 Pseq Qseq Hseq αseq J Jb hJb1 hJbJ hH2seq hα0 Tann VJ V L X
    hT1 hqT hP3 hPQ hQT hκ30Q hLL5 hVJ η ε hα hη2 hTX hX0 hdebit hL0 hqlog hV1 hVδ hT₀T
    hG1 hG2 hG3 hG4 hlogT1 hTL hLe hlogV (H83 X theta293) hH2 N Xd P Q Ms a b cf hcf1 hM
    hbudget hHj hB3 hBT hκ30 hBT10 hWL hgate Rbd hRbd t₁ hR E herr KS hKS hfl.1 χ
  -- ⟦the block leg, priced at `θ₂₉₃`⟧
  have hmain := balance_priced_main X (H83 X theta293) Cq CR KS Rbd P Q hL0 hH0
    (ramI_card_le_pin X P Q hQ0 hQhigh hLXe) (le_of_eq hHeq) hfl.2
    hCq.le hKS0 hRbd hRgrade hKSgate hCqgate
  -- ⟦Lemma 12's error leg, absorbed⟧
  have hrem := rem_priced X Tann (H83 X theta293) εr EP2 E hL1 hX0 hTann0
    (le_of_eq hHeq.symm) habs hEP2 hErow
  -- ⟦the balance⟧
  have hbal := hUG_balance (chiBarCoeff q χ a) (chiBarCoeff q χ c) N Pseq Qseq Hseq αseq J
    X Tann (t₁ χ) εr _ _ hεr hL1 hX0 hTgate hU hmain hrem
  exact prop_A3_T1_row_split_weightedG (chiBarCoeff q χ a) N (chiBarCoeff q χ c) Pseq Qseq
    Hseq αseq J X Tann (t₁ χ) (S χ) _ hL0.le hTann0 hX0 hXN hN2
    (chiBarCoeff_seam_supp χ hsupp) (hSup χ) hbal

end

section
open Salt.Entropy.Chowla
open scoped BigOperators
set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: one application of a ~45-binder capstone.
/-- **⟦STANDOFF TWIN⟧** `m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs` (`Salt/MR/V7B.lean:1572`):
its statement under the three standoff binders, its proof verbatim with
`m4_rowChi_capstone_perBlock_bounded_cs` replaced by the standoff form. -/
theorem m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ 126848 / 10 ^ 8 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hcapstone⟩ :=
    (m4_rowChi_capstone_perBlock_bounded_cs_of_standoff hcS hSieg)
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, ?_⟩
  intro K R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (AdoorL M) (s13GK K M))
    (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU_L_gk K M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0_L_gk K M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU_L_gk K M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum_L_gk] at hres
  simpa using hres

end

section
open Salt.Entropy.Chowla
open scoped BigOperators
set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the wire's own statement re-elaborates.
/-- **⟦STANDOFF TWIN⟧** `m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs` (`Salt/MR/V7B.lean:1634`):
its statement under the three standoff binders, its proof verbatim with
`m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs` replaced by the standoff form. -/
theorem m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧
      ∀ (K : ℕ) (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
              (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
              G2Scaffold.DoorCapErrWS_L_gk K M (A + s) q Xd P Q b cf (2 * T) E Mtail
                ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                      ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                        (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU_L_gk K M)))
                        (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                    → DoorCapBasePerBlock_L_gk K Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf
                        (2 * T) VJ V Lr η εd (ε (A + s)) Rbd CR KS E EP2)) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq, hKqb, hKs, hwire⟩ :=
    (m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs_of_standoff hcS hSieg)
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hcsf, hT₀, hKq,
    le_trans hKqb kq_closed_form_le_exp_hundred, hKs, ?_⟩
  intro K R M cU ε hc1 hcapWS
  refine hwire K R M cU ε hc1 ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, Mtail, hws, hrest⟩ :=
    hcapWS H L q j A s hsb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hsb.2.2.2.1.ne'⟩
  exact ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2,
    hrest (G2Scaffold.m4_capE_at_door_L_gk K hws)⟩

end

section
open Salt.Entropy.Chowla
open scoped BigOperators
set_option maxHeartbeats 3200000 in
-- Same cause as the landed original: the eighteen-slot `hcapWS` family re-elaborates.
/-- **⟦STANDOFF TWIN⟧** `s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin`
(`Salt/MR/V7Ks.lean:246`): its statement under the three standoff binders, its proof verbatim with
`m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs` replaced by the standoff form. -/
theorem s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin_of_standoff
    {cS : ℝ} (hcS : 0 < cS) (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ Cq cs T₀ Kq Ks C : ℝ, 0 < Cq ∧ 0 < cs ∧ Real.exp (-100) ≤ cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧
      Kq ≤ Real.exp 100 ∧ 0 < Ks ∧ 0 < C ∧ Real.log C ≤ 40 ∧
      ∀ K : ℕ,
        (Kq ≤ Real.exp 100 →
        ∀ (R : ChowlaRegime) (M : ℕ), 1 ≤ M → loglogFloor50 ≤ R.Hlo →
          Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 →
          T₀ ≤ Real.exp (Real.sqrt ((R.Hlo : ℕ) : ℝ) / 2) →
          (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → s13BlockFloor_L_gk K M ≤ A + s) →
          S16CofactorSupply_L_gk K Cq R M → S16BaseScaleCap96_L_gk K R M →
          S15CrossingBound_L_gk K R M) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hwire⟩ :=
    (m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs_of_standoff hcS hSieg)
  obtain ⟨C, hC0, hC40, hband⟩ := m4_tail_mass_at_band_bounded
  refine ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40, ?_⟩
  intro K hKq R M hM hfl hKsw hT₀ hblk hcof hcap
  -- ⟦THE cs RIDER, SPENT FROM THE PREFIX⟧ `hcsf` is the carried conjunct (V7-B);
  -- ⟦THE Ks RIDER, SPENT AS A WINDOW⟧ `hKs0` is the prefix's own positivity
  have hgate := s16_capGate_supply_L_gk_sharpT0_kswin K hM hfl hcsf hblk hT₀ hKq hKs0 hKsw
    hC0 hC40 (fun _ => le_rfl) hcap hcof
  refine hwire K R M liouvilleC (fun _ => theta293 - 1 / 500) liouvilleC_norm_le_one ?_
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock_L_gk K hband hM hNd hq hg hT1 hThi hTll

end

end Salt.MR

namespace Salt.Entropy.Chowla

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction
/-- **⟦STANDOFF TWIN⟧** `primeWindow_sum_inv_ge_bounded`
(`Salt/Entropy/Chowla/HeadPinLeaves.lean:61`): its statement under the three standoff binders, its
proof verbatim with `Salt.Chen.lambda_mass_lower` replaced by the standoff form. -/
theorem primeWindow_sum_inv_ge_bounded_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H : ℕ), H₀ ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      c / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ :=
      (Salt.Chen.lambda_mass_lower_of_SW (Salt.SW.siegelWalfisz_of_standoff hcS hSieg))
  refine ⟨1 / 4, by norm_num, le_rfl, max (96 ^ 8) (⌈Real.exp (64 * K)⌉₊ + 1), ?_⟩
  intro eps H hH0 hreg heps1
  set N := ⌊eps ^ 2 * (H : ℚ)⌋₊ with hNdef
  -- H-side size facts
  have hH96 : (96 : ℝ) ^ 8 ≤ (H : ℝ) := by
    have h1 : 96 ^ 8 ≤ H := le_trans (le_max_left _ _) hH0
    exact_mod_cast h1
  have hHexp : Real.exp (64 * K) < (H : ℝ) := by
    have h1 : ⌈Real.exp (64 * K)⌉₊ + 1 ≤ H := le_trans (le_max_right _ _) hH0
    have h2 : (⌈Real.exp (64 * K)⌉₊ : ℝ) + 1 ≤ (H : ℝ) := by exact_mod_cast h1
    have h3 : Real.exp (64 * K) ≤ (⌈Real.exp (64 * K)⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hH1 : (1 : ℝ) < (H : ℝ) := lt_of_lt_of_le (by norm_num) hH96
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hlogH_pos : 0 < Real.log (H : ℝ) := Real.log_pos hH1
  have hsqrtH1 : (1 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (le_of_lt hH1)
  -- N-side size facts
  have hfloorQ : eps ^ 2 * (H : ℚ) < (N : ℚ) + 1 := by
    rw [hNdef]; exact Nat.lt_floor_add_one _
  have hfloorR : (eps : ℝ) ^ 2 * (H : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hfloorQ
  have hsqrtN : Real.sqrt (H : ℝ) ≤ (N : ℝ) := by linarith
  have hN96 : (96 : ℝ) ^ 4 ≤ (N : ℝ) := by
    have hsq : Real.sqrt ((96 : ℝ) ^ 8) = (96 : ℝ) ^ 4 := by
      rw [show ((96 : ℝ) ^ 8) = ((96 : ℝ) ^ 4) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have h1 := Real.sqrt_le_sqrt hH96
    rw [hsq] at h1
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN96
  have hN1 : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN96
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hN8 : 8 ≤ N := by
    have h1 : (8 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN96
    exact_mod_cast h1
  -- `N ≤ H` (this is where `ε² ≤ 1` enters)
  have heps1Q : eps ^ 2 ≤ (1 : ℚ) := by exact_mod_cast heps1
  have hNleH : N ≤ H := by
    rw [hNdef]
    have hq : eps ^ 2 * (H : ℚ) ≤ (H : ℚ) :=
      mul_le_of_le_one_left (by positivity) heps1Q
    have h2 := Nat.floor_le_floor hq
    rwa [Nat.floor_natCast] at h2
  have hNHR : (N : ℝ) ≤ (H : ℝ) := by exact_mod_cast hNleH
  have hlogNH : Real.log (N : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hN_pos hNHR
  -- `log N ≥ 32K` (from `H > exp(64K)` through `log N ≥ (1/2) log H`)
  have hlogN32K : 32 * K ≤ Real.log (N : ℝ) := by
    have h64 : 64 * K < Real.log (H : ℝ) := by
      have h1 := Real.log_lt_log (Real.exp_pos _) hHexp
      rwa [Real.log_exp] at h1
    have hhalf : Real.log (H : ℝ) / 2 ≤ Real.log (N : ℝ) := by
      have h1 : Real.log (Real.sqrt (H : ℝ)) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (lt_of_lt_of_le one_pos hsqrtH1) hsqrtN
      rwa [Real.log_sqrt hH0R] at h1
    linarith
  -- the `t = N^(1/4)` budget machinery
  set t : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with htdef
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hN_pos _
  have ht4 : t ^ (4 : ℕ) = (N : ℝ) := by
    rw [htdef, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hN_pos.le]
    norm_num
  have ht2 : t ^ (2 : ℕ) = Real.sqrt (N : ℝ) := by
    rw [htdef, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hN_pos.le,
      Real.sqrt_eq_rpow]
    norm_num
  have ht96 : (96 : ℝ) ≤ t := by
    have h1 : ((96 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hN96 (by norm_num)
    rwa [← Real.rpow_natCast (96 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 96),
      show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one, ← htdef] at h1
  have hlogt : Real.log (N : ℝ) ≤ 4 * t := by
    have h2 : Real.log (N : ℝ) = 4 * Real.log t := by
      rw [← ht4, Real.log_pow]
      push_cast
      ring
    have h3 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht_pos
    linarith
  -- the three budget pieces: `1 + 2KN/log N + (log N + 2√N·log N) ≤ N/16 + N/16 + N/8 = N/4`
  have hb1 : (1 : ℝ) ≤ (N : ℝ) / 16 := by
    have h16 : (16 : ℝ) ≤ (96 : ℝ) ^ 4 := by norm_num
    linarith
  have hb2 : 2 * K * (N : ℝ) / Real.log (N : ℝ) ≤ (N : ℝ) / 16 := by
    rw [div_le_div_iff₀ hlogN_pos (by norm_num : (0 : ℝ) < 16)]
    have h1 := mul_le_mul_of_nonneg_left hlogN32K hN_pos.le
    nlinarith
  have hb3 : Real.log (N : ℝ) + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) / 8 := by
    have e1 : 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ 8 * t ^ 3 := by
      have h1 : 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)
          ≤ 2 * Real.sqrt (N : ℝ) * (4 * t) :=
        mul_le_mul_of_nonneg_left hlogt (by positivity)
      have h2 : 2 * Real.sqrt (N : ℝ) * (4 * t) = 8 * t ^ 3 := by
        rw [← ht2]; ring
      linarith
    have e2 : 4 * t + 8 * t ^ 3 ≤ t ^ 4 / 8 := by
      have hC : 0 ≤ (t - 96) * t ^ 3 := mul_nonneg (by linarith) (pow_pos ht_pos 3).le
      have hA : 0 ≤ (t - 1) * t := mul_nonneg (by linarith) ht_pos.le
      have hB : 0 ≤ (t - 1) * t * t := mul_nonneg hA ht_pos.le
      nlinarith [hA, hB, hC]
    linarith [hlogt, e1, e2, ht4]
  -- the Λ-mass over the twin window, boundary point split off
  have hmass0 := hK N hN8
  have htw : Salt.Chen.twinWindow N = Finset.Icc (N / 2) (N - 2) := rfl
  have hIcc : Finset.Icc (N / 2) (N - 2) = insert (N / 2) (Finset.Ioc (N / 2) (N - 2)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hnm : N / 2 ∉ Finset.Ioc (N / 2) (N - 2) := by simp
  rw [htw, hIcc, Finset.sum_insert hnm] at hmass0
  have hbdry : vonMangoldt (N / 2) ≤ Real.log (N : ℝ) := by
    calc vonMangoldt (N / 2) ≤ Real.log ((N / 2 : ℕ) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (N : ℝ) := by
          have hpos : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by
            have h1 : 0 < N / 2 := by omega
            exact_mod_cast h1
          exact Real.log_le_log hpos (by exact_mod_cast Nat.div_le_self N 2)
  -- prime / non-prime split over the `Ioc`
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc (N / 2) (N - 2)) (fun n => n.Prime) (fun n => vonMangoldt n)
  -- the prime-power junk: `≤ ψ(N) − θ(N) ≤ 2√N·log N`
  have hjunk : ∑ n ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => ¬n.Prime), vonMangoldt n
      ≤ 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    have hsubJ : (Finset.Ioc (N / 2) (N - 2)).filter (fun n => ¬n.Prime)
        ⊆ (Finset.Ioc 0 N).filter (fun n => ¬n.Prime) :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc (Nat.zero_le _) (by omega))
    calc ∑ n ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => ¬n.Prime), vonMangoldt n
        ≤ ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬n.Prime), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubJ
            (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
          rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      _ ≤ 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
          Chebyshev.psi_sub_theta_le (by linarith)
  -- the θ-mass of the window primes: `≥ N/4`
  have hquarter : (N : ℝ) / 4
      ≤ ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), Real.log (p : ℝ) := by
    have hlogform :
        ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), Real.log (p : ℝ)
          = ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), vonMangoldt p :=
      Finset.sum_congr rfl (fun p hp =>
        (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm)
    rw [hlogform]
    linarith [hmass0, hbdry, hjunk, hsplit, hb1, hb2, hb3]
  -- the window primes live in `primeWindow eps H`
  have hsub2 : (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime) ⊆ primeWindow eps H := by
    intro p hp
    obtain ⟨hmem, hpp⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_Ioc] at hmem
    rw [mem_primeWindow, ← hNdef]
    refine ⟨by omega, hpp, ?_⟩
    have h2p : (N : ℚ) + 1 ≤ 2 * (p : ℚ) := by exact_mod_cast (by omega : N + 1 ≤ 2 * p)
    linarith [hfloorQ]
  -- per-prime flip: `1/p ≥ log p / (N log N)`
  have hden_pos : 0 < (N : ℝ) * Real.log (N : ℝ) := mul_pos hN_pos hlogN_pos
  have hstep : ∀ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime),
      Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) ≤ 1 / (p : ℝ) := by
    intro p hp
    obtain ⟨hmem, hpp⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_Ioc] at hmem
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hpN : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : p ≤ N)
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlogpN : Real.log (p : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hp_pos hpN
    rw [div_le_div_iff₀ hden_pos hp_pos]
    nlinarith [mul_le_mul hpN hlogpN hlogp_nn hN_pos.le]
  -- assemble
  calc (1 / 4 : ℝ) / Real.log (H : ℝ)
      = 1 / (4 * Real.log (H : ℝ)) := by rw [div_div]
    _ ≤ 1 / (4 * Real.log (N : ℝ)) := by
        apply one_div_le_one_div_of_le
        · linarith
        · linarith
    _ ≤ (∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), Real.log (p : ℝ))
          / ((N : ℝ) * Real.log (N : ℝ)) := by
        rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log (N : ℝ)) hden_pos]
        nlinarith [mul_le_mul_of_nonneg_right hquarter hlogN_pos.le]
    _ = ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime),
          Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) := by
        rw [Finset.sum_div]
    _ ≤ ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), 1 / (p : ℝ) :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ p ∈ primeWindow eps H, 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity)

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction
set_option maxHeartbeats 1600000 in
-- The replayed budget aggregation (∫F unfold + three window totals + double-sum
-- reduction) is a large single elaboration, as at the landed `HBudget.lean:440`;
-- the ceiling here is that declaration's, unchanged.
open private window_Z_pos absX_le_one window_sum_inv_sq IF_unfold per_term boundary_card_le from
  Salt.Entropy.Chowla.HBudget in
/-- **⟦STANDOFF TWIN⟧** `hbudget_holds_bounded` (`Salt/Entropy/Chowla/HeadPinLeaves.lean:264`): its
statement under the three standoff binders, its proof verbatim with `primeWindow_sum_inv_ge_bounded`
replaced by the standoff form. -/
theorem hbudget_holds_bounded_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, hcge, H₀, hD3⟩ := (primeWindow_sum_inv_ge_bounded_of_standoff hcS hSieg)
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
  -- abbreviations kept raw (they interface with the window lemmas via linarith)
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := window_Z_pos hx hω
  have hZlb : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    (harmonic_window_bounds hx hω hωx).1
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hε2H0 : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hSP_lb : c / Real.log H ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    hD3 eps H hH0 hsqrt hepssq
  have hSPpos : (0 : ℝ) < ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) hSP_lb
  have habsX : |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| ≤ 1 := absX_le_one hx hω
  have hcard : ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime eps H hsqrt hH3
  have hxωH : H ≤ x / ω := by
    have hpos : (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) := by positivity
    have h2 : ω * H ≤ x := by
      have : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ω), Nat.mul_comm]; exact h2
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (by omega : 0 < ω)
  have hε_le1 : (eps : ℝ) ≤ 1 := by nlinarith [hepssq, hepsR]
  have hlogε2H : (0 : ℝ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hple : ∀ p ∈ primeWindow eps H, (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    intro p hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hZbig' : 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64
      ≤ (eps : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    have h2 : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hepsR.le
    have hlhs : (eps : ℝ) * ((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ))
        = 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 := by field_simp
    rw [hlhs] at h3; exact h3
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    nlinarith [hZbig', hlogε2H, hε_le1, hZpos, mul_le_mul_of_nonneg_right hε_le1 hZpos.le]
  -- === total 1: the Z-controlled (collapse+swap) slice ≤ (1/8)·SP·H·ε ===
  have hZεbound : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
      / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) ≤ (eps : ℝ) / 8 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    nlinarith [hZbig']
  have hT1 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
        * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hstep : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      have hle : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          ≤ ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < (p : ℕ))
        have hlogle : Real.log (p : ℕ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          Real.log_le_log hpR (hple p hp)
        gcongr
      have heq : ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (((p : ℕ) : ℝ) * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          = (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
      linarith [hle, heq.le, heq.ge]
    calc (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (H : ℝ) * ((2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hHR.le
      _ ≤ (H : ℝ) * ((eps : ℝ) / 8 * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hHR.le
          exact mul_le_mul_of_nonneg_right hZεbound hSPpos.le
      _ = (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by ring
  -- === total 2: the shift slice ≤ (1/16)·SP·H·ε ===
  have key2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      = ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
  have hHsq : (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2)
      ≤ (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (window_sum_inv_sq eps H) hHR.le
    have h2 : (H : ℝ) * ((2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        = (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hSpos2 : (0 : ℝ) ≤ 3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    positivity
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hle : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by
      nlinarith [hxbig, (show (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        by positivity)]
    nlinarith [hle, mul_pos hωR hHR]
  have hxbound : 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (eps : ℝ) / (16 * (1 + 2 / (eps : ℝ) ^ 2)) := by
    have hxZ : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      have hx1 : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := by
        nlinarith [hxbig, (show (0 : ℝ) ≤ (ω : ℝ) * (H : ℝ) by positivity)]
      calc 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := hx1
        _ = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hZ1 hxpos.le
    rw [div_le_iff₀ hepsR] at hxZ
    rw [div_div, div_le_div_iff₀ (mul_pos hxpos hZpos) (by positivity)]
    nlinarith [hxZ]
  have hT2 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    rw [key2]
    have hfac : ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hHsq]) hSpos2
    have hmul : (H : ℝ) * (((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
      have hCbound := hxbound
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (1 + 2 / (eps : ℝ) ^ 2))] at hCbound
      nlinarith [mul_le_mul_of_nonneg_left hCbound
        (mul_nonneg (mul_nonneg hHR.le hSPpos.le) (by norm_num : (0:ℝ) ≤ (1:ℝ)/16))]
    exact le_trans (mul_le_mul_of_nonneg_left hfac hHR.le) hmul
  -- === total 3: the boundary slice ≤ (1/16)·SP·H·ε ===
  have hT3 : ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have h32 : (eps : ℝ) * (32 * Real.log 4) ≤ c := (le_div_iff₀ (by positivity)).mp heps_small
    have hkey3' : 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))
        ≤ (1 / 16) * c * (H : ℝ) * (eps : ℝ) := by
      nlinarith [h32, mul_nonneg (mul_nonneg hepsR.le hHR.le) hepsR.le, hlog4]
    calc ((primeWindow eps H).card : ℝ) * |_|
        ≤ ((primeWindow eps H).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left habsX (Nat.cast_nonneg _)
      _ = ((primeWindow eps H).card : ℝ) := mul_one _
      _ ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) := hcard
      _ = (2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))) / Real.log H := by ring
      _ ≤ ((1 / 16) * c * (H : ℝ) * (eps : ℝ)) / Real.log H := by
          gcongr
      _ = (1 / 16) * (c / Real.log H) * (H : ℝ) * (eps : ℝ) := by ring
      _ ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSP_lb (by norm_num)) hHR.le) hepsR.le
  -- === the reduction: |IF − MAIN| ≤ H·ΣB + card·|X| ≤ T1 + T2 + T3 ===
  have hIF : (∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)
            else 0) ∂(logMeasure x ω) := by
    rw [IF_unfold eps H]
    exact Finset.sum_coe_sort (primeWindow eps H)
      (fun p => ∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod p) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + p) : ℝ) else 0) ∂(logMeasure x ω))
  have hMAIN : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hIF, hMAIN, ← Finset.sum_sub_distrib]
  have hcombine : ∀ p ∈ primeWindow eps H,
      (∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
        - ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))
      = ∑ j ∈ Finset.range H,
          ((∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
              (ArithmeticFunction.liouville (n + j + 1) : ℝ)
                * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
            - (1 / (p : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))) :=
    fun p _ => by rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hcombine]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun j hj =>
    per_term eps H hx hω hωx hxωH p hp j (Finset.mem_range.mp hj)))).trans ?_
  -- split the inner sum (per-pair bound j-independent; boundary term counted separately)
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hbnd_total : ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
      (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0)
      ≤ ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
    have hbnd : ∀ p ∈ primeWindow eps H, (∑ j ∈ Finset.range H,
        (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0))
        ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < p)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcardp : (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast boundary_card_le H p
      calc (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) * ((1 / (p : ℝ)) * |_|)
          ≤ (p : ℝ) * ((1 / (p : ℝ)) * |_|) :=
            mul_le_mul_of_nonneg_right hcardp (by positivity)
        _ = |_| := by rw [← mul_assoc, mul_one_div, div_self hpR.ne', one_mul]
    calc ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0)
        ≤ ∑ p ∈ primeWindow eps H, |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| :=
          Finset.sum_le_sum hbnd
      _ = ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hT1, hT2, hT3, hbnd_total]

end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction
/-- **⟦STANDOFF TWIN⟧** `hreduce_holds_final_bounded`
(`Salt/Entropy/Chowla/HeadPinLeaves.lean:520`): its statement under the three standoff binders, its
proof verbatim with `hbudget_holds_bounded` replaced by the standoff form. -/
theorem hreduce_holds_final_bounded_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  obtain ⟨c, hc, hcge, H₀, hbud⟩ := (hbudget_holds_bounded_of_standoff hcS hSieg)
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig hseed
  exact hreduce_holds eps H hseed
    (hbud eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig)

end

end Salt.Entropy.Chowla

namespace Salt.MR

section
open scoped BigOperators
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_head_uniform_xceil_epsW` (`Salt/MR/FlatDoorEpsRung2.lean:4740`): its
statement under the three standoff binders, its proof verbatim with `primeWindow_sum_inv_ge_bounded`
and `hreduce_holds_final_bounded` replaced by the standoff form. -/
theorem flat_head_uniform_xceil_epsW_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    {c : ℕ} (hc1 : 1 ≤ c) (hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε) (P : ChowlaRegime → Prop)
    (hP : ∀ R : ChowlaRegime, R.eps = ε →
      MRTUniformityXiL2 R ((ε : ℝ) / (256 * (1 + 4 * Real.log 4))) →
      (∀ ρ : ℝ, 0 < ρ → ρ ≤ (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) →
        MRTUniformityXiL2 R ρ → ¬ logChowla2Fails R.eps R.x R.ω) → P R) :
    FlatHeadFormEpsW ε c P := by
  classical
  unfold FlatHeadFormEpsW
  obtain ⟨cE, hcE, hcEge, H₀red, hred⟩ := (hreduce_holds_final_bounded_of_standoff hcS hSieg)
  obtain ⟨cD3', hcD3', hcD3'ge, H₀D3, hD3'⟩ :=
      (primeWindow_sum_inv_ge_bounded_of_standoff hcS hSieg)
  obtain ⟨C', hC', hCcap, hcm'⟩ := circle_method_estimate_sq_bounded (2 * Real.log 4)
    (by have := Real.log_pos (by norm_num : (1 : ℝ) < 4); linarith)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  -- ⟦THE LEAVES' WITNESSES, PINNED⟧ the door-head's device (`DoorReceipt.lean:949–958`)
  obtain ⟨cD3, hcD3def⟩ : ∃ c : ℝ, c = 1 / 4 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ c : ℝ, c = 1 + 2 * (2 * Real.log 4) := ⟨_, rfl⟩
  have hcD3 : 0 < cD3 := by rw [hcD3def]; norm_num
  have hcD3ge : 1 / 4 ≤ cD3 := by rw [hcD3def]
  have hC : 0 < C := by rw [hCdef]; positivity
  have hCnum : C ≤ 655 / 100 := by rw [hCdef, hlog4eq]; linarith
  have hCle : C' ≤ C := by rw [hCdef]; exact hCcap
  -- ⟦THE `ε` BOUNDS⟧ E1's recipe, read off `ε ≤ 1/500` instead of off the pin
  have hεR0 : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  have hεle : (ε : ℝ) ≤ 1 / 500 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hε
  have hεcE : (ε : ℝ) ≤ cE / (32 * Real.log 4) := by
    have h : (1 : ℝ) / 500 ≤ cE / (32 * Real.log 4) := by
      rw [le_div_iff₀ (by positivity), hlog4eq]; linarith
    linarith
  have hε_half_lt : (ε : ℝ) < 1 / 2 := by linarith
  have hε_D3 : (ε : ℝ) ≤ cD3 / 16 := by
    have h : (1 : ℝ) / 500 ≤ cD3 / 16 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]; linarith
    linarith
  have hε_D3C : (ε : ℝ) ≤ cD3 / (16 * C) := by
    have h : (1 : ℝ) / 500 ≤ cD3 / (16 * C) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * C)]; linarith
    linarith
  have hεQ1 : ε ≤ 1 / 2 := by
    have h2 : (1 : ℚ) / 500 ≤ 1 / 2 := by norm_num
    linarith
  -- ⟦THE MINT⟧ the head's `δ₀` at the pinned witnesses IS the frozen file's term, exactly
  have hmint : cD3 / (16 * C) * (ε : ℝ) / 4 = (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) := by
    rw [hcD3def, hCdef]
    have hne : (1 : ℝ) + 2 * (2 * Real.log 4) ≠ 0 := by positivity
    field_simp
    ring
  -- ⟦THE MINT AGAINST THE PIN, AT THE CHARGE⟧ the source's `hqcap`/`hcapR`/`hδnum` at `c`
  -- in place of `8103`: `1 ≤ 500·c·ε` gives `838400·c·ε ≥ 1676.8`, and the mint's own
  -- denominator is `256·(1 + 8·log 2) ≤ 256 · 6.5451774464 = 1675.5654262784` — the source's
  -- own margin, now `1.2345737216` wide and INDEPENDENT of `c`.
  have hcQ : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hqcap : (1 : ℚ) ≤ 500 * (c : ℚ) * ε := by
    rw [div_le_iff₀ hcQ0] at hcε; linarith
  have hcapR : (1 : ℝ) ≤ 500 * (c : ℝ) * (ε : ℝ) := by exact_mod_cast hqcap
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hδnum : (1 : ℝ) / (838400 * (c : ℝ)) ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by
    rw [hmint, div_le_div_iff₀ (by linarith) (by positivity), hlog4eq]
    linarith
  -- ⟦THE COUNT HOOK AT THE CAP⟧ §2, in place of the pinned hook
  obtain ⟨K, hK, hKb, H₀xi, _hH₀xi2, hxi⟩ := bigXi_bounded_ceiling_eps ε hε0 hε hc1 hcε
  obtain ⟨β, hβdef⟩ : ∃ b : ℝ, b = cD3 * (ε : ℝ) / (144 * Real.log 4) := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβdef]; exact div_pos (mul_pos hcD3 hεR0) (by positivity)
  -- ⟦THE HEAD'S OWN FOUR-ARM FLOOR⟧ (flat) — `A`-FREE, which is the whole point
  obtain ⟨Hopq, hOpqdef⟩ : ∃ n : ℕ, n = max (max H₀red H₀D3) H₀xi := ⟨_, rfl⟩
  refine ⟨K, cD3 / (16 * C) * (ε : ℝ) / 4, β, Hopq, hε0, hK, hKb,
    div_pos (mul_pos (div_pos hcD3 (mul_pos (by norm_num) hC)) hεR0) (by norm_num),
    hc1, hcε, hδnum, hβpos, ?_⟩
  -- ⟦THE HOIST⟧ the landed proof chose `A := max A₀ (budgetAFlat ε β)` HERE
  intro A hA26 hAge hAL
  -- ⟦THE TOWER FLOOR THE NINTH ARM PAYS⟧ `50 + Lc ≤ 45 + A/2 ≤ 3.2·A` at `A ≥ 26`
  have hlamA : 50 + Real.log (c : ℝ) ≤ 3.2 * A := by linarith
  obtain ⟨F, hFdef⟩ : ∃ n : ℕ, n = max Hopq (budgetFloorFlat (ε : ℝ) β A) := ⟨_, rfl⟩
  refine ⟨max (flatDesignFloor A) (max F (4 * ⌈(1 / ε : ℚ)⌉₊ ^ 4)), by rw [hFdef], ?_⟩
  intro extraFloor U1floor g₅ hg₅
  obtain ⟨Rf, hReps, hRA, hRHlo, hRg, _hRcapEq, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_head_xceil_at (50 + Real.log (c : ℝ)) A hA26 hlamA ε hε0 hεQ1
      (max F (max extraFloor U1floor)) g₅ hg₅
  obtain ⟨hFlo, hxiHlo, hbudHlo, hredHlo⟩ :=
    Salt.Entropy.Chowla.flatHeadFloors_facts hOpqdef hFdef hRHlo
  refine ⟨Rf.toChowlaRegime, hReps,
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hRHlo,
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hRHlo, hRg, hRx, ?_,
    fun _ => hRwid, ?_, ?_⟩
  · -- ⟦THE EXPORTED COUNT GATE⟧ the road's `hXi`, at this head's own `ε`
    intro H' _ hlo' _
    rw [hReps]
    exact hxi H' (le_trans hxiHlo hlo')
  · -- ⟦THE CAP⟧ the flat base equation, shuffled onto the consumer's floors
    rw [_hRcapEq]
    exact uniformCap_shuffle _ _ _ _ _
  -- ⟦THE SLOT⟧ `P R` from the door AT THE MINT and the tail AT THE MINT
  intro ρ _hρpos hρ hdoor
  refine hP Rf.toChowlaRegime hReps
    (mrtUniformityXiL2_mono (le_trans hρ hmint.le) hdoor) ?_
  intro ρ' _hρ'pos hρ'le hdoor' hfail
  have hρ4 : ρ' ≤ cD3 / (16 * C) * (ε : ℝ) / 4 := by rw [hmint]; exact hρ'le
  obtain ⟨H, hlo, hhi, _hdvd, hMI⟩ := entropy_decrementFlat Rf
  have hH4 : 4000000 ≤ H := le_trans Rf.hHlo_floor hlo
  haveI : NeZero H := ⟨by omega⟩
  have hI : I[residueWindow Rf.eps H : liouvilleWindow H ; logMeasure Rf.x Rf.ω]
      ≤ (H : ℝ) / (Rf.A * Real.log H) := by
    rw [mutualInfo_window_comm_flat]; exact hMI
  have hepsc : (Rf.eps : ℝ) ≤ cE / (32 * Real.log 4) := by rw [hReps]; exact hεcE
  have hH₀ : max H₀red H₀D3 ≤ H := le_trans hredHlo hlo
  have hβR : cD3 * (Rf.eps : ℝ) / (144 * Real.log 4) = β := by rw [hReps, hβdef]
  have hAgeR : budgetAFlat (Rf.eps : ℝ) (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) ≤ Rf.A := by
    rw [hβR, hReps, hRA]; exact hAge
  have hfloorH : budgetFloorFlat (Rf.eps : ℝ)
      (cD3 * (Rf.eps : ℝ) / (144 * Real.log 4)) Rf.A ≤ H := by
    rw [hβR, hReps, hRA]
    exact le_trans hbudHlo hlo
  obtain ⟨t, g, ht, hg, hgle, hbudget1⟩ :=
    hbudget1_witnessFlat Rf H cD3 C hcD3 hC
      (by rw [hReps]; exact le_of_lt hε_half_lt)
      (by rw [hReps]; exact hε_D3)
      (by rw [hReps]; exact hε_D3C) hhi hAgeR hfloorH
  -- ⟦THE K-FREE hbudget2⟧ `ρ ≤ c₀ε/4 < c₀ε`
  have hbudget2 : ρ' < cD3 / (16 * C) * (Rf.eps : ℝ) := by
    rw [hReps]
    have hc0pos : (0 : ℝ) < cD3 / (16 * C) := div_pos hcD3 (mul_pos (by norm_num) hC)
    have hpos : (0 : ℝ) < cD3 / (16 * C) * (ε : ℝ) := mul_pos hc0pos hεR0
    linarith [hρ4, hpos]
  -- ⟦THE CORE⟧ at the FLAT threshold `κ = H/(A·log H)`, with the two transports supplied here
  refine spine_False_core_xi_sq_uniform Rf.toChowlaRegime hdoor' cE hcE H₀red hred cD3 hcD3
    H₀D3 ?_ C hC ?_ H hlo hhi hH₀ hepsc t g
    ((H : ℝ) / (Rf.A * Real.log H)) (cD3 / (16 * C))
    ht hg hgle hI hbudget1 hbudget2 hfail
  · -- ⟦TRANSPORT 1⟧ the `D3` FLOOR moves DOWN to the pinned `1/4`
    intro eps H' hH0 hsq h1
    refine le_trans ?_ (hD3' eps H' hH0 hsq h1)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by rw [hcD3def]; exact hcD3'ge)
      (inv_nonneg.mpr (Real.log_natCast_nonneg H'))
  · -- ⟦TRANSPORT 2⟧ the circle-method GRADE moves UP to the pinned `1 + 2·(2·log 4)`
    intro eps H' _ x1 hx1 hcard
    refine le_trans (hcm' eps H' x1 hx1 hcard) ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle ?_) ?_
    · rw [div_eq_mul_inv]
      exact mul_nonneg (Nat.cast_nonneg _) (inv_nonneg.mpr (Real.log_natCast_nonneg _))
    · positivity

end

section
open scoped BigOperators
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_kswin_generic_epsW` (`Salt/MR/FlatDoorEpsRung2.lean:5276`): its
statement under the three standoff binders, its proof verbatim with
`s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin` replaced by the standoff form. -/
theorem flat_kswin_generic_epsW_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop) (Awin : ℝ)
    (h : FlatConditionalFormEpsW ε c P Awin) :
    FlatKswinFormEpsW ε c P Awin := by
  unfold FlatKswinFormEpsW
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hKcb, hMflb, hβ, hcondU⟩ :=
    h
  -- ⟦THE CROSSING CONSTANTS, HOISTED ABOVE THE LEVER⟧ — §4's windowed twin
  obtain ⟨Cq, cs, T₀, Kq, Ks, C, hCq, hcs0, hcsf, hT₀3, hKq0, hKqb, hKs0, hC0, hC40,
    hsupplyU⟩ :=
        (s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin_of_standoff hcS hSieg)
  -- ⟦THE `ε`-CEILING⟧ read off ONE regime's own `heps1`, at ONE admissible design constant
  have hc0 : 0 < c := by omega
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  obtain ⟨_Ct0, -, -, hcond0⟩ := hcondU 0
  -- ⛔ THE ONE MINTED `A` OUTSIDE THE NINTH ARM.  Rung 1 read one regime's `heps1` at
  -- `max 162 (budgetAFlat ε β)`; at the charge the form's third `A`-binder is
  -- `10 + 2·Lc ≤ A`, which that `max` does NOT pay (it would need `Lc ≤ 76`, i.e. a numeral
  -- cap on `c`).  The arm is re-minted at `162 + 2·Lc`, which pays all three at `0 ≤ Lc`.
  obtain ⟨Hcap0, -, hbody0⟩ :=
    hcond0 (max (162 + 2 * Real.log (c : ℝ)) (budgetAFlat (ε : ℝ) β))
      (le_trans (by linarith) (le_max_left _ _)) (le_max_right _ _)
      (le_trans (by linarith) (le_max_left _ _))
  have hzero : XCeilRiderStrictAt (50 + Real.log (c : ℝ)) ε (fun _ _ : ℕ => 0) :=
    xceilRiderStrictAt_zero _ ε
  obtain ⟨R0, hR0eps, -, -, -, -, -⟩ :=
    hbody0 (max Hcap0 (max arcFloor36 loglogFloor50)) (fun _ _ => 0) hzero le_rfl
  have hε2q : ε ≤ 1 / 2 := by rw [← hR0eps]; exact R0.heps1
  have hε2 : (ε : ℝ) ≤ 1 / 2 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hε2q
  -- ⟦THE CHARGE, IN THE REAL SPELLING⟧ the `_L` siblings take the pin over `ℝ`; the RATIONAL
  -- spelling the `_b9` twins needed a second cast for is now the form's own `hεpin`, at `c`.
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hεR : (1 : ℝ) / (500 * (c : ℝ)) ≤ (ε : ℝ) := by
    have hq := hεpin
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  refine ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40, ?_⟩
  intro K
  obtain ⟨Ct, hCt, hCtb, hcond⟩ := hcondU K
  have hsupply := hsupplyU K
  refine ⟨Ct, hCt, ?_⟩
  intro A hA26 hAwin hAge hAL hKw
  obtain ⟨Hcap, hCapLe, hbody⟩ := hcond A hA26 hAge hAL
  refine ⟨fun hopq => flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 le_rfl hA26 hAL hβ
    hεR hε2 hε hεpin hAge hopq, ?_⟩
  intro hx0win hopq hT₀ hKsw g hg
  obtain ⟨R, hReps, hHlo, hRg, hRx, hRtow, hfire⟩ :=
    hbody (flatWitFloor ε β A Hopq) g hg (flatCap_le_flatWitFloor hCapLe)
  have hdes : 3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    rw [hHlo]; exact flatWitFloor_design ε β A Hopq
  have hbaseceil : Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) ≤ 3.2 * A + Real.log 2 := by
    rw [hHlo, flat_witFloor_eq_designBase_L (h := c) hc0 hLc0 le_rfl hA26 hAL hβ
      hεR hε2 hε hεpin hAge hopq]
    exact flatDesignBase_loglog_le hA26
  have hwin : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2) :=
    flat_L_width_priced hA26 hbaseceil hdes hRtow
  refine ⟨R, hReps, hHlo, hRg, hRx, hRtow, hdes, hwin, ?_⟩
  intro hcof hcapsc
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le (flat162_ge_26 hA26)
  -- `1/(2^9·c) ≤ 1/(500·c) ≤ ε`, the source's step at the charge: `500 ≤ 512 = 2^9`
  have heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]
    have h512 : (500 : ℚ) * (c : ℚ) ≤ 2 ^ 9 * (c : ℚ) := by
      have h9 : (2 : ℚ) ^ 9 = 512 := by norm_num
      rw [h9]; linarith
    have hb : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ 1 / (500 * (c : ℚ)) :=
      one_div_le_one_div_of_le (by linarith) h512
    linarith [hεpin]
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA26
  -- ⟦THE BRIDGE⟧ the `A`-scoped window becomes §4's regime-scoped one at the flat floor
  have hKswR : Real.log (1 / Ks) ≤ 3 * Real.log ((R.Hlo : ℕ) : ℝ) / 16 := by linarith
  -- `1/(838400·2^12·c²) ≤ 1/(838400·c)`: `c ≤ 4096·c²` at `c ≥ 1`
  have hδb : (1 : ℝ) / (838400 * 2 ^ 12 * (c : ℝ) ^ 2) ≤ δ₀ := by
    refine le_trans ?_ hδpin
    have hden : (838400 : ℝ) * (c : ℝ) ≤ 838400 * 2 ^ 12 * (c : ℝ) ^ 2 := by
      have h12 : (2 : ℝ) ^ (12 : ℕ) = 4096 := by norm_num
      rw [h12]; nlinarith
    exact one_div_le_one_div_of_le (by linarith) hden
  have hsel := s15_sel''_L_gk_witness_flat_bumped_win_L hA26 K hKw (h := c) hc0 hLc0 le_rfl hAL
    hδ₀ hδb hKc (epsRung2_one_le_Kb hc1) hKcb (epsRung2_log_Kb_le hc1)
    hCt hCtb hCgle (hMflb A hA26 hAwin) hx0win heps hlo hwin
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hblk : ∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
      s13BlockFloor_L_gk K (flatDoorM A) ≤ Aw + s := by
    intro H L q j Aw s hb
    exact s15_block_at_socket_L_gk K (socketBase_of_socketBaseL hM1 hb)
      (regime_Hfloor_of_loglogFloor50 (le_trans hfl hb.1)) hsel.blk
  exact hfire (flatDoorM A) hsel hKw
    (hsupply hKqb R (flatDoorM A) hM1 hfl hKswR (by rw [hHlo]; exact hT₀) hblk hcof hcapsc)

end

section
open scoped BigOperators
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_v7_generic_epsW` (`Salt/MR/FlatDoorEpsRung2.lean:5399`): its statement
under the three standoff binders, its proof verbatim with `s16_bandLaneWinL_holdsU` replaced by the
standoff form. -/
theorem flat_v7_generic_epsW_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : ∀ Awin : ℝ, S16BandLaneCBoundedL_winU Awin → FlatKswinFormEpsW ε c P Awin)
    (A₀ : ℝ) :
    V7RatedFormEpsW ε c P A₀ := by
  unfold V7RatedFormEpsW
  obtain ⟨Awin, -, hband⟩ := (s16_bandLaneWinL_holdsU_of_standoff hcS hSieg)
  -- ⟦THE cs-FREE, Ks-WINDOWED FLAT TERMINAL⟧ V7Ks §5
  obtain ⟨Cg, Kc, δ₀, β, x₀, Hopq, Mfl, Cq, cs, T₀, Kq, Ks, C, hε, hCg, hKc, hδ₀, hMfl1,
    hCgle, hc1, hεpin, hδpin, hMflb, hβ, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hmainU⟩ :=
    h Awin hband
  have hc0 : 0 < c := by omega
  have hLc0 : (0 : ℝ) ≤ Real.log (c : ℝ) := Real.log_nonneg (by exact_mod_cast hc1)
  -- ⟦THE RATED CO-FACTOR SUPPLY⟧ four Skolem REALS, still minted BEFORE the lever; the obtain
  -- moves below the terminal's only because the charge `1 ≤ c` is a component of the form.
  obtain ⟨Xsk, Y0, Kvt, Cb, hXsk0, hY0pin, hKvt0, hCb0, hcofR⟩ :=
    cofkR_cofactorSupply_L_gk_rated_L c hc0 hLc0 le_rfl
  -- ⟦THE DESIGN CONSTANT, EIGHT ARMS⟧ the seven landed arms verbatim (`A'`), the eighth
  -- (`armVt Kvt`) outermost — every constant still minted BEFORE the lever: `Kvt` arrives at
  -- the supply obtain above, before the mint.
  obtain ⟨A', hA'def⟩ : ∃ a : ℝ, a = max (16 * Real.log (1 / Ks) / 3) (max T₀
      (max (max (max (max A₀ 162) Awin) (cofkRThr Cq Cb Xsk Y0))
        (max (budgetAFlat (ε : ℝ) β) (max (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))))) := ⟨_, rfl⟩
  -- ⟦THE NINTH ARM⟧ `162 + 2·Lc`, OUTERMOST, the source's eight verbatim inside it.  It is the
  -- only place the charge is spent on the design constant, and it pays five demands at once:
  -- `162 ≤ A` (via `hlift`, as the source), `10 + 2·Lc ≤ A` (the forms' new binder),
  -- `518 + 6·Lc ≤ loglog H₋` (3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc), `cofkRThr + 2·Lc ≤ log H₋`
  -- and `Lc ≤ e^(1.6·A)`.  ⛔ `10 + 2·Lc ≤ A` does NOT pay the third, which is why the arm is
  -- `162 + 2·Lc` and not `10 + 2·Lc`.
  obtain ⟨A, hAdef⟩ : ∃ a : ℝ, a = max (162 + 2 * Real.log (c : ℝ)) (max (armVt Kvt) A') :=
    ⟨_, rfl⟩
  have hA162b : 162 + 2 * Real.log (c : ℝ) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAL : 10 + 2 * Real.log (c : ℝ) ≤ A := by linarith
  have harmA : armVt Kvt ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hlift : A' ≤ A := by
    rw [hAdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hKsA : 16 * Real.log (1 / Ks) / 3 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]; exact le_max_left _ _
  have hT₀A : T₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hA162 : (162 : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_right A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hA₀A : A₀ ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_trans (le_max_left A₀ 162)
      (le_max_left (max A₀ 162) Awin)) (le_max_left _ (cofkRThr Cq Cb Xsk Y0)))
      (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAwinA : Awin ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (max A₀ 162) Awin)
      (le_max_left _ (cofkRThr Cq Cb Xsk Y0))) (le_max_left _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hthrA : cofkRThr Cq Cb Xsk Y0 ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_right (max (max A₀ 162) Awin)
      (cofkRThr Cq Cb Xsk Y0)) (le_max_left _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hAge : budgetAFlat (ε : ℝ) β ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_max_left (budgetAFlat (ε : ℝ) β) _)
      (le_max_right _ _)) (le_max_right _ _)) (le_max_right _ _)
  have hx0A : 4 * (x₀ : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_left (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hopqA : ((Hopq : ℕ) : ℝ) ≤ A := by
    refine le_trans ?_ hlift; rw [hA'def]
    exact le_trans (le_trans (le_trans (le_trans (le_max_right (4 * (x₀ : ℝ)) ((Hopq : ℕ) : ℝ))
      (le_max_right (budgetAFlat (ε : ℝ) β) _)) (le_max_right _ _)) (le_max_right _ _))
      (le_max_right _ _)
  have hx0nn : (0 : ℝ) ≤ (x₀ : ℝ) := Nat.cast_nonneg _
  have hexp1 : 3.2 * A + 1 ≤ Real.exp (3.2 * A) := Real.add_one_le_exp _
  -- ⟦THE `Ks` WINDOW, AT THE SEVENTH ARM⟧ as in the parent
  have hKswin : Real.log (1 / Ks) ≤ 3 * Real.exp (3.2 * A) / 16 := by linarith
  have hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10) :=
    Salt.MR.x0_le_exp_exp_of_four_le hx0nn hx0A
  have hopq : Hopq ≤ flatDesignBase A := le_flatDesignBase_of_le hopqA
  have hA26 : (26 : ℝ) ≤ A := by linarith
  have hKw : KlevF A ≤ 170000000 * flatDoorM A := KlevF_le_wideCeiling hA26
  obtain ⟨Ct, hCt, hmain⟩ := hmainU (KlevF A)
  obtain ⟨hbase, hfire⟩ := hmain A hA162 hAwinA hAge hAL hKw
  -- ⟦THE `T₀` ARM⟧ V7-C's discharge, as in the parent
  have hT₀ : T₀ ≤ Real.exp (Real.sqrt ((flatDesignBase A : ℕ) : ℝ) / 2) :=
    t0_arm_le_tolerance hA162 hT₀A
  -- ⟦THE EXHIBITED CALLER⟧ `g ≡ 0` meets the strict rider; the `g`-conjunct is discarded
  obtain ⟨R, hReps, hHlo, -, hRx, hRtow, hdes, hwin, hfire2⟩ :=
    hfire hx0win hopq (by rw [hbase hopq]; exact hT₀) hKswin (fun _ _ : ℕ => 0)
      (xceilRiderStrictAt_zero _ ε)
  -- ⟦THE BASE-SCALE CAP⟧ at `K = KlevF A`, as in the parent
  have heps500 : (1 : ℚ) / (500 * (c : ℚ)) ≤ R.eps := by
    rw [hReps]; exact hεpin
  have hxceil : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [hReps]; exact hRx
  -- ⟦THE RATED SUPPLY, WITH THE CUSHION PAID BY THE EIGHTH ARM⟧
  have hM1 : 1 ≤ flatDoorM A := flatDoorM_one_le hA26
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have heps500R : (1 : ℝ) / (500 * (c : ℝ)) ≤ (R.eps : ℝ) := by
    rw [hReps]
    have hq := hεpin
    rw [div_le_iff₀ (by linarith)] at hq
    have h1R : (1 : ℝ) ≤ (ε : ℝ) * (500 * (c : ℝ)) := by exact_mod_cast hq
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- ⟦THE NINTH ARM, FIRST READER⟧ `3.2·(162 + 2·Lc) = 518.4 + 6.4·Lc ≥ 518 + 6·Lc` at `0 ≤ Lc`
  have h518 : (518 : ℝ) + 6 * Real.log (c : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) := by
    linarith [hdes, hA162b, hLc0]
  have hfl : loglogFloor50 ≤ R.Hlo := by rw [hHlo]; exact flatWitFloor_ll _ _ _ _
  have hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    rw [hHlo]; exact flatWitFloor_log_ge hA162
  -- ⟦THE NINTH ARM, SECOND READER⟧ `cofkRThr ≤ A`, `2·Lc ≤ A`, `2·A ≤ 3.2·A + 1 ≤ e^(3.2A)`
  have hthrgate : cofkRThr Cq Cb Xsk Y0 + 2 * Real.log (c : ℝ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    linarith [hthrA, hlo, hexp1, hAL, hA162]
  have hKvtcush : 32 * Kvt
      + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
      ≤ Real.log (R.Hhi : ℝ) / 4 :=
    cofkR_cushion_of_armVt R hKvt0 harmA hlo
  -- ⟦THE NINTH ARM, THIRD READER⟧ `Lc ≤ A ≤ 1.6·A + 1 ≤ e^(1.6·A)`
  have hexp16 : 3.2 * A / 2 + 1 ≤ Real.exp (3.2 * A / 2) := Real.add_one_le_exp _
  have hLt : Real.log (c : ℝ) ≤ Real.exp (3.2 * A / 2) := by linarith
  have hcofsupply : S16CofactorSupply_L_gk (KlevF A) Cq R (flatDoorM A) :=
    s16CofactorSupply_L_of_LH hc0
      (hcofR (KlevF A) Cq R (flatDoorM A) hM1 hCq heps500R h518 hfl hthrgate hKvtcush)
  have hfireR : P R :=
    hfire2 hcofsupply
      (s16BaseScaleCap96_L_of_LH hc0
        (s16_baseScaleCap96_LH_at_klevF_L (h := c) hc0 hLc0 le_rfl
          hA26 hLt (flatDoorM_one_le hA26) heps500 hxceil hwin))
  exact ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C,
    hε, hCg, hKc, hδ₀, hCt, hMfl1, hCq, hcs0, hcsf, hT₀3, hKq0, hKs0, hC0, hC40,
    hCgle, hc1, hεpin, hδpin, hMflb A hA162 hAwinA, hβ, hA162, hA₀A,
    R, hReps, by rw [hHlo]; exact hbase hopq, hRtow, hdes, hwin, hfireR⟩

end

section
open scoped BigOperators
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flat_chain_generic_epsW` (`Salt/MR/FlatDoorEpsRung2.lean:5544`): its
statement under the three standoff binders, its proof verbatim with `flat_kswin_generic_epsW` and
`flat_v7_generic_epsW` replaced by the standoff form. -/
theorem flat_chain_generic_epsW_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (ε : ℚ) (c : ℕ) (P : ChowlaRegime → Prop)
    (h : FlatHeadFormEpsW ε c P) (A₀ : ℝ) : V7RatedFormEpsW ε c P A₀ :=
  (flat_v7_generic_epsW_of_standoff hcS hSieg) ε c P (fun Awin hband =>
      (flat_kswin_generic_epsW_of_standoff hcS hSieg) ε c P Awin
    (flat_conditional_generic_epsW ε c P Awin
      (flat_capstone_generic_epsW ε c P
        (flat_road_generic_epsW ε c P
          (flat_doorL2_generic_epsW ε c P (flat_socket_generic_epsW ε c P h))) Awin hband))) A₀

end

section
open scoped BigOperators
open Salt.Entropy.Chowla
/-- **⟦STANDOFF TWIN⟧** `flatDoorEpsFamilyW_holds` (`Salt/MR/FlatDoorEpsRung2.lean:5570`): its
statement under the three standoff binders, its proof verbatim with `flat_head_uniform_xceil_epsW`
and `flat_chain_generic_epsW` replaced by the standoff form. -/
theorem flatDoorEpsFamilyW_holds_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) : FlatDoorEpsFamilyW := by
  unfold FlatDoorEpsFamilyW
  intro ε hε0 hε A₀
  have hε0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε0
  obtain ⟨c, hcdef⟩ : ∃ n : ℕ, n = ⌈(1 / (500 * ε) : ℚ)⌉₊ := ⟨_, rfl⟩
  have hεQ0 : (0 : ℚ) < 500 * ε := by linarith
  have hc1 : 1 ≤ c := by
    have h : 0 < c := by
      rw [hcdef]; exact Nat.ceil_pos.mpr (div_pos one_pos hεQ0)
    omega
  have hcQ1 : (1 : ℚ) ≤ (c : ℚ) := by exact_mod_cast hc1
  have hcQ0 : (0 : ℚ) < 500 * (c : ℚ) := by linarith
  have hcε : (1 : ℚ) / (500 * (c : ℚ)) ≤ ε := by
    have hle : (1 : ℚ) / (500 * ε) ≤ (c : ℚ) := by rw [hcdef]; exact Nat.le_ceil _
    rw [div_le_iff₀ hεQ0] at hle
    rw [div_le_iff₀ hcQ0]
    linarith
  have hV := (flat_chain_generic_epsW_of_standoff hcS hSieg) ε c
    (fun R : ChowlaRegime => MRTUniformityXiL2 R ((ε : ℝ) / (256 * (1 + 4 * Real.log 4))) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ (ε : ℝ) / (256 * (1 + 4 * Real.log 4)) →
        MRTUniformityXiL2 R ρ → ¬ logChowla2Fails R.eps R.x R.ω)
    (
        (flat_head_uniform_xceil_epsW_of_standoff hcS hSieg) ε hε0 hε hc1 hcε _
            (fun _ _ hd hs => ⟨hd, hs⟩)) A₀
  obtain ⟨Cg, Kc, δ₀, Ct, A, β, Mfl, Cq, cs, T₀, Kq, Ks, C, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hA162, hA₀A, R, hReps, hHlo, -, hdes, -, hdoor, hslot⟩ := hV
  exact ⟨(ε : ℝ) / (256 * (1 + 4 * Real.log 4)), A, by positivity, le_rfl,
    flatDoorMint_floor_le_grade (ε : ℝ) hε0R.le, hA162, hA₀A, R, hReps, hHlo, hdes,
    hdoor, hslot⟩

end

end Salt.MR

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **⟦THEOREM 4.25 UNDER THE STANDOFF⟧** `logChowla2_epsFamily_flatDoor_floor_holds`'s
conclusion token for token under three leading binders `{cS} (hcS : 0 < cS)
(hSieg : NoSiegelZerosAt cS)`: `logChowla2_epsFamily_of_flatDoor_floor` applied to the standoff
twin of `flatDoorEpsFamilyW_holds`.  See the certificate below for what it does not reach.
Nothing here bears on twin primes. -/
theorem logChowla2_epsFamily_flatDoor_floor_of_standoff {cS : ℝ} (hcS : 0 < cS)
    (hSieg : Salt.SW.NoSiegelZerosAt cS) (ε : ℚ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 500)
    (extraFloor : ℕ) :
    ∃ R : ChowlaRegime, R.eps = ε ∧ extraFloor ≤ R.Hlo ∧ ¬ logChowla2Fails R.eps R.x R.ω :=
  logChowla2_epsFamily_of_flatDoor_floor (flatDoorEpsFamilyW_holds_of_standoff hcS hSieg)
    ε hε0 hε extraFloor

end Salt.MR

open Salt.SW.StandoffCert

-- T: the targets must exist here, or every NOT-REACHED below is vacuous.
#assert_targets_exist

-- P+ (the instrument must see the reach it exists to see): Theorem 4.25 as landed, through each
-- cut node, and channel C's own entry.
#assert_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_holds Salt.SW.siegel_theorem
#assert_reaches Salt.MR.siegel_real_carve Salt.SW.siegel_theorem
#assert_reaches Salt.Chen.lambda_mass_lower Salt.SW.siegel_theorem

-- THE CERTIFICATE: the root reaches none of the three Siegel names.
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff Salt.SW.siegel_theorem
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff
  Salt.SW.siegel_L_one_exceptional
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff Salt.SW.L1_lower_siegel

-- And none of the three cut nodes it replaces.
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff
  Salt.MR.siegel_real_carve
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff
  Salt.SW.siegelWalfisz_holds
#assert_not_reaches Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff
  Salt.SW.psi1AP_main_bound

-- TOKEN CHECKS: each conclusion is its landed statement after the three standoff binders.
#assert_conclusion_is Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff 3
  Salt.MR.logChowla2_epsFamily_flatDoor_floor_holds
#assert_conclusion_is Salt.MR.standoff_real_carve 3 Salt.MR.siegel_real_carve
#assert_conclusion_is Salt.MR.xiCarveWidth_of_siegel_of_standoff 3
  Salt.MR.xiCarveWidth_of_siegel
#assert_conclusion_is Salt.MR.mmuChiRate_holds_gated_of_standoff 3
  Salt.MR.mmuChiRate_holds_gated
#assert_conclusion_is Salt.MR.s16_bandLaneWinL_holdsU_of_standoff 3
  Salt.MR.s16_bandLaneWinL_holdsU
#assert_conclusion_is Salt.MR.twisted_rect_zero_free_siegel_bounded_of_standoff 3
  Salt.MR.twisted_rect_zero_free_siegel_bounded
#assert_conclusion_is Salt.MR.halasz_primes_chi_pair_of_gates_bounded_cs_of_standoff 3
  Salt.MR.halasz_primes_chi_pair_of_gates_bounded_cs
#assert_conclusion_is Salt.MR.halaszPrimesChi_holds_gated_bounded_cs_of_standoff 3
  Salt.MR.halaszPrimesChi_holds_gated_bounded_cs
#assert_conclusion_is Salt.MR.halaszPrimesChi_pointwise_of_gates_bounded_cs_of_standoff 3
  Salt.MR.halaszPrimesChi_pointwise_of_gates_bounded_cs
#assert_conclusion_is Salt.MR.usetGChi_window_meansq_gated_family_perBlock_bounded_cs_of_standoff 3
  Salt.MR.usetGChi_window_meansq_gated_family_perBlock_bounded_cs
#assert_conclusion_is Salt.MR.usetGChi_row_exit_perChi_perBlock_bounded_cs_of_standoff 3
  Salt.MR.usetGChi_row_exit_perChi_perBlock_bounded_cs
#assert_conclusion_is Salt.MR.m4_rowChi_capstone_perBlock_bounded_cs_of_standoff 3
  Salt.MR.m4_rowChi_capstone_perBlock_bounded_cs
#assert_conclusion_is Salt.MR.m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs_of_standoff 3
  Salt.MR.m4_hcap_at_door_perBlock_L_gk_bounded_khoist_cs
#assert_conclusion_is Salt.MR.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs_of_standoff 3
  Salt.MR.m4_fuse_hcap_of_capWS_L_gk_ceiling_khoist_cs
open Salt.MR in
#assert_conclusion_is s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin_of_standoff 3
  Salt.MR.s15_crossing_supplied_L_gk_ceiling_sharpT0_khoist_csfree_kswin
#assert_conclusion_is Salt.Entropy.Chowla.primeWindow_sum_inv_ge_bounded_of_standoff 3
  Salt.Entropy.Chowla.primeWindow_sum_inv_ge_bounded
#assert_conclusion_is Salt.Entropy.Chowla.hbudget_holds_bounded_of_standoff 3
  Salt.Entropy.Chowla.hbudget_holds_bounded
#assert_conclusion_is Salt.Entropy.Chowla.hreduce_holds_final_bounded_of_standoff 3
  Salt.Entropy.Chowla.hreduce_holds_final_bounded
#assert_conclusion_is Salt.MR.flat_head_uniform_xceil_epsW_of_standoff 3
  Salt.MR.flat_head_uniform_xceil_epsW
#assert_conclusion_is Salt.MR.flat_kswin_generic_epsW_of_standoff 3
  Salt.MR.flat_kswin_generic_epsW
#assert_conclusion_is Salt.MR.flat_v7_generic_epsW_of_standoff 3
  Salt.MR.flat_v7_generic_epsW
#assert_conclusion_is Salt.MR.flat_chain_generic_epsW_of_standoff 3
  Salt.MR.flat_chain_generic_epsW
#assert_conclusion_is Salt.MR.flatDoorEpsFamilyW_holds_of_standoff 3
  Salt.MR.flatDoorEpsFamilyW_holds

#closure_report Salt.MR.logChowla2_epsFamily_flatDoor_floor_of_standoff
