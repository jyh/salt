/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuS5

/-!
# ShiuS5b — the last stretch: Class III + Class IV discharges and `ShiuCore`

This file closes the pinned-scale composition begun in `ShiuS5`.  The partition
spine, the corner, and the degenerate/I/II discharges landed there; here we supply
the remaining two class discharges and glue everything into
`sum_tau_in_ap_le : ShiuCore` (defined in `ShiuBlocks`).
-/

namespace Salt.Maynard

open Finset

/-! ## §1  A poly-beats-polylog threshold helper (quarter-power form) -/

/-- **Quarter-power poly-beats-polylog.**  For any `K`, eventually
`K·y^{1/4}·(1+log y) ≤ y`.  Packages `eventually_poly_beats_polylog 1 (3/4)`. -/
private lemma quarter_poly_beats (K : ℝ) :
    ∃ Y0 : ℝ, ∀ y : ℝ, Y0 ≤ y → K * (y ^ (1 / 4 : ℝ) * (1 + Real.log y)) ≤ y := by
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.mp
    (eventually_poly_beats_polylog 1 (3 / 4) K (by norm_num))
  refine ⟨max Y0 1, fun y hy => ?_⟩
  have hyY0 : Y0 ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_right _ _) hy
  have hypos : (0 : ℝ) < y := by linarith
  have hpb := hY0 y hyY0
  rw [pow_one] at hpb
  have hy14 : (0 : ℝ) ≤ y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hypos.le _
  calc K * (y ^ (1 / 4 : ℝ) * (1 + Real.log y))
      = y ^ (1 / 4 : ℝ) * (K * (1 + Real.log y)) := by ring
    _ ≤ y ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_left hpb hy14
    _ = y := by
        rw [← Real.rpow_add hypos, show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num, Real.rpow_one]

/-! ## §2  The Class III discharge -/

set_option maxHeartbeats 1200000 in
-- A long chain of rpow/exp estimates through one declaration; 200000 is insufficient.
/-- **Class III discharge.**  At the pinned scale (`W = ⌊z^{1/48000}⌋`,
`w = ⌊z^{1/24000}⌋`, `P₀ = ⌊log z⌋`), fire `shiu_classIII_le` with `δ = 1/1536000`
and the RAW Rankin bound `RB = W^{-1/4}·∏_{p≤P₀}(1-p^{-3/4})^{-2}` (σ = 3/4).  The
Euler product is subpolynomial (`sum_rpow_neg_sub_inv_le` + Mertens), so `z^δ·RB ≤ 1`
beyond a poly-beats threshold, and the junk `z^δ·w(1+log w)` folds as in deg/I/II. -/
theorem classIII_discharge :
    ∃ (CIII BIII : ℝ), 0 ≤ CIII ∧ ∀ (z q a : ℕ), BIII ≤ Real.log z → 1 ≤ q →
      Nat.Coprime a q → (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000) →
      ∑ n ∈ (Finset.Icc 1 z).filter
          (fun n => n % q = a ∧ shiuClassIII (wp z) (Wp z) (P0p z) n),
          (n.divisors.card : ℝ)
        ≤ CIII * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  obtain ⟨Cδ, hCδ, htau⟩ := card_divisors_le_rpow (1 / 1536000) (by norm_num)
  obtain ⟨Cmert, hmert⟩ := sum_inv_prime_le
  set Cmert' : ℝ := max Cmert 0 with hCmert'
  have hCmert'0 : 0 ≤ Cmert' := le_max_right _ _
  set Kc : ℝ := (1 / 4) * (Real.log 4 + 5) + 1 + Cmert' with hKc
  obtain ⟨Y0, hY0⟩ := quarter_poly_beats (512000 * (8 * Kc))
  refine ⟨3 * Cδ, max Y0 (max (96000 * Real.log 2) 2), by positivity, ?_⟩
  intro z q a hLz hq ha hqz
  have hY0le : Y0 ≤ Real.log z := le_trans (le_max_left _ _) hLz
  have hL96 : 96000 * Real.log 2 ≤ Real.log z :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLz
  have hL2 : (2 : ℝ) ≤ Real.log z :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLz
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogzpos : (0 : ℝ) < Real.log z := by linarith
  have hz2 : 2 ≤ z := by
    rcases Nat.lt_or_ge z 2 with h | h
    · interval_cases z <;>
        simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one] at hlogzpos <;>
        linarith
    · exact h
  have hz1 : 1 ≤ z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hlogz1 : (1 : ℝ) ≤ Real.log z := by linarith
  -- pinned-scale facts
  have hP2 : 2 ≤ P0p z := by rw [P0p]; exact Nat.le_floor (by exact_mod_cast hL2)
  have hP1 : 1 ≤ P0p z := by omega
  have hW1 : 1 ≤ Wp z := one_le_Wp hz1
  have hw1 : 1 ≤ wp z := one_le_wp hz1
  have hzdiv : (z : ℝ) ^ ((1 : ℝ) / 8000) ≤ (z : ℝ) / (q.totient : ℝ) :=
    z_rpow_le_div_phi hq hz1 hqz
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  set P : Finset ℕ := (Finset.range (P0p z + 1)).filter Nat.Prime with hPdef
  set σ : ℝ := 3 / 4 with hσdef
  set y : ℝ := Real.log z with hydef
  set L : ℝ := Real.log y with hLdef
  set M : ℝ := y ^ (1 / 4 : ℝ) * (1 + L) with hMdef
  set S : ℝ := ∑ p ∈ P, (p : ℝ) ^ (-σ) with hSdef
  -- the raw Rankin bound and its nonnegativity
  set RB : ℝ := (Wp z : ℝ) ^ (-(1 - σ))
    * ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 with hRBdef
  have hprodnn : (0 : ℝ) ≤ ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 := by
    apply Finset.prod_nonneg; intro p _; positivity
  have hRank : ∑ c ∈ (Finset.Icc 1 (wp z)).filter
      (fun c => (∀ p ∈ c.primeFactors, p ≤ P0p z) ∧ Wp z < c),
      (c.divisors.card : ℝ) / (c : ℝ) ≤ RB :=
    sum_tau_smooth_gt_rankin_le (wp z) (P0p z) (Wp z) σ hP2 (by norm_num) (by norm_num) hW1
  have hRBnn : 0 ≤ RB := by
    rw [hRBdef]; exact mul_nonneg (Real.rpow_nonneg (by positivity) _) hprodnn
  -- log facts about P₀
  have hP0R : (P0p z : ℝ) ≤ Real.log z := by rw [P0p]; exact Nat.floor_le hlogzpos.le
  have hP0pos : (0 : ℝ) < (P0p z : ℝ) := by exact_mod_cast (by omega : 0 < P0p z)
  have hlogP0pos : (0 : ℝ) < Real.log (P0p z) := Real.log_pos (by exact_mod_cast hP2)
  have hlogP0_le : Real.log (P0p z) ≤ L := by
    rw [hLdef, hydef]; exact Real.log_le_log hP0pos hP0R
  have hloglogP0_le : Real.log (Real.log (P0p z)) ≤ L :=
    le_trans (le_trans (Real.log_le_sub_one_of_pos hlogP0pos) (by linarith)) hlogP0_le
  -- basic bounds on y, L, M
  have hLnn : (0 : ℝ) ≤ L := by rw [hLdef]; exact Real.log_nonneg (by rw [hydef]; linarith)
  have hy14ge : (1 : ℝ) ≤ y ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by rw [hydef]; linarith) (by norm_num)
  have hy14nn : (0 : ℝ) ≤ y ^ (1 / 4 : ℝ) := by linarith
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]; calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ y ^ (1 / 4 : ℝ) * (1 + L) := mul_le_mul hy14ge (by linarith) (by norm_num) hy14nn
  -- ## bound Σ_{p≤P₀} p^{-3/4} ≤ Kc·M
  have hsig_split :
      S = (∑ p ∈ P, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)) + ∑ p ∈ P, (p : ℝ)⁻¹ := by
    rw [hSdef, Finset.sum_sub_distrib]; ring
  have hmertP : ∑ p ∈ P, (p : ℝ)⁻¹ ≤ Real.log (Real.log (P0p z)) + Cmert := by
    have h := hmert (P0p z) hP2; simp only [one_div] at h; rw [hPdef]; exact h
  have hsubP : ∑ p ∈ P, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)
      ≤ (1 - σ) * (P0p z : ℝ) ^ (1 - σ) * (Real.log (P0p z) + (Real.log 4 + 4)) := by
    rw [hPdef, hσdef]
    exact sum_rpow_neg_sub_inv_le (P0p z) (σ := 3 / 4) hP1 (by norm_num) (by norm_num)
  have hA : (1 - σ) * (P0p z : ℝ) ^ (1 - σ) * (Real.log (P0p z) + (Real.log 4 + 4))
      ≤ (1 / 4) * (Real.log 4 + 5) * M := by
    have h1σ : (1 - σ) = (1 / 4 : ℝ) := by rw [hσdef]; norm_num
    have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hlfac : Real.log (P0p z) + (Real.log 4 + 4) ≤ (Real.log 4 + 5) * (1 + L) := by
      have hexp : (Real.log 4 + 5) * (1 + L) = Real.log 4 + 5 + Real.log 4 * L + 5 * L := by ring
      rw [hexp]; linarith [hlogP0_le, hLnn, mul_nonneg hlog4nn hLnn]
    have hbase : (P0p z : ℝ) ^ (1 - σ) ≤ y ^ (1 / 4 : ℝ) := by
      rw [h1σ, hydef]; exact Real.rpow_le_rpow hP0pos.le hP0R (by norm_num)
    rw [h1σ]
    calc (1 / 4 : ℝ) * (P0p z : ℝ) ^ (1 / 4 : ℝ) * (Real.log (P0p z) + (Real.log 4 + 4))
        ≤ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) * ((Real.log 4 + 5) * (1 + L)) := by
          apply mul_le_mul _ hlfac (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [h1σ] at hbase; exact hbase
      _ = (1 / 4) * (Real.log 4 + 5) * M := by rw [hMdef]; ring
  have hB : Real.log (Real.log (P0p z)) + Cmert ≤ (1 + Cmert') * M := by
    have hML : L ≤ M := by
      rw [hMdef]; calc L ≤ 1 + L := by linarith
        _ = 1 * (1 + L) := by ring
        _ ≤ y ^ (1 / 4 : ℝ) * (1 + L) := mul_le_mul_of_nonneg_right hy14ge (by linarith)
    have h1 : Real.log (Real.log (P0p z)) ≤ M := le_trans hloglogP0_le hML
    have h2 : Cmert ≤ Cmert' * M :=
      le_trans (le_max_left _ _) (le_mul_of_one_le_right hCmert'0 hM1)
    have hexp : (1 + Cmert') * M = M + Cmert' * M := by ring
    rw [hexp]; linarith [h1, h2]
  have hsigma : S ≤ Kc * M := by
    rw [hKc]
    calc S = (∑ p ∈ P, ((p : ℝ) ^ (-σ) - (p : ℝ)⁻¹)) + ∑ p ∈ P, (p : ℝ)⁻¹ :=
          hsig_split
      _ ≤ (1 - σ) * (P0p z : ℝ) ^ (1 - σ) * (Real.log (P0p z) + (Real.log 4 + 4))
            + (Real.log (Real.log (P0p z)) + Cmert) := add_le_add hsubP hmertP
      _ ≤ (1 / 4) * (Real.log 4 + 5) * M + (1 + Cmert') * M := add_le_add hA hB
      _ = ((1 / 4) * (Real.log 4 + 5) + 1 + Cmert') * M := by ring
  -- the exp-argument threshold: 8·S ≤ (1/512000)·log z
  have h8sig : 8 * S ≤ (1 / 512000) * y := by
    have hbeat := hY0 y hY0le
    rw [show Real.log y = L from hLdef.symm] at hbeat
    calc 8 * S ≤ 8 * (Kc * M) := mul_le_mul_of_nonneg_left hsigma (by norm_num)
      _ = (1 / 512000) * (512000 * (8 * Kc) * M) := by ring
      _ ≤ (1 / 512000) * y :=
          mul_le_mul_of_nonneg_left (by rw [hMdef]; exact hbeat) (by norm_num)
  -- ## z^δ · RB ≤ 1
  have hWgain : (Wp z : ℝ) ^ (-(1 - σ)) ≤ (z : ℝ) ^ (-(1 / 384000 : ℝ)) := by
    have hWpos : (0 : ℝ) < (Wp z : ℝ) := by exact_mod_cast one_le_Wp hz1
    have hlogWge : (1 / 96000 : ℝ) * Real.log z ≤ Real.log (Wp z) := logWp_ge hL96
    have key : Real.log (Wp z) * (-(1 - σ)) ≤ Real.log z * (-(1 / 384000 : ℝ)) := by
      rw [hσdef, show -(1 - (3 / 4 : ℝ)) = -(1 / 4 : ℝ) by norm_num]; linarith [hlogWge]
    calc (Wp z : ℝ) ^ (-(1 - σ)) = Real.exp (Real.log (Wp z) * (-(1 - σ))) := by
          rw [Real.rpow_def_of_pos hWpos]
      _ ≤ Real.exp (Real.log z * (-(1 / 384000 : ℝ))) := Real.exp_le_exp.mpr key
      _ = (z : ℝ) ^ (-(1 / 384000 : ℝ)) := by rw [Real.rpow_def_of_pos hzpos]
  have hProd :
      ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2 ≤ (z : ℝ) ^ (1 / 512000 : ℝ) := by
    have hpe := prod_one_sub_rpow_neg_sq_le_exp (P0p z) (σ := σ) (by rw [hσdef]; norm_num)
    calc ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2
        ≤ Real.exp (8 * S) := by rw [hSdef, hPdef]; exact hpe
      _ ≤ Real.exp ((1 / 512000) * y) := Real.exp_le_exp.mpr h8sig
      _ = (z : ℝ) ^ (1 / 512000 : ℝ) := by
          rw [hydef, Real.rpow_def_of_pos hzpos]; congr 1; ring
  have hzRB : (z : ℝ) ^ (1 / 1536000 : ℝ) * RB ≤ 1 := by
    rw [hRBdef]
    have hstep : (z : ℝ) ^ (1 / 1536000 : ℝ)
          * ((Wp z : ℝ) ^ (-(1 - σ)) * ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2)
        ≤ (z : ℝ) ^ (1 / 1536000 : ℝ)
          * ((z : ℝ) ^ (-(1 / 384000 : ℝ)) * (z : ℝ) ^ (1 / 512000 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hWgain hProd hprodnn (by positivity)) (by positivity)
    calc (z : ℝ) ^ (1 / 1536000 : ℝ)
          * ((Wp z : ℝ) ^ (-(1 - σ)) * ∏ p ∈ P, (1 - (p : ℝ) ^ (-σ))⁻¹ ^ 2)
        ≤ (z : ℝ) ^ (1 / 1536000 : ℝ)
          * ((z : ℝ) ^ (-(1 / 384000 : ℝ)) * (z : ℝ) ^ (1 / 512000 : ℝ)) := hstep
      _ = 1 := by
          rw [← Real.rpow_add hzpos, ← Real.rpow_add hzpos,
            show (1 / 1536000 : ℝ) + (-(1 / 384000) + 1 / 512000) = 0 by norm_num, Real.rpow_zero]
  -- ## fire the class-III bound and fold
  have hIII := shiu_classIII_le (z := z) (q := q) (a := a) (w := wp z) (W := Wp z) (P₀ := P0p z)
    (1 / 1536000) Cδ RB hq hw1 ha hCδ (by norm_num) htau hRank
  have hzq_le : (z : ℝ) / q ≤ (z : ℝ) / (q.totient : ℝ) :=
    div_le_div_of_nonneg_left hzpos.le hφpos hφq
  have hTerm1 : Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ) * ((z : ℝ) / q * RB)
      ≤ Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    calc Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ) * ((z : ℝ) / q * RB)
        = (Cδ * ((z : ℝ) / q)) * ((z : ℝ) ^ (1 / 1536000 : ℝ) * RB) := by ring
      _ ≤ (Cδ * ((z : ℝ) / q)) * 1 := mul_le_mul_of_nonneg_left hzRB (by positivity)
      _ = Cδ * ((z : ℝ) / q) := by ring
      _ ≤ Cδ * ((z : ℝ) / (q.totient : ℝ)) := mul_le_mul_of_nonneg_left hzq_le hCδ.le
      _ ≤ Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
          le_mul_of_one_le_right (by positivity) hlogz1
  have hTerm2 : Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ) * ((wp z : ℝ) * (1 + Real.log (wp z)))
      ≤ 2 * Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    have hlogw0 : (0 : ℝ) ≤ 1 + Real.log (wp z) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (wp z : ℝ) by exact_mod_cast hw1); linarith
    have hlogwle : 1 + Real.log (wp z) ≤ 2 * Real.log z := by
      have := logwp_le hz2; linarith [hlogz1]
    have hchain : (z : ℝ) ^ (1 / 1536000 : ℝ) * ((wp z : ℝ) * (1 + Real.log (wp z)))
        ≤ 2 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
      have hexple :
          (z : ℝ) ^ ((1 / 1536000 : ℝ) + 1 / 24000) ≤ (z : ℝ) ^ (1 / 8000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hz1) (by norm_num)
      calc (z : ℝ) ^ (1 / 1536000 : ℝ) * ((wp z : ℝ) * (1 + Real.log (wp z)))
          ≤ (z : ℝ) ^ (1 / 1536000 : ℝ)
              * ((z : ℝ) ^ (1 / 24000 : ℝ) * (2 * Real.log z)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul wp_le hlogwle hlogw0 (by positivity)
        _ = (2 * Real.log z)
              * ((z : ℝ) ^ (1 / 1536000 : ℝ) * (z : ℝ) ^ (1 / 24000 : ℝ)) := by
            ring
        _ = (2 * Real.log z) * (z : ℝ) ^ ((1 / 1536000 : ℝ) + 1 / 24000) := by
            rw [← Real.rpow_add hzpos]
        _ ≤ (2 * Real.log z) * (z : ℝ) ^ (1 / 8000 : ℝ) :=
            mul_le_mul_of_nonneg_left hexple (by linarith [hlogz1])
        _ ≤ (2 * Real.log z) * ((z : ℝ) / (q.totient : ℝ)) :=
            mul_le_mul_of_nonneg_left hzdiv (by linarith [hlogz1])
        _ = 2 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring
    calc Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ) * ((wp z : ℝ) * (1 + Real.log (wp z)))
        = Cδ * ((z : ℝ) ^ (1 / 1536000 : ℝ)
            * ((wp z : ℝ) * (1 + Real.log (wp z)))) := by ring
      _ ≤ Cδ * (2 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z) :=
          mul_le_mul_of_nonneg_left hchain hCδ.le
      _ = 2 * Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring
  calc ∑ n ∈ (Finset.Icc 1 z).filter
          (fun n => n % q = a ∧ shiuClassIII (wp z) (Wp z) (P0p z) n), (n.divisors.card : ℝ)
      ≤ Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ)
          * ((z : ℝ) / q * RB + (wp z : ℝ) * (1 + Real.log (wp z))) := hIII
    _ = Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ) * ((z : ℝ) / q * RB)
          + Cδ * (z : ℝ) ^ (1 / 1536000 : ℝ)
            * ((wp z : ℝ) * (1 + Real.log (wp z))) := by ring
    _ ≤ Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
          + 2 * Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := add_le_add hTerm1 hTerm2
    _ = 3 * Cδ * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring

/-! ## §3  The Class IV discharge -/

set_option maxHeartbeats 1600000 in
-- Seven Rbin/vCut floor facts + the Mertens fold + the double-exp junk in one
-- declaration; the default 200000 heartbeats is insufficient.
/-- **Class IV discharge.**  Fires `shiu_classIV_le` with `Kd = 48000` at the pinned
scale.  The Mertens fold `exp(2 Σ_{p≤W²}1/p)/log(W²) ≤ e^{2C}·log(W²)` collapses the
main term to `C·(z/φq)·log z`; the junk `Σ_{r=2}^R A₅^{r+1}` (`A₅ = 2^{48000}`) closes
because `R ≤ y/(24000(loglog z - log2))` makes `A₅^{R+1} = z^{o(1)}` beyond the
double-exponential threshold `loglog z ≥ 192001·log 2`. -/
theorem classIV_discharge :
    ∃ (CIV BIV : ℝ), 0 ≤ CIV ∧ ∀ (z q a : ℕ), BIV ≤ Real.log z → 1 ≤ q →
      Nat.Coprime a q → (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000) →
      ∑ n ∈ (Finset.Icc 1 z).filter
          (fun n => n % q = a ∧ shiuClassIV (wp z) (Wp z) (P0p z) n),
          (n.divisors.card : ℝ)
        ≤ CIV * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  obtain ⟨Cmain, Cjunk, hCmain0, hCjunk0, hIV⟩ := shiu_classIV_le 48000 (by norm_num)
  obtain ⟨Cmert, hmert⟩ := sum_inv_prime_le
  obtain ⟨Y1, hY1⟩ :=
    Filter.eventually_atTop.mp (eventually_poly_beats_polylog 1 1 192000 (by norm_num))
  obtain ⟨W2b, hW2b⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually_ge_atTop (192001 * Real.log 2))
  refine ⟨Cmain * Real.exp (2 * Cmert) + Cjunk * (2 * 2 ^ 48000),
      max (max Y1 W2b) (max (96000 * Real.log 2) 4),
      by positivity, ?_⟩
  intro z q a hLz hq ha hqz
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hYm1 : Y1 ≤ Real.log z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLz
  have hW2 : W2b ≤ Real.log z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLz
  have hL96 : 96000 * Real.log 2 ≤ Real.log z :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLz
  have hL4 : (4 : ℝ) ≤ Real.log z :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLz
  have hlogzpos : (0 : ℝ) < Real.log z := by linarith
  have hz2 : 2 ≤ z := by
    rcases Nat.lt_or_ge z 2 with h | h
    · interval_cases z <;>
        simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one] at hlogzpos <;>
        linarith
    · exact h
  have hz1 : 1 ≤ z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hlogz1 : (1 : ℝ) ≤ Real.log z := by linarith
  set y : ℝ := Real.log z with hydef
  -- master poly-beats and double-exp facts
  have hmaster : 192000 * (1 + Real.log y) ≤ y := by
    have := hY1 y hYm1; rwa [pow_one, Real.rpow_one] at this
  have hlogy : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hlogz1
  have hdblexp : 192001 * Real.log 2 ≤ Real.log y := hW2b y hW2
  -- pinned scales
  have hW1 : 1 ≤ Wp z := one_le_Wp hz1
  have hw1 : 1 ≤ wp z := one_le_wp hz1
  have hWR1 : (1 : ℝ) < (Wp z : ℝ) := by
    have hWge : (z : ℝ) ^ ((1 : ℝ) / 96000) ≤ (Wp z : ℝ) := Wp_ge hL96
    have h2 : (2 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 96000) := by
      rw [Real.rpow_def_of_pos hzpos,
        show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
      exact Real.exp_le_exp.mpr (by rw [hydef] at *; nlinarith [hL96])
    linarith
  have hW2nat : 2 ≤ Wp z := by
    have h : 1 < Wp z := by exact_mod_cast hWR1
    omega
  have hlogW : (0 : ℝ) < Real.log (Wp z) := Real.log_pos hWR1
  have hlogWlo : (1 / 96000 : ℝ) * y ≤ Real.log (Wp z) := by rw [hydef]; exact logWp_ge hL96
  have hlogWhi : Real.log (Wp z) ≤ (1 / 48000 : ℝ) * y := by rw [hydef]; exact logWp_le hz2
  have hlog2W : Real.log 2 ≤ Real.log (Wp z) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hW2nat)
  -- P₀ facts
  have hP0R : (P0p z : ℝ) ≤ y := by rw [hydef, P0p]; exact Nat.floor_le hlogzpos.le
  have hP0lt : y < (P0p z : ℝ) + 1 := by rw [hydef, P0p]; exact Nat.lt_floor_add_one _
  have hP0half : y / 2 ≤ (P0p z : ℝ) := by linarith
  have hP4 : 4 ≤ P0p z := by rw [P0p]; exact Nat.le_floor (by exact_mod_cast hL4)
  have hP2 : 2 ≤ P0p z := by omega
  have hP3 : 3 ≤ P0p z := by omega
  have hP0pos : (0 : ℝ) < (P0p z : ℝ) := by exact_mod_cast (by omega : 0 < P0p z)
  have hlogP0 : (0 : ℝ) < Real.log (P0p z) := Real.log_pos (by exact_mod_cast hP2)
  have hlog2P0 : Real.log 2 ≤ Real.log (P0p z) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hP2)
  have hlog4P0 : Real.log 4 ≤ Real.log (P0p z) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hP4)
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlogP0hi : Real.log (P0p z) ≤ Real.log y := by
    rw [hydef] at hP0R ⊢; exact Real.log_le_log hP0pos hP0R
  have hlogP0lo : Real.log y - Real.log 2 ≤ Real.log (P0p z) := by
    have : Real.log (y / 2) ≤ Real.log (P0p z) := Real.log_le_log (by linarith) hP0half
    rwa [Real.log_div (by linarith) (by norm_num)] at this
  -- R facts
  set R : ℕ := Rbin (Wp z) (P0p z) with hRdef
  have hRle : (R : ℝ) ≤ 2 * Real.log (Wp z) / Real.log (P0p z) := by
    rw [hRdef, Rbin]; exact Nat.floor_le (by positivity)
  have hRlogP0 : (R : ℝ) * Real.log (P0p z) ≤ 2 * Real.log (Wp z) := by
    rw [le_div_iff₀ hlogP0] at hRle; linarith [hRle]
  -- hkey: 2 log W ≤ P₀ · log P₀
  have hkey : 2 * Real.log (Wp z) ≤ (P0p z : ℝ) * Real.log (P0p z) := by
    have h1 : 2 * Real.log (Wp z) ≤ y / 24000 := by linarith [hlogWhi]
    have h2 : y / 24000 ≤ (y / 2) * Real.log 2 := by
      nlinarith [Real.log_two_gt_d9, hlogzpos, hydef]
    have h3 : (y / 2) * Real.log 2 ≤ (P0p z : ℝ) * Real.log (P0p z) :=
      mul_le_mul hP0half hlog2P0 hlog2.le hP0pos.le
    linarith
  have hRleP0 : (R : ℝ) ≤ (P0p z : ℝ) := by
    have hb : 2 * Real.log (Wp z) / Real.log (P0p z) ≤ (P0p z : ℝ) := by
      rw [div_le_iff₀ hlogP0]; linarith [hkey]
    linarith [hRle, hb]
  have hR2 : 2 ≤ R := by
    rw [hRdef, Rbin]
    apply Nat.le_floor
    rw [Nat.cast_ofNat, le_div_iff₀ hlogP0]
    have : Real.log (P0p z) ≤ Real.log (Wp z) := by
      calc Real.log (P0p z) ≤ Real.log y := hlogP0hi
        _ ≤ 1 + Real.log y := by linarith
        _ ≤ y / 192000 := by linarith [hmaster]
        _ ≤ (1 / 96000 : ℝ) * y := by linarith
        _ ≤ Real.log (Wp z) := hlogWlo
    linarith
  have hR1 : 1 ≤ R := by omega
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
  -- vCut hyps
  have hWpos : (0 : ℝ) < (Wp z : ℝ) := by linarith
  have hvR3 : 3 ≤ vCut (Wp z) R := by
    rw [vCut]
    apply Nat.le_floor
    have hexp : Real.log (P0p z) ≤ (2 : ℝ) / (R : ℝ) * Real.log (Wp z) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hRpos]; nlinarith [hRlogP0]
    have hpow : (P0p z : ℝ) ≤ (Wp z : ℝ) ^ ((2 : ℝ) / (R : ℝ)) := by
      rw [← Real.exp_log hP0pos, ← Real.exp_log (Real.rpow_pos_of_pos hWpos _)]
      apply Real.exp_le_exp.mpr
      rw [Real.log_rpow hWpos]; exact hexp
    exact le_trans (by exact_mod_cast hP3) hpow
  have htR2 : 2 ≤ vCut (Wp z) (R + 1) := by
    rw [vCut]
    apply Nat.le_floor
    have hR1P0 : (R : ℝ) * Real.log 2 ≤ Real.log (Wp z) := by
      have : (R : ℝ) * (2 * Real.log 2) ≤ 2 * Real.log (Wp z) := by
        calc (R : ℝ) * (2 * Real.log 2) = (R : ℝ) * Real.log 4 := by rw [hlog4eq]
          _ ≤ (R : ℝ) * Real.log (P0p z) := mul_le_mul_of_nonneg_left hlog4P0 hRpos.le
          _ ≤ 2 * Real.log (Wp z) := hRlogP0
      linarith
    have hexp : Real.log 2 ≤ (2 : ℝ) / ((R + 1 : ℕ) : ℝ) * Real.log (Wp z) := by
      rw [show ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 from by push_cast; ring,
        div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [hR1P0, hlog2W]
    have hpow : (2 : ℝ) ≤ (Wp z : ℝ) ^ ((2 : ℝ) / ((R + 1 : ℕ) : ℝ)) := by
      rw [← Real.log_le_log_iff (by norm_num) (Real.rpow_pos_of_pos hWpos _), Real.log_rpow hWpos]
      exact hexp
    exact_mod_cast hpow
  have hRlogR : (R : ℝ) * Real.log R ≤ 2 * Real.log (Wp z) := by
    have hlogRP0 : Real.log R ≤ Real.log (P0p z) := Real.log_le_log hRpos hRleP0
    calc (R : ℝ) * Real.log R ≤ (R : ℝ) * Real.log (P0p z) :=
          mul_le_mul_of_nonneg_left hlogRP0 hRpos.le
      _ ≤ 2 * Real.log (Wp z) := hRlogP0
  have hlogzKd : Real.log z ≤ 48000 * Real.log ((Wp z : ℝ) ^ 2) := by
    rw [Real.log_pow]; push_cast; nlinarith [hlogWlo]
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hzdiv : (z : ℝ) ^ ((1 : ℝ) / 8000) ≤ (z : ℝ) / (q.totient : ℝ) :=
    z_rpow_le_div_phi hq hz1 hqz
  have hzq0 : (0 : ℝ) ≤ (z : ℝ) / (q.totient : ℝ) := by positivity
  -- fire the Class IV bound
  have hbnd := hIV z q a (wp z) (Wp z) (P0p z) hq hW2nat hw1 ha hP2
    (by rw [← hRdef]; exact hR2) (by rw [← hRdef]; exact hvR3) (by rw [← hRdef]; exact htR2)
    (by rw [← hRdef]; exact hRlogR) hlogzKd
  rw [← hRdef] at hbnd
  set A5 : ℝ := Real.exp (48000 * Real.log 2) with hA5def
  set E : ℝ := ∑ p ∈ (Finset.range (Wp z ^ 2 + 1)).filter Nat.Prime, (p : ℝ)⁻¹ with hEdef
  set T : ℝ := Real.log ((Wp z : ℝ) ^ 2) with hTdef
  have hA51 : (1 : ℝ) ≤ A5 := by rw [hA5def]; exact Real.one_le_exp (by positivity)
  have hA5nn : (0 : ℝ) ≤ A5 := by linarith
  have hA5eq : A5 = (2 : ℝ) ^ (48000 : ℕ) := by
    rw [hA5def, show (48000 : ℝ) = ((48000 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (by norm_num)]
  have hTeq : T = 2 * Real.log (Wp z) := by rw [hTdef, Real.log_pow]; push_cast; ring
  have hTpos : (0 : ℝ) < T := by rw [hTeq]; linarith [hlogW]
  have hTlogz : T ≤ Real.log z := by rw [hTeq, ← hydef]; linarith only [hlogWhi, hlogz1]
  -- ## main-term fold (Mertens)
  have hW2sq : 2 ≤ Wp z ^ 2 := le_trans hW2nat (Nat.le_self_pow (by norm_num) _)
  have hEle : E ≤ Real.log T + Cmert := by
    have hm := hmert (Wp z ^ 2) hW2sq
    simp only [one_div] at hm
    rw [hEdef, hTdef, show ((Wp z ^ 2 : ℕ) : ℝ) = (Wp z : ℝ) ^ 2 from by push_cast; ring] at *
    exact hm
  have hexp2E : Real.exp (2 * E) ≤ T ^ 2 * Real.exp (2 * Cmert) := by
    calc Real.exp (2 * E) ≤ Real.exp (2 * Real.log T + 2 * Cmert) :=
          Real.exp_le_exp.mpr (by linarith [hEle])
      _ = Real.exp (2 * Real.log T) * Real.exp (2 * Cmert) := Real.exp_add _ _
      _ = T ^ 2 * Real.exp (2 * Cmert) := by
          rw [show (2 : ℝ) * Real.log T = Real.log T + Real.log T by ring, Real.exp_add,
            Real.exp_log hTpos]; ring
  have hmainfold : Cmain * Real.exp (2 * E) * ((z : ℝ) / (q.totient : ℝ)) / T
      ≤ Cmain * Real.exp (2 * Cmert) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    rw [div_eq_mul_inv]
    calc Cmain * Real.exp (2 * E) * ((z : ℝ) / (q.totient : ℝ)) * T⁻¹
        ≤ Cmain * (T ^ 2 * Real.exp (2 * Cmert)) * ((z : ℝ) / (q.totient : ℝ)) * T⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hTpos.le)
          apply mul_le_mul_of_nonneg_right _ hzq0
          exact mul_le_mul_of_nonneg_left hexp2E hCmain0
      _ = Cmain * Real.exp (2 * Cmert) * ((z : ℝ) / (q.totient : ℝ)) * T := by
          rw [pow_two]; field_simp
      _ ≤ Cmain * Real.exp (2 * Cmert) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
          mul_le_mul_of_nonneg_left hTlogz (by positivity)
  -- ## junk-term fold (double-exponential threshold)
  have hW3 : (Wp z : ℝ) ^ 3 ≤ (z : ℝ) ^ (1 / 16000 : ℝ) := by
    calc (Wp z : ℝ) ^ 3 ≤ ((z : ℝ) ^ (1 / 48000 : ℝ)) ^ 3 := by gcongr; exact Wp_le
      _ = (z : ℝ) ^ (1 / 16000 : ℝ) := by
          rw [← Real.rpow_natCast ((z : ℝ) ^ (1 / 48000 : ℝ)) 3, ← Real.rpow_mul hzpos.le]
          norm_num
  have hw1logw :
      (wp z : ℝ) * (1 + Real.log (wp z)) ≤ 2 * (z : ℝ) ^ (1 / 24000 : ℝ) * Real.log z := by
    have hlw := logwp_le hz2
    have hlogwle : 1 + Real.log (wp z) ≤ 2 * Real.log z := by linarith [hlogz1]
    have hlogw0 : (0 : ℝ) ≤ 1 + Real.log (wp z) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (wp z : ℝ) by exact_mod_cast hw1); linarith
    calc (wp z : ℝ) * (1 + Real.log (wp z))
        ≤ (z : ℝ) ^ (1 / 24000 : ℝ) * (2 * Real.log z) :=
          mul_le_mul wp_le hlogwle hlogw0 (by positivity)
      _ = 2 * (z : ℝ) ^ (1 / 24000 : ℝ) * Real.log z := by ring
  have hRexp : (R : ℝ) * (48000 * Real.log 2) ≤ (1 / 96000) * Real.log z := by
    have hRD : (R : ℝ) * (Real.log y - Real.log 2) ≤ Real.log z / 24000 := by
      calc (R : ℝ) * (Real.log y - Real.log 2)
          ≤ (R : ℝ) * Real.log (P0p z) := mul_le_mul_of_nonneg_left hlogP0lo (by positivity)
        _ ≤ 2 * Real.log (Wp z) := hRlogP0
        _ ≤ Real.log z / 24000 := by rw [← hydef]; linarith only [hlogWhi]
    have hRprod : 192000 * ((R : ℝ) * Real.log 2) ≤ (R : ℝ) * (Real.log y - Real.log 2) := by
      have h0 := mul_nonneg (Nat.cast_nonneg R : (0:ℝ) ≤ (R:ℝ))
        (by linarith only [hdblexp] : (0:ℝ) ≤ Real.log y - Real.log 2 - 192000 * Real.log 2)
      have he : (R : ℝ) * (Real.log y - Real.log 2 - 192000 * Real.log 2)
          = (R : ℝ) * (Real.log y - Real.log 2) - 192000 * ((R : ℝ) * Real.log 2) := by ring
      rw [he] at h0; linarith only [h0]
    have hgoal : (R : ℝ) * (48000 * Real.log 2) = 48000 * ((R : ℝ) * Real.log 2) := by ring
    rw [hgoal]; linarith only [hRD, hRprod]
  have hA5R1 : A5 ^ (R + 1) ≤ (2 : ℝ) ^ (48000 : ℕ) * (z : ℝ) ^ (1 / 96000 : ℝ) := by
    rw [hA5def, ← Real.exp_nat_mul]
    have harg : ((R + 1 : ℕ) : ℝ) * (48000 * Real.log 2)
        ≤ (1 / 96000) * Real.log z + 48000 * Real.log 2 := by
      rw [show ((R + 1 : ℕ) : ℝ) = (R : ℝ) + 1 from by push_cast; ring]
      have he : ((R : ℝ) + 1) * (48000 * Real.log 2)
          = (R : ℝ) * (48000 * Real.log 2) + 48000 * Real.log 2 := by ring
      rw [he]; linarith only [hRexp]
    calc Real.exp (((R + 1 : ℕ) : ℝ) * (48000 * Real.log 2))
        ≤ Real.exp ((1 / 96000) * Real.log z + 48000 * Real.log 2) := Real.exp_le_exp.mpr harg
      _ = Real.exp ((1 / 96000) * Real.log z) * Real.exp (48000 * Real.log 2) := Real.exp_add _ _
      _ = (z : ℝ) ^ (1 / 96000 : ℝ) * (2 : ℝ) ^ (48000 : ℕ) := by
          rw [← hA5def, hA5eq]; congr 1
          rw [Real.rpow_def_of_pos hzpos]; congr 1; ring
      _ = (2 : ℝ) ^ (48000 : ℕ) * (z : ℝ) ^ (1 / 96000 : ℝ) := by rw [mul_comm]
  have hSum : (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1)) ≤ (R : ℝ) * A5 ^ (R + 1) := by
    calc ∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1) ≤ ∑ _r ∈ Finset.Icc 2 R, A5 ^ (R + 1) := by
          apply Finset.sum_le_sum; intro r hr; rw [Finset.mem_Icc] at hr
          exact pow_le_pow_right₀ hA51 (by omega)
      _ = ((Finset.Icc 2 R).card : ℝ) * A5 ^ (R + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R : ℝ) * A5 ^ (R + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Icc]; exact_mod_cast (by omega : R + 1 - 2 ≤ R)
  have hRlogz : (R : ℝ) ≤ Real.log z := by
    have h : (R : ℝ) * Real.log 2 ≤ Real.log z / 24000 := by
      calc (R : ℝ) * Real.log 2 ≤ (R : ℝ) * Real.log (P0p z) :=
            mul_le_mul_of_nonneg_left hlog2P0 (by positivity)
        _ ≤ 2 * Real.log (Wp z) := hRlogP0
        _ ≤ Real.log z / 24000 := by rw [← hydef]; linarith only [hlogWhi]
    have hRlb : (0.6 : ℝ) * (R : ℝ) ≤ (R : ℝ) * Real.log 2 := by
      have h0 := mul_nonneg (Nat.cast_nonneg R : (0:ℝ) ≤ (R:ℝ))
        (by linarith only [Real.log_two_gt_d9] : (0:ℝ) ≤ Real.log 2 - 0.6)
      have he : (R : ℝ) * (Real.log 2 - 0.6) = (R : ℝ) * Real.log 2 - 0.6 * (R : ℝ) := by ring
      rw [he] at h0; linarith only [h0]
    linarith only [h, hRlb, hlogz1]
  have hlogsq : (Real.log z) ^ 2 ≤ (z : ℝ) ^ (1 / 96000 : ℝ) := by
    have h2ly : 2 * Real.log y ≤ (1 / 96000) * Real.log z := by
      rw [← hydef]; linarith only [hmaster]
    have hsqexp : (Real.log z) ^ 2 = Real.exp (2 * Real.log y) := by
      have hexp : Real.exp (Real.log y) = y := Real.exp_log hlogzpos
      rw [two_mul, Real.exp_add, hexp, hydef]; ring
    rw [hsqexp]
    calc Real.exp (2 * Real.log y) ≤ Real.exp ((1 / 96000) * Real.log z) :=
          Real.exp_le_exp.mpr h2ly
      _ = (z : ℝ) ^ (1 / 96000 : ℝ) := by rw [Real.rpow_def_of_pos hzpos]; congr 1; ring
  have hlogz0 : (0 : ℝ) ≤ Real.log z := by linarith [hlogz1]
  have hwfac : (0 : ℝ) ≤ (wp z : ℝ) * (1 + Real.log (wp z)) := by
    have h1 : (0 : ℝ) ≤ 1 + Real.log (wp z) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (wp z : ℝ) by exact_mod_cast hw1); linarith
    exact mul_nonneg (by positivity) h1
  have hpow2nn : (0 : ℝ) ≤ (2 : ℝ) ^ (48000 : ℕ) := pow_nonneg (by norm_num) _
  have hsumnn : (0 : ℝ) ≤ ∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1) :=
    Finset.sum_nonneg (fun r _ => pow_nonneg hA5nn _)
  have hjunkfold : Cjunk * (Wp z : ℝ) ^ 3 * ((wp z : ℝ) * (1 + Real.log (wp z)))
        * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1))
      ≤ Cjunk * (2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    have hsumle : (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1))
        ≤ Real.log z * ((2 : ℝ) ^ (48000 : ℕ) * (z : ℝ) ^ (1 / 96000 : ℝ)) :=
      le_trans hSum (mul_le_mul hRlogz hA5R1 (pow_nonneg hA5nn _) hlogz0)
    have hbouter : (0 : ℝ)
        ≤ (z : ℝ) ^ (1 / 16000 : ℝ) * (2 * (z : ℝ) ^ (1 / 24000 : ℝ) * Real.log z) :=
      mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hlogz0)
    have hprod : (Wp z : ℝ) ^ 3 * ((wp z : ℝ) * (1 + Real.log (wp z)))
          * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1))
        ≤ (z : ℝ) ^ (1 / 16000 : ℝ) * (2 * (z : ℝ) ^ (1 / 24000 : ℝ) * Real.log z)
            * (Real.log z * ((2 : ℝ) ^ (48000 : ℕ) * (z : ℝ) ^ (1 / 96000 : ℝ))) :=
      mul_le_mul (mul_le_mul hW3 hw1logw hwfac (by positivity)) hsumle hsumnn hbouter
    have hzmerge : (z : ℝ) ^ (1 / 16000 : ℝ) * (2 * (z : ℝ) ^ (1 / 24000 : ℝ) * Real.log z)
          * (Real.log z * ((2 : ℝ) ^ (48000 : ℕ) * (z : ℝ) ^ (1 / 96000 : ℝ)))
        = (2 * 2 ^ (48000 : ℕ)) * (Real.log z) ^ 2
            * ((z : ℝ) ^ (1 / 16000 : ℝ) * (z : ℝ) ^ (1 / 24000 : ℝ)
                * (z : ℝ) ^ (1 / 96000 : ℝ)) := by
      generalize (2 : ℝ) ^ (48000 : ℕ) = c; ring
    have hpowmerge : (z : ℝ) ^ (1 / 16000 : ℝ) * (z : ℝ) ^ (1 / 24000 : ℝ)
          * (z : ℝ) ^ (1 / 96000 : ℝ)
        = (z : ℝ) ^ (11 / 96000 : ℝ) := by
      rw [← Real.rpow_add hzpos, ← Real.rpow_add hzpos]; norm_num
    have hfinal : (2 * 2 ^ (48000 : ℕ)) * (Real.log z) ^ 2 * (z : ℝ) ^ (11 / 96000 : ℝ)
        ≤ (2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) ^ (1 / 8000 : ℝ)) := by
      calc (2 * 2 ^ (48000 : ℕ)) * (Real.log z) ^ 2 * (z : ℝ) ^ (11 / 96000 : ℝ)
          ≤ (2 * 2 ^ (48000 : ℕ)) * (z : ℝ) ^ (1 / 96000 : ℝ)
              * (z : ℝ) ^ (11 / 96000 : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hlogsq (by positivity)
        _ = (2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) ^ (1 / 8000 : ℝ)) := by
            rw [mul_assoc, ← Real.rpow_add hzpos,
              show (1 / 96000 : ℝ) + 11 / 96000 = 1 / 8000 by norm_num]
    calc Cjunk * (Wp z : ℝ) ^ 3 * ((wp z : ℝ) * (1 + Real.log (wp z)))
          * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1))
        = Cjunk * ((Wp z : ℝ) ^ 3 * ((wp z : ℝ) * (1 + Real.log (wp z)))
            * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1))) := by ring
      _ ≤ Cjunk * ((2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) ^ (1 / 8000 : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCjunk0
          calc (Wp z : ℝ) ^ 3 * ((wp z : ℝ) * (1 + Real.log (wp z)))
                * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1))
              ≤ (2 * 2 ^ (48000 : ℕ)) * (Real.log z) ^ 2
                  * ((z : ℝ) ^ (1 / 16000 : ℝ) * (z : ℝ) ^ (1 / 24000 : ℝ)
                      * (z : ℝ) ^ (1 / 96000 : ℝ)) := by
                rw [← hzmerge]; exact hprod
            _ = (2 * 2 ^ (48000 : ℕ)) * (Real.log z) ^ 2 * (z : ℝ) ^ (11 / 96000 : ℝ) := by
                rw [hpowmerge]
            _ ≤ (2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) ^ (1 / 8000 : ℝ)) := hfinal
      _ ≤ Cjunk * ((2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) / (q.totient : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCjunk0
          apply mul_le_mul_of_nonneg_left hzdiv (by positivity)
      _ ≤ Cjunk * (2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
          rw [← mul_assoc]
          exact le_mul_of_one_le_right
            (mul_nonneg (mul_nonneg hCjunk0 (mul_nonneg (by norm_num) hpow2nn)) hzq0) hlogz1
  -- ## combine
  calc ∑ n ∈ (Finset.Icc 1 z).filter
          (fun n => n % q = a ∧ shiuClassIV (wp z) (Wp z) (P0p z) n), (n.divisors.card : ℝ)
      ≤ Cmain * Real.exp (2 * E) * ((z : ℝ) / (q.totient : ℝ)) / T
          + Cjunk * (Wp z : ℝ) ^ 3 * ((wp z : ℝ) * (1 + Real.log (wp z)))
            * (∑ r ∈ Finset.Icc 2 R, A5 ^ (r + 1)) := hbnd
    _ ≤ Cmain * Real.exp (2 * Cmert) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
          + Cjunk * (2 * 2 ^ (48000 : ℕ)) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
        add_le_add hmainfold hjunkfold
    _ = (Cmain * Real.exp (2 * Cmert) + Cjunk * (2 * 2 ^ 48000))
          * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
        generalize (2 : ℝ) ^ 48000 = c; ring

/-! ## §4  The glue: `sum_tau_in_ap_le : ShiuCore` -/

/-- **The Shiu core.**  Assembling the partition spine, the corner, and the five
per-class discharges gives `Σ_{n≤z, n≡a(q)} τ(n) ≤ C·(z/φ(q))·log z` for all `z ≥ 2`,
`q ≤ z^{1-1/8000}`, `(a,q)=1`.  The threshold `z₀ := ⌈exp(max Bx)⌉₊+1` splits the
astronomical asymptotic regime (all discharges fire) from the corner (crude
divisor-summatory folded into `C`). -/
theorem sum_tau_in_ap_le : ShiuCore := by
  obtain ⟨CI, BI, hCI0, hI⟩ := classI_discharge
  obtain ⟨CII, BII, hCII0, hII⟩ := classII_discharge
  obtain ⟨CIII, BIII, hCIII0, hIII⟩ := classIII_discharge
  obtain ⟨CIV, BIV, hCIV0, hIV⟩ := classIV_discharge
  set M : ℝ := max BI (max BII (max BIII BIV)) with hMdef
  set z₀ : ℕ := ⌈Real.exp M⌉₊ + 1 with hz0def
  have hz0pos : 0 < z₀ := by omega
  refine ⟨max (3 * (z₀ : ℝ)) (3 + CI + CII + CIII + CIV), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  · intro z q a hz hq hqz ha
    have hz1 : 1 ≤ z := by omega
    have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hlogz0 : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
    have hzφnn : (0 : ℝ) ≤ (z : ℝ) / (q.totient : ℝ) := by positivity
    rcases lt_or_ge z z₀ with hlt | hge
    · -- corner regime
      calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
          ≤ (3 * z₀ : ℝ) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
            shiu_corner_le z₀ z q a hz hq hqz hlt
        _ ≤ max (3 * (z₀ : ℝ)) (3 + CI + CII + CIII + CIV)
              * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left _ _) hzφnn) hlogz0
    · -- main regime: all discharges fire
      have hMlogz : M ≤ Real.log z := by
        have hexpM : Real.exp M ≤ (z : ℝ) := by
          have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
          have h2 : ((z₀ : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hge
          rw [hz0def] at h2; push_cast at h2; linarith
        calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
          _ ≤ Real.log z := Real.log_le_log (Real.exp_pos M) hexpM
      have hBI : BI ≤ Real.log z := le_trans (le_max_left _ _) hMlogz
      have hBII : BII ≤ Real.log z :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMlogz
      have hBIII : BIII ≤ Real.log z :=
        le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_max_right _ _)) hMlogz
      have hBIV : BIV ≤ Real.log z :=
        le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_max_right _ _)) hMlogz
      have hDeg := classDeg_discharge z q a hz hq hqz
      have hI' := hI z q a hBI hq ha hqz
      have hII' := hII z q a hBII hq ha hqz
      have hIII' := hIII z q a hBIII hq ha hqz
      have hIV' := hIV z q a hBIV hq ha hqz
      calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
          ≤ (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg (wp z) n),
                (n.divisors.card : ℝ))
            + (∑ n ∈ (Finset.Icc 1 z).filter
                (fun n => n % q = a ∧ shiuClassI (wp z) (Wp z) n),
                (n.divisors.card : ℝ))
            + (∑ n ∈ (Finset.Icc 1 z).filter
                (fun n => n % q = a ∧ shiuClassII (wp z) (Wp z) n),
                (n.divisors.card : ℝ))
            + (∑ n ∈ (Finset.Icc 1 z).filter
                (fun n => n % q = a ∧ shiuClassIII (wp z) (Wp z) (P0p z) n),
                (n.divisors.card : ℝ))
            + (∑ n ∈ (Finset.Icc 1 z).filter
                (fun n => n % q = a ∧ shiuClassIV (wp z) (Wp z) (P0p z) n),
                (n.divisors.card : ℝ)) := shiu_partition z q a (wp z) (Wp z) (P0p z)
        _ ≤ 3 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
              + CI * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
              + CII * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
              + CIII * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
              + CIV * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
            add_le_add (add_le_add (add_le_add (add_le_add hDeg hI') hII') hIII') hIV'
        _ = (3 + CI + CII + CIII + CIV) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring
        _ ≤ max (3 * (z₀ : ℝ)) (3 + CI + CII + CIII + CIV)
              * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) hzφnn) hlogz0

end Salt.Maynard
