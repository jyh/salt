/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.Headline4
import Salt.Chen.SuperClose
import Salt.Chen.FchainPoint
import Salt.Chen.WindowMembership
import Salt.Chen.WLower
import Salt.Chen.CountW

/-!
# FIN-LED — the `hL` ledger bundle of `chen_headline_of_A3_ledger`

Design: `docs/blueprints/flags.md`, the `2026-07-15 HCOUNT-3` entry ("EVERY INPUT OF THE FINAL
WIRING NOW EXISTS. fin8d = HEB …").  This module supplies the **F2 ledger** hypothesis `hL` of
`Headline4.chen_headline_of_A3_ledger` at the concrete carriers `M1`/`M2`/`M3` by instantiating
`GlueNormalized.normalized_package` at the frozen operating point.

The five certificate/count rows `normalized_package` consumes, discharged here at op:

* `hcertA1` — `9779/10000 ≤ fchain (maxDepth (twinA1SieveW …)) (logRatio (opZ x)(opD x))`:
  `SuperClose.fchain_A1_final` (needs `2 ≤ maxDepth`, from Bertrand-chained prime existence in
  `[opW', opZ x)`) ∘ `WindowMembership.logRatio_A1_mem`.
* `hcertA3` — `Fchain (maxDepth (switchSieve …)) (logRatio (opY x)(opDlev x)) ≤ 243/100`:
  `FchainPoint.Fchain_switch_le` (needs `1 ≤ maxDepth`) ∘ the tower membership `opf_tower`
  conjunct `logRatio (opY x)(opDlev x) ∈ [149/100, 151/100]`.
* `hcertA2` — the window-perturbed A₂ cert (`A2Window.A2grid_window_le` chain).
* `hcount` — THE SEAM: `CountAtOp3.hcount_slot_closed` is in `tripleSumW`; `M3`'s carrier `T`
  is `tripleSum/φ(opQ)`.  We fold the two-sided `CountW.tripleSumW_equidist_mertens` into a
  WIDER `ecount'` — the genuine analytic step.
* `hEbundle ≤ 1/200` — the four error shares at the tower.

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Real ArithmeticFunction

/-! ## Part A — the `maxDepth` lower bounds (Bertrand-chained prime existence in the window) -/

/-- For `x ≥ (4·opW'+1)^8`, the `⌊x^{1/8}⌋` floor `opZ x` exceeds `4·opW'`.  Self-contained
floor/`rpow` bound (`(a^8)^{1/8} = a`); the operating tower is far larger, but this crude
threshold is all the two-prime window count needs. -/
theorem opZ_gt_of_ge (x : ℕ) (hx : (4 * opW' + 1) ^ 8 ≤ x) : 4 * opW' < opZ x := by
  rw [opZ]
  have hxR : ((4 * opW' + 1 : ℕ) : ℝ) ^ (8 : ℕ) ≤ (x : ℝ) := by exact_mod_cast hx
  have key : (((4 * opW' + 1 : ℕ) : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) = ((4 * opW' + 1 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast ((4 * opW' + 1 : ℕ) : ℝ) 8, ← Real.rpow_mul (by positivity)]
    norm_num
  have hmono : (((4 * opW' + 1 : ℕ) : ℝ) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (by positivity) hxR (by norm_num)
  rw [key] at hmono
  have hfloor : 4 * opW' + 1 ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ := Nat.le_floor (by exact_mod_cast hmono)
  omega

/-- For `x ≥ (4·opW'+1)^3`, the `⌊x^{1/3}⌋` floor `opY x` exceeds `4·opW'`. -/
theorem opY_gt_of_ge (x : ℕ) (hx : (4 * opW' + 1) ^ 3 ≤ x) : 4 * opW' < opY x := by
  rw [opY]
  have hxR : ((4 * opW' + 1 : ℕ) : ℝ) ^ (3 : ℕ) ≤ (x : ℝ) := by exact_mod_cast hx
  have key : (((4 * opW' + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = ((4 * opW' + 1 : ℕ) : ℝ) := by
    rw [← Real.rpow_natCast ((4 * opW' + 1 : ℕ) : ℝ) 3, ← Real.rpow_mul (by positivity)]
    norm_num
  have hmono : (((4 * opW' + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hxR (by norm_num)
  rw [key] at hmono
  have hfloor : 4 * opW' + 1 ≤ ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := Nat.le_floor (by exact_mod_cast hmono)
  omega

/-- **`2 ≤ maxDepth (twinA1SieveW …)`.**  `maxDepth = #{primes in [opW', opZ x)}`; two Bertrand
steps produce distinct primes `p₁ ∈ (opW', 2·opW']`, `p₂ ∈ (p₁, 2·p₁] ⊆ (opW', 4·opW']`, both
`< opZ x` once `4·opW' < opZ x` (`opZ_gt_of_ge`). -/
theorem two_le_maxDepth_A1 (x : ℕ) (hx : (4 * opW' + 1) ^ 8 ≤ x) :
    2 ≤ maxDepth (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)) := by
  have hw'0 : opW' ≠ 0 := by have := opf_w'3; omega
  have hzgt : 4 * opW' < opZ x := opZ_gt_of_ge x hx
  obtain ⟨p₁, hp₁, hlt1, hle1⟩ := Nat.bertrand opW' hw'0
  obtain ⟨p₂, hp₂, hlt2, hle2⟩ := Nat.bertrand p₁ hp₁.pos.ne'
  unfold maxDepth
  rw [twinA1SieveW_prodPrimes, opf_P_primeFactors]
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.add_one_le_iff, Finset.one_lt_card_iff]
  refine ⟨p₁, p₂, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp₁⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp₂⟩
  · omega

/-- **`1 ≤ maxDepth (switchSieve …)`.**  `maxDepth = #{primes in [opW', opY x)}`; one Bertrand
step gives `p ∈ (opW', 2·opW'] ⊆ [opW', opY x)` once `4·opW' < opY x` (`opY_gt_of_ge`). -/
theorem one_le_maxDepth_switch (x : ℕ) (hx : (4 * opW' + 1) ^ 3 ≤ x) :
    1 ≤ maxDepth (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x)) := by
  have hw'0 : opW' ≠ 0 := by have := opf_w'3; omega
  have hygt : 4 * opW' < opY x := opY_gt_of_ge x hx
  obtain ⟨p, hp, hlt, hle⟩ := Nat.bertrand opW' hw'0
  unfold maxDepth
  rw [switchSieve_prodPrimes, opf_Ps_primeFactors]
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp⟩⟩

/-! ## Part B — the certificate rows at the operating point -/

/-- **`hcertA1` at op.**  `fchain_A1_final` (at `N = maxDepth ≥ 2`) ∘ `logRatio_A1_mem`. -/
theorem hcertA1_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (9779 / 10000 : ℝ) ≤
      fchain (maxDepth (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)))
        (logRatio (opZ x) (opD x)) := by
  obtain ⟨xm, hmem⟩ := logRatio_A1_mem
  refine ⟨max xm ((4 * opW' + 1) ^ 8), fun x hx => ?_⟩
  have hxm : xm ≤ x := le_trans (le_max_left _ _) hx
  have hx8 : (4 * opW' + 1) ^ 8 ≤ x := le_trans (le_max_right _ _) hx
  have h2N := two_le_maxDepth_A1 x hx8
  have hmemx : logRatio (opZ x) (opD x) ∈ Set.Icc (39992 / 10000 : ℝ) 4 := by
    rw [opZ, opD]; exact hmem x hxm
  exact fchain_A1_final _ h2N _ hmemx

/-- **`hcertA3` at op.**  `Fchain_switch_le` (at `N = maxDepth ≥ 1`) ∘ the tower membership. -/
theorem hcertA3_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    Fchain (maxDepth (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x)))
        (logRatio (opY x) (opDlev x)) ≤ 243 / 100 := by
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max xt ((4 * opW' + 1) ^ 3), fun x hx => ?_⟩
  have hxt : xt ≤ x := le_trans (le_max_left _ _) hx
  have hx3 : (4 * opW' + 1) ^ 3 ≤ x := le_trans (le_max_right _ _) hx
  have h1N := one_le_maxDepth_switch x hx3
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem, _, _⟩ := htower x hxt
  exact Fchain_switch_le _ h1N _ hmem

/-! ## Part C — THE hcount SEAM (the genuine analytic step)

`hcount_slot_closed` bounds `log x · tripleSumW` (the AP-restricted count); `M3`'s carrier `T`
is `tripleSum/φ(opQ)` (the *unrestricted* count over `φ`).  We fold the two-sided
equidistribution bound `|tripleSumW − tripleSum/φ| ≤ E` (`CountW.tripleSumW_equidist`, the base
of the Mertens-closed row) into a WIDER `ecount' = ecountOp C x + e`, with `e ≤ 8/log x` the
honest equidistribution crumb.

The crumb `e = log x·E·φ/S` (`S = ∑Λ`, the window mass) folds through the LANDED E_SW
machinery: `pairSum_le_at_op` (`Σ 1/(p₁p₂) ≤ 16`), `pairSet_card_le` (`|pairSet| ≤ opY·√x`),
`esw_main_le13` (the `x/(log x)^{11}` power-suppression at base 7) and `op_ls_facts` (each
`x^{5/6}·polylog` / `x/(log x)^{11}` term `≤ x/log x`), over the PNT window mass `S ≥ x/4`
(`lambda_mass_lower`).  Every ingredient is a landed op-row; the fold is the honest algebra
`log x·E·φ ≤ 2·(x/log x)` and `e ≤ 2·(x/log x)/(x/4) = 8/log x`.

`maxRecDepth` is raised because the op context carries many long inequalities (`hslot'`, the
equidist bound, the E_SW rows) and `nlinarith`/`field_simp` certificate elaboration over it
exceeds the default recursion depth. -/
set_option maxRecDepth 8000 in
/-- **`hcount_seam` — the count slot at `tripleSum/φ(opQ)`.**  Past a threshold, for the widened
`ecount = ecountOp C x + e` with `0 ≤ e ≤ 8/log x`, the ledger's A₃ count carrier is dominated by
`(cbar + (ecountOp C x + e))·((∑Λ)/φ(opQ))`. -/
theorem hcount_seam : ∃ (C : ℝ) (x₁ : ℕ), 0 ≤ C ∧ ∀ x : ℕ, x₁ ≤ x →
    ∃ e : ℝ, 0 ≤ e ∧ e ≤ 8 / Real.log x ∧
      Real.log x * (tripleSum x (opZ x) (opY x) / (opQ.totient : ℝ))
        ≤ (cbar + (ecountOp C x + e))
            * ((∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ)) := by
  obtain ⟨C, xS, hC0, hslot⟩ := hcount_slot_closed
  obtain ⟨K, N₀, hKpos, hequi⟩ := tripleSumW_equidist (A := 13) (C := 2) (by norm_num) (by norm_num)
  obtain ⟨xAP, hAP⟩ := hcount_op_AP3
  obtain ⟨xLv, hLv⟩ := hcount_Lval_rows N₀
  obtain ⟨xF, hF⟩ := op_at_facts
  obtain ⟨xLS, hLS⟩ := op_ls_facts K
  obtain ⟨xP, hP16⟩ := pairSum_le_at_op
  obtain ⟨Km, hKm0, hmass⟩ := lambda_mass_lower
  obtain ⟨xm, hm⟩ := a12_log_ge (16 * Km)
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨C, max (xS + xAP + xLv + xF + xLS + xP + xm + xt + 8) (10 ^ 48), hC0, fun x hx => ?_⟩
  have hBIG : xS + xAP + xLv + xF + xLS + xP + xm + xt + 8 ≤ x := le_trans (le_max_left _ _) hx
  have h48 : 10 ^ 48 ≤ x := le_trans (le_max_right _ _) hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast h48
  have hx8 : 8 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  -- extract the per-row facts
  have hslot' := hslot x (by omega)
  have hAP' := hAP x (by omega)
  have hLv' := hLv x (by omega)
  have hF' := hF x (by omega)
  have hLS' := hLS x (by omega)
  have hP16' := hP16 x (by omega)
  have hmass' := hmass x hx8
  have hm' := (hm x (by omega)).2
  obtain ⟨hQpos, hQcop, hQz⟩ := hAP'
  obtain ⟨hLval3, hLvalN₀, hLval4, hLvalrange⟩ := hLv'
  obtain ⟨hL96, _, _, _, _, _, _, _, _⟩ := hF'
  obtain ⟨_, _, hbd3, hbd4⟩ := hLS'
  -- abbreviations
  set L := Real.log x with hLdef
  set φ := (opQ.totient : ℝ) with hφdef
  set S := ∑ n ∈ twinWindow x, vonMangoldt n with hSdef
  set logLval := Real.log (Lval x (opY x)) with hLvaldef
  have hLnn : 0 ≤ L := le_trans (by norm_num) hL96
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL96
  have hφpos : 0 < φ := by rw [hφdef]; exact_mod_cast Nat.totient_pos.mpr hQpos
  have hxge8R : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx8
  have h1x8 : (1 : ℝ) ≤ (x : ℝ) / 8 := by linarith only [hxge8R]
  have hKmx : 2 * Km * x / L ≤ (x : ℝ) / 8 := by
    rw [div_le_div_iff₀ hLpos (by norm_num)]
    have hprod : (x : ℝ) * (16 * Km) ≤ (x : ℝ) * L := mul_le_mul_of_nonneg_left hm' hxpos.le
    linarith only [hprod]
  have hSpos : 0 < S := by linarith only [hmass', hKmx, h1x8]
  have hSge : (x : ℝ) / 4 ≤ S := by linarith only [hmass', hKmx, h1x8]
  have hφleL : φ ≤ L := by
    have h1 : φ ≤ (opQ : ℝ) := by rw [hφdef]; exact_mod_cast Nat.totient_le opQ
    have h2 : (opQ : ℝ) ≤ L := (htower x (by omega)).1
    linarith only [h1, h2]
  have hlogLval4 : (4 : ℝ) ≤ logLval := hLval4
  have hlogLvalpos : 0 < logLval := lt_of_lt_of_le (by norm_num) hlogLval4
  have hlogLval7 : L / 7 ≤ logLval := by
    have h6 := logLval_op_ge hx48R
    have hlog2 := Real.log_two_lt_d9
    rw [← hLvaldef, ← hLdef] at h6
    linarith only [hL96, h6, hlog2]
  -- the equidistribution bound and its `Ebound` closure
  have hequi' := hequi opQ opA x (opZ x) (opY x) hQpos hQcop hQz hLval3 hLvalN₀ hLvalrange
  -- coefficient nonneg
  have hcoeff_nn : 0 ≤ K * (x : ℝ) / logLval ^ (13 : ℝ) :=
    div_nonneg (mul_nonneg hKpos.le hxpos.le) (Real.rpow_nonneg hlogLvalpos.le _)
  have hcard : ((pairSet x (opZ x) (opY x)).card : ℝ)
      ≤ (opY x : ℝ) * (Nat.sqrt x : ℝ) := by exact_mod_cast pairSet_card_le x (opZ x) (opY x)
  set Ebound := 16 * K * (x : ℝ) / logLval ^ (13 : ℝ) + 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ))
    with hEbdef
  have hEbound_nn : 0 ≤ Ebound := by
    rw [hEbdef]
    have h1 : 0 ≤ 16 * K * (x : ℝ) / logLval ^ (13 : ℝ) :=
      div_nonneg (by positivity) (Real.rpow_nonneg hlogLvalpos.le _)
    have h2 : 0 ≤ 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) := by positivity
    linarith
  have habs : |tripleSumW opQ opA x (opZ x) (opY x)
      - tripleSum x (opZ x) (opY x) / φ| ≤ Ebound := by
    refine le_trans hequi' ?_
    rw [hEbdef]
    have hpair : K * (x : ℝ) / logLval ^ (13 : ℝ)
          * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))
        ≤ 16 * K * (x : ℝ) / logLval ^ (13 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hP16' hcoeff_nn
      calc K * (x : ℝ) / logLval ^ (13 : ℝ)
              * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))
          ≤ K * (x : ℝ) / logLval ^ (13 : ℝ) * 16 := this
        _ = 16 * K * (x : ℝ) / logLval ^ (13 : ℝ) := by ring
    have hbdry : 2 * ((pairSet x (opZ x) (opY x)).card : ℝ)
        ≤ 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) := by linarith [hcard]
    linarith [hpair, hbdry]
  -- `TS/φ ≤ TSW + Ebound`
  have hTSφ : tripleSum x (opZ x) (opY x) / φ
      ≤ tripleSumW opQ opA x (opZ x) (opY x) + Ebound := by
    have := (abs_le.mp habs).1; linarith
  -- the crumb bound `L·Ebound·φ ≤ 2·(x/L)`
  have hpart1 : φ * L * (K * (x : ℝ) / logLval ^ (13 : ℝ) * 16) ≤ (x : ℝ) / L := by
    have hesw := esw_main_le13 (φ := φ) (x := (x : ℝ)) (logLval := logLval) (M := 16) (Ksw := K)
      hφleL hLpos hlogLval7 (by norm_num) hKpos.le hxpos.le
    rw [← hLdef] at hesw
    linarith [hesw, hbd4]
  have hoYsx_nn : 0 ≤ (opY x : ℝ) * (Nat.sqrt x : ℝ) := by positivity
  have hpart2 : 2 * (φ * L) * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) ≤ (x : ℝ) / L := by
    have hφL : φ * L ≤ L ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hφleL hLnn
    have hmul : 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) * (φ * L)
        ≤ 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) * L ^ 2 :=
      mul_le_mul_of_nonneg_left hφL (by positivity)
    linarith only [hmul, hbd3]
  have hLEφ : L * Ebound * φ ≤ 2 * ((x : ℝ) / L) := by
    have hid : L * Ebound * φ
        = φ * L * (K * (x : ℝ) / logLval ^ (13 : ℝ) * 16)
          + 2 * (φ * L) * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) := by
      rw [hEbdef]; ring
    rw [hid]; linarith [hpart1, hpart2]
  have hLEφ_nn : 0 ≤ L * Ebound * φ := mul_nonneg (mul_nonneg hLnn hEbound_nn) hφpos.le
  -- assemble `e` and its bound
  refine ⟨L * Ebound * φ / S, ?_, ?_, ?_⟩
  · exact div_nonneg hLEφ_nn hSpos.le
  · -- `e ≤ 8/L`
    have h1S : 1 / S ≤ 4 / (x : ℝ) := by
      rw [div_le_div_iff₀ hSpos hxpos]; linarith only [hSge]
    have he1 : L * Ebound * φ / S = (L * Ebound * φ) * (1 / S) := by ring
    have he2 : (L * Ebound * φ) * (1 / S) ≤ (L * Ebound * φ) * (4 / (x : ℝ)) :=
      mul_le_mul_of_nonneg_left h1S hLEφ_nn
    have he3 : (L * Ebound * φ) * (4 / (x : ℝ)) ≤ 2 * ((x : ℝ) / L) * (4 / (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hLEφ (by positivity)
    have he4 : 2 * ((x : ℝ) / L) * (4 / (x : ℝ)) = 8 / L := by
      have hxne : (x : ℝ) ≠ 0 := hxpos.ne'
      have hLne : L ≠ 0 := hLpos.ne'
      field_simp; ring
    rw [he1]; linarith only [he2, he3, he4]
  · -- the count slot at `tripleSum/φ`
    have hSne : S ≠ 0 := hSpos.ne'
    have hφne : φ ≠ 0 := hφpos.ne'
    have hcancel : L * Ebound * φ / S * (S / φ) = L * Ebound := by
      field_simp
    have heq : (cbar + (ecountOp C x + L * Ebound * φ / S)) * (S / φ)
        = (cbar + ecountOp C x) * (S / φ) + L * Ebound := by
      have hre : cbar + (ecountOp C x + L * Ebound * φ / S)
          = (cbar + ecountOp C x) + L * Ebound * φ / S := by ring
      rw [hre, add_mul, hcancel]
    have hstep1 : L * (tripleSum x (opZ x) (opY x) / φ)
        ≤ L * (tripleSumW opQ opA x (opZ x) (opY x) + Ebound) :=
      mul_le_mul_of_nonneg_left hTSφ hLnn
    have hstep2 : L * (tripleSumW opQ opA x (opZ x) (opY x) + Ebound)
        = L * tripleSumW opQ opA x (opZ x) (opY x) + L * Ebound := by ring
    rw [heq]
    linarith [hslot', hstep1, hstep2]

/-! ## Part D — the crude `X_W` lower bound (the ledger's R/strip-share denominator)

`X_W = totalMass·W(twinA1SieveW) = (∑Λ/φ(opQ))·W`.  The sharp Chen `W`-lower `W_twinA1_ge`
(`W ≥ exp(−35)/log z`) through the `rfl` bridge `twinA1SieveW_W_eq`, over the PNT window mass
`∑Λ ≥ x/4` (`lambda_mass_lower`), gives `X_W ≥ exp(−35)·x/(4·φ(opQ)·log(opZ x))` — the
`x/(polylog)`-scale denominator that kills every `R_i/X_W` and strip error share of the ledger
(`hEbundle`'s `e1`/`e4` and the `R_i/X_W` crumbs).  This is the reusable brick GLU-2's strip
argument consumes; it is independent of the A₂ carrier (`hcertA2`). -/

/-- **`XW_lower_at_op` — the crude ledger-normalisation lower bound.**  Past a threshold,
`exp(−35)·x/(4·φ(opQ)·log(opZ x)) ≤ X_W`, with `X_W = totalMass·W(twinA1SieveW …)`. -/
theorem XW_lower_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    Real.exp (-35) * (x : ℝ) / (4 * (opQ.totient : ℝ) * Real.log (opZ x))
      ≤ (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)).totalMass
        * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)) := by
  obtain ⟨Km, hKm0, hmass⟩ := lambda_mass_lower
  obtain ⟨xm, hm⟩ := a12_log_ge (16 * Km)
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨xm + xt + 8, fun x hx => ?_⟩
  have hx8 : 8 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hx1R : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 1 < x)
  have hLpos : 0 < Real.log x := Real.log_pos hx1R
  have hm' := (hm x (by omega)).2
  have hz3 : 3 ≤ opZ x := (htower x (by omega)).2.2.2.1
  have hφpos : (0 : ℝ) < (opQ.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  have hzR2 : (2 : ℝ) ≤ (opZ x : ℝ) := by exact_mod_cast (by omega : 2 ≤ opZ x)
  have hzR1 : (1 : ℝ) < (opZ x : ℝ) := by exact_mod_cast (by omega : 1 < opZ x)
  have hlogz : 0 < Real.log (opZ x : ℝ) := Real.log_pos hzR1
  -- ∑Λ ≥ x/4
  have hSge : (x : ℝ) / 4 ≤ ∑ n ∈ twinWindow x, vonMangoldt n := by
    have hbnd := hmass x hx8
    have hKmx : 2 * Km * x / Real.log x ≤ (x : ℝ) / 8 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]
      have hprod : (x : ℝ) * (16 * Km) ≤ (x : ℝ) * Real.log x :=
        mul_le_mul_of_nonneg_left hm' hxpos.le
      linarith only [hprod]
    have h1x8 : (1 : ℝ) ≤ (x : ℝ) / 8 := by
      have : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx8
      linarith
    linarith only [hbnd, hKmx, h1x8]
  have hSnn : 0 ≤ ∑ n ∈ twinWindow x, vonMangoldt n := le_trans (by positivity) hSge
  -- the sharp Chen W-lower through the rfl bridge
  have hpz : ∀ p ∈ (opP x).primeFactors, (p : ℝ) < (opZ x : ℝ) := by
    intro p hp
    rw [opf_P_primeFactors, Finset.mem_filter, Finset.mem_Ico] at hp
    exact_mod_cast hp.1.2
  have hWge : Real.exp (-35) / Real.log (opZ x : ℝ)
      ≤ Salt.BrunLower.W (twinA1Sieve x (opP x) (opf_P_sq x) (opf_Podd x)) :=
    W_twinA1_ge (opf_P_sq x) (opf_Podd x) hzR2 hpz
  rw [twinA1SieveW_totalMass,
    twinA1SieveW_W_eq opQ opA x (opP x) (opf_P_sq x) (opf_Podd x)]
  -- the product bound
  have hTMge : (x : ℝ) / 4 / (opQ.totient : ℝ)
      ≤ (∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ) := by gcongr
  have hprod : (x : ℝ) / 4 / (opQ.totient : ℝ) * (Real.exp (-35) / Real.log (opZ x : ℝ))
      ≤ (∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ)
        * Salt.BrunLower.W (twinA1Sieve x (opP x) (opf_P_sq x) (opf_Podd x)) :=
    mul_le_mul hTMge hWge (by positivity) (div_nonneg hSnn hφpos.le)
  have hLHSeq : Real.exp (-35) * (x : ℝ) / (4 * (opQ.totient : ℝ) * Real.log (opZ x : ℝ))
      = (x : ℝ) / 4 / (opQ.totient : ℝ) * (Real.exp (-35) / Real.log (opZ x : ℝ)) := by
    field_simp
  rw [hLHSeq]
  exact hprod

end Salt.Chen
