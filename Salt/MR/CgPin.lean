/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ParsevalStone
import Salt.MR.ConstantsExposed

/-!
# ⟦THE `Cg` CARRY⟧ — the sieve-mass constant, capped along the whole road (node EPSPIN)

`ConstantsExposed.typical_density_le_bounded` is the WIRED ROOT of the `Cg`
chain: the landed `typical_density_le` conclusion re-derived with the numeral
`C ≤ 2·10^12` in the statement.  CG-SCOPE's byte-read (recorded at
`S15Witness.lean:67`) traced the road's `Cg` back to it through EIGHT `∃ C`
links, links 2–8 being verbatim re-emits and link 1→2 a raise to `max C₀ 1`.

This file walks that chain, one additive twin per link.  Each twin is its landed
statement with ONE conjunct — `C ≤ 2·10^12` — inserted after `1 ≤ C`, and its
landed body verbatim underneath, reading the previous twin instead of the landed
link.  No landed declaration is touched.

The terminal twin `parseval_insert_budget_door_bounded` is what
`HloExportMR`'s `_pinned` road twins consume: with it, `Cg ≤ 2·10^12` rides the
capstone's `∃`-prefix beside the head's `1/500 ≤ ε` and `1/838400 ≤ δ₀`, which is
exactly the triple the `24·Cg/δ₀ ≤ M` register needs at numerals.

⟦THE VALUE⟧ `CgExpr = 2·exp(19/log 2) + 1 = 1.605·10^12` (`ConstantsExposed.Cg_le`
proves the `2·10^12` ceiling); the `max C₀ 1` of link 2 cannot move it, since
`1 ≤ 2·10^12`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **Link 2** — `SieveGlue.card_blockfree_le` (`SieveGlue.lean:183`), the one link that
does NOT re-emit verbatim: it raises to `max C₀ 1` (harmless above `1`), so the cap
is `max_le`. -/
theorem card_blockfree_le_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (P Q X : ℕ), 2 ≤ P → P ≤ Q →
        Real.log Q ≤ Real.sqrt (Real.log X) →
        (100 : ℝ) ≤ Real.sqrt (Real.log X) →
        ((Nat.sqrt X : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (X : ℝ) * (Real.log P / Real.log Q) →
        (((Finset.Ioc X (2 * X)).filter (fun n => blockOmega P Q n = 0)).card : ℝ)
          ≤ C * (Real.log P / Real.log Q) * X := by
  obtain ⟨C₀, hC₀, hC₀le, hden⟩ := typical_density_le_bounded
  refine ⟨max C₀ 1, le_max_right _ _, max_le hC₀le (by norm_num), ?_⟩
  intro P Q X hP hPQ hreg hbig herr
  have hQ2 : 2 ≤ Q := le_trans hP hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ2)
  have hXnn : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hratio : (0 : ℝ) ≤ Real.log P / Real.log Q := div_nonneg hlogP.le hlogQ.le
  -- ⟦the bridge: `ω(n;P,Q) = 0` ⟹ coprime to the band radical, for `n ≠ 0`⟧
  have hsub : ((Finset.Ioc X (2 * X)).filter (fun n => blockOmega P Q n = 0)).card
      ≤ ((Finset.Ioc X (2 * X)).filter (fun n => (bandProd P Q).Coprime n)).card := by
    refine Finset.card_le_card ?_
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨hn.1, coprime_bandProd_of_blockOmega_zero (by omega) hn.2⟩
  have hcast :
      (((Finset.Ioc X (2 * X)).filter (fun n => blockOmega P Q n = 0)).card : ℝ)
        ≤ (((Finset.Ioc X (2 * X)).filter
              (fun n => (bandProd P Q).Coprime n)).card : ℝ) := by
    exact_mod_cast hsub
  refine hcast.trans ((hden P Q X hP hPQ (densGate_of_sqrt hQ2 hreg hbig) herr).trans ?_)
  have hmax : C₀ ≤ max C₀ 1 := le_max_left _ _
  nlinarith [mul_nonneg hratio hXnn]

/-- **Link 3** — `SieveGlue.hsieve_of_engine` (`SieveGlue.lean:438`), verbatim re-emit. -/
theorem hsieve_of_engine_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (A G M J X : ℕ) (Nlg : Finset ℕ),
      1 ≤ A → 1 ≤ G → 1 ≤ M →
      Nlg ⊆ Finset.Ioc X (2 * X) → 0 < (X : ℝ) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (1 / (X : ℝ))
          * ((Nlg.filter (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
        ≤ C * ∑ j ∈ Finset.Icc 1 J,
            Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ) := by
  obtain ⟨C, hC, hCle, hcard⟩ := card_blockfree_le_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro A G M J X Nlg hA hG hM hNlg hX hbig hreg herr
  have hXne : (X : ℝ) ≠ 0 := ne_of_gt hX
  -- ⟦STEP 1: the union bound (p. 31 (e), the pure-counting part)⟧
  have h1 := card_not_memS_le_sum Nlg (calP A G) (calQK A G M) J
  -- ⟦STEP 2: each block, by the engine⟧
  have h2 : ∀ j ∈ Finset.Icc 1 J,
      ((Nlg.filter
          (fun n => blockOmega (calP A G j) (calQK A G M j) n = 0)).card : ℝ)
        ≤ C * (Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) * X := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hP2 : 2 ≤ calP A G j := two_le_calP hA hG j
    have hPQ : calP A G j ≤ calQK A G M j := calP_le_calQK hM hj1
    have hmono : ((Nlg.filter
        (fun n => blockOmega (calP A G j) (calQK A G M j) n = 0)).card : ℝ)
        ≤ (((Finset.Ioc X (2 * X)).filter
            (fun n => blockOmega (calP A G j) (calQK A G M j) n = 0)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hNlg)
    exact hmono.trans (hcard _ _ _ hP2 hPQ (hreg j hj) hbig (herr j hj))
  -- ⟦STEP 3: sum and normalise⟧
  have h3 : ((Nlg.filter
      (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
      ≤ ∑ j ∈ Finset.Icc 1 J,
          C * (Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) * X := by
    refine le_trans ?_ (Finset.sum_le_sum h2)
    exact_mod_cast h1
  have h4 : ∑ j ∈ Finset.Icc 1 J,
      C * (Real.log ((calP A G j : ℕ) : ℝ)
        / Real.log ((calQK A G M j : ℕ) : ℝ)) * X
      = C * X * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h4] at h3
  calc (1 / (X : ℝ))
        * ((Nlg.filter (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
      ≤ (1 / (X : ℝ)) * (C * X * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C * ∑ j ∈ Finset.Icc 1 J,
          Real.log ((calP A G j : ℕ) : ℝ)
            / Real.log ((calQK A G M j : ℕ) : ℝ) := by
        field_simp

/-- **Link 4** — `M4Sieve.notMemS_window_count_le` (`M4Sieve.lean:468`), verbatim re-emit. -/
theorem notMemS_window_count_le_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (A G M J X : ℕ) (Wm : Finset ℕ),
      1 ≤ A → 1 ≤ G → 1 ≤ M →
      Wm ⊆ Finset.Icc X (2 * X) → 0 < (X : ℝ) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      ((Wm.filter (fun m => ¬ MemS (calP A G) (calQK A G M) J m)).card : ℝ)
        ≤ C * (X : ℝ) * ratioSumK A G M J + 1 := by
  obtain ⟨C, hC, hCle, heng⟩ := hsieve_of_engine_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro A G M J X Wm hA hG hM hsub hX hbig hreg herr
  have hIoc := heng A G M J X (Finset.Ioc X (2 * X)) hA hG hM (subset_refl _) hX hbig hreg herr
  have hIoc' : (((Finset.Ioc X (2 * X)).filter
      (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
      ≤ C * (X : ℝ) * ratioSumK A G M J := by
    have hmul := mul_le_mul_of_nonneg_left hIoc hX.le
    rw [← mul_assoc, mul_one_div, div_self (ne_of_gt hX), one_mul] at hmul
    calc (((Finset.Ioc X (2 * X)).filter
          (fun n => ¬ MemS (calP A G) (calQK A G M) J n)).card : ℝ)
        ≤ (X : ℝ) * (C * ratioSumK A G M J) := hmul
      _ = C * (X : ℝ) * ratioSumK A G M J := by ring
  exact le_trans (card_notMemS_of_subset_Icc _ _ J hsub) (by linarith)

/-- **Link 5** — `M4Sieve.m4_sieve_block_mass` (`M4Sieve.lean:588`), verbatim re-emit. -/
theorem m4_sieve_block_mass_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (A G M J X H a b : ℕ) (δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 8 * C / δ ≤ (M : ℝ) →
      0 < (X : ℝ) → X ≤ a → Finset.Ioc a (b + H) ⊆ Finset.Icc X (2 * X) →
      (100 : ℝ) ≤ Real.sqrt (Real.log X) →
      (∀ j ∈ Finset.Icc 1 J,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log X)) →
      (∀ j ∈ Finset.Icc 1 J,
        ((Nat.sqrt X : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (X : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
              / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      ∑ n ∈ Finset.Ioc a b,
          ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) * (n : ℝ)⁻¹
        ≤ δ / 4 * (H : ℝ) + (H : ℝ) / (X : ℝ) := by
  obtain ⟨C, hC, hCle, hcnt⟩ := notMemS_window_count_le_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro A G M J X H a b δ hA hG hM hδ hMδ hX hXa hcov hbig hreg herr
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hC0 : (0 : ℝ) < C := by linarith
  have hS0 : 0 ≤ ratioSumK A G M J := ratioSumK_nonneg hA hG hM J
  -- ⟦STEP 1: the double count and the block weight⟧
  have hwt := sum_notMemSCount_weighted_le (b := b) hX hXa (calP A G) (calQK A G M) J H
  -- ⟦STEP 2: the count, by `hsieve_of_engine` + the endpoint⟧
  have hNc := hcnt A G M J X (Finset.Ioc a (b + H)) hA hG hM hcov hX hbig hreg herr
  -- ⟦STEP 3: the M-gate⟧
  have hmass := sieve_mass_le_quarter hA hG hM J hC hδ hMδ
  -- ⟦STEP 4: the arithmetic⟧
  set Nc := (((Finset.Ioc a (b + H)).filter
    (fun m => ¬ MemS (calP A G) (calQK A G M) J m)).card : ℝ) with hNcdef
  have hNc0 : (0 : ℝ) ≤ Nc := Nat.cast_nonneg _
  have hXinv : (0 : ℝ) ≤ 1 / (X : ℝ) := by positivity
  have h1 : (1 / (X : ℝ)) * ((H : ℝ) * Nc)
      ≤ (1 / (X : ℝ)) * ((H : ℝ) * (C * (X : ℝ) * ratioSumK A G M J + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNc hH0) hXinv
  have h2 : (1 / (X : ℝ)) * ((H : ℝ) * (C * (X : ℝ) * ratioSumK A G M J + 1))
      = (H : ℝ) * (C * ratioSumK A G M J) + (H : ℝ) / (X : ℝ) := by
    field_simp
  have h3 : (H : ℝ) * (C * ratioSumK A G M J) ≤ (H : ℝ) * (δ / 4) :=
    mul_le_mul_of_nonneg_left hmass hH0
  rw [hNcdef] at hwt
  linarith

/-- **Link 6** — `M4Door.m4_door_sieve_mass` (`M4Door.lean:616`), verbatim re-emit. -/
theorem m4_door_sieve_mass_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (A G M J x ω H k : ℕ) (δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 8 * C / δ ≤ (M : ℝ) →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      ∑ n ∈ Finset.Ioc (x / ω) x,
          ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) * (n : ℝ)⁻¹
        ≤ (k : ℝ) * (δ / 4 * (H : ℝ)) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hCle, hblk⟩ := m4_sieve_block_mass_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro A G M J x ω H k δ hA hG hM hδ hMδ hxH hreach hpow hgate
  refine door_cover_sum_le
    (f := fun n => ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) * (n : ℝ)⁻¹)
    (P := δ / 4 * (H : ℝ)) (fun n => by positivity) hxH hreach hpow ?_
  intro i hi
  obtain ⟨hX0, hbig, hreg, herr⟩ := hgate i hi
  exact hblk A G M J (doorLadder x H (i + 1)) H (doorLadder x H (i + 1))
    (doorLadder x H i) δ hA hG hM hδ hMδ hX0 le_rfl (doorLadder_block_subset x H i)
    hbig hreg herr

/-- **Link 7** — `M4ParsevalStone.m4_door_insert_mass_integral`
(`M4ParsevalStone.lean:281`), verbatim re-emit. -/
theorem m4_door_insert_mass_integral_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (A G M J x ω H k : ℕ) (δ : ℝ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (∫ n, ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) ∂(logMeasure x ω))
        ≤ δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
  obtain ⟨C, hC, hCle, hmass⟩ := m4_door_sieve_mass_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro A G M J x ω H k δ hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg H
  have hpowR : (2 : ℝ) ^ (k + 1) ≤ (x : ℝ) := by exact_mod_cast hpow
  have hx0 : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hpowR
  -- ⟦the normaliser⟧
  have hZlo : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_norm_ge hx hω hωx
  have hZ0 : (0 : ℝ) < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  -- ⟦the mass, at the per-block grade δ/3 — the M-gate 24C/δ IS 8C/(δ/3)⟧
  have hδ3 : (0 : ℝ) < δ / 3 := by linarith
  have hMδ3 : 8 * C / (δ / 3) ≤ (M : ℝ) := by
    have he : 8 * C / (δ / 3) = 24 * C / δ := by field_simp; ring
    rw [he]; exact hMδ
  have hB := hmass A G M J x ω H k (δ / 3) hA hG hM hδ3 hMδ3 hxH hreach hpow hgate
  -- ⟦the sharp normalisation⟧
  have hint : (∫ n, ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ)
        ∂(logMeasure x ω))
      ≤ ((k : ℝ) * (δ / 3 / 4 * (H : ℝ)) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))
          / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    integral_logMeasure_le_div hZ0 hB
  -- ⟦the absorption⟧
  have hk3 : (k : ℝ) ≤ 3 * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    door_count_le_three_mul_norm hL hk hZlo
  have habs := door_mass_normalised_le (k := k)
    (Z := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) (δ := δ) (Hr := (H : ℝ))
    (Gm := 4 * 2 ^ k * (H : ℝ) / (x : ℝ)) hZ0 hk3 hδ.le hH0
  -- ⟦the endpoint term: `Z ≥ 1` can only help⟧
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
  have hnn : (0 : ℝ) ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by positivity
  have hend : (4 * 2 ^ k * (H : ℝ) / (x : ℝ)) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹
      ≤ 4 * 2 ^ k * (H : ℝ) / (x : ℝ) := by
    rw [div_le_iff₀ hZ0]
    nlinarith
  linarith

/-- **Link 8, THE TERMINAL** — `M4ParsevalStone.parseval_insert_budget_door`
(`M4ParsevalStone.lean:341`), verbatim re-emit.  This is the `Cg` the `L²` door
reads (`HloExportMR.lean:126`), so `Cg ≤ 2·10^12` is now citable ON THE ROAD. -/
theorem parseval_insert_budget_door_bounded :
    ∃ C : ℝ, 1 ≤ C ∧ C ≤ 2 * 10 ^ 12 ∧ ∀ (A G M J x ω H k : ℕ) [NeZero H] (a : ℕ → ℂ) (δ : ℝ)
      (Xi : Finset (ZMod H)),
      (∀ m, ‖a m‖ ≤ 1) →
      1 ≤ A → 1 ≤ G → 1 ≤ M → 0 < δ → 24 * C / δ ≤ (M : ℝ) →
      2 ≤ x → 2 ≤ ω → ω ≤ x → 4 ≤ Real.log ω →
      H + 1 ≤ x → doorLadder x H k ≤ x / ω → 2 ^ (k + 1) ≤ x →
      (k : ℝ) ≤ Real.log ω / Real.log 2 + 2 →
      (∀ i < k, SieveBlockGate A G M J (doorLadder x H (i + 1))) →
      (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi,
          ∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
              - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
                  (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω)
        ≤ δ / 4 + 4 * 2 ^ k / (x : ℝ) := by
  obtain ⟨C, hC, hCle, hmass⟩ := m4_door_insert_mass_integral_bounded
  refine ⟨C, hC, hCle, ?_⟩
  intro A G M J x ω H k _ a δ Xi ha hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast NeZero.pos H
  -- the pointwise stone, at every window position `n`
  have hpt : ∀ n : ℕ, ∑ ξ ∈ Xi, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
        - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
            (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2
      ≤ (H : ℝ) * ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ) := by
    intro n
    have hb := parseval_stone_budget (H := H) ha (calP A G) (calQK A G M) J n Xi
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul,
      div_le_div_iff₀ (by positivity) hHpos] at hb
    nlinarith [Nat.cast_nonneg (α := ℝ) (notMemSCount (calP A G) (calQK A G M) J H n), hHpos]
  -- the ξ-sum of integrals, bounded by the door's mass integral
  have hsum : ∑ ξ ∈ Xi, (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
          - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
              (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω))
      ≤ ∫ n, (H : ℝ) * ((notMemSCount (calP A G) (calQK A G M) J H n : ℕ) : ℝ)
          ∂(logMeasure x ω) :=
    sum_integral_logMeasure_le Xi _ _ hpt
  rw [integral_const_mul] at hsum
  have hmassI := hmass A G M J x ω H k δ hA hG hM hδ hMδ hx hω hωx hL hxH hreach hpow hk hgate
  have hchain : ∑ ξ ∈ Xi, (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
          - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
              (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω))
      ≤ (H : ℝ) * (δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (x : ℝ)) :=
    le_trans hsum (mul_le_mul_of_nonneg_left hmassI hHpos.le)
  have hfinal : (1 / (H : ℝ) ^ 2) * ((H : ℝ) * (δ / 4 * (H : ℝ)
      + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))) = δ / 4 + 4 * 2 ^ k / (x : ℝ) := by
    field_simp
  calc (1 / (H : ℝ) ^ 2) * ∑ ξ ∈ Xi,
        (∫ n, ‖absWindowSum a H n (-(ξ.val : ℝ) / (H : ℝ))
            - absWindowSum (memSCoeff (calP A G) (calQK A G M) J a) H n
                (-(ξ.val : ℝ) / (H : ℝ))‖ ^ 2 ∂(logMeasure x ω))
      ≤ (1 / (H : ℝ) ^ 2) * ((H : ℝ) * (δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = δ / 4 + 4 * 2 ^ k / (x : ℝ) := hfinal

end Salt.MR

end

