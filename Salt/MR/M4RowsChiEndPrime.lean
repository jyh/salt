/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4RowsChiEnd
import Salt.MR.M4AssemblyPrime

/-!
# ⟦R4 — THE `χ`-SIDE `hrows` SUPPLIER AT `a2Mrow'`⟧ (`M4RowsChiEndPrime`)

Design provenance: `docs/blueprints/flags.md` 2026-07-30 17:51 (⟦R3-A + R3-B LAND⟧), ⟦THE
RESIDUE (the R4 wave)⟧ item (1): *"the `χ`-side `hrows` supplier at `a2Mrow'` (the
`M4RowsChiEnd` genre re-run)"*.

`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` — the R1×R2 join at the door —
carries an `hrows` binder stated at `ThmA2Prime.a2Mrow'`.  On the `q = 1` side that binder's
supplier is `A3Middle.a2Rows_of_capfree3_end'`.  On the `χ` page there was none: every
declaration of `M4RowsChiEnd` lands in `ThmA2.a2Mrow`, whose Lemma-12 slot reads
`a2RowsSum`'s `16·log₂(2X_d)/𝒫ⱼ`.  This file is that page re-run at ⟦R1⟧'s pricer.

## ⚠ ⟦THE DIRECTION, ONE MORE TIME⟧

`a2Mrow' ≤ a2Mrow` (`ThmA2Prime.a2Mrow'_le_a2Mrow`), so a conclusion stated at `a2Mrow'` is
STRONGER and **cannot** be obtained from `M4RowsChiEnd.m4MrowChiEnd_le_a2Mrow`.  Every step
below re-runs its landed sibling against `M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end'`;
not one applies `a2RowsSum'_le_a2RowsSum`.  In particular the bridge

  `m4MrowChiEnd' … ≤ a2Mrow' …`

is a NEW inequality between NEW objects: `m4MrowChiEnd'` carries the `X_d`-FREE `24/𝒫ⱼ` in
its own Lemma-12 summand, so the `2880 ≤ 5760` half of ⟦AMENDMENT G⟧'s `×4` cover is spent
against the primed row sum, exactly as `A3Middle.a3_term3_weigh_mr` spends it at `q = 1`.
It is in that sense — and only that sense — that "the primed sum's smaller `p²`-term weakens
the bridge's demand": the demand moves with the object on BOTH sides.

## The one hypothesis that moves

`sum_lemma12RowsMR_priced_calibratedK2_end'`'s only new demand is the census's `4 ≤ P` floor,
stated as `2 ≤ A`.  It is read off `CalFrameK.A_floor` (`24 ≤ A`) exactly where the landed
page reads `1 ≤ A` off it, and at the door `Adoor M ≥ 2^18`.  So §3–§7 carry the landed
hypothesis lists BYTE FOR BYTE.

## Contents

* §1 `sum_lemma12RowsMR_priced_chi_end'` — the FOUR-row Lemma-12 price at twisted data, at
  ⟦R1⟧'s bracket (`M4RowsChiEnd` §2's twin; §1's pair-law lifts are reused verbatim);
* §2 `m4_rowChi_number_of_capstone_end'` — the per-`χ` seam row as a number
  (`M4RowsChiEnd` §3's twin);
* §3 `m4MrowChiEnd'` and `m4_rowChi_weighed_end'` — the weighting page
  (`M4RowsChiEnd` §4's twin; that file's helpers are `private`, so they are re-minted here);
* §4 `m4_hrowsSum_chi_end'` — the `hrowsSum` slot per character;
* §5 `m4MrowChiEnd'_le_a2Mrow'` and `m4_hrowsSum_chi_door_end'` — the door instance;
* §6 **THE FUSE**: `m4_hrowsSlot_at_door_end'` meets
  `M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'`'s `hrows` binder, and
  `m4_chiSummedFreeRow_of_doorAssembly_pool_end'` is ⟦item 11⟧ at the JOIN with that slot
  GONE from the residue.

⟦PURELY ADDITIVE⟧  No landed declaration is touched.  `M4RowsChiEnd.DoorRowEndBase` is REUSED
unchanged — the per-base gate bundle reads no `p²` numeral.

⟦THE FOUR LOG SCALES⟧ stay apart exactly as in `M4RowsChiEnd`.  `arcDen 12 H` is never
evaluated.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE FOUR-ROW LEMMA-12 PRICE AT TWISTED DATA, AT ⟦R1⟧'s BRACKET

`M4RowsChiEnd` §2 with `M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end` replaced by its
primed sibling.  The pricer is datum-generic and carries no factorization hypothesis, so the
lift is `TLegChi` §1's four coefficient transports and nothing else — `M4RowsChiEnd` §1's
`chiBarCoeff_seamCoefWS` is not even needed here (it enters in §2). -/

/-- **⟦R1⟧ THE FOUR-ROW LEMMA-12 ROW SUM, PRICED AT TWISTED DATA**
(`sum_lemma12RowsMR_priced_chi_end'`).  `M4RowsChiEnd.sum_lemma12RowsMR_priced_chi_end` with
the bracket's `p²` slot at the `X_d`-FREE constant `24/𝒫ⱼ`.  Two lines move against the
landed twin: the numeral, and `1 ≤ A ↦ 2 ≤ A` (the census's `4 ≤ P` floor). -/
theorem sum_lemma12RowsMR_priced_chi_end' :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a c : ℕ → ℂ) (b : ℕ → ℕ → ℂ),
      2 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H1 →
      (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) →
      (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ)
            * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) T
            (chiBarCoeff q χ a) (chiBarCoeff q χ (b j)) (chiBarCoeff q χ c)
        ≤ 960 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 24 / ((calP A G j : ℕ) : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hK2⟩ := sum_lemma12RowsMR_priced_calibratedK2_end'
  refine ⟨C, hC, ?_⟩
  intro q _ χ A G M Jb N Xd H1 T a c b hA hG hM hXd hN hT hH1 hN4 hreg hbig hdom ha hb hc
    hasupp
  exact hK2 A G M Jb N Xd H1 T (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j))
    (chiBarCoeff q χ c) hA hG hM hXd hN hT hH1 hN4 hreg hbig hdom
    (norm_chiBarCoeff_le_one χ ha) (chiBarCoeff_bfam_le_one χ hb)
    (chiBarCoeff_cseq_le_one χ hc) (chiBarCoeff_dyadic_supp χ hasupp)

/-! ## §2 — THE PER-`χ` SEAM ROW AS A NUMBER, AT ⟦R1⟧'s BRACKET

`M4RowsChiEnd` §3 verbatim, with §1 in the pricing step.  The composition is unchanged:
`TLegExit.TLeg_feeds_capstone_gen` with its row slot left open, instantiated at the FOUR-row
strict/fused exit `M4RowMR.lemma12_on_TsetG_mr_windowed_end`, fused with §1.

⟦THE ONE MOVED READ⟧ `2 ≤ A`, from `CalFrameK.A_floor`'s `24 ≤ A` — exactly the read
`A3Middle.seam_row_number_nocap3_end'` performs at `q = 1`. -/

set_option maxHeartbeats 1000000 in
-- Same cause as `M4RowsChiEnd.m4_rowChi_number_of_capstone_end`: the leg's exit and the
-- pricer's exit are elaborated against one another at full ladder width.
/-- **⟦R1⟧ THE PER-`χ` SEAM ROW AS A NUMBER, STRICT/FUSED**
(`m4_rowChi_number_of_capstone_end'`).  `M4RowsChiEnd.m4_rowChi_number_of_capstone_end` with
the Lemma-12 bracket's `p²` slot at the `X_d`-FREE constant `24/𝒫ⱼ`.  The hypothesis list is
the landed one BYTE FOR BYTE. -/
theorem m4_rowChi_number_of_capstone_end' :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X Tann t₁ S η ε : ℝ),
        CalFrameK η H1 A G M Jb Xd →
        0 ≤ Tann → 2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW, UNTWISTED⟧ (`hwin` is NOT here)
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        -- ⟦THE RECONCILIATION GATES (R1), (R2), (R4)⟧
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
                / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        -- ⟦THE A3 CAPSTONE ROW, CARRIED⟧ (`M4RowsChi.m4_rowChi_capstone` supplies it)
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S ^ 2
              + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
        (∫ t in seamAnn X Tann, ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Ct * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + 960 * (Tann / (Xd : ℝ) + 1)
                    * ((∑ j ∈ Finset.Icc 1 Jb,
                          ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                              * (Real.exp 1 / (Xd : ℝ) ^ 2))
                            + 24 / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + Cp * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Ct, hCt, hfeed⟩ := TLeg_feeds_capstone_gen
  obtain ⟨Cp, hCp, hprice⟩ := sum_lemma12RowsMR_priced_chi_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X Tann t₁ S η ε hF hT0 hNXd hN4
    hcoefWS hasupp hQXd hXdbig hdom hcap
  -- ⟦THE FRAME'S OWN READS⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hA2 : 2 ≤ A := le_trans (by norm_num) hF.A_floor
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hP1nat : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast hP1nat
    linarith
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith) (one_le_calQK A G M 1) hQ1Xd hv
  have hHj : ∀ j ∈ Finset.Icc 1 Jb, (2 : ℝ) ≤ calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    rw [calH]
    nlinarith [hF.H1_two]
  have hPj1 : ∀ j : ℕ, 1 ≤ calP A G j := fun j => by
    simp only [calP]; exact Nat.one_le_two_pow
  have hasuppχ := chiBarCoeff_dyadic_supp χ hasupp
  -- ⟦THE ROW SLOT, AT THE FOUR-ROW STRICT/FUSED EXIT⟧
  have hrowfam : ∀ j ∈ Finset.Icc 1 Jb,
      (∫ t in (seamAnn X Tann \ seamBall X t₁)
            ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1) (mrAlpha η) Jb j,
          ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
        ≤ 2 * ((ramI (calH H1 j) (calP A G j) (calQK A G M j)).card : ℝ)
            * (∑ v ∈ ramI (calH H1 j) (calP A G j) (calQK A G M j),
                ∫ t in (seamAnn X Tann \ seamBall X t₁)
                    ∩ TsetG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                        (mrAlpha η) Jb j,
                  ‖ramMain (calH H1 j) N Xd (calP A G j) (calQK A G M j)
                    (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) v t‖ ^ 2)
          + lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
              (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) := by
    intro j hj
    exact lemma12_on_TsetG_mr_windowed_end (chiBarCoeff q χ c) (calP A G) (calQK A G M)
      (calH H1) (mrAlpha η) Jb j (hHj j hj) N Xd hXd1 hNXd (hPj1 j)
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c)
      (chiBarCoeff_seamCoefWS χ (hcoefWS j hj)) (chiBarCoeff_bfam_le_one χ hb1 j)
      (chiBarCoeff_cseq_le_one χ hc1) (hasupp_real_of_nat hasuppχ) X Tann t₁ hT0
  have hleg := hfeed (chiBarCoeff q χ c) (chiBarCoeff q χ a)
    (fun j => chiBarCoeff q χ (bfam j)) (calP A G) (calQK A G M) (calH H1) η Jb N Xd
    (calP A G 1) X Tann t₁ S ε
    (fun j => lemma12RowsMR_end N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c))
    hη hη6 hJb1 hXd1 hT0 hP1pos (levelGates_calibratedK hF) hH1two hP1nat
    (calP_le_calQK hM1 le_rfl) hbot1 (chiBarCoeff_bfam_le_one χ hb1)
    (chiBarCoeff_cseq_le_one χ hc1) hrowfam hcap
  -- ⟦THE PRICE OF `Σ_j lemma12RowsMR_end`, AT THE TWISTED DATUM, AT ⟦R1⟧'s NUMERAL⟧
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hK2 := hprice q χ A G M Jb N Xd H1 Tann a c bfam hA2 hG1 hM1 hXd1 hNXd hT0 hF.H1_two
    hN4 hreg hXdbig hdom ha1 hb1 hc1 hasupp
  exact hleg.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2)) le_rfl)

/-! ## §3 — THE WEIGHTING, AT ⟦R1⟧'s BRACKET

`M4RowsChiEnd` §4's page.  The four numerals `9`/`244`/`3`/`3/2` are CHARACTER-BLIND and
ROW-BLIND arithmetic and do not move; the Lemma-12 summand still weighs `960·3 = 2880`.
What moves is the OBJECT the third weighing lands in — the primed bracket.

`M4RowsChiEnd`'s helpers are `private` to that file, so the page is re-minted here at its own
names (same statements, same proofs), with the row-sum nonnegativity restated at the primed
bracket — where it is STRICTLY easier, the `log₂(2X_d) ≥ 0` step disappearing. -/

/-- `M4RowsChiEnd.d5_weight_gates`, re-minted (that one is `private`). -/
private lemma d5p_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
    (hT : X / h ≤ T) (hXd : X ≤ 4 * Xd) (hQ1 : Q1 ≤ h) (hQ10 : 0 ≤ Q1) :
    0 ≤ X / h / T ∧ X / h / T ≤ 1 ∧
      X / h / T * (2 * T * Q1 / Xd + 1) ≤ 9 ∧
      X / h / T * (2 * (2 * T) / Xd + 240) ≤ 244 ∧
      X / h / T * (2 * T / Xd + 1) ≤ 3 ∧
      X / h / T * (2 * T / X + 1) ≤ 3 / 2 := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hu0 : (0 : ℝ) < X / h := div_pos hX0 hh0
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le hu0 hT
  have hXd0 : (0 : ℝ) < Xd := by linarith
  have hw0 : (0 : ℝ) ≤ X / h / T := le_of_lt (div_pos hu0 hT0)
  have hw1 : X / h / T ≤ 1 := (div_le_one hT0).mpr hT
  have hratio : X / h / Xd ≤ 4 / h := by
    rw [div_div, div_le_div_iff₀ (by positivity) hh0]
    nlinarith
  refine ⟨hw0, hw1, ?_, ?_, ?_, ?_⟩
  · have hid : X / h / T * (2 * T * Q1 / Xd + 1) = 2 * Q1 * (X / h / Xd) + X / h / T := by
      field_simp
    have hstep : 2 * Q1 * (X / h / Xd) ≤ 2 * Q1 * (4 / h) :=
      mul_le_mul_of_nonneg_left hratio (by linarith)
    have hval : 2 * Q1 * (4 / h) ≤ 8 := by
      rw [show 2 * Q1 * (4 / h) = 8 * Q1 / h by ring, div_le_iff₀ hh0]
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * (2 * T) / Xd + 240)
        = 4 * (X / h / Xd) + 240 * (X / h / T) := by field_simp; ring
    have hstep : 4 * (X / h / Xd) ≤ 4 * (4 / h) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    have hval : 4 * (4 / h) ≤ 4 := by
      rw [show 4 * (4 / h) = 16 / h by ring, div_le_iff₀ hh0]
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / Xd + 1) = 2 * (X / h / Xd) + X / h / T := by field_simp
    have hstep : 2 * (X / h / Xd) ≤ 2 * (4 / h) :=
      mul_le_mul_of_nonneg_left hratio (by norm_num)
    have hval : 2 * (4 / h) ≤ 2 := by
      rw [show 2 * (4 / h) = 8 / h by ring, div_le_iff₀ hh0]
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / X + 1) = 2 / h + X / h / T := by field_simp
    have h2 : 2 / h ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hh0 (by norm_num)]
      linarith
    rw [hid]; linarith

/-- `M4RowsChiEnd.d5_row_weigh`, re-minted. -/
private lemma d5p_row_weigh {w Sq A B C D s a b c d : ℝ}
    (hS : w * Sq ≤ s) (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (Sq + (A + B + C) + D) ≤ s + (a + b + c) + d := by
  have h : w * (Sq + (A + B + C) + D) = w * Sq + (w * A + w * B + w * C) + w * D := by ring
  rw [h]; linarith

/-- `M4RowsChiEnd.d5_level1_weigh`, re-minted. -/
private lemma d5p_level1_weigh {w Hq Lq R Pq Br : ℝ}
    (hHL : 0 ≤ 2 * (Hq * Lq + 1)) (hPq : 0 ≤ Pq) (hBr : 0 ≤ Br) (hR9 : w * R ≤ 9) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 18 * (Hq * Lq + 1) * Pq * Br := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = (2 * (Hq * Lq + 1) * Pq * Br) * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 2 * (Hq * Lq + 1) * Pq * Br := by positivity
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hR9 h0]

/-- `M4RowsChiEnd.d5_term2_weigh`, re-minted: `1536·244 = 374784`. -/
private lemma d5p_term2_weigh {w Ct R Y : ℝ} (hCt : 0 ≤ Ct) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Ct * Real.exp 3 * R * Y) ≤ 374784 * Ct * Real.exp 3 * Y := by
  have hid : w * (1536 * Ct * Real.exp 3 * R * Y)
      = 1536 * Ct * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Ct * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- `M4RowsChiEnd.d5_term3_weigh`, re-minted: `960·3 = 2880`, at ANY nonnegative bracket —
which is why the primed row sum passes through it untouched. -/
private lemma d5p_term3_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3) :
    w * (960 * R * Z) ≤ 2880 * Z := by
  have hid : w * (960 * R * Z) = 960 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 960) hZ)]

/-- `M4RowsChiEnd.d5_term4_weigh`, re-minted: `2·(3/2) = 3`. -/
private lemma d5p_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]

/-- `M4RowsChiEnd.d5_ball_weigh`, re-minted. -/
private lemma d5p_ball_weigh {w S : ℝ} (hw1 : w ≤ 1) :
    w * (8 * S ^ 2) ≤ 8 * S ^ 2 := by nlinarith [sq_nonneg S]

/-- **THE PER-`χ` ROW NUMBER AT ⟦R1⟧'s BRACKET** (`m4MrowChiEnd'`).
`M4RowsChiEnd.m4MrowChiEnd` with its Lemma-12 summand's `p²` slot at the `X_d`-FREE constant
`24/𝒫ⱼ`.  Every other summand — the ball leg, the §8.1 level-1 term, the `𝒯`-leg and the
`𝒰`-leg — is byte-identical, and the weighed prefactor is still `2880`. -/
def m4MrowChiEnd' (Ct Cp : ℝ) (A G M Jb Xd : ℕ) (H1 η X ε S : ℝ) : ℝ :=
  8 * S ^ 2
    + (18 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
          * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
          * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
              + 60 * (calH H1 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / calH H1 1))
        + 374784 * Ct * Real.exp 3 * (1 / ((calP A G 1 : ℕ) : ℝ))
        + 2880 * ((∑ j ∈ Finset.Icc 1 Jb,
              ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                  * (Real.exp 1 / (Xd : ℝ) ^ 2))
                + 24 / ((calP A G j : ℕ) : ℝ)
                + 1 / (Xd : ℝ)))
            + Cp * (2 / (M : ℝ))))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-- The primed Lemma-12 row sum is a sum of nonnegative terms.  `M4RowsChiEnd`'s
`d5_rowsSum_nonneg` at ⟦R1⟧'s bracket — strictly easier, the `log₂(2X_d) ≥ 0` step gone. -/
private lemma d5p_rowsSum_nonneg {A G Jb Xd : ℕ} {H1 : ℝ} (hXd : 1 ≤ Xd) (hH1 : 2 ≤ H1) :
    (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 Jb,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 24 / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ)) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH H1 j := by rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP A G j : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G j := by simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 24 / ((calP A G j : ℕ) : ℝ) :=
    div_nonneg (by norm_num) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

set_option maxHeartbeats 400000 in
-- Same cause as `M4RowsChiEnd.m4_rowChi_weighed_end`: the `hrow` hypothesis is the full
-- number-row, and matching it summand by summand against `m4MrowChiEnd'` costs more than the
-- default budget in elaboration alone.
/-- **THE WEIGHTED ROW AT ⟦R1⟧'s BRACKET** (`m4_rowChi_weighed_end'`).  §2's number-row at
`T_ann = 2T`, weighted by `(X/h)/T`, lands inside the `T`-FREE constant `m4MrowChiEnd'`. -/
theorem m4_rowChi_weighed_end' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {a : ℕ → ℂ}
    {N Xd A G M Jb : ℕ} {H1 X h S η ε Ct Cp T : ℝ}
    (hXd1 : 1 ≤ Xd) (hH1 : 2 ≤ H1) (hη : 0 < η) (hη6 : η < 1 / 6)
    (hCt : 0 ≤ Ct) (hCp : 0 ≤ Cp) (hM1 : 1 ≤ M)
    (hh4 : 4 ≤ h) (hX0 : 0 < X) (hL0 : 0 ≤ Real.log X) (hX4Xd : X ≤ 4 * (Xd : ℝ))
    (hQ1h : ((calQK A G M 1 : ℕ) : ℝ) ≤ h)
    (hT : X / h ≤ T)
    (hrow : (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ 8 * S ^ 2
        + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
              * (2 * T * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
              * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
              * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                    * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                  + 60 * (calH H1 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / calH H1 1))
            + 1536 * Ct * Real.exp 3 * (2 * (2 * T) / (Xd : ℝ) + 240)
                * (1 / ((calP A G 1 : ℕ) : ℝ))
            + 960 * (2 * T / (Xd : ℝ) + 1)
                * ((∑ j ∈ Finset.Icc 1 Jb,
                      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                          * (Real.exp 1 / (Xd : ℝ) ^ 2))
                        + 24 / ((calP A G j : ℕ) : ℝ)
                        + 1 / (Xd : ℝ)))
                  + Cp * (2 / (M : ℝ))))
        + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) :
    X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ m4MrowChiEnd' Ct Cp A G M Jb Xd H1 η X ε S := by
  have hQ10 : (0 : ℝ) ≤ ((calQK A G M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    d5p_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK A G M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hrow hw0).trans ?_
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1pos : (0 : ℝ) < calH H1 1 := by rw [hcalH1]; linarith
  have hα1 : 0 < mrAlpha η 1 := mrAlpha_pos η hη hη6 le_rfl
  have hα1' : mrAlpha η 1 ≤ 1 / 4 := by rw [mrAlpha]; nlinarith
  have hHL0 : (0 : ℝ) ≤ 2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1) := by
    have hQlog : (0 : ℝ) ≤ Real.log ((calQK A G M 1 : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((calQK A G M 1 : ℕ) : ℝ) := by
        exact_mod_cast one_le_calQK A G M 1
      exact Real.log_nonneg h
    nlinarith
  have hPq0 : (0 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBr0 : (0 : ℝ) ≤ 4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
      * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
    + 60 * (calH H1 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / calH H1 1) := by
    have h1 : (0 : ℝ) < 1 - 2 * mrAlpha η 1 := by linarith
    have h2 : (0 : ℝ) ≤ calH H1 1 / (1 - 2 * mrAlpha η 1) := by positivity
    have h3 : (0 : ℝ) ≤ calH H1 1 / mrAlpha η 1 := by positivity
    have e1 : (0 : ℝ) < Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1) := Real.exp_pos _
    have e2 : (0 : ℝ) < Real.exp (4 * mrAlpha η 1 / calH H1 1) := Real.exp_pos _
    nlinarith
  have hY0 : (0 : ℝ) ≤ 1 / ((calP A G 1 : ℕ) : ℝ) := by positivity
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 Jb,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 24 / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5p_rowsSum_nonneg (A := A) (G := G) (Jb := Jb) (Xd := Xd) (H1 := H1) hXd1 hH1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) := Real.rpow_nonneg hL0 _
  unfold m4MrowChiEnd'
  exact d5p_row_weigh (d5p_ball_weigh hw1)
    (d5p_level1_weigh hHL0 hPq0 hBr0 hg9)
    (d5p_term2_weigh hCt hY0 hg244) (d5p_term3_weigh hRS0 hg3) (d5p_term4_weigh hZ0 hg32)

/-! ## §4 — THE DELIVERABLE: the `hrowsSum` slot, per character, at ⟦R1⟧'s bracket

`M4RowsChiEnd` §5 verbatim over §2 + §3.  The residue list is that section's, unchanged:
the carried A3 capstone family, the `𝒯`-side frame, the reconciliation gates (R1)–(R6), and
the weighting frame.  `hwin` is absent here as it is there. -/

/-- **⟦THE R4 DELIVERABLE⟧ THE PER-`χ` ROW FAMILY AT ⟦R1⟧'s BRACKET** (`m4_hrowsSum_chi_end'`).
`M4RowsChiEnd.m4_hrowsSum_chi_end` landing in `m4MrowChiEnd'`. -/
theorem m4_hrowsSum_chi_end' :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd A G M Jb : ℕ) (H1 X h η ε : ℝ)
        (t₁ S : DirichletCharacter ℂ q → ℝ),
        CalFrameK η H1 A G M Jb Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 Jb,
          SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 Jb,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP A G j : ℕ) : ℝ)
                / Real.log ((calQK A G M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK A G M 1 : ℕ) : ℝ) ≤ h →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ (`M4RowsChi.m4_rowChi_capstone` supplies it)
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * S χ ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP A G) (calQK A G M) (calH H1)
                      (mrAlpha η) Jb,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ m4MrowChiEnd' Ct Cp A G M Jb Xd H1 η X ε (S χ) := by
  obtain ⟨Ct, Cp, hCt, hCp, hnum⟩ := m4_rowChi_number_of_capstone_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hrow := hnum q χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X (2 * T) (t₁ χ) (S χ) η ε
    hF (by linarith) hNXd hN4 hcoefWS hasupp hQXd hXdbig hdom
    (hcap χ T hT hTX2 hTgate hTll)
  exact m4_rowChi_weighed_end' hXd1 hF.H1_two hF.eta_pos hF.eta_lt hCt.le hCp.le hF.one_le_M
    hh4 hX0 hL0 hX4Xd hQ1h hT hrow

/-! ## §5 — THE DOOR INSTANCE: `m4MrowChiEnd'` INSIDE `a2Mrow'`

`M4RowsChiEnd` §6 at ⟦R1⟧'s bracket.  At the door family `(Adoor M, 3072M, M, 2, H1door M)`
the primed row sum IS `ThmA2.a2RowsSum'` — the two definitions have the same text — so the
bridge is the landed one's arithmetic verbatim: `2880 ≤ 5760`, i.e. HALF of ⟦AMENDMENT G⟧'s
`×4` cover, spent against the primed object on both sides.  **`ThmA2Prime.a2Mrow'` does not
move.** -/

/-- **THE DOOR BRIDGE AT ⟦R1⟧'s BRACKET** (`m4MrowChiEnd'_le_a2Mrow'`).  At the door family and
the vacuous ball, the primed per-`χ` row number sits inside `ThmA2Prime.a2Mrow'`. -/
theorem m4MrowChiEnd'_le_a2Mrow' {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd' Ct Cp (Adoor M) (3072 * M) M 2 Xd (H1door M) (1 / 12) X ε 0
      ≤ a2Mrow' Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 24 / ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5p_rowsSum_nonneg (A := Adoor M) (G := 3072 * M) (Jb := 2) (Xd := Xd)
      (H1 := H1door M) hXd (H1door_two hM)]
  unfold m4MrowChiEnd' a2Mrow' a2Level1 a2RowsSum'
  have hlvl' : 18 * (calH (H1door M) 1
        * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1)
      * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
      * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
            * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
          + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
              * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1))
      ≤ 47520 * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc 18 * (calH (H1door M) 1
            * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1)
          * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
          * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
              + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                  * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1))
        = 2 * (calH (H1door M) 1
              * Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) + 1) * 9
            * ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
            * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                  * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
                + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                    * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1)) := by ring
      _ ≤ 5280 * 9 * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := hlvl
      _ = 47520 * ((Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by ring
  linarith

/-- **⟦THE R4 DELIVERABLE AT THE DOOR⟧** (`m4_hrowsSum_chi_door_end'`).  §4 at the door family
and the vacuous ball, landed inside `ThmA2Prime.a2Mrow'`: this is
`ThmA2Prime.thm_a2'_of_rows_chiSummed_pool'`'s `hrowsSum` slot at the constant families
`Cs χ := Ct`, `Ccc χ := Cp`, `ε χ := ε`. -/
theorem m4_hrowsSum_chi_door_end' :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (Adoor M) (3072 * M) j) (calQK (Adoor M) (3072 * M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) j)
                    (calQK (Adoor M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (3072 * M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (3072 * M))
                      (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow' Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (Adoor M) (3072 * M) M 2 (H1door M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at M Xd hM hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow' hM hXd1 hCp.le

/-! ## §6 — ⟦THE FUSE⟧: the JOIN's `hrows` slot, MET AND DISCHARGED

`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` carries an `hrows` binder stated
at `a2Mrow'`.  §5's successor fills it, through the SAME datum bridge the landed page uses
(`M4Assembly.chiBarCoeff_doorRowDatum`), and `M4RowsChiEnd.DoorRowEndBase` is reused
unchanged — the per-base bundle reads no `p²` numeral, so R1 is invisible to it. -/

/-- **⟦THE SLOT, MET AT THE JOIN⟧** (`m4_hrowsSlot_at_door_end'`).  The statement below is
`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'`'s `hrows` binder VERBATIM at
`Cs ≡ Ct`, `Ccc ≡ Cp` — the compile is the certificate of the byte-fit. -/
theorem m4_hrowsSlot_at_door_end' :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ a2Mrow' Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  -- ⟦THE DOOR INSTANCE'S OWN FRAME⟧
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum] using hslot

/-- **⟦A4 — ITEM 11 AT THE R1×R2 JOIN, WITH THE `hrows` SLOT GONE⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_end'`) — **THE FUSE**.
`M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'` instantiated at §6's supplier:
`M4ChiSummed.M4ChiSummedFreeRow` — ⟦item 11⟧ of `m4_second_road` — at the JOINED door grade
`a2DoorGrade_pool`, from the named gates alone, **with `hrows` no longer among them**.

⟦THE RESIDUE, AFTER THE FUSE⟧ (the PORT-AUDIT law)
* `hM` — `1 ≤ M`;
* `hb1`, `hc1` — the two `1`-bounds on the door's untwisted Ramaré data;
* `hframe` — `M4AssemblyPrime.DoorFuseFrame_pool'` at every base (TEN fields), with the
  base-indexed pool `π₀`; no field caps the base (that module's `μ`-ledger);
* `hbase` — `M4RowsChiEnd.DoorRowEndBase` at every base: the STRICT pair law plus the
  `q = 1` chain's own `X_d`-side reconciliation gates and the two weighting-frame numerals.
  **This is what replaced `hrows`**;
* `hcap` — the carried A3 capstone family at the door pin `S ≡ 0`; supplier
  `M4RowsChi.m4_rowChi_capstone`;
* `hband` — the `T₀`-band per character;
* `hpool` — `0 ≤ π₀` at every base;
* `henv` — THE ARITHMETIC, `arcDen 12 H · a2DoorGrade_pool … ≤ RSbig j H`.

Nothing else survives; in particular the assembly's `hrows` binder does not appear. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end' :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame_pool' M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloor M ≤ j →
          arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool' (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-! ## §GK — the G-lever twin

⟦R1⟧'s primed door page at `G := s13GK K M`.  `ThmA2Prime.a2Mrow'_gk` / `ThmA2.a2RowsSum'_gk`
are the moved objects; `M4RowsChiEnd.DoorRowEndBase_gk` is reused unchanged (the per-base
bundle reads no `p²` numeral, so R1 stays invisible to it).

⟦BLOCKED, NOT ATTEMPTED⟧ `m4_chiSummedFreeRow_of_doorAssembly_pool_end'` (:721) — one `exact`
at `M4AssemblyPrime.m4_chiSummedFreeRow_of_doorAssembly_pool'`, which carries no `_gk`
sibling (`M4AssemblyPrime` has no `§GK` section at all). -/

/-- **THE DOOR BRIDGE AT ⟦R1⟧'s BRACKET, AT THE G-LEVER**
(`m4MrowChiEnd'_le_a2Mrow'_gk`).  Re-derived, not weakened through `a2Mrow'_le_a2Mrow_gk`. -/
theorem m4MrowChiEnd'_le_a2Mrow'_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd' Ct Cp (Adoor M) (s13GK K M) M 2 Xd (H1door M) (1 / 12) X ε 0
      ≤ a2Mrow'_gk K Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_gk K (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 24 / ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5p_rowsSum_nonneg (A := Adoor M) (G := s13GK K M) (Jb := 2) (Xd := Xd)
      (H1 := H1door M) hXd (H1door_two hM)]
  unfold m4MrowChiEnd' a2Mrow'_gk a2RowsSum'_gk
  rw [← a2Level1_gk_eq K M]
  have hlvl' : 18 * (calH (H1door M) 1
        * Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) + 1)
      * ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
      * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
            * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
          + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
              * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1))
      ≤ 47520 * ((Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc 18 * (calH (H1door M) 1
            * Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) + 1)
          * ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
          * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
              + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                  * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1))
        = 2 * (calH (H1door M) 1
              * Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) + 1) * 9
            * ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
            * (4 * (calH (H1door M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                  * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1door M) 1)
                + 60 * (calH (H1door M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                    * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1door M) 1)) := by ring
      _ ≤ 5280 * 9 * ((Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := hlvl
      _ = 47520 * ((Real.log ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by ring
  linarith

/-- **⟦THE R4 DELIVERABLE AT THE DOOR⟧ AT THE G-LEVER**
(`m4_hrowsSum_chi_door_end'_gk`).  Frame: `ThmA2.calFrameK_doorH1_at_gk`, whence
`K ≤ 1.7·10⁸`. -/
theorem m4_hrowsSum_chi_door_end'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (Adoor M) (s13GK K M) j) (calQK (Adoor M) (s13GK K M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (Adoor M) (s13GK K M) j)
                    (calQK (Adoor M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (Adoor M) (s13GK K M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (Adoor M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (Adoor M) (s13GK K M))
                      (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow'_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (s13GK K M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (Adoor M) (s13GK K M) M 2 (H1door M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_gk K hM hXd1 hCp.le

/-- **⟦THE SLOT, MET AT THE JOIN⟧ AT THE G-LEVER**
(`m4_hrowsSlot_at_door_end'_gk`). -/
theorem m4_hrowsSlot_at_door_end'_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorRowEndBase_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (s13GK K M))
                        (calQK (Adoor M) (s13GK K M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end'_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  -- ⟦THE DOOR INSTANCE'S OWN FRAME⟧
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_gk K M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_gk] using hslot

-- #audit (temporary)

end Salt.MR
