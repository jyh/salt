/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4SocketLinear

/-!
# ⟦LADDER-L G3 §3⟧ — `M4RowsChiEndPrime` + `M4RowsChiZeroPrime` at the LINEAR anchor
(`M4RowsChiPrimeLinear`)

⟦COMPOSE-FLAT-2⟧'s ladder re-cut, at ⟦R1⟧'s primed bracket.  The `_L` twins of the two primed
`χ`-row door pages at `AdoorL M = 2^36·M`.

⟦WHY THIS PAGE IS SHORT⟧ both landed files' ENGINES — `m4_rowChi_number_of_capstone_end'`,
`m4_rowChi_weighed_end'`, `m4_hrowsSum_chi_end'`, `m4_hrowsSum_chi_zero'`,
`sum_lemma12RowsMR_*` — are `(A, G, H1, Jb)`-GENERIC: they bind the ladder's parameters
explicitly and never read `Adoor`.  Only the DOOR INSTANCES move, and each moves by
substituting `AdoorL M` for `Adoor M` and `H1doorL M` for `H1door M` in the instantiation.
`m4MrowChiEnd'` itself is likewise `(A, G)`-generic and needs no twin.

PURELY ADDITIVE: no landed declaration moves.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE DOOR BRIDGE AT ⟦R1⟧'s BRACKET, AT THE LINEAR DOOR -/

/-- `M4RowsChiEndPrime.d5p_rowsSum_nonneg` (:380), re-proved here because the landed lemma is
`private` to its file.  `(A, G, H1)`-GENERIC — nothing about the door enters. -/
private lemma d5pL_rowsSum_nonneg {A G Jb Xd : ℕ} {H1 : ℝ} (hXd : 1 ≤ Xd) (hH1 : 2 ≤ H1) :
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

/-- **THE DOOR BRIDGE AT ⟦R1⟧'s BRACKET, AT THE LINEAR DOOR** (`m4MrowChiEnd'_le_a2Mrow'_L`).
`M4RowsChiEndPrime.m4MrowChiEnd'_le_a2Mrow'` (:544) at `AdoorL`: at the linear door family and
the vacuous ball, the primed per-`χ` row number sits inside `a2Mrow'_L`.  The arithmetic is
the landed one verbatim (`2880 ≤ 5760`), read through `level1_term_door_decays_L`. -/
theorem m4MrowChiEnd'_le_a2Mrow'_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd' Ct Cp (AdoorL M) (3072 * M) M 2 Xd (H1doorL M) (1 / 12) X ε 0
      ≤ a2Mrow'_L Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_L (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 24 / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5pL_rowsSum_nonneg (A := AdoorL M) (G := 3072 * M) (Jb := 2) (Xd := Xd)
      (H1 := H1doorL M) hXd (H1door_two_L hM)]
  unfold m4MrowChiEnd' a2Mrow'_L a2Level1_L a2RowsSum'_L
  have hlvl' : 18 * (calH (H1doorL M) 1
        * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) + 1)
      * ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
      * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
            * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
          + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
              * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1))
      ≤ 47520 * ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc 18 * (calH (H1doorL M) 1
            * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) + 1)
          * ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
          * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
              + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                  * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1))
        = 2 * (calH (H1doorL M) 1
              * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) + 1) * 9
            * ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
            * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                  * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
                + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                    * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1)) := by ring
      _ ≤ 5280 * 9 * ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := hlvl
      _ = 47520 * ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by ring
  linarith

/-! ## §2 — ⟦THE R4 DELIVERABLE AT THE LINEAR DOOR⟧ -/

/-- **⟦THE R4 DELIVERABLE AT THE LINEAR DOOR⟧** (`m4_hrowsSum_chi_door_end'_L`).
`M4RowsChiEndPrime.m4_hrowsSum_chi_door_end'` (:592) at `AdoorL`.  The engine
`m4_hrowsSum_chi_end'` is `(A, G, H1)`-GENERIC and is reused verbatim; the frame is
`ThmA2Linear.calFrameK_doorH1_at_L`. -/
theorem m4_hrowsSum_chi_door_end'_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (3072 * M) j) (calQK (AdoorL M) (3072 * M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (3072 * M))
                      (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow'_L Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (3072 * M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L M Xd hM hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L hM hXd1 hCp.le

/-- **⟦THE SLOT, MET AT THE JOIN, AT THE LINEAR DOOR⟧** (`m4_hrowsSlot_at_door_end'_L`) —
`m4_chiSummedFreeRow_of_doorAssembly_pool'_L`'s `hrows` binder VERBATIM at `Cs ≡ Ct`,
`Ccc ≡ Cp`. -/
theorem m4_hrowsSlot_at_door_end'_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end'_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_L M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_L M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L] using hslot

/-- **⟦A4 — ITEM 11 AT THE R1×R2 JOIN, AT THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L`) — THE FUSE, at `AdoorL`. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'_L
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-! ## §3 — THE DENSITY-FREE PRIMED DOOR PAGE, AT THE LINEAR DOOR -/

/-- **⟦THE `a2Mrow'`-GENRE ROW FAMILY AT THE LINEAR DOOR, DENSITY-FREE⟧**
(`m4_hrowsSum_chi_door_zero'_L`).  `M4RowsChiZeroPrime.m4_hrowsSum_chi_door_zero'` (:622) at
`AdoorL`; the engine `m4_hrowsSum_chi_zero'` is `(A, G, H1)`-GENERIC. -/
theorem m4_hrowsSum_chi_door_zero'_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (3072 * M) j) (calQK (AdoorL M) (3072 * M) M j)
            (winCutH Xd (doorCoeffU_L M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (3072 * M))
                      (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L M))) t‖ ^ 2)
            ≤ a2Mrow'_L Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (3072 * M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L M Xd hM hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L hM hXd1 hCp

/-- **⟦THE SLOT, MET, DENSITY-FREE, AT THE LINEAR DOOR⟧** (`m4_hrowsSlot_at_door_zero'_L`). -/
theorem m4_hrowsSlot_at_door_zero'_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero'_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L] using hslot

/-- **⟦A4 — ITEM 11 AT A FREE DENSITY CONSTANT AND THE FREE POOL, AT THE LINEAR DOOR⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L`). -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (3072 * M))
                        (calQK (AdoorL M) (3072 * M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_L (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv

/-! ## §GK — the `G`-lever twins, at the LINEAR door -/


/-- **THE DOOR BRIDGE AT ⟦R1⟧'s BRACKET, AT THE G-LEVER**
(`m4MrowChiEnd'_le_a2Mrow'_L_gk`).  Re-derived, not weakened through `a2Mrow'_L_le_a2Mrow_gk`. -/
theorem m4MrowChiEnd'_le_a2Mrow'_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd' Ct Cp (AdoorL M) (s13GK K M) M 2 Xd (H1doorL M) (1 / 12) X ε 0
      ≤ a2Mrow'_L_gk K Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_L_gk K (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 24 / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5pL_rowsSum_nonneg (A := AdoorL M) (G := s13GK K M) (Jb := 2) (Xd := Xd)
      (H1 := H1doorL M) hXd (H1door_two_L hM)]
  unfold m4MrowChiEnd' a2Mrow'_L_gk a2RowsSum'_L_gk
  rw [← a2Level1_L_gk_eq K M]
  have hlvl' : 18 * (calH (H1doorL M) 1
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1)
      * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
      * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
            * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
          + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
              * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1))
      ≤ 47520 * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
    calc 18 * (calH (H1doorL M) 1
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1)
          * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
          * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
              + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                  * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1))
        = 2 * (calH (H1doorL M) 1
              * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1) * 9
            * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12 : ℝ) 1))
            * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12 : ℝ) 1))
                  * Real.exp ((1 - 2 * mrAlpha (1 / 12 : ℝ) 1) / calH (H1doorL M) 1)
                + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12 : ℝ) 1)
                    * Real.exp (4 * mrAlpha (1 / 12 : ℝ) 1 / calH (H1doorL M) 1)) := by ring
      _ ≤ 5280 * 9 * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := hlvl
      _ = 47520 * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
            / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by ring
  linarith

/-- **⟦THE R4 DELIVERABLE AT THE DOOR⟧ AT THE G-LEVER**
(`m4_hrowsSum_chi_door_end'_L_gk`).  Frame: `ThmA2.calFrameK_doorH1_at_L_gk`, whence
`K ≤ 1.7·10⁸`. -/
theorem m4_hrowsSum_chi_door_end'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L_gk K hM hXd1 hCp.le

/-- **⟦THE SLOT, MET AT THE JOIN⟧ AT THE G-LEVER**
(`m4_hrowsSlot_at_door_end'_L_gk`). -/
theorem m4_hrowsSlot_at_door_end'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end'_L_gk K hK
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
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_L_gk K M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot


/-- **⟦THE `a2Mrow'`-GENRE ROW FAMILY AT THE LINEAR DOOR, DENSITY-FREE⟧ AT THE G-LEVER**
(`m4_hrowsSum_chi_door_zero'_L_gk`).  `m4_hrowsSum_chi_door_zero'_L` (:269) at the levered
`G = s13GK K M`; frame `ThmA2Linear.calFrameK_doorH1_at_L_gk`, whence `K ≤ 1.7·10⁸`. -/
theorem m4_hrowsSum_chi_door_zero'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_L_gk K M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L_gk K M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ) hNXd hN4 hcoefWS (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L_gk K hM hXd1 hCp


/-- **⟦THE SLOT, MET, DENSITY-FREE, AT THE LINEAR DOOR⟧ AT THE G-LEVER**
(`m4_hrowsSlot_at_door_zero'_L_gk`).  `m4_hrowsSlot_at_door_zero'_L` (:317) at the lever —
the missing cross-group twin consumed by `M4ClosureRepairLinear` and `S16FlatTerminalLinear`. -/
theorem m4_hrowsSlot_at_door_zero'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero'_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot


/-- **⟦A4 — ITEM 11 AT THE R1×R2 JOIN, AT THE LINEAR DOOR⟧ AT THE G-LEVER**
(`m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk`) — THE FUSE, at `AdoorL` and the levered
`G = s13GK K M`.  `m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L` (:220) at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'_L_gk K hK
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv


/-- **⟦A4 — ITEM 11 AT A FREE DENSITY CONSTANT AND THE FREE POOL, AT THE LINEAR DOOR⟧ AT THE
G-LEVER** (`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk`).
`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L` (:368) at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk (K : ℕ)
    (hK : K ≤ 170000000) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk K hK
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband hpool henv


/-! ## §Xw — ⟦KWIDE-65⟧ THE WIDE-CEILING TWINS (this file)

Mechanical widening of the flat `hK` ceiling binders on the `L`-chain: the ceiling moves
INSIDE the internal `∀ M` as `≤ 170000000 * M`, so the raised lever `KlevF` can flow.
Statements and proofs are verbatim apart from that antecedent and the `_kwide` re-pointing.
The originals are untouched.
-/

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSum_chi_door_end'_L_gk_kwide`) —
`m4_hrowsSum_chi_door_end'_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_hrowsSum_chi_door_end'_L_gk_kwide (K : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            a (bfam j) c) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end'
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hKw hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L_gk_kwide K M Xd hM hKw hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L_gk K hM hXd1 hCp.le

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSlot_at_door_end'_L_gk_kwide`) —
`m4_hrowsSlot_at_door_end'_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_hrowsSlot_at_door_end'_L_gk_kwide (K : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s → DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        -- ⟦THE CARRIED A3 CAPSTONE FAMILY⟧ at the door pin `S ≡ 0`
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end'_L_gk_kwide K
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  -- ⟦THE DOOR INSTANCE'S OWN FRAME⟧
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have ha1 : ∀ n : ℕ, ‖winCutH (A + s) (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  have hslot := hrows q cU (winCutH (A + s) (doorCoeffU_L_gk K M)) bU ha1 hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hKw hD.Q2_le le_rfl hN4 hD.coefWS (fun n hn => winCutH_asupp hn) hD.reg hD.big hD.dom
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSum_chi_door_zero'_L_gk_kwide`) —
`m4_hrowsSum_chi_door_zero'_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_hrowsSum_chi_door_zero'_L_gk_kwide (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (q : ℕ) [NeZero q] (c : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          SeamCoefWS Xd (calP (AdoorL M) (s13GK K M) j) (calQK (AdoorL M) (s13GK K M) M j)
            (winCutH Xd (doorCoeffU_L_gk K M)) (bfam j) c) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
            ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        4 ≤ h → 0 < X → 0 ≤ Real.log X → X ≤ 4 * (Xd : ℝ) →
        ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        (∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ 8 * (0 : ℝ) ^ 2
              + (∫ t in (seamAnn X (2 * T) \ seamBall X (t₁ χ))
                  ∩ seamTtotG (chiBarCoeff q χ c) (calP (AdoorL M) (s13GK K M))
                      (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                      (mrAlpha (1 / 12)) 2,
                  ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
              + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) →
        ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
          TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T),
              ‖spoly N (chiBarCoeff q χ (winCutH Xd (doorCoeffU_L_gk K M))) t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_zero'
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp q _ c bfam hb1 hc1 N Xd M X h ε t₁ hM hKw hXdQ hNXd hN4 hcoefWS hQXd
    hXdbig hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have ha1 : ∀ n : ℕ, ‖winCutH Xd (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
    fun n => norm_winCutH_le
      (fun m => norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 m) n
  refine (hrows Cp hCp q c (winCutH Xd (doorCoeffU_L_gk K M)) bfam ha1 hb1 hc1 N Xd
    (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h (1 / 12) ε t₁ (fun _ => 0)
    (calFrameK_doorH1_at_L_gk_kwide K M Xd hM hKw hXdQ) hNXd hN4 hcoefWS
    (fun n hn => winCutH_asupp hn)
    (fun i hi => blockLive_winCutH_doorCoeffU_L_gk K M Xd hi) hQXd hXdbig hh4 hX0 hL0 hX4Xd hQ1h
    hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd'_le_a2Mrow'_L_gk K hM hXd1 hCp

/-- ⟦WIDE CEILING TWIN⟧ (`m4_hrowsSlot_at_door_zero'_L_gk_kwide`) —
`m4_hrowsSlot_at_door_zero'_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_hrowsSlot_at_door_zero'_L_gk_kwide (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ)
        (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
                * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ a2Mrow'_L_gk K Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, hCt, hrows⟩ := m4_hrowsSum_chi_door_zero'_L_gk_kwide K
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap H L q j A s hb χ T hT hTX2 hTgate hTll
  have hq : 0 < q := hb.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  haveI : NeZero q := ⟨hq.ne'⟩
  have hD := hbase H L q j A s hb
  have hAs : 0 < A + s := lt_of_lt_of_le hA (Nat.le_add_right A s)
  have hAsR : (0 : ℝ) < (((A + s : ℕ)) : ℝ) := by exact_mod_cast hAs
  have hN4 : (((2 * (A + s) : ℕ)) : ℝ) ≤ 4 * (((A + s : ℕ)) : ℝ) := by push_cast; linarith
  have hslot := hrows Cp hCp q cU bU hb1 hc1
    (2 * (A + s)) (A + s) M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (ε (A + s)) (t₁ q)
    hM hKw hD.Q2_le le_rfl hN4 hD.coefWS hD.reg hD.big
    hD.h_four hAsR (log_natCast_nonneg' (A + s)) (by linarith) hD.Q1_le_h
    (by simpa only [chiBarCoeff_doorRowDatum_L_gk] using hcap H L q j A s hb) χ T
    hT hTX2 hTgate hTll
  simpa only [chiBarCoeff_doorRowDatum_L_gk] using hslot

/-- ⟦WIDE CEILING TWIN⟧ (`m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk_kwide`) —
`m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_end'_L_gk_kwide (K : ℕ) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowEndBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end'_L_gk_kwide K
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hKw hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) hband hpool henv

/-- ⟦WIDE CEILING TWIN⟧ (`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk_kwide`) —
`m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk` with the flat ceiling moved inside the `∀ M`.
The widened antecedent is `K ≤ 170000000 * M`; statement and proof otherwise verbatim, off
the `_kwide` upstream. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_pool_zero'_L_gk_kwide (K : ℕ) :
    ∃ Ct : ℝ, 0 < Ct ∧
      ∀ (Cp : ℝ), 0 < Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε π₀ : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → K ≤ 170000000 * M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorFuseFrame_pool'_L_gk K M (A + s) j Ct Cp (ε (A + s)) (π₀ (A + s))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          DoorRowZeroBase_L_gk K M (A + s) j cU bU) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) (t₁ q χ))
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (AdoorL M) (s13GK K M))
                        (calQK (AdoorL M) (s13GK K M) M) (calH (H1doorL M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_L_gk K χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s)))) →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_L_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s)))
                  (M₀ (A + s))) →
        (∀ A : ℕ, 0 ≤ π₀ A) →
        (∀ H j A s : ℕ, doorRowFloorL M ≤ j →
          arcDen 12 H * a2DoorGrade_pool_L_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ)
              (C₁ (A + s)) (M₀ (A + s)) (π₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  obtain ⟨Ct, hCt, hslot⟩ := m4_hrowsSlot_at_door_zero'_L_gk_kwide K
  refine ⟨Ct, hCt, ?_⟩
  intro Cp hCp R M C₁ M₀ ε π₀ RSbig cU bU t₁ hM hKw hb1 hc1 hframe hbase hcap hband hpool henv
  exact m4_chiSummedFreeRow_of_doorAssembly_pool'_L_gk K (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM hframe
    (hslot Cp hCp.le R M ε cU bU t₁ hM hKw hb1 hc1 hbase hcap) hband hpool henv
