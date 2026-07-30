/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Assembly

/-!
# ⟦D5 — THE ENDPOINT-WALL REPAIR ON THE `χ` PAGE⟧ (`M4RowsChiEnd`)

`docs/blueprints/flags.md` ⟦ASSEMBLY-WIRE lands⟧, section ⟦THE WALL = D5⟧.  The `q = 1` side
made this repair on 2026-07-29 (`ThmA2Rows.a2Rows_of_capfree3_end`,
`CapFreeArm3.seam_row_number_capfree3_end`); this file brings the `χ` page to parity.

## The wall, and the cut that dissolves it

`M4RowsChi.m4_hrowsSum_chi_door` cannot fill the `hrows` slot of
`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`: it carries the **GLOBAL, unconditional**
Lemma-12 factorization together with `hasupp` (the datum pinned to `[X_d, 2X_d]`), and
`M4Assembly.doorRows_global_hcoef_kills_block` proves that pair KILLS the block whenever the
block spans a ratio `> 2` — which the door's ladder does.  The door's own datum is
window-cut (`M4DoorRow.winCutH`), so it is exactly the datum the wall refutes.

The repair is the one the `q = 1` side made: re-cut the chain at
`SeamRowWindowed.SeamCoefWS` — the STRICT RELATIVIZED pair law, asking the factorization only
on `X_d < p·m ≤ 2X_d`.  A half-open cut inhabits it with **no endpoint obligation whatever**
(`M4Band.memSCoeff_seamCoefWS_band_gen`), and the endpoint mass it releases is paid on the
ROW, inside `M4RowMR.lemma12RowsMR_end`'s fused `p²` filter.

**This file is a NOT a wrapper over the `_all_chi` forms.**  Three shapes differ and each
difference is paid in the open:

* **the pair law** — landed: the global unconditional `hcoef`; here: `SeamCoefWS`, the
  strict relativized law;
* **the Lemma-12 exit** — landed: `TLegPreamble.lemma12_on_TsetG`, THREE rows, `hwin`
  carried; here: `M4RowMR.lemma12_on_TsetG_mr_windowed_end`, FOUR rows, `hwin` GONE;
* **the row prefactor** — landed: `480·(T/X_d+1)`, weighed at `1440`; here:
  `960·(T/X_d+1)`, weighed at `2880`.

⟦THE `hwin` BINDER DISAPPEARS⟧  The four-row MR exit is `hwin`-free (⟦WALL 1⟧,
`CapFreeArm3.lean:811`), so the whole window binder
`c p · b j m ≠ 0 → X_d ≤ p·m ≤ 2X_d` — which `M4RowsChi` §6/§7/§9/§11 all carry — is
**absent from every statement here**.  The `_end` chain asks strictly less of its datum than
the landed one on that axis, and strictly less on the endpoint.

⟦THE PREFACTOR IS NOT ABSORBED⟧  `960` is the four-row exit's honest price
(`M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end`), so the `3`-gate gives `2880` where the
three-row chain gives `1440`.  `m4MrowChiEnd` carries `2880` in the open, and
`m4MrowChiEnd_le_a2Mrow` spends HALF of ⟦AMENDMENT G⟧'s `×4` cover (`2880 ≤ 5760`) — exactly
what the `q = 1` side spends at `ThmA2Rows.a2_term3_weigh_mr`.  **`ThmA2.a2Mrow` does not
move**, so the frozen five-summand interface and the assembly's binders are untouched.

## Contents

* §1 the STRICT pair law lifts to the twist (`chiBarCoeff_seamCoefWS`);
* §2 the FOUR-row Lemma-12 price at twisted data (`sum_lemma12RowsMR_priced_chi_end`);
* §3 the per-`χ` seam row AS A NUMBER, at the strict/fused row
  (`m4_rowChi_number_of_capstone_end`);
* §4 the weighting: `m4MrowChiEnd`, and `m4_rowChi_weighed_end`;
* §5 **the deliverable**: `m4_hrowsSum_chi_end`, the `hrowsSum` slot per character;
* §6 the door instance: `m4MrowChiEnd_le_a2Mrow` and `m4_hrowsSum_chi_door_end`;
* §7 **THE FUSE**: `m4_hrowsSlot_at_door_end` meets `m4_chiSummedFreeRow_of_doorAssembly`'s
  `hrows` binder, and `m4_chiSummedFreeRow_of_doorAssembly_end` is ⟦item 11⟧ with that slot
  GONE from the residue.

⟦PURELY ADDITIVE⟧  No landed declaration is touched; every statement here is a new theorem
beside its landed twin.  The frozen shapes — `ThmA2.a2Mrow`, `SeamRowWindowed.SeamCoefWS`,
`M4ChiSummed.M4ChiSummedFreeRow`, `M4Assembly.SocketBase`/`DoorFuseFrame` and the assembly's
five binders — are met, never adjusted.

⟦THE FOUR LOG SCALES⟧ stay apart exactly as in `M4RowsChi`: `log(qT_ann)` (the graded razor),
`log(5T_ann+1)` (the socket gates), `L ≥ log(qT_ann)` (the `𝒯_L` kill) and `log X` (the
grades); `√(log X_d)` is the FIFTH and is never identified with `√(log X)`.  `arcDen 12 H` is
never evaluated and never conflated with a `log X` scale.

Source pins (D5): `docs/blueprints/flags.md` ⟦ASSEMBLY-WIRE lands⟧ (2026-07-30) ⟦THE WALL⟧;
⟦ENDPOINT-ROW-SCOPE⟧ / ⟦ENDPOINT-REF⟧; MR arXiv **v4** (`1501.04585v4`) §8.1–§8.3.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE STRICT PAIR LAW LIFTS TO THE TWIST

`HybridMoments.chiBar_hcoef` is the GLOBAL law's lift; the strict law's lift is the same one
line, because the two extra antecedents `X_d < p·m` and `p·m ≤ 2X_d` are conditions on the
INDEX and the twist does not touch indices. -/

/-- **THE STRICT PAIR LAW SURVIVES THE TWIST** (`chiBarCoeff_seamCoefWS`).
`SeamRowWindowed.SeamCoefWS` at `(a, b, c)` gives it at `(χ̄a, χ̄b, χ̄c)`: `χ̄(pm) = χ̄(p)χ̄(m)`
is unconditional (`HybridMoments.conj_chi_natCast_mul`) and the two window antecedents are
index conditions the twist is blind to. -/
theorem chiBarCoeff_seamCoefWS {q : ℕ} (χ : DirichletCharacter ℂ q) {Xd P Q : ℕ}
    {a b c : ℕ → ℂ} (h : SeamCoefWS Xd P Q a b c) :
    SeamCoefWS Xd P Q (chiBarCoeff q χ a) (chiBarCoeff q χ b) (chiBarCoeff q χ c) := by
  intro p m hp hPp hpQ hpm hlo hhi
  rw [chiBarCoeff_apply, chiBarCoeff_apply, chiBarCoeff_apply,
    conj_chi_natCast_mul q χ p m, h p m hp hPp hpQ hpm hlo hhi]
  ring

/-- The levelled form: the door/K-ladder family of strict laws lifts level by level. -/
theorem chiBarCoeff_seamCoefWS_levels {q : ℕ} (χ : DirichletCharacter ℂ q) {A G M Jb Xd : ℕ}
    {a c : ℕ → ℂ} {bfam : ℕ → ℕ → ℂ}
    (h : ∀ j ∈ Finset.Icc 1 Jb, SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c) :
    ∀ j ∈ Finset.Icc 1 Jb, SeamCoefWS Xd (calP A G j) (calQK A G M j)
      (chiBarCoeff q χ a) (chiBarCoeff q χ (bfam j)) (chiBarCoeff q χ c) :=
  fun j hj => chiBarCoeff_seamCoefWS χ (h j hj)

/-- **⟦IRON RULE 1: THIS PAGE ASKS STRICTLY LESS⟧** (`seamCoefWS_levels_of_global`).  The
GLOBAL, unconditional Lemma-12 factorization family that `M4RowsChi.m4_hrowsSum_chi_door`
carries IMPLIES the strict relativized family this page carries
(`SeamRowWindowed.seamCoefW_of_global` then `seamCoefWS_of_seamCoefW`).  So every model of
the landed page's hypothesis is a model of this one's, and nothing here is a strengthening.

⟦AND THE CONVERSE FAILS FOR A REASON⟧  at a datum supported in `[X_d, 2X_d]` on a block of
ratio `> 2`, the global family is CONTRADICTORY
(`M4Assembly.doorRows_global_hcoef_kills_block`), while the strict one simply never asserts
the offending instance — its antecedent `p·m ≤ 2X_d` fails there.  That asymmetry is the
whole content of the D5 repair. -/
theorem seamCoefWS_levels_of_global {A G M Jb Xd : ℕ} {a c : ℕ → ℂ} {bfam : ℕ → ℕ → ℂ}
    (hcoef : ∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
      ¬ p ∣ m → a (p * m) = bfam j m * c p) :
    ∀ j ∈ Finset.Icc 1 Jb, SeamCoefWS Xd (calP A G j) (calQK A G M j) a (bfam j) c :=
  fun j hj => seamCoefWS_of_seamCoefW (seamCoefW_of_global (hcoef j hj))

/-! ## §2 — THE FOUR-ROW LEMMA-12 PRICE AT TWISTED DATA

`M4RowMR.sum_lemma12RowsMR_priced_calibratedK2_end` at `(χ̄a, χ̄b, χ̄c)`.  The pricer is
fully datum-generic and carries **no factorization hypothesis at all** — the fused `p²`
coefficient `ramP2coeffEndMR` is an object, not a contract — so the lift is the four
coefficient hypotheses of `TLegChi` §1 and nothing else.

⟦WHAT MOVES AGAINST `M4RowsChi` §6⟧ the prefactor is `960` (four rows) not `480` (three),
and `hwin` is GONE.  Both are stated, neither is absorbed. -/

/-- **⟦D5⟧ THE FOUR-ROW LEMMA-12 ROW SUM, PRICED AT TWISTED DATA**
(`sum_lemma12RowsMR_priced_chi_end`).  `M4RowsChi.sum_lemma12Rows_priced_chi`'s strict/fused
twin: the rows are `M4RowMR.lemma12RowsMR_end`, the prefactor is `960`, and the window binder
`hwin` is absent.  The hypotheses are stated on the UNTWISTED sequences and the bound is the
`q = 1` one VERBATIM. -/
theorem sum_lemma12RowsMR_priced_chi_end :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a c : ℕ → ℂ) (b : ℕ → ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → 2 ≤ H1 →
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
                    + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hK2⟩ := sum_lemma12RowsMR_priced_calibratedK2_end
  refine ⟨C, hC, ?_⟩
  intro q _ χ A G M Jb N Xd H1 T a c b hA hG hM hXd hN hT hH1 hN4 hreg hbig hdom ha hb hc
    hasupp
  exact hK2 A G M Jb N Xd H1 T (chiBarCoeff q χ a) (fun j => chiBarCoeff q χ (b j))
    (chiBarCoeff q χ c) hA hG hM hXd hN hT hH1 hN4 hreg hbig hdom
    (norm_chiBarCoeff_le_one χ ha) (chiBarCoeff_bfam_le_one χ hb)
    (chiBarCoeff_cseq_le_one χ hc) (chiBarCoeff_dyadic_supp χ hasupp)

/-! ## §3 — THE PER-`χ` SEAM ROW AS A NUMBER, AT THE STRICT/FUSED ROW

`M4RowsChi` §7's twin.  There the composition is `TLegChi.TLeg_feeds_capstone_chi` (which
instantiates its row slot at the THREE-row `hwin`-carrying exit) fused with §6; here it is
`TLegExit.TLeg_feeds_capstone_gen` — the row slot LEFT OPEN — instantiated at the FOUR-row
strict/fused exit `M4RowMR.lemma12_on_TsetG_mr_windowed_end` and fused with §2.  This is
exactly the route `CapFreeArm3.seam_row_calibratedK_nocap3_end` takes at `q = 1`; the only
`χ`-specific content is §1's lift and `TLegChi` §1's three.

⟦THE CAPSTONE ROW IS CARRIED, exactly as at `q = 1` and in `M4RowsChi` §7⟧  Its supplier is
`M4RowsChi.m4_rowChi_capstone`, whose own residue is that theorem's docstring; the two gate
families are reconciled at the STATION, which is where the corpus has always reconciled them
(`TLegExit` H-4, `TLegChi` §3, `M4RowsChi` §7).  Nothing here manufactures their simultaneous
satisfiability.

⟦THE SIX RECONCILIATION GATES⟧ (R1) `log Q_Jb ≤ √(log X_d)`, (R2) `100 ≤ √(log X_d)`,
(R3) `N ≤ 4X_d`, (R4) the per-level error-domination product, (R5) `‖aₙ‖ ≤ 1`,
(R6) `aₙ ≠ 0 → X_d ≤ n ≤ 2X_d` — character-FREE, verbatim. -/

set_option maxHeartbeats 1000000 in
-- Same cause as `M4RowsChi.m4_rowChi_number_of_capstone` and
-- `CapFreeArm3.seam_row_calibratedK_nocap3_end`: the leg's exit and the pricer's exit are
-- elaborated against one another at full ladder width.
/-- **⟦D5⟧ THE PER-`χ` SEAM ROW AS A NUMBER, STRICT/FUSED**
(`m4_rowChi_number_of_capstone_end`).  `M4RowsChi.m4_rowChi_number_of_capstone` re-cut at
`SeamRowWindowed.SeamCoefWS`:

  `∫_{Ann} ‖spoly N (χ̄a)‖² ≤ 8S² + [level-1 term] + 1536·Ct·e³·(2T_ann/X_d+240)/P₁`
  `                                 + 960·(T_ann/X_d+1)·(Σ_j rows + Cp·2/M)`
  `                              + 2·(T_ann/X + 1)·(log X)^{−θ₂₉₃+ε}`.

⟦THE TWO SHAPE CHANGES, IN THE OPEN⟧ the pair-law binder is the STRICT relativized one
(the factorization asked only on `X_d < p·m ≤ 2X_d`), and the window binder `hwin` is GONE —
the four-row exit does not read it.  The price is the prefactor `960` in place of `480`.

`Ct` and `Cp` are the `q = 1` universal constants (`TLegExit.TLeg_feeds_capstone_gen`'s and
`M4RowMR`'s): bound outside `q` and outside `χ`. -/
theorem m4_rowChi_number_of_capstone_end :
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
                            + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                            + 1 / (Xd : ℝ)))
                      + Cp * (2 / (M : ℝ))))
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Ct, hCt, hfeed⟩ := TLeg_feeds_capstone_gen
  obtain ⟨Cp, hCp, hprice⟩ := sum_lemma12RowsMR_priced_chi_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X Tann t₁ S η ε hF hT0 hNXd hN4
    hcoefWS hasupp hQXd hXdbig hdom hcap
  -- ⟦THE FRAME'S OWN READS⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hA1 : 1 ≤ A := le_trans (by norm_num) hF.A_floor
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
  -- ⟦THE PRICE OF `Σ_j lemma12RowsMR_end`, AT THE TWISTED DATUM⟧
  have hreg : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    refine le_trans (Real.log_le_log ?_ ?_) hQXd
    · have h : (0 : ℕ) < calQK A G M j := lt_of_lt_of_le Nat.zero_lt_one (one_le_calQK A G M j)
      exact_mod_cast h
    · exact_mod_cast calQK_mono A hG1 hj.2
  have hK2 := hprice q χ A G M Jb N Xd H1 Tann a c bfam hA1 hG1 hM1 hXd1 hNXd hT0 hF.H1_two
    hN4 hreg hXdbig hdom ha1 hb1 hc1 hasupp
  exact hleg.trans
    (add_le_add (add_le_add le_rfl (add_le_add le_rfl hK2)) le_rfl)

/-! ## §4 — THE WEIGHTING: the `T`-family collapses to ONE number

`M4RowsChi` §8's page at the strict/fused row.  The weight `w = (X/h)/T` kills the four
`T`-linear factors at the same four numerals — `9`, `244`, `3`, `3/2` — because those are
CHARACTER-BLIND and ROW-BLIND arithmetic; what moves is only the Lemma-12 summand's
prefactor, `960·3 = 2880` where the three-row chain has `480·3 = 1440`.

`M4RowsChi`'s own helpers are `private` to that file (as `ThmA2Rows`' are to theirs), so the
page is re-derived here at its own names.  No content is re-proved: the arithmetic is
`(X/h)/X_d ≤ 4/h` and `w ≤ 1`, twice each. -/

/-- **THE FOUR NUMERALS** (`d5_weight_gates`) — `M4RowsChi.m4_weight_gates` at its own name
(that one is `private`).  With `w := (X/h)/T`: `0 ≤ w ≤ 1`, and the four `T`-linear factors
of the seam row weigh in at `9`, `244`, `3`, `3/2`. -/
private lemma d5_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
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

/-- The row's five summands weigh independently. -/
private lemma d5_row_weigh {w Sq A B C D s a b c d : ℝ}
    (hS : w * Sq ≤ s) (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (Sq + (A + B + C) + D) ≤ s + (a + b + c) + d := by
  have h : w * (Sq + (A + B + C) + D) = w * Sq + (w * A + w * B + w * C) + w * D := by ring
  rw [h]; linarith

/-- The level-1 summand: the weight meets the `T`-carrying factor at the `9`-gate. -/
private lemma d5_level1_weigh {w Hq Lq R Pq Br : ℝ}
    (hHL : 0 ≤ 2 * (Hq * Lq + 1)) (hPq : 0 ≤ Pq) (hBr : 0 ≤ Br) (hR9 : w * R ≤ 9) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 18 * (Hq * Lq + 1) * Pq * Br := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = (2 * (Hq * Lq + 1) * Pq * Br) * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 2 * (Hq * Lq + 1) * Pq * Br := by positivity
  rw [hid]
  nlinarith [mul_le_mul_of_nonneg_left hR9 h0]

/-- The `Ct`-summand, at the `244`-gate: `1536·244 = 374784`. -/
private lemma d5_term2_weigh {w Ct R Y : ℝ} (hCt : 0 ≤ Ct) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Ct * Real.exp 3 * R * Y) ≤ 374784 * Ct * Real.exp 3 * Y := by
  have hid : w * (1536 * Ct * Real.exp 3 * R * Y)
      = 1536 * Ct * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Ct * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- **⟦THE ONE NUMERAL THAT MOVES⟧** the Lemma-12 summand at the FOUR-row exit, weighed at the
`3`-gate: `960·3 = 2880` in place of the three-row chain's `480·3 = 1440`.  The debit is
carried in `m4MrowChiEnd`, never absorbed. -/
private lemma d5_term3_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3) :
    w * (960 * R * Z) ≤ 2880 * Z := by
  have hid : w * (960 * R * Z) = 960 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 960) hZ)]

/-- The `𝒰`-leg summand, at the `3/2`-gate: `2·(3/2) = 3`. -/
private lemma d5_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]

/-- The ball leg passes the weighting untouched (`w ≤ 1`). -/
private lemma d5_ball_weigh {w S : ℝ} (hw1 : w ≤ 1) :
    w * (8 * S ^ 2) ≤ 8 * S ^ 2 := by nlinarith [sq_nonneg S]

/-- **THE PER-`χ` ROW NUMBER, STRICT/FUSED** (`m4MrowChiEnd`).  `M4RowsChi.m4MrowChi` with
the Lemma-12 summand at the FOUR-row exit's weighed prefactor `2880` (that chain's `1440`
prices THREE rows).  Every other summand is byte-identical. -/
def m4MrowChiEnd (Ct Cp : ℝ) (A G M Jb Xd : ℕ) (H1 η X ε S : ℝ) : ℝ :=
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
                + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                + 1 / (Xd : ℝ)))
            + Cp * (2 / (M : ℝ))))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-- The Lemma-12 row sum is a sum of nonnegative terms (`1 ≤ X_d`, `2 ≤ H₁`, `1 ≤ P_j`). -/
private lemma d5_rowsSum_nonneg {A G Jb Xd : ℕ} {H1 : ℝ} (hXd : 1 ≤ Xd) (hH1 : 2 ≤ H1) :
    (0 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 Jb,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ)) := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH H1 j := by rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP A G j : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G j := by simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

set_option maxHeartbeats 400000 in
-- The `hrow` hypothesis is the full number-row; matching it summand by summand against
-- `m4MrowChiEnd` costs more than the default budget in elaboration alone.
/-- **THE WEIGHTED ROW, STRICT/FUSED** (`m4_rowChi_weighed_end`).  §3's number-row at
`T_ann = 2T`, weighted by `(X/h)/T`, lands inside the `T`-FREE constant `m4MrowChiEnd` — the
`hrowsSum` slot's shape. -/
theorem m4_rowChi_weighed_end {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {a : ℕ → ℂ}
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
                        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
                        + 1 / (Xd : ℝ)))
                  + Cp * (2 / (M : ℝ))))
        + 2 * ((2 * T / X + 1) * (Real.log X) ^ (-theta293 + ε))) :
    X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (chiBarCoeff q χ a) t‖ ^ 2)
      ≤ m4MrowChiEnd Ct Cp A G M Jb Xd H1 η X ε S := by
  have hQ10 : (0 : ℝ) ≤ ((calQK A G M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    d5_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
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
        + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP A G j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5_rowsSum_nonneg (A := A) (G := G) (Jb := Jb) (Xd := Xd) (H1 := H1) hXd1 hH1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) := Real.rpow_nonneg hL0 _
  unfold m4MrowChiEnd
  exact d5_row_weigh (d5_ball_weigh hw1)
    (d5_level1_weigh hHL0 hPq0 hBr0 hg9)
    (d5_term2_weigh hCt hY0 hg244) (d5_term3_weigh hRS0 hg3) (d5_term4_weigh hZ0 hg32)

/-! ## §5 — THE DELIVERABLE: the `hrowsSum` slot, per character, STRICT/FUSED

§3 at `T_ann = 2T` composed with §4, quantified over the height family.  The statement's
shape is `ThmA2ChiSummed.thm_a2_spine_chiSummed`'s `hrowsSum` binder BYTE FOR BYTE, at the
datum `a χ := chiBarCoeff q χ a` and the row constant `Mrow χ := m4MrowChiEnd … (S χ)`.

⟦THE RESIDUE, ENUMERATED⟧ (the PORT-AUDIT law: no under-counted list)
1. **the carried A3 capstone family** `hcap` — supplied by `M4RowsChi.m4_rowChi_capstone` at
   `T_ann = 2T`, whose own residue is that theorem's docstring (the graded razor's gates at
   `(q, 2T)`, the socket floor `T₀ ≤ 2T` + G1–G4, the co-factor binder `Rbd` with its grade —
   supplier landed in `RbdSupply` —, the `𝒯_S` budget `KS`, Lemma 12's `χ`-summed error row
   `E`, and the carried ball binder `hSup` at the per-`χ` centre `t₁ χ` and sup `S χ`;
   vacuous at `t₁ ≡ 0`, `S ≡ 0` by `CapFreeArm.ball_leg_vacuous_at_zero`, which is the wire
   `M4Assembly.m4_hSup_door_at_zero` takes);
2. **the `𝒯`-side frame** — `CalFrameK η H₁ A G M Jb X_d`, the STRICT pair law of `a` with
   its two `1`-bounds and its dyadic support pin, and `2X_d ≤ N`;
3. **the reconciliation gates** (R1)–(R6) of `SeamNumber`, character-free;
4. **the weighting frame** — `4 ≤ h`, `0 < X`, `0 ≤ log X`, `X ≤ 4X_d`, `Q₁ ≤ h`.

⟦WHAT IS NOT IN THE LIST⟧ the window binder `hwin` — `M4RowsChi.m4_hrowsSum_chi` carries it,
this page does not. -/

/-- **⟦THE D5 DELIVERABLE⟧ THE PER-`χ` ROW FAMILY, STRICT/FUSED** (`m4_hrowsSum_chi_end`).
For every character and every height in the seam family,

  `(X/h)/T · ∫_{Ann(X,2T)} ‖spoly N (χ̄a) t‖² ≤ m4MrowChiEnd Ct Cp A G M Jb X_d H₁ η X ε (S χ)`,

the `hrowsSum` slot of `thm_a2_spine_chiSummed` / `thm_a2'_of_rows_chiSummed`, with the
pair-law binder at `SeamRowWindowed.SeamCoefWS` and `hwin` gone. -/
theorem m4_hrowsSum_chi_end :
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
            ≤ m4MrowChiEnd Ct Cp A G M Jb Xd H1 η X ε (S χ) := by
  obtain ⟨Ct, Cp, hCt, hCp, hnum⟩ := m4_rowChi_number_of_capstone_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X h η ε t₁ S hF hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK A G M Jb) hF.Q_le_Xd
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hrow := hnum q χ c a bfam ha1 hb1 hc1 N Xd A G M Jb H1 X (2 * T) (t₁ χ) (S χ) η ε
    hF (by linarith) hNXd hN4 hcoefWS hasupp hQXd hXdbig hdom
    (hcap χ T hT hTX2 hTgate hTll)
  exact m4_rowChi_weighed_end hXd1 hF.H1_two hF.eta_pos hF.eta_lt hCt.le hCp.le hF.one_le_M
    hh4 hX0 hL0 hX4Xd hQ1h hT hrow

/-! ## §6 — THE DOOR INSTANCE: `m4MrowChiEnd` INSIDE `a2Mrow`

`M4RowsChi` §11 at the strict/fused row.  The only summand that moves is the Lemma-12 one:
`2880` against `a2Mrow`'s `5760`, i.e. ⟦AMENDMENT G⟧'s `×4` cover of `1440` spent HALF — the
same half the `q = 1` side spends at `ThmA2Rows.a2_term3_weigh_mr`.  **The interface numeral
does not move**, so `ThmA2.a2Mrow` and the whole frozen five-summand interface are untouched
and `thm_a2'_of_rows_chiSummed`'s slot is met in its own genre. -/

/-- **THE DOOR BRIDGE, STRICT/FUSED** (`m4MrowChiEnd_le_a2Mrow`).  At the door family and the
vacuous ball, the per-`χ` strict/fused row number sits inside the frozen interface's
`a2Mrow`; the Lemma-12 summand is weighed at `2880 ≤ 5760`. -/
theorem m4MrowChiEnd_le_a2Mrow {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd Ct Cp (Adoor M) (3072 * M) M 2 Xd (H1door M) (1 / 12) X ε 0
      ≤ a2Mrow Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1door M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            / ((calP (Adoor M) (3072 * M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5_rowsSum_nonneg (A := Adoor M) (G := 3072 * M) (Jb := 2) (Xd := Xd)
      (H1 := H1door M) hXd (H1door_two hM)]
  unfold m4MrowChiEnd a2Mrow a2Level1 a2RowsSum
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

/-- **⟦THE D5 DELIVERABLE AT THE DOOR⟧ THE `a2Mrow`-GENRE ROW FAMILY, STRICT/FUSED**
(`m4_hrowsSum_chi_door_end`).  §5 at the door family and the vacuous ball, landed inside the
FROZEN interface's row constant: this is `thm_a2'_of_rows_chiSummed`'s `hrowsSum` slot at the
constant families `Cs χ := Ct`, `Ccc χ := Cp`, `ε χ := ε`.

**This is `M4RowsChi.m4_hrowsSum_chi_door`'s successor**: same conclusion, same frame, with
the GLOBAL `hcoef` that `M4Assembly.doorRows_global_hcoef_kills_block` refutes replaced by the
STRICT relativized pair law, and the window binder `hwin` dropped.  The door's own datum is
window-cut, which is precisely where the relativized law lives and the global one dies. -/
theorem m4_hrowsSum_chi_door_end :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (Adoor M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW⟧ in place of the refuted global `hcoef`
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
            ≤ a2Mrow Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (Adoor M) (3072 * M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (Adoor M) (3072 * M) M 2 (H1door M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at M Xd hM hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow hM hXd1 hCp.le

/-! ## §7 — ⟦THE FUSE⟧: the assembly's `hrows` slot, MET and DISCHARGED

`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly` carries five binders; `hrows` is the one its
header records as unfillable from the D2 door page (⟦THE WALL⟧).  §6's successor fills it.

The datum reconciliation is `M4Assembly.chiBarCoeff_doorRowDatum`: the assembly speaks the
door's row datum as `winCutH X_d (doorChiCoeff χ M)`, §6 speaks it as `chiBarCoeff q χ a` at
`a := winCutH X_d (doorCoeffU M)`, and the two are the SAME function — the `χ̄`-twist commutes
with both the sieve indicator and the half-open cut.  So the plug is a rewrite along one
proved equation, not a re-statement of either shape.

⟦WHAT THE FUSE COSTS, AND WHAT IT REMOVES⟧  It removes the assembly's `hrows` binder outright.
It adds, per base, `DoorRowEndBase` — the strict pair law and the `q = 1` chain's own
`X_d`-side reconciliation gates — plus the carried A3 capstone family, whose supplier is
`M4RowsChi.m4_rowChi_capstone`.  **The strict pair law is inhabitable at the door datum**
(`M4Band.doorChiCoeff_seamCoefWS_at_door_H` is the twisted witness of exactly this shape,
with `ha0`/`hend` gone), whereas the global one is refuted there by
`M4Assembly.doorRows_global_hcoef_kills_block`.  That asymmetry is the whole content of D5. -/

/-- **THE PER-BASE GATE BUNDLE OF THE DOOR ROW SUPPLIER** (`DoorRowEndBase`) — exactly what
`m4_hrowsSum_chi_door_end` asks at ONE socket base `X_d` and window index `j`, at the door
instance `N = 2X_d`, `X = X_d`, `h = 2^j`, datum `winCutH X_d (doorCoeffU M)`.

Field by field these are the `q = 1` chain's own `X_d`-side gates; nothing is absorbed and
nothing is weakened.  `coefWS` is ⟦THE REPAIR⟧: the STRICT relativized pair law
(`SeamRowWindowed.SeamCoefWS`) where the landed page carried the global contract. -/
structure DoorRowEndBase (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`, which is also `CalFrameK`'s at the door family. -/
  Q2_le : calQK (Adoor M) (3072 * M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (Adoor M) (3072 * M) i) (calQK (Adoor M) (3072 * M) M i)
      (winCutH Xd (doorCoeffU M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R4) the per-level error-domination product. -/
  dom : ∀ i ∈ Finset.Icc 1 2,
    ((Nat.sqrt Xd : ℝ) + 1)
        * ∏ p ∈ primeBand (calP (Adoor M) (3072 * M) i)
              (calQK (Adoor M) (3072 * M) M i), (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log ((calP (Adoor M) (3072 * M) i : ℕ) : ℝ)
          / Real.log ((calQK (Adoor M) (3072 * M) M i : ℕ) : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j` (`DoorFuseFrame.h_four`'s twin). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

/-- **⟦THE SLOT, MET⟧** (`m4_hrowsSlot_at_door_end`).  The statement below is
`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s `hrows` binder VERBATIM at
`Cs ≡ Ct`, `Ccc ≡ Cp` — the compile is the certificate of the byte-fit.  Supplied by §6
through the datum bridge `M4Assembly.chiBarCoeff_doorRowDatum`.

`cU`, `bU` are the door's UNTWISTED Ramaré data (the twist is applied by the chain, not by
the consumer); `t₁` is the per-modulus ball-centre family the carried capstone speaks at. -/
theorem m4_hrowsSlot_at_door_end :
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
              ≤ a2Mrow Ct Cp M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)) := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_door_end
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

/-- **⟦A4 — ITEM 11, WITH THE `hrows` SLOT GONE⟧**
(`m4_chiSummedFreeRow_of_doorAssembly_end`).  `M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`
instantiated at §7's supplier: `M4ChiSummed.M4ChiSummedFreeRow` — ⟦item 11⟧ of
`m4_second_road` — at the door grade

  `RS j H = if doorRowFloor M ≤ j then RSbig j H else 4·arcDen 12 H`,

from the named gates alone, **with `hrows` no longer among them**.

⟦THE RESIDUE, AFTER THE FUSE⟧ (the PORT-AUDIT law)
* `hM` — `1 ≤ M`;
* `hb1`, `hc1` — the two `1`-bounds on the door's untwisted Ramaré data;
* `hframe` — `M4Assembly.DoorFuseFrame` at every base (eleven fields), unchanged;
* `hbase` — `DoorRowEndBase` at every base: the STRICT pair law plus the `q = 1` chain's own
  `X_d`-side reconciliation gates and the two weighting-frame numerals.  **This is what
  replaced `hrows`**;
* `hcap` — the carried A3 capstone family at the door pin `S ≡ 0`; supplier
  `M4RowsChi.m4_rowChi_capstone` (its own residue is that theorem's docstring);
* `hband` — the `T₀`-band per character, discharged by
  `M4T0DatumDischarge.m4_hT0band_at_door_discharged` under its own named gates;
* `henv` — THE ARITHMETIC, `arcDen 12 H · a2DoorGrade … ≤ RSbig j H`, still the only thing
  the assembly leaves open (the `φ(q) ≤ q ≤ arcDen 12 H` ledger IN THE OPEN).

Nothing else survives; in particular the assembly's `hrows` binder does not appear. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_end :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ ε : ℕ → ℝ) (RSbig : ℕ → ℕ → ℝ)
        (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (t₁ : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
        1 ≤ M → (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
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
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s))) →
        (∀ H j A s : ℕ, doorRowFloor M ≤ j →
          arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
              (M₀ (A + s))
            ≤ RSbig j H) →
        M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  obtain ⟨Ct, Cp, hCt, hCp, hslot⟩ := m4_hrowsSlot_at_door_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro R M C₁ M₀ ε RSbig cU bU t₁ hM hb1 hc1 hframe hbase hcap hband henv
  exact m4_chiSummedFreeRow_of_doorAssembly (Cs := fun _ => Ct) (Ccc := fun _ => Cp)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) hM hframe
    (hslot R M ε cU bU t₁ hM hb1 hc1 hbase hcap) hband henv

end Salt.MR
