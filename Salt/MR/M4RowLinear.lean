/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Gauss
import Salt.MR.M4T0Discharge
import Salt.MR.M4ChiSocketWire
import Salt.MR.M4RowsChi
import Salt.MR.M4T0DatumDischarge
import Salt.MR.M4Join
import Salt.MR.M4CapWire
import Salt.MR.M4SecondRoad
import Salt.MR.M4WaveLinear

/-!
# `M4RowLinear` — THE ROW / `T₀` LAYER at the LINEAR door (`AdoorL M = 2^36·M`)

⟦LADDER-L, lane G2, layer 1⟧  ⟦COMPOSE-FLAT-2⟧ kernelized `flat_landed_ladder_break`: the
road and the fuse read the door a SECOND time, through the LADDER
`calP (Adoor M) (s13GK K M)` — a copy the register's re-cut (⟦LINEAR-PAGE⟧) missed.  This
page and its two successors (`M4RowAssemblyLinear`, `M4RowSpineLinear`) carry the `_L` twin
family of the ROW/`T₀`/ASSEMBLY layer at `AdoorL M = 2^36·M`, with the `G`-slot unchanged
(`3072·M`, resp. `s13GK K M`).

Purely ADDITIVE: no landed declaration moves.  Every twin below is a RESTATEMENT of its
landed original with the landed body replayed — the analytic chain under the door is
`(A,G)`-parametric, so the anchor never leaves its symbol slot and the proofs transcribe.
The seed is `M4WaveLinear.doorChiCoeff_L`(`_gk`) (G1's root); what is minted here is the
free-base row datum (`M4ChiFreeRowMeanSq_L`, `chiFreeRowSq_L`), the door row's carried
register (`DoorRowCarried_L`, `DoorRowCarriedT0_L`), the `T₀`-band arm and its discharge, the
`Σ_χ` socket above the linear door's floor (`M4ChiSummedFreeRowBig_L`), and the Gauss/strata
bridge.

⟦THE ONE NEW HYPOTHESIS⟧ `1 ≤ M`, wherever the landed proof used the UNCONDITIONAL anchor
floor `2^36 ≤ Adoor M` (`AdoorL 0 = 0`).  Every door consumer already carries it.

⟦THE CROSS-LANE SCAFFOLD, §0⟧  The wave-closure exits here
(`m4_wave_structurally_closed_L`, `m4_wave_closed_T0_discharged_L`, the second road, the
arithmetic-page exit and their `_gk` twins) consume the M4-wave closure spine
(`M4Close`/`M4WaveClosed`/`M4Maximal`/`M4ClassPrice`/`M4Join`/`M4BridgeBlock`/
`M4BridgeCover`/`M4BridgePhase`/`M4CapWire`/`RamErrWS`/`S13FramesB`/`M4SocketDischarge`/
`M4DoorRow`), whose own `_L` twins sit at a LOWER import depth than this page and belong to a
DIFFERENT lane of the ⟦LADDER-L⟧ wave.  §0 carries them inside the sub-namespace
`Salt.MR.G2Scaffold` — public (so the two successor pages can consume them) but namespaced,
so nothing here can collide with the lower lane's own public twins.  When that lane lands,
`G2Scaffold` becomes redundant and deletes verbatim: every declaration in it is a
byte-for-byte restatement at `AdoorL` with the landed proof replayed.

Source pins: `docs/blueprints/flags.md` ⟦COMPOSE-FLAT-2⟧, ⟦H1-ANCHOR⟧, ⟦FLAT-REF⟧
amendment 0; `Salt.MR.DoorLinear` (`W0`), `Salt.MR.ArithPageLinear` (⟦LINEAR-PAGE⟧),
`Salt.MR.M4WaveLinear` (⟦LADDER-L⟧ G1).
-/

noncomputable section

open scoped BigOperators
open Complex MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

-- ⟦THE LINEAR ANCHOR'S ELABORATION COST⟧ every twin below reads `AdoorL M = 2^36·M` where its
-- landed original reads `Adoor M = 2^36·(⌊log₂ M⌋ + 1)`, so each `calP`/`calQK` occurrence
-- carries a longer term and the register-against-register instantiations (~40–100 conjuncts,
-- no tactic search anywhere) cost proportionally more `whnf` steps.  The limit is raised
-- file-wide rather than per-declaration because the cost is uniform across the page.
set_option maxHeartbeats 4000000

/-! ## §0a — in-lane roots hoisted for the scaffold -/

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

/-- **THE FREE-BASE ROW MEAN SQUARE, PER CHARACTER** (`chiFreeRowSq_L χ M j X`) — the door's
sieved, χ-twisted, UN-PHASED datum in `ThmA2.thm_a2'_of_rows`' own currency at the dyadic
window length `2^j` and the scale `X`, with the capstone's two pins `X_d = X`, `N = 2X_d`.

It is `M4CoprimeSupply.M4ChiFreeRowMeanSq`'s body at `X := A + s`, named so the `Σ_χ` socket
can quantify over it. -/
def chiFreeRowSq_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M j X : ℕ) : ℝ :=
  1 / ((X : ℕ) : ℝ)
    * (∫ y in ((X : ℕ) : ℝ)..(2 * ((X : ℕ) : ℝ)),
        ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
            * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * X) ((X : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖ ^ 2)

/-- **THE UNTWISTED DOOR DATUM** (`doorCoeffU_L M = 1_𝒮·λ`) — `doorChiCoeff_L`'s untwisted twin at
the door's own K-family.  `liouvilleC`, never `lam` (the ⟦lam collision⟧: the row's sum runs
over integers). -/
def doorCoeffU_L (M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC

/-- **⟦THE SLOT FUSE + THE SHAPE CLOSE⟧** (`m4_chiFreeRowSq_sum_at_door_L`).

`ThmA2ChiSummed.thm_a2'_of_rows_chiSummed` instantiated at the door datum

  `N := 2X_d`,  `X := X_d`,  `h := 2^j`,  `a χ := winCutH X_d (doorChiCoeff_L χ M)`,

whose LEFT-hand side is `∑_χ chiFreeRowSq_L χ M j X_d` — `M4ChiSummed.chiFreeRowSq`'s body at
the same two pins, with the cut invisible to the row's short sum
(`M4DoorRow.shortSum_winCutH_seamS0`) — and whose RIGHT-hand side collapses to
`φ(q)·a2DoorGrade_L M X_d 2^j C₁ M₀`.

⟦THE GATE LIST — nothing absorbed⟧
* `hM` — `1 ≤ M`, the door's parameter;
* `hX`, `hX3` — `e ≤ X_d` and `3 ≤ X_d` (the frozen interface's scale pins);
* `hh4`, `hhX` — `4 ≤ 2^j` (the AS-2 MVT guard) and Lemma 14's window frame
  `2^j ≤ X_d·(log X_d)^{−1/5}`;
* `hTann`, `hceil` — `TannGate X_d (2X_d/2^j)` and `5 ≤ loglog(2X_d/2^j)`, the `h`-ceiling;
* `hrowsSum` — the weighted seam-row family at `a2Mrow_L Cs Ccc M X_d X_d ε`, PER CHARACTER, in
  `thm_a2'_of_rows_chiSummed_L`'s own frozen binder.  **CARRIED, NOT DISCHARGED** — see the
  header's ⟦THE WALL⟧: `M4RowsChi.m4_hrowsSum_chi_door` meets this shape but its own `hcoef`
  is the global factorization contract `ThmA2Spine.seam_coef_contract_absurd` refutes at a
  window-cut datum, and the door's datum is window-cut;
* `hT0bandSum` — the `T₀`-band at `t0BandB X_d (cfbC₁ X_d C₁) M₀`, PER CHARACTER.  This slot
  IS discharged by `M4T0DatumDischarge.m4_hT0band_at_door_discharged` (whose datum is
  literally `winCutH X_d (doorChiCoeff_L χ M)`), under its own named gates: `400 ≤ X_d`,
  `x₀ ≤ X_d`, `16 ≤ X_d`, `q ≤ (log X_d)^{10}`, the covering window `[P, Q]`, the three
  Rankin/mass gates per `k ∈ [X_d, 2X_d]`, the grade fit and `hErr`;
* `hgP1`, `hgRows`, `hL4096` — the three GRADING gates of the frozen interface;
* `hεwin` — the `𝒰`-leg's exponent room `0 ≤ ε ≤ θ₂₉₃ − 1/500`.

The datum-side binders `ha`/`hsupp` are NOT hypotheses: they are discharged in-file from
`M4DoorRow.doorRow_ha1` / `doorRow_hsupp0_L`, and `hN2` is the pin `N = 2X_d` itself. -/
theorem m4_chiFreeRowSq_sum_at_door_L {q : ℕ} [NeZero q] {M Xd j : ℕ} {Cs Ccc C₁ M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)) (hX3 : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ))
    (hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ))
    (hhX : ((2 ^ j : ℕ) : ℝ)
      ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ)))
    (hTann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
    (hceil : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ ((Xd : ℕ) : ℝ) →
      TannGate ((Xd : ℕ) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      ((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
          * (∫ t in seamAnn ((Xd : ℕ) : ℝ) (2 * T),
              ‖spoly (2 * Xd) (winCutH Xd (doorChiCoeff_L χ M)) t‖ ^ 2)
        ≤ a2Mrow_L Cs Ccc M Xd ((Xd : ℕ) : ℝ) ε)
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 ((Xd : ℕ) : ℝ)))..(seamT0 ((Xd : ℕ) : ℝ)),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) t‖ ^ 2)
        ≤ t0BandB ((Xd : ℕ) : ℝ) (cfbC₁ ((Xd : ℕ) : ℝ) C₁) M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j Xd
      ≤ (q.totient : ℝ) * a2DoorGrade_L M ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hbase := thm_a2'_of_rows_chiSummed_L (q := q) (N := 2 * Xd) (M := M) (Xd := Xd)
    (a := fun χ => winCutH Xd (doorChiCoeff_L χ M)) (X := ((Xd : ℕ) : ℝ))
    (h := ((2 ^ j : ℕ) : ℝ)) (Cs := fun _ => Cs) (Ccc := fun _ => Ccc)
    (C₁' := fun _ => cfbC₁ ((Xd : ℕ) : ℝ) C₁) (M₀ := fun _ => M₀) (ε := fun _ => ε)
    hM hX hX3 hh4 hhX (fun χ n => doorRow_ha1_L χ M Xd n)
    (fun χ n hn => doorRow_hsupp0_L χ M Xd n hn) hN2 hTann hceil hrowsSum hT0bandSum
    (fun _ => hgP1) (fun _ => hgRows) (fun _ => hεwin) hL4096
  simp only [shortSum_winCutH_seamS0] at hbase
  refine le_trans hbase (le_of_eq ?_)
  rw [a2_sum_const_chars]
  unfold a2DoorGrade_L
  ring

/-- **THE FUSE FRAME AT ONE BASE** (`DoorFuseFrame_L`) — the CHARACTER-BLIND half of
`m4_chiFreeRowSq_sum_at_door_L`'s gate list, field by field.  Nothing is absorbed: each field is
one of `ThmA2.thm_a2'_of_rows`' own in-statement side conditions, read at `X := X_d`,
`h := 2^j`. -/
structure DoorFuseFrame_L (M Xd j : ℕ) (Cs Ccc ε : ℝ) : Prop where
  /-- `e ≤ X_d` — the frozen interface's lower scale pin. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j` — the AS-2 MVT guard (NOT `3`). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame `2^j ≤ X_d·(log X_d)^{−1/5}`. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- `TannGate X_d (2X_d/2^j)` — the annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- `5 ≤ loglog(2X_d/2^j)` — the `h`-ceiling, MRT's bare `h ≥ 3` replaced honestly. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))
  /-- The first GRADING gate, on the `𝒯`-leg constant `Cs`. -/
  gP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The second GRADING gate, on the Lemma-12 row sum and the density constant `Ccc`. -/
  gRows : 5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ)))
    ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
  /-- The `𝒰`-leg's exponent room, lower end. -/
  eps_lo : 0 ≤ ε
  /-- The `𝒰`-leg's exponent room, upper end (`θ₂₉₃ = 1/(32(3e+1))`). -/
  eps_hi : ε ≤ theta293 - 1 / 500
  /-- The third GRADING gate. -/
  L4096 : 4096 ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)

/-- **THE DOOR BRIDGE, STRICT/FUSED** (`m4MrowChiEnd_le_a2Mrow_L`).  At the door family and the
vacuous ball, the per-`χ` strict/fused row number sits inside the frozen interface's
`a2Mrow_L`; the Lemma-12 summand is weighed at `2880 ≤ 5760`. -/
theorem m4MrowChiEnd_le_a2Mrow_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChiEnd Ct Cp (AdoorL M) (3072 * M) M 2 Xd (H1doorL M) (1 / 12) X ε 0
      ≤ a2Mrow_L Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_L (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [d5_rowsSum_nonneg (A := AdoorL M) (G := 3072 * M) (Jb := 2) (Xd := Xd)
      (H1 := H1doorL M) hXd (H1door_two_L hM)]
  unfold m4MrowChiEnd a2Mrow_L a2Level1_L a2RowsSum_L
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

/-- **⟦THE D5 DELIVERABLE AT THE DOOR⟧ THE `a2Mrow_L`-GENRE ROW FAMILY, STRICT/FUSED**
(`m4_hrowsSum_chi_door_end_L`).  §5 at the door family and the vacuous ball, landed inside the
FROZEN interface's row constant: this is `thm_a2'_of_rows_chiSummed_L`'s `hrowsSum` slot at the
constant families `Cs χ := Ct`, `Ccc χ := Cp`, `ε χ := ε`.

**This is `M4RowsChi.m4_hrowsSum_chi_door`'s successor**: same conclusion, same frame, with
the GLOBAL `hcoef` that `M4Assembly.doorRows_global_hcoef_kills_block` refutes replaced by the
STRICT relativized pair law, and the window binder `hwin` dropped.  The door's own datum is
window-cut, which is precisely where the relativized law lives and the global one dies. -/
theorem m4_hrowsSum_chi_door_end_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        -- ⟦THE STRICT RELATIVIZED PAIR LAW⟧ in place of the refuted global `hcoef`
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
            ≤ a2Mrow_L Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi_end
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoefWS hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (3072 * M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L M Xd hM hXdQ) hNXd hN4 hcoefWS
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChiEnd_le_a2Mrow_L hM hXd1 hCp.le

/-- **THE PER-BASE GATE BUNDLE OF THE DOOR ROW SUPPLIER** (`DoorRowEndBase_L`) — exactly what
`m4_hrowsSum_chi_door_end_L` asks at ONE socket base `X_d` and window index `j`, at the door
instance `N = 2X_d`, `X = X_d`, `h = 2^j`, datum `winCutH X_d (doorCoeffU_L M)`.

Field by field these are the `q = 1` chain's own `X_d`-side gates; nothing is absorbed and
nothing is weakened.  `coefWS` is ⟦THE REPAIR⟧: the STRICT relativized pair law
(`SeamRowWindowed.SeamCoefWS`) where the landed page carried the global contract. -/
structure DoorRowEndBase_L (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`, which is also `CalFrameK`'s at the door family. -/
  Q2_le : calQK (AdoorL M) (3072 * M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (AdoorL M) (3072 * M) i) (calQK (AdoorL M) (3072 * M) M i)
      (winCutH Xd (doorCoeffU_L M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R4) the per-level error-domination product. -/
  dom : ∀ i ∈ Finset.Icc 1 2,
    ((Nat.sqrt Xd : ℝ) + 1)
        * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
              (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
          / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j` (`DoorFuseFrame_L.h_four`'s twin). -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

/-- ⟦THE CANONICAL M4Assembly-SIDE MINT⟧ **THE UNTWISTED DOOR DATUM AT THE G-LEVER**
(`doorCoeffU_L_gk`) — `M4Assembly.doorCoeffU` (:171) at `G := s13GK K M`.

It is minted HERE, not in `M4Assembly`, and `M4Assembly`'s own `§GK` header ratifies that:
the two files are SIBLINGS, so a second declaration there would collide at their first common
descendant.  This mint and the two bridges below are the canonical ones. -/
def doorCoeffU_L_gk (K M : ℕ) : ℕ → ℂ :=
  memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC

/-- **THE PER-BASE GATE BUNDLE, DENSITY-FREE** (`DoorRowZeroBase_L`) — `DoorRowEndBase_L` with
the field `dom` REMOVED.  Six fields:

1. `Q2_le` — the door's cutoff `Q₂ ≤ X_d` (also `CalFrameK`'s at the door family);
2. `coefWS` — the STRICT relativized pair law `SeamRowWindowed.SeamCoefWS`, level by level;
3. `reg` — (R1) `log Q₂ ≤ √(log X_d)`;
4. `big` — (R2) `100 ≤ √(log X_d)`;
5. `h_four` — the weighting frame's floor `4 ≤ 2^j`;
6. `Q1_le_h` — the weighting frame's `Q₁ ≤ 2^j`.

⟦THE BONUS⟧ `DoorRowEndBase_L.dom` — the per-level error-domination product
`(√X_d + 1)·∏_{p∈[P_i,Q_i]}(1 + 3/p) ≤ X_d·(log P_i/log Q_i)` — is GONE.  It existed only to
feed `TypicalPrice.blockfree_sum_le`, whose row is now identically zero, and it was the field
that imposed an `X_d ≳ (M i²)⁸` floor on every socket base.  `reg` and `big` are NOT dropped:
they gate ⟦AMENDMENT 1⟧'s endpoint absorption in the `p²` row, which survives. -/
structure DoorRowZeroBase_L (M Xd j : ℕ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) : Prop where
  /-- The door's cutoff `Q₂ ≤ X_d`. -/
  Q2_le : calQK (AdoorL M) (3072 * M) M 2 ≤ Xd
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law, level by level. -/
  coefWS : ∀ i ∈ Finset.Icc 1 2,
    SeamCoefWS Xd (calP (AdoorL M) (3072 * M) i) (calQK (AdoorL M) (3072 * M) M i)
      (winCutH Xd (doorCoeffU_L M)) (bU i) cU
  /-- (R1) `log Q₂ ≤ √(log X_d)`. -/
  reg : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- (R2) `100 ≤ √(log X_d)`. -/
  big : (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))
  /-- The weighting frame's floor `4 ≤ 2^j`. -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- The weighting frame's `Q₁ ≤ h` at `h = 2^j`. -/
  Q1_le_h : ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)

namespace G2Scaffold

/-- **THE PER-BASE GATE BUNDLE OF THE `T₀`-BAND SUPPLIER** (`DoorBandBase_L`) — exactly what
`M4T0DatumDischarge.m4_hT0band_at_door_discharged` asks at ONE socket base `X_d = A + s` and
modulus `q`, after the door's covering window and the pin `N = 2X_d` are supplied.

`x₀` and `C'` are the supplier's own existential witnesses (see the header, ⟦WHAT THE
`∃C' ∃x₀` IS⟧); `Aexp` is its saving parameter, carried symbolically. -/
structure DoorBandBase_L (x₀ : ℕ) (C' Aexp : ℝ) (M Xd q : ℕ) (C₁ M₀ : ℝ) : Prop where
  /-- `400 ≤ X_d` — the supplier's base floor (it also gives `16 ≤ X_d`). -/
  X400 : (400 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `1 ≤ C₁` — the band constant's normalisation. -/
  C₁_one : (1 : ℝ) ≤ C₁
  /-- `x₀ ≤ X_d` — the supplier's threshold, VISIBLE. -/
  x₀_le : x₀ ≤ Xd
  /-- `q ≤ (log X_d)^{10}` — the BASE-side conductor gate.  **Not** `SocketBaseL`'s
  `q ≤ arcDen 12 H`, which is an `H`-side gate; the two are independent. -/
  qfit : (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
  /-- The half-range mass gate, on `[X_d, 2X_d]`. -/
  gHalf : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    16 * Aexp * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)
  /-- The `O(1)`-range Rankin gate at the door's upper cutoff `Q₂`. -/
  gO1 : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    8 * Aexp * Real.log (Real.log (k : ℝ))
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.log (k : ℝ)
  /-- The covering-window gate at `[P₁, Q₂]`. -/
  gWin : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    Real.exp (2 * Real.exp 1
        * (Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ))
            - Real.log (Real.log ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) + 25))
      ≤ (Real.log (k : ℝ)) ^ Aexp
  /-- The grade fit `8C' ≤ (log X_d)^{A − 1/2 + 1/1000}`. -/
  grade : 8 * C' ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- `cfb_t0band_supply_of_sup`'s own `hErr`. -/
  err : 4 * Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
    ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)

/-- **THE PER-BASE GATE BUNDLE OF THE `T₀`-BAND SUPPLIER, AT THE G-LEVER**
(`DoorBandBase_L_gk`).  NINE fields, names UNCHANGED and in this order: `X400`, `C₁_one`,
`x₀_le`, `qfit`, `gHalf`, `gO1`, `gWin`, `grade`, `err`.  Only `gO1` and `gWin` read the
ladder, and both read it at LEVEL 2 (`𝒬₂`) and level 1 (`𝒫₁`) — so `gWin`'s `log log 𝒫₁` leg
is K-INVARIANT and only its `𝒬₂` leg moves. -/
structure DoorBandBase_L_gk (K : ℕ) (x₀ : ℕ) (C' Aexp : ℝ) (M Xd q : ℕ) (C₁ M₀ : ℝ) : Prop where
  /-- `400 ≤ X_d` — the supplier's base floor (it also gives `16 ≤ X_d`). -/
  X400 : (400 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `1 ≤ C₁` — the band constant's normalisation. -/
  C₁_one : (1 : ℝ) ≤ C₁
  /-- `x₀ ≤ X_d` — the supplier's threshold, VISIBLE. -/
  x₀_le : x₀ ≤ Xd
  /-- `q ≤ (log X_d)^{10}` — the BASE-side conductor gate.  **Not** `SocketBaseL`'s
  `q ≤ arcDen 12 H`, which is an `H`-side gate; the two are independent. -/
  qfit : (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
  /-- The half-range mass gate, on `[X_d, 2X_d]`. -/
  gHalf : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    16 * Aexp * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)
  /-- The `O(1)`-range Rankin gate at the door's upper cutoff `Q₂`. -/
  gO1 : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    8 * Aexp * Real.log (Real.log (k : ℝ))
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.log (k : ℝ)
  /-- The covering-window gate at `[P₁, Q₂]`. -/
  gWin : ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
    Real.exp (2 * Real.exp 1
        * (Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ))
            - Real.log (Real.log ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) + 25))
      ≤ (Real.log (k : ℝ)) ^ Aexp
  /-- The grade fit `8C' ≤ (log X_d)^{A − 1/2 + 1/1000}`. -/
  grade : 8 * C' ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- `cfb_t0band_supply_of_sup`'s own `hErr`. -/
  err : 4 * Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
    ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)

structure DoorCapBase_L (Cq cs T₀ Kq Ks : ℝ) (M Nd q Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
    (Tann VJ V Lr η εd εr Rbd CR KS E EP2 : ℝ) : Prop where
  -- ⟦(A) THE GRADED RAZOR FAMILY AT `(q, Tann)`⟧
  /-- `1 ≤ Jb` — the razor's designated level is a level. -/
  Jb_lo : 1 ≤ Jb
  /-- `Jb ≤ J = 2` — the door's partition has two levels. -/
  Jb_hi : Jb ≤ 2
  /-- `2 ≤ H_Jb` at the door's calibrated `H`-family. -/
  Hseq_two : 2 ≤ calH (H1doorL M) Jb
  /-- `0 ≤ α_Jb` at the door's `mrAlpha (1/12)`. -/
  alpha_nonneg : 0 ≤ mrAlpha (1 / 12) Jb
  /-- `1 ≤ T_ann`. -/
  Tann_one : 1 ≤ Tann
  /-- `1 < q·T_ann` — the razor's modulus-height scale. -/
  qTann_one : 1 < (q : ℝ) * Tann
  /-- `3 ≤ P_Jb`. -/
  P_three : 3 ≤ calP (AdoorL M) (3072 * M) Jb
  /-- `P_Jb ≤ Q_Jb`. -/
  PQ : calP (AdoorL M) (3072 * M) Jb ≤ calQK (AdoorL M) (3072 * M) M Jb
  /-- `Q_Jb ≤ q·T_ann` — the block top under the razor's scale. -/
  QTann : ((calQK (AdoorL M) (3072 * M) M Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- `30 ≤ log(q·T_ann)/log Q_Jb` — ⟦MR (21)⟧'s κ-gate at the designated level. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (AdoorL M) (3072 * M) M Jb : ℕ) : ℝ)
  /-- `5 ≤ loglog(q·T_ann)`. -/
  loglog5 : 5 ≤ Real.log (Real.log ((q : ℝ) * Tann))
  /-- The razor's `V_J` cap over the designated block's `H·log p` grid. -/
  VJ_bound : ∀ v ∈ ramI (calH (H1doorL M) Jb) (calP (AdoorL M) (3072 * M) Jb)
      (calQK (AdoorL M) (3072 * M) M Jb),
    Real.exp (mrAlpha (1 / 12) Jb * (v : ℝ) / calH (H1doorL M) Jb) ≤ VJ
  /-- `α_Jb ≤ 1/4 − η` — the razor's exponent room. -/
  alpha_eta : mrAlpha (1 / 12) Jb ≤ 1 / 4 - η
  /-- `2η ≤ 1`. -/
  eta_half : 2 * η ≤ 1
  /-- `T_ann ≤ X` — the annulus sits under the base. -/
  Tann_X : Tann ≤ ((Nd : ℕ) : ℝ)
  /-- `0 < X`. -/
  X_pos : (0 : ℝ) < ((Nd : ℕ) : ℝ)
  /-- ⟦THE CHARACTER DEBIT⟧ `q^{2α_Jb} ≤ X^{εd}` — spent inside the razor's budget. -/
  debit : (q : ℝ) ^ (2 * mrAlpha (1 / 12) Jb) ≤ ((Nd : ℕ) : ℝ) ^ εd
  /-- `0 < log X`. -/
  logX_pos : 0 < Real.log ((Nd : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — the modulus gate the `φ(q)` repayment is charged to. -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  /-- `1 ≤ V`. -/
  V_one : 1 ≤ V
  /-- `V⁻¹ ≤ (log X)^{−106}` — the level pin. -/
  V_inv : V⁻¹ ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-106 : ℝ)
  -- ⟦(B) THE PER-`(q, T)` SOCKET FLOOR⟧
  /-- `T₀ ≤ T_ann` — the capstone's own height floor. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1 — the VK strip constant against `loglog(5T+1)`. -/
  floor1 : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 2. -/
  floor2 : 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
    ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 3 — the `Kq` arm. -/
  floor3 : Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
    ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)
  /-- Floor gate 4 — the `Ks` arm. -/
  floor4 : (q : ℝ) ^ ((1 : ℝ) / 16)
    ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
  /-- `1 ≤ log(q·T_ann)`. -/
  logqT_one : 1 ≤ Real.log ((q : ℝ) * Tann)
  /-- `log(q·T_ann) ≤ L`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ Lr
  /-- `e ≤ L`. -/
  L_exp : Real.exp 1 ≤ Lr
  /-- `log V ≤ 100·log L`. -/
  logV_L : Real.log V ≤ 100 * Real.log Lr
  -- ⟦(C) THE `X`-SIDE FRAME⟧
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `e ≤ log X`. -/
  logX_exp : Real.exp 1 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `4 ≤ log X`. -/
  logX_four : 4 ≤ Real.log ((Nd : ℕ) : ℝ)
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `‖cf n‖ ≤ 1` — Lemma 12's prime-side coefficient. -/
  cf_one : ∀ n : ℕ, ‖cf n‖ ≤ 1
  /-- `P₈₃ X θ₂₉₃ ≤ P`. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- The co-factor range sits in `[1, Mr]` at every block. -/
  range : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd j ⊆ Finset.Icc 1 Mr
  /-- ⟦THE GRADED BUDGET⟧ `thinBundleGChi(q·T_ann)·X^{1−2η+εd} ≤ Mr`. -/
  budget : thinBundleGChi ((q : ℝ) * Tann) VJ (calH (H1doorL M) Jb)
      (calP (AdoorL M) (3072 * M) Jb) (calQK (AdoorL M) (3072 * M) M Jb)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * η + εd) ≤ (Mr : ℝ)
  /-- `H₈₃ ≤ j` on the grid. -/
  Hj : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ (j : ℝ)
  /-- `3 ≤ Q_base` on the grid. -/
  B3 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j
  /-- `Q_base ≤ q·T_ann` on the grid. -/
  BT : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ (q : ℝ) * Tann
  /-- The κ-gate on the grid. -/
  kappa30 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)
  /-- `Q_base ≤ T_ann^{10}` on the grid. -/
  BT10 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ Tann ^ 10
  /-- `log Q_base ≤ L` on the grid. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ Lr
  /-- The `cs`-gate on the grid. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * Lr * Lr ^ ((3 : ℝ) / 4) * (Real.log Lr) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧ (supplier §4a)
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧ `Rbd ≤ CR·(log X)^{−ρ₂₉₃}`. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧ `1728·Cq·CR² ≤ (log X)^{2θ₂₉₃}`. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` BINDER⟧ the co-factor polynomial is `≤ Rbd` off the door ball. -/
  Rbd_binder : ∀ χ : DirichletCharacter ℂ q,
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ∀ t ∈ seamAnn ((Nd : ℕ) : ℝ) Tann \ seamBall ((Nd : ℕ) : ℝ) 0,
      ‖ramR (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd
  -- ⟦(F) THE `𝒯_S` BUDGET AND LEMMA 12's ERROR ROW⟧ (suppliers §4b, §4c)
  /-- `0 ≤ KS`. -/
  KS_nonneg : 0 ≤ KS
  /-- ⟦THE `𝒯_S` BUDGET BINDER⟧ (supplier `USetPrice.KS_priced`, §4b). -/
  KS_binder : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    5128 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (Mr : ℝ) * (1 + Real.log (2 * Tann))
        * (∑ m ∈ Finset.Icc 1 Mr,
            ‖ramRcoeff (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ KS
  /-- ⟦THE `𝒯_S` GRADE GATE⟧ `32(log X)^{2+2θ}·KS ≤ (log X)^{−θ}`. -/
  KS_gate : 32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * KS
    ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
  /-- `0 ≤ εr` — the remainder absorption exponent. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}` — the absorption. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- Lemma 12's three rows collected into `E`. -/
  E_row : E ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293 + EP2)
  /-- ⟦LEMMA 12's `χ`-SUMMED ERROR ROW⟧ (conditional supplier §4c — see the header). -/
  E_binder : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
      ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
        (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L M))) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E

/-- `DoorCapBase_L` (:179), at the lever.  Seven of the fifty-eight fields read the ladder and
move — `P_three`, `PQ`, `QTann`, `kappa30Q`, `VJ_bound`, `budget`, `E_binder`; the other
fifty-one are VERBATIM (`calH (H1doorL M)` is LEVEL 1). -/
structure DoorCapBase_L_gk (K : ℕ) (Cq cs T₀ Kq Ks : ℝ) (M Nd q Xd P Q Mr Jb : ℕ)
    (b cf : ℕ → ℂ)
    (Tann VJ V Lr η εd εr Rbd CR KS E EP2 : ℝ) : Prop where
  -- ⟦(A) THE GRADED RAZOR FAMILY AT `(q, Tann)`⟧
  /-- `1 ≤ Jb`. -/
  Jb_lo : 1 ≤ Jb
  /-- `Jb ≤ J = 2`. -/
  Jb_hi : Jb ≤ 2
  /-- `2 ≤ H_Jb` at the door's calibrated `H`-family (LEVEL 1: K-invariant). -/
  Hseq_two : 2 ≤ calH (H1doorL M) Jb
  /-- `0 ≤ α_Jb`. -/
  alpha_nonneg : 0 ≤ mrAlpha (1 / 12) Jb
  /-- `1 ≤ T_ann`. -/
  Tann_one : 1 ≤ Tann
  /-- `1 < q·T_ann`. -/
  qTann_one : 1 < (q : ℝ) * Tann
  /-- `3 ≤ P_Jb`, at the lever. -/
  P_three : 3 ≤ calP (AdoorL M) (s13GK K M) Jb
  /-- `P_Jb ≤ Q_Jb`, at the lever. -/
  PQ : calP (AdoorL M) (s13GK K M) Jb ≤ calQK (AdoorL M) (s13GK K M) M Jb
  /-- `Q_Jb ≤ q·T_ann`, at the lever. -/
  QTann : ((calQK (AdoorL M) (s13GK K M) M Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- ⟦MR (21)⟧'s κ-gate at the designated level, at the lever. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (AdoorL M) (s13GK K M) M Jb : ℕ) : ℝ)
  /-- `5 ≤ loglog(q·T_ann)`. -/
  loglog5 : 5 ≤ Real.log (Real.log ((q : ℝ) * Tann))
  /-- The razor's `V_J` cap over the levered block's `H·log p` grid. -/
  VJ_bound : ∀ v ∈ ramI (calH (H1doorL M) Jb) (calP (AdoorL M) (s13GK K M) Jb)
      (calQK (AdoorL M) (s13GK K M) M Jb),
    Real.exp (mrAlpha (1 / 12) Jb * (v : ℝ) / calH (H1doorL M) Jb) ≤ VJ
  /-- `α_Jb ≤ 1/4 − η`. -/
  alpha_eta : mrAlpha (1 / 12) Jb ≤ 1 / 4 - η
  /-- `2η ≤ 1`. -/
  eta_half : 2 * η ≤ 1
  /-- `T_ann ≤ X`. -/
  Tann_X : Tann ≤ ((Nd : ℕ) : ℝ)
  /-- `0 < X`. -/
  X_pos : (0 : ℝ) < ((Nd : ℕ) : ℝ)
  /-- ⟦THE CHARACTER DEBIT⟧ `q^{2α_Jb} ≤ X^{εd}`. -/
  debit : (q : ℝ) ^ (2 * mrAlpha (1 / 12) Jb) ≤ ((Nd : ℕ) : ℝ) ^ εd
  /-- `0 < log X`. -/
  logX_pos : 0 < Real.log ((Nd : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}`. -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  /-- `1 ≤ V`. -/
  V_one : 1 ≤ V
  /-- `V⁻¹ ≤ (log X)^{−106}`. -/
  V_inv : V⁻¹ ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-106 : ℝ)
  -- ⟦(B) THE PER-`(q, T)` SOCKET FLOOR⟧
  /-- `T₀ ≤ T_ann`. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1. -/
  floor1 : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 2. -/
  floor2 : 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
    ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 3 — the `Kq` arm. -/
  floor3 : Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
    ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)
  /-- Floor gate 4 — the `Ks` arm. -/
  floor4 : (q : ℝ) ^ ((1 : ℝ) / 16)
    ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
  /-- `1 ≤ log(q·T_ann)`. -/
  logqT_one : 1 ≤ Real.log ((q : ℝ) * Tann)
  /-- `log(q·T_ann) ≤ L`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ Lr
  /-- `e ≤ L`. -/
  L_exp : Real.exp 1 ≤ Lr
  /-- `log V ≤ 100·log L`. -/
  logV_L : Real.log V ≤ 100 * Real.log Lr
  -- ⟦(C) THE `X`-SIDE FRAME⟧
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `e ≤ log X`. -/
  logX_exp : Real.exp 1 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `4 ≤ log X`. -/
  logX_four : 4 ≤ Real.log ((Nd : ℕ) : ℝ)
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `‖cf n‖ ≤ 1`. -/
  cf_one : ∀ n : ℕ, ‖cf n‖ ≤ 1
  /-- `P₈₃ X θ₂₉₃ ≤ P`. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- The co-factor range sits in `[1, Mr]` at every block. -/
  range : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd j ⊆ Finset.Icc 1 Mr
  /-- ⟦THE GRADED BUDGET⟧ at the levered block. -/
  budget : thinBundleGChi ((q : ℝ) * Tann) VJ (calH (H1doorL M) Jb)
      (calP (AdoorL M) (s13GK K M) Jb) (calQK (AdoorL M) (s13GK K M) M Jb)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * η + εd) ≤ (Mr : ℝ)
  /-- `H₈₃ ≤ j` on the grid. -/
  Hj : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ (j : ℝ)
  /-- `3 ≤ Q_base` on the grid. -/
  B3 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j
  /-- `Q_base ≤ q·T_ann` on the grid. -/
  BT : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ (q : ℝ) * Tann
  /-- The κ-gate on the grid. -/
  kappa30 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)
  /-- `Q_base ≤ T_ann^{10}` on the grid. -/
  BT10 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ Tann ^ 10
  /-- `log Q_base ≤ L` on the grid. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ Lr
  /-- The `cs`-gate on the grid. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * Lr * Lr ^ ((3 : ℝ) / 4) * (Real.log Lr) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧ `Rbd ≤ CR·(log X)^{−ρ₂₉₃}`. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` BINDER⟧. -/
  Rbd_binder : ∀ χ : DirichletCharacter ℂ q,
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ∀ t ∈ seamAnn ((Nd : ℕ) : ℝ) Tann \ seamBall ((Nd : ℕ) : ℝ) 0,
      ‖ramR (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd
  -- ⟦(F) THE `𝒯_S` BUDGET AND LEMMA 12's ERROR ROW⟧
  /-- `0 ≤ KS`. -/
  KS_nonneg : 0 ≤ KS
  /-- ⟦THE `𝒯_S` BUDGET BINDER⟧. -/
  KS_binder : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    5128 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (Mr : ℝ) * (1 + Real.log (2 * Tann))
        * (∑ m ∈ Finset.Icc 1 Mr,
            ‖ramRcoeff (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ KS
  /-- ⟦THE `𝒯_S` GRADE GATE⟧. -/
  KS_gate : 32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * KS
    ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
  /-- `0 ≤ εr`. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}`. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- Lemma 12's three rows collected into `E`. -/
  E_row : E ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293 + EP2)
  /-- ⟦LEMMA 12's `χ`-SUMMED ERROR ROW⟧, at the levered datum. -/
  E_binder : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
      ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
        (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L_gk K M))) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E

/-- **⟦THE PER-BASE ERROR BUNDLE⟧** (`DoorCapErrWS_L`).  Everything `m4_capE_at_door_L` needs, as
ONE structure — the shape the S11 spine instantiates alongside `DoorCapBase_L`.

⟦THE ANALYTIC FIELD IS SHARED, NOT NEW⟧ `coefWS` is `DoorRowZeroBase_L.coefWS` at the door's
level-`i` block: any model of the row bundle supplies it at `P := calP (AdoorL M) (3072M) i`,
`Q := calQK (AdoorL M) (3072M) M i`, `b := bU i`, `cf := cU`.  The other nine fields are
arithmetic on `(N_d, P, H₈₃)` plus the coprime-tail mass and the `E` slack. -/
structure DoorCapErrWS_L (M Nd q Xd P Q : ℕ) (b cf : ℕ → ℂ) (Tann E Mtail : ℝ) : Prop where
  /-- ⟦THE PIN⟧ the ram-block dyadic parameter IS the socket base (the datum's own window). -/
  Xd_eq : Xd = Nd
  /-- `1 ≤ N_d`. -/
  Nd_one : 1 ≤ Nd
  /-- `2 ≤ H₈₃ X θ₂₉₃` — `DoorCapBase_L.H83_two`, verbatim. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `H₈₃ X θ₂₉₃ ≤ X` — `RamareMR.seam_rows_grade`'s standing window-vs-base hypothesis. -/
  H83_le : H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ)
  /-- `1 ≤ P`. -/
  P_one : 1 ≤ P
  /-- `0 ≤ T_ann`. -/
  Tann_nonneg : 0 ≤ Tann
  /-- `‖b m‖ ≤ 1` — the co-factor sequence is `1`-bounded. -/
  b_one : ∀ m, ‖b m‖ ≤ 1
  /-- `‖cf p‖ ≤ 1` — `DoorCapBase_L.cf_one`, verbatim. -/
  cf_one : ∀ p, ‖cf p‖ ≤ 1
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law at the door datum —
  `M4RowsChiZero.DoorRowZeroBase.coefWS`'s shape. -/
  coefWS : SeamCoefWS Xd P Q (winCutH Nd (doorCoeffU_L M)) b cf
  /-- ⟦R3a⟧ the coprime-tail (sieve-remainder) mass, priced not pinned. -/
  tail : ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
      ‖winCutH Nd (doorCoeffU_L M) n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail
  /-- `E` dominates the priced four-row bound (`ramErr_meanSq_all_chi_ws_priced` at the
  door's numerals). -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * Mtail) ≤ E

/-- `DoorCapErrWS_L` (:424), at the lever.  Two of the eleven fields move — `coefWS` and `tail`,
both at the levered datum `winCutH Nd (doorCoeffU_L_gk K M)`; the other nine are VERBATIM. -/
structure DoorCapErrWS_L_gk (K : ℕ) (M Nd q Xd P Q : ℕ) (b cf : ℕ → ℂ)
    (Tann E Mtail : ℝ) : Prop where
  /-- ⟦THE PIN⟧ the ram-block dyadic parameter IS the socket base. -/
  Xd_eq : Xd = Nd
  /-- `1 ≤ N_d`. -/
  Nd_one : 1 ≤ Nd
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `H₈₃ X θ₂₉₃ ≤ X`. -/
  H83_le : H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ)
  /-- `1 ≤ P`. -/
  P_one : 1 ≤ P
  /-- `0 ≤ T_ann`. -/
  Tann_nonneg : 0 ≤ Tann
  /-- `‖b m‖ ≤ 1`. -/
  b_one : ∀ m, ‖b m‖ ≤ 1
  /-- `‖cf p‖ ≤ 1`. -/
  cf_one : ∀ p, ‖cf p‖ ≤ 1
  /-- ⟦THE REPAIR⟧ the STRICT relativized pair law at the LEVERED door datum. -/
  coefWS : SeamCoefWS Xd P Q (winCutH Nd (doorCoeffU_L_gk K M)) b cf
  /-- ⟦R3a⟧ the coprime-tail mass at the levered datum, priced not pinned. -/
  tail : ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
      ‖winCutH Nd (doorCoeffU_L_gk K M) n‖ ^ 2 / (n : ℝ) ^ 2 ≤ Mtail
  /-- `E` dominates the priced four-row bound. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann
            + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * Mtail) ≤ E

/-- **THE PER-BLOCK MEAN SQUARE** — the shape bridges 1–4 deliver, one `doorLadder` block at
a time, uniformly over the admissible window range and over tight-major frequencies:

`∑_{n ∈ (X_{i+1}, X_i]} ‖∑_{n<m≤n+H} 1_𝒮(m)λ(m)e(αm)‖² ≤ B_blk(H)·H²·X_{i+1}`.

The right side is "grade × block content": `X_{i+1}` is the block bottom, which by the
ladder's fit (`doorLadder_top_le_two_mul`) is within a factor `2` of the block top and of the
block cardinality.  `H²` is the mean square's own normalisation (`thm_a2'_L`'s carrier is
`‖(1/h)·shortSum‖²`).  The blocks and the count `k` are the SAME ones `m4_door_glue` eats. -/
def M4BlockMeanSq_L (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          ‖absWindowSum (doorSievedCoeff_L M) H n α‖ ^ 2
        ≤ Bblk H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE PER-LADDER-BLOCK BLOCKED MEAN SQUARE.**  `M4Join.M4BlockMeanSqSup` at the blocked
integrand: the door ladder's block `(X_{i+1}, X_i]` against "block count × grade × ℓ² × block
bottom".

Two block notions meet here and must not be confused: the DOOR ladder's blocks (index `i < k`,
the harmonic cover of `(x/ω, x]`) and the DRIFT blocks (index `m < N`, the cut of the window
`(n, n+H]`).  They are independent; §5 records how the drift blocks sit inside the door
block's own doubled interval. -/
def M4BlockMeanSqBlk_L (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff_L M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE PER-LADDER-BLOCK BLOCKED MEAN SQUARE AT THE LEVER** — `M4BlockMeanSqBlk_L`
(:485). -/
def M4BlockMeanSqBlk_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    1 ≤ ℓ H q → ℓ H q ≤ H → (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ) →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
        ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2
            * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE PER-BLOCK MEAN SQUARE, AT B-2's CARRIER** (`M4BlockMeanSqSup_L`).
`M4BridgeCover.M4BlockMeanSq` with the two changes that define the sup route
(`M4BridgePhase.M4SievedDoorSqSup`'s own two):

* the frequency is the RATIONAL `b/q` with `0 < q ≤ arcDen 12 H`, not the tight-major `α`;
* the integrand is the sup over sub-window lengths `K ≤ H`, not the full window sum.

The blocks, the count `k` and the right-hand side (`grade × H² × block bottom`) are
`M4BlockMeanSq_L`'s, unchanged. -/
def M4BlockMeanSqSup_L (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE `q`-GRADED PER-BLOCK MEAN SQUARE** — `M4Join.M4BlockMeanSqSup` with the class
modulus carried in the grade, matching `M4BridgePhase.M4SievedDoorSqSup`'s re-cut.  This is
the predicate the class price naturally produces: its supplier's loss is `q` classes, and
demoting that before the socket's `1/q` meets it wastes a factor `q²`. -/
def M4BlockMeanSqSupQ_L (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE `q`-GRADED PER-BLOCK MEAN SQUARE AT THE LEVER** — `M4BlockMeanSqSupQ_L` (:336). -/
def M4BlockMeanSqSupQ_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- `M4BlockMeanSqSup_L` (:203), at the lever. -/
def M4BlockMeanSqSup_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ Bblk H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE PER-BLOCK MEAN SQUARE AT THE LEVER** — `M4BlockMeanSq_L` (:386). -/
def M4BlockMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bblk : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α →
    ∀ i < k,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          ‖absWindowSum (doorSievedCoeff_L_gk K M) H n α‖ ^ 2
        ≤ Bblk H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE SHIFTED FIXED-LENGTH DATUM** (`M4ChiShiftBlockMeanSq_L`) — the block mean square of
the sieved, χ-twisted window sums at the DYADIC lengths `2^j ≤ H` and at every shift `s ≤ H`
of the ladder block, LENGTH-GRADED: the grade is `F j H`, one per dyadic scale.  The shifts
are exactly the bases the dyadic pieces of a sub-window have; the grade is normalised by the
UNSHIFTED block bottom `X_{i+1}`, so the shift costs nothing in the currency. -/
def M4ChiShiftBlockMeanSq_L (R : ChowlaRegime) (M k : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1) + s) (doorLadder R.x H i + s),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE SHIFTED FIXED-LENGTH FAMILY AT THE LEVER** — `M4ChiShiftBlockMeanSq_L` (:776). -/
def M4ChiShiftBlockMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, ∀ s ≤ H,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1) + s) (doorLadder R.x H i + s),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE WAVE'S REMAINING INPUT** (`M4RowMeanSq_L`) — the mean square of the door's PHASED
sieved datum on one ladder block, in `ThmA2.thm_a2'_of_rows`' own currency.

The instantiation is forced, not chosen: at the block `(X_{i+1}, X_i]` the fits of
`M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` read `X := X_{i+1}` (`le_rfl`) and
`X_i + H ≤ 2X_{i+1}` (`doorLadder_fit`), and the index set is `seamS0 (2X_{i+1}) X_{i+1}` —
so `N = 2X_d`, `X_d = X`, which are exactly `M4MeanSq.m4_meansq_per_chi_gen`'s two pins.  The
window length `h` is the door's own `H`.

This predicate is the wave's ⟦RESIDUE⟧: see the module header for the two obstructions that
keep it from being discharged from `m4_meansq_per_chi_gen_L` today. -/
def M4RowMeanSq_L (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorCoeffPhase (doorSievedCoeff_L M) α)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

/-- **THE RE-CUT ROW INPUT** (`M4RowMeanSqUnphased_L`) — `M4Join.M4RowMeanSq` with the phase
gone: the same block, the same `thm_a2'_L` currency, the same seam index set, the same window
length, and the door's sieved datum carried BARE.

The `α`-quantifier and its `NearRatTight` premise are gone with the phase: after §1 there is
no frequency left in the integrand to quantify over. -/
def M4RowMeanSqUnphased_L (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorSievedCoeff_L M)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

/-- **THE RE-CUT ROW INPUT AT THE LEVER** — `M4RowMeanSqUnphased_L` (:863). -/
def M4RowMeanSqUnphased_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorSievedCoeff_L_gk K M)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

/-- `M4RowMeanSq_L` (:311), at the lever. -/
def M4RowMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (MS : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ, NearRatTight (arcDen 12 H) H α → ∀ i < k,
    1 / (doorLadder R.x H (i + 1) : ℝ)
        * (∫ y in (doorLadder R.x H (i + 1) : ℝ)..(2 * (doorLadder R.x H (i + 1) : ℝ)),
            ‖((1 / (H : ℝ) : ℝ) : ℂ)
                * shortSum (doorCoeffPhase (doorSievedCoeff_L_gk K M) α)
                    (seamS0 (2 * doorLadder R.x H (i + 1))
                      (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H

/-- **THE BLOCKED SOCKET** — ⟦THE ③×④ INTERFACE⟧, stated once.

`M4BridgePhase.M4SievedDoorSqSup`'s statement with three changes, and only these three:

* the integrand is the BLOCK SUM `blockSupSq` at cap `ℓ H q` and bases `n + m·ℓ H q`, not the
  single sup at cap `H`;
* the right-hand side is `Bblk H · N · ℓ²` — "block count × per-block grade × block length²" —
  instead of `Braw H · q² · H²`.  ⟦NO `q²`⟧ the blocked price carries no residue-class factor
  at all: the class machinery is wave ④'s, and lives in `Bblk`;
* three admissibility binders on `ℓ` are premises, so a supplier need only produce the bound
  at legal block lengths.

⟦THE `N²ℓ² = H²` CONTRACT⟧  `m4_sievedDoorSq_of_blk_L` composes this with the blocked drift's
own factor `(1 + 2π)²·N`, giving `(1 + 2π)²·Bblk H·(N·ℓ)²`; since `N·ℓ ≤ H + ℓ ≤ 2H` the
assembled price is `4·(1 + 2π)²·Bblk H·H²` (and exactly `(1+2π)²·Bblk H·H²` when `ℓ ∣ H`).
That identity is the whole reason the blocking is free.

The band transport is carried as the same premise, so the ⟦A2-5⟧ binder stays visible and is
never unfolded. -/
def M4SievedDoorSqBlk_L (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ) (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff_L M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- **THE BLOCKED SOCKET AT THE LEVER** — `M4SievedDoorSqBlk_L` (:369). -/
def M4SievedDoorSqBlk_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (ℓ : ℕ → ℕ → ℕ)
    (Bblk : ℕ → ℝ) : Prop :=
  M4BandTransport →
    ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ (b : ℤ) (q : ℕ), 0 < q →
      (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q → ℓ H q ≤ H →
      (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ) →
        (∫ n, blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ))
            ∂(logMeasure R.x R.ω))
          ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2

/-- **⟦THE PER-BASE GATE⟧** (`S13CapGate_L`).  Exactly the fields of `DoorCapErrWS_L` and
`DoorCapBase_L` that survive §2's pins, plus five supply-side inputs — 36 lines, against the
two bundles' 69.

Everything here is stated at the door's own numerals; nothing is absorbed, and every field
is either a bundle field VERBATIM, a strictly weaker reduction of one (`logqT_L` at the
pinned `Lr`; `budget` at the pinned `η`, `εd`, `VJ`; `KS_gate` at the pinned `KS`; `E_ge` at
the pinned `E` and `Mtail`), or one of the FIVE supply-side inputs the wires consume in place
of a harder field (`Rbd_socket` for `Rbd_binder`; `m0_two`/`m0_bot`/`Mr_sharp` for
`KS_binder`; `Q2_reg` — `DoorRowZeroBase_L.reg`, already carried by the spine's row bundle —
for §1's band gate).

⚠ `KS_gate` and `E_ge` are the pair flagged in the header's ⟦BAND-WIDTH TENSION⟧: they pull
`log Q/log P` in opposite directions.  This structure asserts nothing about their joint
satisfiability. -/
structure S13CapGate_L (Cq cs T₀ Kq Ks : ℝ) (M Nd q P Q Mr : ℕ) (m₀ : ℕ → ℕ)
    (Tann Rrad Rbd CR EP2 εr : ℝ) : Prop where
  -- ⟦THE SCALE FLOOR — the one line every discharged field reads⟧
  /-- `4 ≤ log X` — `DoorCapBase_L.logX_four` verbatim; `logX_pos` and `logX_exp` come off it. -/
  logX_four : 4 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `2 ≤ H₈₃ X θ₂₉₃` — `DoorCapBase_L.H83_two` = `DoorCapErrWS_L.H83_two`, ONE field for both. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  -- ⟦(A) THE RAZOR — the three that do not reduce⟧
  /-- `𝒬K₂ ≤ q·T_ann` — `DoorCapBase_L.QTann` at `Jb = 2`. -/
  QTann : ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- ⟦MR (21)⟧'s κ-gate at the designated level — `DoorCapBase_L.kappa30Q`. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — `DoorCapBase_L.q_logX`.  (Independent of `DoorBandBase_L.qfit`'s
  base-side `q ≤ (log X_d)^{10}`; the two are never identified.) -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  -- ⟦(B) THE SOCKET FLOOR AT `(q, T_ann)`⟧
  /-- `T₀ ≤ T_ann` — the capstone's own height floor at its opaque `T₀`. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1 — the VK strip constant against `loglog(5T+1)`. -/
  floor1 : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 2. -/
  floor2 : 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
    ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 3 — the `Kq` arm. -/
  floor3 : Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
    ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)
  /-- Floor gate 4 — the `Ks` arm. -/
  floor4 : (q : ℝ) ^ ((1 : ℝ) / 16)
    ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
  /-- `log(q·T_ann) ≤ Lr` AT THE PINNED `Lr = (log X)^{11/10}` — `DoorCapBase_L.logqT_L`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ s13Lr Nd
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `P₈₃ X θ₂₉₃ ≤ P` — `DoorCapBase_L.P_low`; also the band gate §1 reads. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `log 𝒬K₂ ≤ √(log X)` — `M4RowsChiZero.DoorRowZeroBase.reg` VERBATIM (the spine's row
  bundle already carries it at this base); §1's band gate is `door_band_gate_of_log` off it. -/
  Q2_reg : Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)
    ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- The co-factor range sits in `[1, Mr]` at every block. -/
  range : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd j ⊆ Finset.Icc 1 Mr
  /-- ⟦THE GRADED BUDGET⟧ at the pinned `VJ`, `η`, `εd`. -/
  budget : thinBundleGChi ((q : ℝ) * Tann) (s13VJ M) (calH (H1doorL M) 2)
      (calP (AdoorL M) (3072 * M) 2) (calQK (AdoorL M) (3072 * M) M 2)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ (Mr : ℝ)
  /-- `H₈₃ ≤ j` on the grid. -/
  Hj : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ (j : ℝ)
  /-- `3 ≤ Q_base` on the grid. -/
  B3 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j
  /-- `Q_base ≤ q·T_ann` on the grid. -/
  BT : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ (q : ℝ) * Tann
  /-- The κ-gate on the grid. -/
  kappa30 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)
  /-- `Q_base ≤ T_ann^{10}` on the grid. -/
  BT10 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ Tann ^ 10
  /-- `log Q_base ≤ Lr` on the grid, at the pinned `Lr`. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ s13Lr Nd
  /-- The `cs`-gate on the grid, at the pinned `Lr` — the field that CAPS `Lr` from above. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧ `Rbd ≤ CR·(log X)^{−ρ₂₉₃}`. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧ `1728·Cq·CR² ≤ (log X)^{2θ₂₉₃}`. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` SUPPLY⟧ the door's un-phased co-factor socket, at the door pin's FREE centre
  (`RbdSupply.m4_supplier_all_chi`'s own conclusion shape at `Ps := 1`).  `M4CapWire`
  §4a converts it into `DoorCapBase_L.Rbd_binder`; its threshold constant is the `_vt` floor's
  `K` (a `cffKVt`-genre symbol), **never** `DoorArithFrameRho_L`'s `K`. -/
  Rbd_socket : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
    CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q Tann Rrad t₁ Rbd
      (doorCofactor0 χ (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) 2 1)
  -- ⟦(F) THE `𝒯_S` BUDGET AND LEMMA 12's ERROR ROW⟧
  /-- ⟦V4a⟧'s co-factor length family, lower pin. -/
  m0_two : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 ≤ m₀ j
  /-- ⟦V4a⟧'s co-factor length family against `ramRbot`. -/
  m0_bot : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Nd j
  /-- The sharpness gate `Mr ≤ 4(m₀ j − 1)` — with `range`, the pair that pins `Mr ≍ ramRbot`. -/
  Mr_sharp : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ((Mr : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)
  /-- ⟦THE `𝒯_S` GRADE GATE⟧ at the pinned `KS`. ⚠ one half of the band-width tension. -/
  KS_gate : 32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * s13KS Nd Tann
    ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
  /-- `0 ≤ εr`. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}`. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- ⟦`DoorCapErrWS_L.E_ge`⟧ at the pinned `E` and `Mtail`. ⚠ the other half of the tension. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * s13Mtail M Nd P Q) ≤ s13E Nd Tann EP2

/-- `S13CapGate_L (:248)` at the lever.  Nine fields read the base;
`calH (H1doorL M)` is LEVEL 1 and stays. -/
structure S13CapGate_L_gk (K : ℕ) (Cq cs T₀ Kq Ks : ℝ) (M Nd q P Q Mr : ℕ) (m₀ : ℕ → ℕ)
    (Tann Rrad Rbd CR EP2 εr : ℝ) : Prop where
  -- ⟦THE SCALE FLOOR — the one line every discharged field reads⟧
  /-- `4 ≤ log X` — `DoorCapBase_L_gk K.logX_four` verbatim; `logX_pos`/`logX_exp` come off it. -/
  logX_four : 4 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `2 ≤ H₈₃ X θ₂₉₃` — the two levered bundles' shared field. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  -- ⟦(A) THE RAZOR — the three that do not reduce⟧
  /-- `𝒬K₂ ≤ q·T_ann` — `DoorCapBase_L_gk K.QTann` at `Jb = 2`. -/
  QTann : ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- ⟦MR (21)⟧'s κ-gate at the designated level — `DoorCapBase_L_gk K.kappa30Q`. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — `DoorCapBase_L_gk K.q_logX`.  (Independent of `DoorBandBase_L.qfit`'s
  base-side `q ≤ (log X_d)^{10}`; the two are never identified.) -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  -- ⟦(B) THE SOCKET FLOOR AT `(q, T_ann)`⟧
  /-- `T₀ ≤ T_ann` — the capstone's own height floor at its opaque `T₀`. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1 — the VK strip constant against `loglog(5T+1)`. -/
  floor1 : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 2. -/
  floor2 : 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
    ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 3 — the `Kq` arm. -/
  floor3 : Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
    ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)
  /-- Floor gate 4 — the `Ks` arm. -/
  floor4 : (q : ℝ) ^ ((1 : ℝ) / 16)
    ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
  /-- `log(q·T_ann) ≤ Lr` AT THE PINNED `Lr = (log X)^{11/10}` — `DoorCapBase_L_gk K.logqT_L`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ s13Lr Nd
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `P₈₃ X θ₂₉₃ ≤ P` — `DoorCapBase_L_gk K.P_low`; also the band gate §1 reads. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `log 𝒬K₂ ≤ √(log X)` — `M4RowsChiZero.DoorRowZeroBase.reg` VERBATIM (the spine's row
  bundle already carries it at this base); §1's band gate is `door_band_gate_of_log` off it. -/
  Q2_reg : Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)
    ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- The co-factor range sits in `[1, Mr]` at every block. -/
  range : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd j ⊆ Finset.Icc 1 Mr
  /-- ⟦THE GRADED BUDGET⟧ at the pinned `VJ`, `η`, `εd`. -/
  budget : thinBundleGChi ((q : ℝ) * Tann) (s13VJ_gk K M) (calH (H1doorL M) 2)
      (calP (AdoorL M) (s13GK K M) 2) (calQK (AdoorL M) (s13GK K M) M 2)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ (Mr : ℝ)
  /-- `H₈₃ ≤ j` on the grid. -/
  Hj : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ (j : ℝ)
  /-- `3 ≤ Q_base` on the grid. -/
  B3 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j
  /-- `Q_base ≤ q·T_ann` on the grid. -/
  BT : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ (q : ℝ) * Tann
  /-- The κ-gate on the grid. -/
  kappa30 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)
  /-- `Q_base ≤ T_ann^{10}` on the grid. -/
  BT10 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ Tann ^ 10
  /-- `log Q_base ≤ Lr` on the grid, at the pinned `Lr`. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ s13Lr Nd
  /-- The `cs`-gate on the grid, at the pinned `Lr` — the field that CAPS `Lr` from above. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧ `Rbd ≤ CR·(log X)^{−ρ₂₉₃}`. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧ `1728·Cq·CR² ≤ (log X)^{2θ₂₉₃}`. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` SUPPLY⟧ the door's un-phased co-factor socket, at the door pin's FREE centre
  (`RbdSupply.m4_supplier_all_chi`'s own conclusion shape at `Ps := 1`).  `M4CapWire`
  §4a converts it into `DoorCapBase_L_gk K.Rbd_binder`; its threshold constant is the `_vt` floor's
  `K` (a `cffKVt`-genre symbol), **never** `DoorArithFrameRho_L`'s `K`. -/
  Rbd_socket : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
    CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q Tann Rrad t₁ Rbd
      (doorCofactor0 χ (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 1)
  -- ⟦(F) THE `𝒯_S` BUDGET AND LEMMA 12's ERROR ROW⟧
  /-- ⟦V4a⟧'s co-factor length family, lower pin. -/
  m0_two : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 ≤ m₀ j
  /-- ⟦V4a⟧'s co-factor length family against `ramRbot`. -/
  m0_bot : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Nd j
  /-- The sharpness gate `Mr ≤ 4(m₀ j − 1)` — with `range`, the pair that pins `Mr ≍ ramRbot`. -/
  Mr_sharp : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ((Mr : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)
  /-- ⟦THE `𝒯_S` GRADE GATE⟧ at the pinned `KS`. ⚠ one half of the band-width tension. -/
  KS_gate : 32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * s13KS Nd Tann
    ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
  /-- `0 ≤ εr`. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}`. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- ⟦`DoorCapErrWS_L_gk K.E_ge`⟧ at the pinned `E`/`Mtail`. ⚠ the other half of the tension. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * s13Mtail_gk K M Nd P Q) ≤ s13E Nd Tann EP2

/-- **THE χ-TWISTED SUP** `doorChiSup_L χ M H n` — `sup_{K ≤ H} ‖∑_{m ∈ 𝒮, n < m ≤ n+K} λ(m)χ̄(m)‖`.
The datum is `liouChi χ` (the ⟦lam collision⟧: the sum runs over integers). -/
def doorChiSup_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) : ℝ :=
  (Finset.Icc 0 H).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
    (fun K => ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖)

/-- **THE χ-TWISTED SUP AT THE LEVER** — `doorChiSup_L` (:369). -/
def doorChiSup_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) : ℝ :=
  (Finset.Icc 0 H).sup' ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
    (fun Kw => ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖)

/-- **THE SMALL-`j` COMPARISON AT THE DOOR**, symbolic (`door_smallGrade_fits_L`), re-threaded
onto ⟦LEVER 1′⟧'s weighted head.  The whole `j < j₀` block of `M4Maximal`'s graded assembly
now costs the TWO summands of the geometric head against `H²·MSan H`.  Neither
`(4/3)^{doorRowFloorL M}` nor `(8/3)^{doorRowFloorL M}` moves with `H`, and any density
envelope `MStr H ≤ D` is `H`-free — the block density is `≍ 1/loglog X_d`, bounded by an
absolute constant — so the threshold reads, in bytes,

  `((9/2)(3/2)^{log₂H}(4/3)^{M·AdoorL M}·H + (9/5)(3/2)^{log₂H}(8/3)^{M·AdoorL M})·D
     ≤ H²·MSan H`,

one inequality in `H` at fixed `M`.  Since `(3/2)^{log₂H}·H = H^{1.585}` against `H²`, both
summands read as `H ≳ 2^{M·AdoorL M}` — the uniform route's demand was `4^{M·AdoorL M}`, so the
floor's exponent HALVES.  Under it the graded price is at most twice the ungraded one
(`M4Maximal.m4BclGraded_le_of_fits`), i.e. the small lengths cost the close's budget
nothing. -/
theorem door_smallGrade_fits_L {M H : ℕ} {MSan MStr : ℕ → ℝ} {D : ℝ}
    (hMStr : MStr H ≤ D) (hMSan : 0 ≤ MSan H)
    (hthr : (9 / 2 * (3 / 2 : ℝ) ^ Nat.log 2 H * (4 / 3 : ℝ) ^ doorRowFloorL M * (H : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ Nat.log 2 H * (8 / 3 : ℝ) ^ doorRowFloorL M) * D
        ≤ (H : ℝ) ^ 2 * MSan H) :
    m4SmallGradeFits (doorRowFloorL M) MSan MStr H :=
  m4SmallGradeFits_of_threshold hMStr hMSan hthr

/-- **THE FIVE RAW SUMMANDS**, byte-verbatim from `M4MeanSq.m4_meansq_per_chi_gen`'s
right-hand side: the quality term, the level-1 term, the `(log X)^{−1/500}` term, the
`(log X)^{−43/45}` ball term, and `C₅/h`. -/
def m4RawMS_L (C₁' M₀ : ℝ) (M : ℕ) (X h : ℝ) : ℝ :=
  8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1_L M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

set_option linter.unusedVariables false in
/-- **`m4RawMS_L` AT THE LEVER.**  The five raw summands do not read `G` at all: the level-1
summand is `a2Level1_L M`, which is K-INVARIANT.  The twin exists for uniformity of the
family's shape (`K` first, everywhere), and is definitionally the landed constant. -/
def m4RawMS_L_gk (K : ℕ) (C₁' M₀ : ℝ) (M : ℕ) (X h : ℝ) : ℝ :=
  8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1_L M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- **§3's EXIT** (`m4_blockMeanSq_of_rowMeanSq_L`).  The row input, block by block, IS
`M4BridgeCover.M4BlockMeanSq` at the grade `2·MS` — B-4's ladder lemma (the coverage datum
discharged by `hcov_of_seamS0`, both fits by the ladder) followed by §3's exchange.

`0 < H` is free: `R.Hlo ≤ H` and `R.hHlo_floor` give `H ≥ 4·10⁶`. -/
theorem m4_blockMeanSq_of_rowMeanSq_L {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℝ}
    (hrow : M4RowMeanSq_L R M k MS) :
    M4BlockMeanSq_L R M k (fun H => 2 * MS H) := by
  intro H hlo hhi α harc i hik
  have hH0 : 0 < H := by
    have := R.hHlo_floor
    omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  -- ⟦the coverage datum is free at the block's own seam index set⟧
  have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
          (doorLadder R.x H (i + 1) : ℝ) → doorSievedCoeff_L M m = 0 :=
    hcov_of_seamS0 (doorSievedCoeff_L M) (A := doorLadder R.x H (i + 1))
      (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
      (by omega)
  -- ⟦B-4: the harmonic-weighted block bound⟧
  have hladder := sum_Ioc_absWindowSum_sq_div_le_ladder (doorSievedCoeff_L M)
    (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) α
    (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov (hrow H hlo hhi α harc i hik)
  -- ⟦§3: the exchange⟧
  have hflat := sum_Ioc_le_two_mul_of_harmonic (x := R.x) (H := H) (i := i)
    (f := fun n => ‖absWindowSum (doorSievedCoeff_L M) H n α‖ ^ 2)
    (V := (H : ℝ) ^ 2 * MS H) hxH (fun n _ => by positivity) hladder
  have heq : 2 * ((H : ℝ) ^ 2 * MS H) * (doorLadder R.x H (i + 1) : ℝ)
      = 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring
  rw [heq] at hflat
  exact hflat

/-- `m4_blockMeanSq_of_rowMeanSq_L` (:326), at the lever. -/
theorem m4_blockMeanSq_of_rowMeanSq_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℝ}
    (hrow : M4RowMeanSq_L_gk K R M k MS) :
    M4BlockMeanSq_L_gk K R M k (fun H => 2 * MS H) := by
  intro H hlo hhi α harc i hik
  have hH0 : 0 < H := by
    have := R.hHlo_floor
    omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  -- ⟦the coverage datum is free at the block's own seam index set⟧
  have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
          (doorLadder R.x H (i + 1) : ℝ) → doorSievedCoeff_L_gk K M m = 0 :=
    hcov_of_seamS0 (doorSievedCoeff_L_gk K M) (A := doorLadder R.x H (i + 1))
      (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
      (by omega)
  -- ⟦B-4: the harmonic-weighted block bound⟧
  have hladder := sum_Ioc_absWindowSum_sq_div_le_ladder (doorSievedCoeff_L_gk K M)
    (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) α
    (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov (hrow H hlo hhi α harc i hik)
  -- ⟦§3: the exchange⟧
  have hflat := sum_Ioc_le_two_mul_of_harmonic (x := R.x) (H := H) (i := i)
    (f := fun n => ‖absWindowSum (doorSievedCoeff_L_gk K M) H n α‖ ^ 2)
    (V := (H : ℝ) ^ 2 * MS H) hxH (fun n _ => by positivity) hladder
  have heq : 2 * ((H : ℝ) ^ 2 * MS H) * (doorLadder R.x H (i + 1) : ℝ)
      = 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring
  rw [heq] at hflat
  exact hflat

/-- **§4c — ⟦LEMMA 12's `χ`-SUMMED ERROR ROW — THE CONDITIONAL WIRE⟧**
(`m4_capE_at_door_of_hcoef_L`).  `HybridMoments.ramErr_meanSq_all_chi` at the door datum,
delivering `DoorCapBase_L.E_binder` at the explicit `E`.

⟦THE MISMATCH, REPORTED NOT MASSAGED⟧ the supplier asks the **GLOBAL** block factorization
`hcoef` — `∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬p∣m → a(p·m) = b m · cf p` — for the datum
`a = winCutH Nd (doorCoeffU_L M)`, which is WINDOW-CUT.
`M4Assembly.doorRows_global_hcoef_kills_block`
(itself `ThmA2Spine.seam_coef_contract_forces_vanishing`) shows that pair forces `a(p₁·m) = 0`
for every `m` coprime to `p₁` as soon as one product is live and one block prime pushes off the
window.  So this theorem is stated CONDITIONALLY on `hcoef`, `E_binder` remains a carried field
of `DoorCapBase_L`, and the honest repair — the STRICT relativized pair law
(`SeamRowWindowed.SeamCoefWS`, the shape the `q = 1` supplier `ThmA2Rows.a2Rows_of_capfree3_end`
carries) re-cut through `ramErr_moment_split` — is a design question, not an executor's edit.

Note also: the brief's named supplier `HybridMoments.lemma12_meansq_all_chi` (`:712`) does NOT
fit this slot at all — its left-hand side is `∑_χ ∫ ‖spoly N (χ̄a)‖²`, not the capstone's
`∑_χ ∫ ‖ramErr …‖²`.  `ramErr_meanSq_all_chi` (`:604`) is the shape-correct one. -/
theorem m4_capE_at_door_of_hcoef_L {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ} {Tann : ℝ}
    (hH : 0 < H83 ((Nd : ℕ) : ℝ) theta293) (hP : 1 ≤ P) (hT : 0 ≤ Tann)
    (hcoef : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m →
      winCutH Nd (doorCoeffU_L M) (p * m) = b m * cf p) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ 3 * ((q.totient : ℝ)
            * (2 * Tann * (windowMass (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q b cf) ^ 2)
          + (2 * (q.totient : ℝ) * Tann
                + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 (2 * Nd),
                  ‖ramP2coeff (2 * Nd) P Q (winCutH Nd (doorCoeffU_L M)) b cf n‖ ^ 2
                    / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * Tann
                + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
                  ‖winCutH Nd (doorCoeffU_L M) n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  ramErr_meanSq_all_chi q (H83 ((Nd : ℕ) : ℝ) theta293) hH (2 * Nd) Xd P Q hP
    (winCutH Nd (doorCoeffU_L M)) b cf hcoef Tann hT

/-- `m4_capE_at_door_of_hcoef_L` (:494), at the lever.  The mismatch the landed docstring reports
is UNCHANGED by the lever: `M4Assembly.doorRows_global_hcoef_kills_block_gk` refutes the global
`hcoef` at the levered block exactly as its landed original does at the landed one. -/
theorem m4_capE_at_door_of_hcoef_L_gk (K : ℕ) {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ}
    {Tann : ℝ}
    (hH : 0 < H83 ((Nd : ℕ) : ℝ) theta293) (hP : 1 ≤ P) (hT : 0 ≤ Tann)
    (hcoef : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m →
      winCutH Nd (doorCoeffU_L_gk K M) (p * m) = b m * cf p) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L_gk K M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ 3 * ((q.totient : ℝ)
            * (2 * Tann * (windowMass (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q b cf) ^ 2)
          + (2 * (q.totient : ℝ) * Tann
                + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 (2 * Nd),
                  ‖ramP2coeff (2 * Nd) P Q (winCutH Nd (doorCoeffU_L_gk K M)) b cf n‖ ^ 2
                    / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * Tann
                + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
                  ‖winCutH Nd (doorCoeffU_L_gk K M) n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  ramErr_meanSq_all_chi q (H83 ((Nd : ℕ) : ℝ) theta293) hH (2 * Nd) Xd P Q hP
    (winCutH Nd (doorCoeffU_L_gk K M)) b cf hcoef Tann hT

/-- **`m4_cover_assembly_L` — BRIDGE 5's EXIT.**  The per-block mean square, assembled over the
door ladder and normalised against `logMeasure`, IS `M4Close.M4SievedDoorSq` at the grade
`3·B_blk`.

⟦WHAT IS CONSUMED⟧ the door-gate bundle `M4DoorGates_L` for its ladder data (`hlogω`, `hcount`,
`hpow`, `hreach`) — the same bundle `m4_hbd_of_live_L` reads, so the join needs no new
hypothesis; and `M4Door` §1–§4 through `integral_door_cover_le_clean`.

⟦WHERE THE `3` COMES FROM⟧ the cover has `k ≍ log ω/log 2` blocks and the door normaliser is
`Z ≍ log ω`; `door_count_le_three_mul_norm` cancels them at the absolute ratio `3`.  It is a
grade factor, not an `M`-gate rescale (see the module header's ⟦`Z`'S TWO ROLES⟧). -/
theorem m4_cover_assembly_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSq_L R M k Bblk) :
    M4SievedDoorSq_L R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi α harc
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (H : ℝ) ^ 2 := mul_nonneg (hB0 H) (by positivity)
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => ‖absWindowSum (doorSievedCoeff_L M) H n α‖ ^ 2)
    (P := Bblk H * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi α harc)
  simp only [doorSievedCoeff_L] at hmain
  have heq : 3 * (Bblk H * (H : ℝ) ^ 2) = 3 * Bblk H * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **`m4_cover_assembly_blk_L` — THE BLOCKED ROUTE'S COVERING SIDE.**  The same
`integral_door_cover_le_clean`, the same door-gate bundle, the same absolute factor `3`.

Nothing about the covering argument depends on what the nonnegative integrand *is*, which is
precisely why `M4BridgeCover` §3 could state it at a free `g`. -/
theorem m4_cover_assembly_blk_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk_L R M k ℓ Bblk) :
    M4SievedDoorSqBlk_L R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff_L M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

/-- **THE BLOCKED ROUTE'S COVERING SIDE AT THE LEVER** — `m4_cover_assembly_blk_L` (:499). -/
theorem m4_cover_assembly_blk_L_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {ℓ : ℕ → ℕ → ℕ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L_gk K Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqBlk_L_gk K R M k ℓ Bblk) :
    M4SievedDoorSqBlk_L_gk K R M ℓ (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ h1 h2 h3
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => blockSupSq (doorSievedCoeff_L_gk K M) H (ℓ H q) n ((b : ℝ) / (q : ℝ)))
    (P := Bblk H * (numBlocks H (ℓ H q) : ℝ) * (ℓ H q : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount
    (fun n => blockSupSq_nonneg _ _ _ _ _) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ h1 h2 h3)
  refine le_trans hmain (le_of_eq ?_)
  ring

/-- **BRIDGE 5's EXIT AT THE LEVER** — `m4_cover_assembly_L` (:404) verbatim: the covering
side never reads `G`. -/
theorem m4_cover_assembly_L_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L_gk K Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSq_L_gk K R M k Bblk) :
    M4SievedDoorSq_L_gk K R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi α harc
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (H : ℝ) ^ 2 := mul_nonneg (hB0 H) (by positivity)
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => ‖absWindowSum (doorSievedCoeff_L_gk K M) H n α‖ ^ 2)
    (P := Bblk H * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi α harc)
  simp only [doorSievedCoeff_L_gk] at hmain
  have heq : 3 * (Bblk H * (H : ℝ) ^ 2) = 3 * Bblk H * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **THE M4-7 DELIVERABLE, SPLIT** (`m4_hbd_of_live_split_L`) — the twin of `m4_hbd_of_live_L`
(:464), byte-plug-compatible with `M4Exit.m4_exit_socket_split`'s single open binder.

The proof is the landed one with its final `calc` step re-targeted: the door glue, the
socket, §1's `L²→L¹` descent and the `√`-split are all identical, and the last line reads the
split gate into `δ₀ * H` where the original read `mrtDeliveredGrade C H * H`.

Binder-list diff against the original: `C : ℝ` is GONE; `δ₀ : ℝ` takes its place and the
grade gate is `M4GradeGateSplit`.  `Cg` — the door glue's ONE opened constant — is
unchanged. -/
theorem m4_hbd_of_live_split_L :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (δ₀ δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGateSplit R δ₀ δ Braw k →
        M4SievedDoorSq_L R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ δ₀ * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R δ₀ δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ AdoorL M := by
    have h := AdoorL_ge hgates.hM
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed⟧
  have hglueH := hglue (AdoorL M) (3072 * M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
      (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the SPLIT budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
            (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ δ₀ * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE M4-7 DELIVERABLE, SPLIT, AT THE LEVER** — `m4_hbd_of_live_split_L` (:710). -/
theorem m4_hbd_of_live_split_L_gk (K : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (δ₀ δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates_L_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
        M4GradeGateSplit R δ₀ δ Braw k →
        M4SievedDoorSq_L_gk K R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ δ₀ * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R δ₀ δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ AdoorL M := by
    have h := AdoorL_ge hgates.hM
    omega
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed at the lever's base⟧
  have hglueH := hglue (AdoorL M) (s13GK K M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the SPLIT budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ δ₀ * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE BLOCKED SOCKET THEOREM** — ⟦F3⟧'s exit, the sibling of
`M4BridgePhase.m4_sievedDoorSq_of_sup` (`:434`).

`M4Close.M4SievedDoorSq R M Braw` from the blocked supply at the composed price
`4·(1 + 2π)²·Bblk H ≤ Braw H`.  ⟦THE DRIFT FACTOR IS ABSOLUTE⟧ — no `arcDen`, no `q`.  The
`q` survives only inside the block-length obligations `hℓcnt`/`hℓdrift`, which pin `ℓ H q`
into the interval `H/arcDen ≤ ℓ H q ≤ q·H/arcDen` (nonempty for every `q ≥ 1`); wave ④ owns
the witness. -/
theorem m4_sievedDoorSq_of_blk_L {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ} {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk_L R M ℓ Bblk) : M4SievedDoorSq_L R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff_L M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  -- ⟦the pointwise blocked drift, squared⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked (B₅ := 12) (H := H) (q := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  -- ⟦the integral, and the grade⟧
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  -- ⟦`N²ℓ² ≤ 4H²`: the blocking is loss-free up to the absolute factor `4`⟧
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-- **THE BLOCKED SOCKET THEOREM AT THE LEVER** — `m4_sievedDoorSq_of_blk_L` (:386). -/
theorem m4_sievedDoorSq_of_blk_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {ℓ : ℕ → ℕ → ℕ}
    {Bblk Braw : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hℓ1 : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → 1 ≤ ℓ H q)
    (hℓH : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H → ℓ H q ≤ H)
    (hℓcnt : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (H : ℝ) ≤ arcDen 12 H * (ℓ H q : ℝ))
    (hℓdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      arcDen 12 H * (ℓ H q : ℝ) ≤ (q : ℝ) * (H : ℝ))
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      4 * (1 + 2 * Real.pi) ^ 2 * Bblk H ≤ Braw H)
    (hblk : M4SievedDoorSqBlk_L_gk K R M ℓ Bblk) : M4SievedDoorSq_L_gk K R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  have hℓ1' := hℓ1 H q hlo hhi hq hqQ
  have hℓH' := hℓH H q hlo hhi hq hqQ
  have hℓcnt' := hℓcnt H q hlo hhi hq hqQ
  have hℓdrift' := hℓdrift H q hlo hhi hq hqQ
  have hℓ0 : 0 < ℓ H q := hℓ1'
  set c := doorSievedCoeff_L_gk K M with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  set L := ℓ H q with hL
  set N := numBlocks H L with hN
  -- ⟦the pointwise blocked drift, squared⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β := by
    intro n
    have h := norm_absWindowSum_sq_le_drift_blocked (B₅ := 12) (H := H) (q := q) (n := n)
      (ℓ := L) hq hH hℓ0 (β := β) (θ := α - β) hd hℓdrift' c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    exact h
  -- ⟦the integral, and the grade⟧
  have hmono : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_mono hpt
  have hconst : (∫ n, (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * blockSupSq c H L n β
        ∂(logMeasure R.x R.ω))
      = (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * ∫ n, blockSupSq c H L n β ∂(logMeasure R.x R.ω) :=
    integral_logMeasure_const_mul _ _
  have hsupply := hblk htr H hlo hhi b q hq hqQ hℓ1' hℓH' hℓcnt'
  have hfac0 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) := by positivity
  have hstep : (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := by
    rw [hconst] at hmono
    exact le_trans hmono (mul_le_mul_of_nonneg_left hsupply hfac0)
  -- ⟦`N²ℓ² ≤ 4H²`: the blocking is loss-free up to the absolute factor `4`⟧
  have hNL : N * L ≤ 2 * H := by
    have h1 : N * L ≤ H + L := by rw [hN]; exact numBlocks_mul_le H L
    omega
  have hNLR : (N : ℝ) * (L : ℝ) ≤ 2 * (H : ℝ) := by
    have : ((N * L : ℕ) : ℝ) ≤ ((2 * H : ℕ) : ℝ) := by exact_mod_cast hNL
    push_cast at this
    linarith
  have hNL0 : (0 : ℝ) ≤ (N : ℝ) * (L : ℝ) := by positivity
  have hsq : ((N : ℝ) * (L : ℝ)) ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by nlinarith
  have hB := hB0 H
  have hpi2 : (0 : ℝ) ≤ (1 + 2 * Real.pi) ^ 2 := sq_nonneg _
  have hfin : (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
      ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by
    calc (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2)
        = (1 + 2 * Real.pi) ^ 2 * Bblk H * (((N : ℝ) * (L : ℝ)) ^ 2) := by ring
      _ ≤ (1 + 2 * Real.pi) ^ 2 * Bblk H * (4 * (H : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hpi2 hB)
      _ = 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := by ring
  have hgr := hgrade H hlo hhi
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ (1 + 2 * Real.pi) ^ 2 * (N : ℝ) * (Bblk H * (N : ℝ) * (L : ℝ) ^ 2) := hstep
    _ ≤ 4 * (1 + 2 * Real.pi) ^ 2 * Bblk H * (H : ℝ) ^ 2 := hfin
    _ ≤ Braw H * (H : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hgr (sq_nonneg _)

/-- The untwisted door coefficient is `1`-bounded (`memSCoeff` only deletes terms). -/
theorem norm_doorCoeffU_le_one_L (M n : ℕ) : ‖doorCoeffU_L M n‖ ≤ 1 :=
  norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 n

/-- `norm_doorCoeffU_le_one_L` (:123), at the lever. -/
theorem norm_doorCoeffU_le_one_L_gk (K M n : ℕ) : ‖doorCoeffU_L_gk K M n‖ ≤ 1 :=
  norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 n

/-- The door row datum is `1`-bounded. -/
theorem norm_doorRowDatumU_le_one_L (M Nd n : ℕ) : ‖winCutH Nd (doorCoeffU_L M) n‖ ≤ 1 :=
  norm_winCutH_le (norm_doorCoeffU_le_one_L M) n

/-- `norm_doorRowDatumU_le_one_L` (:132), at the lever. -/
theorem norm_doorRowDatumU_le_one_L_gk (K M Nd n : ℕ) :
    ‖winCutH Nd (doorCoeffU_L_gk K M) n‖ ≤ 1 :=
  norm_winCutH_le (norm_doorCoeffU_le_one_L_gk K M) n

/-- **THE POINTWISE MAXIMAL BOUND AT THE LEVER** — `doorChiSup_sq_le_dyadic_L` (:396). -/
theorem doorChiSup_sq_le_dyadic_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    (doorChiSup_L_gk K χ M H n) ^ 2
      ≤ (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (Nat.log 2 H + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
              ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2)
              * (2 / 3 : ℝ) ^ j := by
  obtain ⟨Kw, hKmem, hKeq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.Icc 0 H)
      ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
      (fun Kw => ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖)
  have hKH : Kw ≤ H := (Finset.mem_Icc.mp hKmem).2
  have hval : doorChiSup_L_gk K χ M H n
      = ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖ := hKeq
  rw [hval]
  simp only [doorSievedWindow_L_gk]
  exact norm_sum_sievedWindow_sq_le_dyadic _ (liouChi χ) H Kw n hKH

/-- **THE SUB-WINDOW SUP, PRICED** — `doorChiSup_L`'s square against the aligned dyadic
family, at the geometric weights.  The sup is over a nonempty finite set, hence attained
(`Finset.exists_mem_eq_sup'`), and the bound is `K`-free. -/
theorem doorChiSup_sq_le_dyadic_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) :
    (doorChiSup_L χ M H n) ^ 2
      ≤ (∑ j ∈ Finset.range (Nat.log 2 H + 1), (3 / 2 : ℝ) ^ j)
        * ∑ j ∈ Finset.range (Nat.log 2 H + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
              ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2)
              * (2 / 3 : ℝ) ^ j := by
  obtain ⟨K, hKmem, hKeq⟩ :=
    Finset.exists_mem_eq_sup' (s := Finset.Icc 0 H)
      ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le H⟩⟩
      (fun K => ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖)
  have hKH : K ≤ H := (Finset.mem_Icc.mp hKmem).2
  have hval : doorChiSup_L χ M H n = ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖ := hKeq
  rw [hval]
  simp only [doorSievedWindow_L]
  exact norm_sum_sievedWindow_sq_le_dyadic _ (liouChi χ) H K n hKH

/-- **THE χ-UNIFORM BLOCK MEAN SQUARE** — the shape the M4/MRT capstone natively produces
(per character, over one ladder block), with the sub-window sup inside. -/
def M4ChiBlockMeanSq_L (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup_L χ M H n) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE χ-UNIFORM BLOCK MEAN SQUARE AT THE LEVER** — `M4ChiBlockMeanSq_L` (:384). -/
def M4ChiBlockMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup_L_gk K χ M H n) ^ 2
        ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)

/-- **THE SHIFTED BRIDGE AT THE LEVER** — `m4_chiShiftBlock_of_dyadicRow_L` (:1042). -/
theorem m4_chiShiftBlock_of_dyadicRow_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiDyadicRowMeanSq_L_gk K R M k MS) :
    M4ChiShiftBlockMeanSq_L_gk K R M k (fun j H => 2 * MS j H) := by
  intro H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  have hstepd := doorLadder_step_le hxH i
  have hfloor := doorLadder_floor hxH (i + 1)
  have h2j : 2 ^ j ≤ H := by
    calc 2 ^ j ≤ 2 ^ Nat.log 2 H := Nat.pow_le_pow_right (by norm_num) hjL
      _ ≤ H := Nat.pow_log_le_self 2 hH0.ne'
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAB : A + s ≤ B + s := by omega
  have hXpos : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by
    have : 0 < A + s := by omega
    exact_mod_cast this
  have hBfit : (((B + s : ℕ)) : ℝ) + ((2 ^ j : ℕ) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s + 2 ^ j ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L_gk K χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff_L_gk K χ M) (A := A + s) (B := B + s) (N := 2 * (A + s))
      (H := 2 ^ j) le_rfl (by omega)
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hladder := sum_Ioc_absWindowSum_sq_div_le (doorChiCoeff_L_gk K χ M)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (X := (((A + s : ℕ)) : ℝ)) (MS := MS j H) hh0 hAB hXpos le_rfl hBfit hcov hMSrow
  -- ⟦the grade is nonnegative, because the harmonic sum is⟧
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H :=
    le_trans (Finset.sum_nonneg fun n _ => by positivity) hladder
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hladder (Nat.cast_nonneg _)
  have hBs : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : B + s ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    refine le_trans hex ?_
    have := mul_le_mul_of_nonneg_right hBs hP0
    calc (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        ≤ 2 * (A : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := this
      _ = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by ring
  simpa only [absWindowSum_doorChiCoeff_zero_L_gk K] using hfinal

/-- **THE SHIFTED BRIDGE** (`m4_chiShiftBlock_of_dyadicRow_L`) — the per-length, per-shift row
mean square becomes the shifted block sum of squared sieved-twisted window sums, at the grade
`2·MS`: B-4's `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le` at the frequency `0` and the
scale `X := X_{i+1}+s`, then the harmonic→flat exchange against `B + s ≤ 2·X_{i+1}`. -/
theorem m4_chiShiftBlock_of_dyadicRow_L {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiDyadicRowMeanSq_L R M k MS) :
    M4ChiShiftBlockMeanSq_L R M k (fun j H => 2 * MS j H) := by
  intro H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  have hstepd := doorLadder_step_le hxH i
  have hfloor := doorLadder_floor hxH (i + 1)
  have h2j : 2 ^ j ≤ H := by
    calc 2 ^ j ≤ 2 ^ Nat.log 2 H := Nat.pow_le_pow_right (by norm_num) hjL
      _ ≤ H := Nat.pow_log_le_self 2 hH0.ne'
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAB : A + s ≤ B + s := by omega
  have hXpos : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by
    have : 0 < A + s := by omega
    exact_mod_cast this
  have hBfit : (((B + s : ℕ)) : ℝ) + ((2 ^ j : ℕ) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s + 2 ^ j ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff_L χ M) (A := A + s) (B := B + s) (N := 2 * (A + s))
      (H := 2 ^ j) le_rfl (by omega)
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hladder := sum_Ioc_absWindowSum_sq_div_le (doorChiCoeff_L χ M)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (X := (((A + s : ℕ)) : ℝ)) (MS := MS j H) hh0 hAB hXpos le_rfl hBfit hcov hMSrow
  -- ⟦the grade is nonnegative, because the harmonic sum is⟧
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H :=
    le_trans (Finset.sum_nonneg fun n _ => by positivity) hladder
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hladder (Nat.cast_nonneg _)
  have hBs : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : B + s ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    refine le_trans hex ?_
    have := mul_le_mul_of_nonneg_right hBs hP0
    calc (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        ≤ 2 * (A : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) := this
      _ = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by ring
  simpa only [absWindowSum_doorChiCoeff_zero_L] using hfinal

/-- **THE CLASS PRICE, ASSEMBLED INTO THE `q`-GRADED BLOCK PREDICATE.**  With a per-class
grade `B H` valid at every sub-window length, every rational modulus in range and every door
index of the block, the block sum is at most `card × q²·(B H)²`, and the ladder's fit bounds
the block's cardinality by its own bottom `X_{i+1}` (`M4Door.doorLadder_fit`).

The resulting block grade is `(B H)²/H²` — i.e. the per-class grade measured against the
window length, which is exactly the currency `M4Join`'s §4 pricing reads. -/
theorem m4_blockMeanSqSupQ_of_classPrice_L {R : ChowlaRegime} {M k : ℕ} {B : ℕ → ℝ}
    (hclass : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        ∀ K, K ≤ H → ∀ r, r < q →
          ‖∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ ≤ B H) :
    M4BlockMeanSqSupQ_L R M k (fun H => B H ^ 2 / (H : ℝ) ^ 2) := by
  intro H hlo hhi b q hq hqQ i hik
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  -- ⟦pointwise on the block: the class price squared⟧
  have hterm : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) ^ 2 * B H ^ 2 := fun n hn =>
    subWindowSup_sq_le_class_count (doorSievedCoeff_L M) H n hq b
      (fun K hK r hr => hclass H hlo hhi q hq hqQ i hik n hn K hK r hr)
  have hcard : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
        * ((q : ℝ) ^ 2 * B H ^ 2) := by
    calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ ∑ _n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ((q : ℝ) ^ 2 * B H ^ 2) := Finset.sum_le_sum hterm
      _ = ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
            * ((q : ℝ) ^ 2 * B H ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i)).card : ℝ)
      ≤ (doorLadder R.x H (i + 1) : ℝ) := by
    rw [Nat.card_Ioc]
    have hfit := doorLadder_fit R.x H i
    have hn : doorLadder R.x H i - doorLadder R.x H (i + 1) ≤ doorLadder R.x H (i + 1) := by
      omega
    exact_mod_cast hn
  have hpos := doorLadder_pos hxH (i + 1)
  have hrhs : B H ^ 2 / (H : ℝ) ^ 2 * (q : ℝ) ^ 2 * (H : ℝ) ^ 2
        * (doorLadder R.x H (i + 1) : ℝ)
      = (doorLadder R.x H (i + 1) : ℝ) * ((q : ℝ) ^ 2 * B H ^ 2) := by
    field_simp
  rw [hrhs]
  refine le_trans hcard ?_
  have hQB : (0 : ℝ) ≤ (q : ℝ) ^ 2 * B H ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hc hQB

/-- **THE `q`-GRADED COVERING SIDE.**  `M4Join.m4_cover_assembly_sup` at the `q`-graded block
predicate: the same `integral_door_cover_le_clean`, the same door-gate bundle, the same
absolute factor `3` — the covering argument never reads what the nonnegative integrand is, so
carrying `q²` through it is free. -/
theorem m4_cover_assembly_supQ_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqSupQ_L R M k Bblk) :
    M4SievedDoorSqSup_L R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2)
    (P := Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ)
  simp only [doorSievedCoeff_L] at hmain
  have heq : 3 * (Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
      = 3 * Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **`m4_cover_assembly_sup_L` — THE SUP ROUTE'S COVERING SIDE.**  `M4BridgeCover`'s §4 at
B-2's carrier: the same `integral_door_cover_le_clean`, the same door-gate bundle, the same
absolute factor `3` (the cover count `k` against the door normaliser `Z`).

Nothing about the covering argument depends on what the nonnegative integrand *is*, which is
precisely why B-5 could state its §3 at a free `g` and defer this repackage. -/
theorem m4_cover_assembly_sup_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ} {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqSup_L R M k Bblk) :
    M4SievedDoorSqSup_L R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (H : ℝ) ^ 2 := mul_nonneg (hB0 H) (by positivity)
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2)
    (P := Bblk H * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ)
  simp only [doorSievedCoeff_L] at hmain
  have heq : 3 * (Bblk H * (H : ℝ) ^ 2) = 3 * Bblk H * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  -- ⟦B-2's `q`-graded socket: the `q`-free block bound is read at `q ≥ 1`⟧
  refine le_trans hmain ?_
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hB : (0 : ℝ) ≤ 3 * Bblk H := by have := hB0 H; linarith
  nlinarith [mul_nonneg hB (sq_nonneg ((H : ℕ) : ℝ)), sq_nonneg ((H : ℕ) : ℝ)]

/-- **THE HOOK — bridge #2's deliverable, `q`-GRADED.**  The sub-window-uniform mean square
at the rationals discharges `M4Close`'s socket, at the drift price
`(1 + 2π·arcDen 12 H / q)²` read against the socket's own `q²`.

The whole of §3 is used once, pointwise in the door variable `n`: the approximant `b/q` is
chosen from `α` alone, so the constant is `n`-free and the bound survives the integral.  The
`q` in `hgrade` is the SAME `q` as the socket's — both come from `NearRatTight`'s witness,
never from a choice made here. -/
theorem m4_sievedDoorSq_of_sup_L {R : ChowlaRegime} {M : ℕ} {Braw Braw' : ℕ → ℝ}
    (hgrade : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * Braw' H) ≤ Braw H)
    (hsup : M4SievedDoorSqSup_L R M Braw') : M4SievedDoorSq_L R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  set c := memSCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC
    with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  -- ⟦the pointwise drift bound, squared — THE `q`-GRADING KEPT (no `hden` demotion)⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * (subWindowSup c H n β) ^ 2 := by
    intro n
    have h := norm_absWindowSum_le_drift (B₅ := 12) (H := H) (q := q) (n := n)
      (β := β) (θ := α - β) hq hH hd c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    calc ‖absWindowSum c H n α‖ ^ 2
        ≤ ((1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) * subWindowSup c H n β) ^ 2 := by
          gcongr
      _ = (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
            * (subWindowSup c H n β) ^ 2 := by ring
  -- ⟦the integral, and the grade⟧
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * (subWindowSup c H n β) ^ 2
          ∂(logMeasure R.x R.ω) := integral_logMeasure_mono hpt
    _ = (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * ∫ n, (subWindowSup c H n β) ^ 2 ∂(logMeasure R.x R.ω) :=
        integral_logMeasure_const_mul _ _
    _ ≤ (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * (Braw' H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsup htr H hlo hhi b q hq hqQ) (sq_nonneg _)
    _ = ((1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * Braw' H))
          * (H : ℝ) ^ 2 := by ring
    _ ≤ Braw H * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (hgrade H q hlo hhi hq hqQ) (sq_nonneg _)

/-- **THE ASSEMBLY** (`m4_blockMeanSqSupQ_of_classMeanSq_L`).  The `q`-graded block predicate
from the per-class block mean square.

The arithmetic, once: pointwise in the door index `n`,

```
   (subWindowSup)²  ≤  (∑_{r<q} classSup_r)²  ≤  q·∑_{r<q} classSup_r²
```

(the split of §1, then Chebyshev at `#(range q) = q`); summing over the block and applying
the per-class datum `q` times gives `q²·B_cl H·H²·X_{i+1}`, which is
`M4ClassPrice.M4BlockMeanSqSupQ`'s right-hand side verbatim.

Compare `M4ClassPrice.m4_blockMeanSqSupQ_of_classPrice`: identical output grade, but its
input is the pointwise class price (a bound at every `n` of the block).  Here the block sum
is the input — the shape a mean-square supplier produces. -/
theorem m4_blockMeanSqSupQ_of_classMeanSq_L {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hcl : M4ClassBlockMeanSq_L R M k Bcl) : M4BlockMeanSqSupQ_L R M k Bcl := by
  intro H hlo hhi b q hq hqQ i hik
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  -- ⟦pointwise: the split, then Chebyshev⟧
  have hpt : ∀ n : ℕ,
      (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff_L M) H n q r) ^ 2 := by
    intro n
    have hsplit := subWindowSup_le_sum_classSup (doorSievedCoeff_L M) H n hq b
    have h0 := subWindowSup_nonneg (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))
    have hsq : (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ r ∈ Finset.range q, classSup (doorSievedCoeff_L M) H n q r) ^ 2 := by
      nlinarith
    refine hsq.trans ?_
    have hcheb := sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := fun r => classSup (doorSievedCoeff_L M) H n q r)
    rwa [Finset.card_range] at hcheb
  -- ⟦the block sum⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff_L M) H n q r) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff_L M) H n q r) ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) H n q r) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hper : ∑ r ∈ Finset.range q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L M) H n q r) ^ 2
      ≤ (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
    calc ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) H n q r) ^ 2
        ≤ ∑ _r ∈ Finset.range q,
            (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :=
          Finset.sum_le_sum fun r hr =>
            hcl H hlo hhi q hq hqQ i hik r (Finset.mem_range.mp hr)
      _ = (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (subWindowSup (doorSievedCoeff_L M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) H n q r) ^ 2 := by rw [← hswap]; exact hstep1
    _ ≤ (q : ℝ) * ((q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left hper hq0
    _ = Bcl H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring

/-- **THE M4-7 DELIVERABLE — `m4_hbd_of_live_L`.**  The `hbd` socket of
`M4Exit.m4_exit_socket`, byte-plug-compatible, from

* the door-data gate bundle `M4DoorGates_L` (M4-8's own list, at the regime),
* the grade gate `M4GradeGate` (the row's budget line, §3-dischargeable),
* the M4-7 socket `M4SievedDoorSq_L` (the sieved mean square at the door), whose own premise
  is the band transport — the ⟦A2-5⟧ binder, supplied here by `m4_bandTransport`.

The door glue's constant `Cg` is opened ONCE, at the head of the statement
(`SieveGlue`'s ⟦ONE CONSTANT⟧ discipline), so the `M`-gate `24·Cg/δ ≤ M` is a legal
argument. -/
theorem m4_hbd_of_live_L :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (C δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
        M4SievedDoorSq_L R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ mrtDeliveredGrade C H * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R C δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ AdoorL M := by
    have h := AdoorL_ge hgates.hM
    omega
  have hG : 1 ≤ 3072 * M := by
    have := hgates.hM
    omega
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed⟧
  have hglueH := hglue (AdoorL M) (3072 * M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
      (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
            (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ mrtDeliveredGrade C H * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE ROW BRIDGE** (`m4_chiBlock_fixed_of_chiRow_L`).  The per-character row mean square
becomes the block sum of squared sieved-twisted window sums, at the grade `2·MS`:

* B-4's `M4BridgeIntegral.sum_Ioc_absWindowSum_sq_div_le_ladder` at the frequency `0` (both
  its fits are `le_rfl` and `M4Door.doorLadder_fit` — ⟦THE ENDPOINT LEDGER⟧: no boundary
  loss at all), with the coverage datum free at the block's own seam index set;
* `M4Join.sum_Ioc_le_two_mul_of_harmonic`, the harmonic→flat exchange, at the ladder's
  factor `2` and nothing else.

This is `M4ChiBlockMeanSq_L`'s body with `doorChiSup_L` replaced by the FIXED length `K = H`.
⟦R1⟧ — the maximal step from here to the sup — is the module header's first residue. -/
theorem m4_chiBlock_fixed_of_chiRow_L {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℝ}
    (hrow : M4ChiRowMeanSq_L R M k MS) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            ‖∑ m ∈ doorSievedWindow_L M H n, liouChi χ m‖ ^ 2
          ≤ 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hfit := doorLadder_fit R.x H i
  -- ⟦the coverage datum is free at the block's own seam index set⟧
  have hcov : ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      ∀ m ∈ Finset.Ioc n (n + H), m ∉ seamS0 (2 * doorLadder R.x H (i + 1))
          (doorLadder R.x H (i + 1) : ℝ) → doorChiCoeff_L χ M m = 0 :=
    hcov_of_seamS0 (doorChiCoeff_L χ M) (A := doorLadder R.x H (i + 1))
      (B := doorLadder R.x H i) (N := 2 * doorLadder R.x H (i + 1)) (H := H) le_rfl
      (by omega)
  -- ⟦the row datum, read at the removed phase⟧
  have hMS0 : 1 / ((doorLadder R.x H (i + 1) : ℕ) : ℝ)
      * (∫ y in ((doorLadder R.x H (i + 1) : ℕ) : ℝ)..(2
            * ((doorLadder R.x H (i + 1) : ℕ) : ℝ)),
          ‖((1 / (H : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L χ M) 0)
                  (seamS0 (2 * doorLadder R.x H (i + 1))
                    (doorLadder R.x H (i + 1) : ℝ)) y (H : ℝ)‖ ^ 2)
      ≤ MS H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi q hq hqQ i hik χ
  -- ⟦B-4: the harmonic-weighted block bound⟧
  have hladder := sum_Ioc_absWindowSum_sq_div_le_ladder (doorChiCoeff_L χ M)
    (seamS0 (2 * doorLadder R.x H (i + 1)) (doorLadder R.x H (i + 1) : ℝ)) 0
    (x := R.x) (H := H) (i := i) (MS := MS H) hH0 hxH hcov hMS0
  -- ⟦the exchange⟧
  have hflat := sum_Ioc_le_two_mul_of_harmonic (x := R.x) (H := H) (i := i)
    (f := fun n => ‖absWindowSum (doorChiCoeff_L χ M) H n 0‖ ^ 2)
    (V := (H : ℝ) ^ 2 * MS H) hxH (fun n _ => by positivity) hladder
  simp only [absWindowSum_doorChiCoeff_zero_L] at hflat
  have heq : 2 * ((H : ℝ) ^ 2 * MS H) * (doorLadder R.x H (i + 1) : ℝ)
      = 2 * MS H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring
  rw [heq] at hflat
  exact hflat

theorem le_doorChiSup_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) {K : ℕ} (hK : K ≤ H) :
    ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖ ≤ doorChiSup_L χ M H n :=
  Finset.le_sup' (f := fun K => ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖)
    (Finset.mem_Icc.mpr ⟨Nat.zero_le K, hK⟩)

/-- **THE M4-7 DELIVERABLE AT THE LEVER** — `m4_hbd_of_live_L` (:464).  The one proof diff:
`1 ≤ s13GK K M` comes from `one_le_s13GK` where the landed line used `omega`. -/
theorem m4_hbd_of_live_L_gk (K : ℕ) :
    ∃ Cg : ℝ, 1 ≤ Cg ∧
      ∀ (R : ChowlaRegime) (C δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
        M4DoorGates_L_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
        M4SievedDoorSq_L_gk K R M Braw →
          ∀ H : ℕ, ∀ [NeZero H], R.Hlo ≤ H → H ≤ R.Hhi → ∀ α : ℝ,
            NearRatTight (arcDen 12 H) H α →
              (∫ n, ‖absWindowSum lamCoeff H n α‖ ∂(logMeasure R.x R.ω))
                ≤ mrtDeliveredGrade C H * (H : ℝ) := by
  obtain ⟨Cg, hCg, hglue⟩ := m4_door_glue_liouville
  refine ⟨Cg, hCg, ?_⟩
  intro R C δ Braw M k hgates hBraw0 hgrade hsock H _ hlo hhi α harc
  -- ⟦the door's own scales, off the regime⟧
  have hA : 1 ≤ AdoorL M := by
    have h := AdoorL_ge hgates.hM
    omega
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hgates.hM
  have hHx : H + 1 ≤ R.x := by
    have hdiv : R.x / R.ω ≤ R.x / 2 := Nat.div_le_div_left R.hω (by norm_num)
    have hle : H ≤ R.x / 2 := le_trans (le_trans hhi R.hheadroom) hdiv
    have h2 : 2 ≤ R.x := R.hx
    omega
  -- ⟦M4-8's glue, consumed at the lever's base⟧
  have hglueH := hglue (AdoorL M) (s13GK K M) M 2 R.x R.ω H k α δ hA hG hgates.hM hgates.hδ
    hgates.hMδ R.hx R.hω R.hωx hgates.hlogω hHx (hgates.hreach H hlo hhi) hgates.hpow
    hgates.hcount (hgates.hblocks H hlo hhi)
  -- ⟦the socket, and §1's `L²→L¹` descent⟧
  have hsq := hsock m4_bandTransport H hlo hhi α harc
  have hcs := integral_logMeasure_le_sqrt_of_sq (x := R.x) (ω := R.ω) R.hx R.hω
    (f := fun n => ‖absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n α‖)
    (fun n => norm_nonneg _) hsq
  have hsplit : Real.sqrt (Braw H * (H : ℝ) ^ 2) = Real.sqrt (Braw H) * (H : ℝ) := by
    rw [Real.sqrt_mul (hBraw0 H), Real.sqrt_sq (Nat.cast_nonneg H)]
  rw [hsplit] at hcs
  -- ⟦the spelling bridge and the budget line⟧
  rw [integral_absWindowSum_lamCoeff_eq]
  calc (∫ n, ‖absWindowSum liouvilleC H n α‖ ∂(logMeasure R.x R.ω))
      ≤ (∫ n, ‖absWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
            (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) H n α‖ ∂(logMeasure R.x R.ω))
          + δ / 4 * (H : ℝ) + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := hglueH
    _ ≤ Real.sqrt (Braw H) * (H : ℝ) + δ / 4 * (H : ℝ)
          + 4 * 2 ^ k * (H : ℝ) / (R.x : ℝ) := by linarith
    _ = (Real.sqrt (Braw H) + δ / 4 + 4 * 2 ^ k / (R.x : ℝ)) * (H : ℝ) := by ring
    _ ≤ mrtDeliveredGrade C H * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (hgrade H hlo hhi) (Nat.cast_nonneg H)

/-- **THE `q`-GRADED COVERING SIDE AT THE LEVER** — `m4_cover_assembly_supQ_L` (:347). -/
theorem m4_cover_assembly_supQ_L_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bblk : ℕ → ℝ}
    (hgates : M4DoorGates_L_gk K Cg R M k δ) (hB0 : ∀ H : ℕ, 0 ≤ Bblk H)
    (hblk : M4BlockMeanSqSupQ_L_gk K R M k Bblk) :
    M4SievedDoorSqSup_L_gk K R M (fun H => 3 * Bblk H) := by
  intro _ H _ hlo hhi b q hq hqQ
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hP : (0 : ℝ) ≤ Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by
    have := hB0 H; positivity
  have hmain := integral_door_cover_le_clean (x := R.x) (ω := R.ω) (H := H) (k := k)
    (g := fun n => (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2)
    (P := Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
    R.hx R.hω R.hωx hgates.hlogω hgates.hcount (fun n => by positivity) hP hxH
    (hgates.hreach H hlo hhi) hgates.hpow (hblk H hlo hhi b q hq hqQ)
  simp only [doorSievedCoeff_L_gk] at hmain
  have heq : 3 * (Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2)
      = 3 * Bblk H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 := by ring
  rw [heq] at hmain
  exact hmain

/-- **THE ASSEMBLY AT THE LEVER** — `m4_blockMeanSqSupQ_of_classMeanSq_L` (:256). -/
theorem m4_blockMeanSqSupQ_of_classMeanSq_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ}
    {Bcl : ℕ → ℝ}
    (hcl : M4ClassBlockMeanSq_L_gk K R M k Bcl) : M4BlockMeanSqSupQ_L_gk K R M k Bcl := by
  intro H hlo hhi b q hq hqQ i hik
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  -- ⟦pointwise: the split, then Chebyshev⟧
  have hpt : ∀ n : ℕ,
      (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
            (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2 := by
    intro n
    have hsplit := subWindowSup_le_sum_classSup (doorSievedCoeff_L_gk K M) H n hq b
    have h0 := subWindowSup_nonneg (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))
    have hsq : (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ r ∈ Finset.range q, classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2 := by
      nlinarith
    refine hsq.trans ?_
    have hcheb := sq_sum_le_card_mul_sum_sq
      (s := Finset.range q) (f := fun r => classSup (doorSievedCoeff_L_gk K M) H n q r)
    rwa [Finset.card_range] at hcheb
  -- ⟦the block sum⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q : ℝ) * ∑ r ∈ Finset.range q,
            (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q : ℝ) * ∑ r ∈ Finset.range q, (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
      = (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  have hper : ∑ r ∈ Finset.range q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
      ≤ (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
    calc ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
        ≤ ∑ _r ∈ Finset.range q,
            (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) :=
          Finset.sum_le_sum fun r hr =>
            hcl H hlo hhi q hq hqQ i hik r (Finset.mem_range.mp hr)
      _ = (q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        (subWindowSup (doorSievedCoeff_L_gk K M) H n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (q : ℝ) * ∑ r ∈ Finset.range q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2 := by rw [← hswap]; exact hstep1
    _ ≤ (q : ℝ) * ((q : ℝ) * (Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ))) :=
        mul_le_mul_of_nonneg_left hper hq0
    _ = Bcl H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by ring

/-- **THE HOOK AT THE LEVER, `q`-GRADED** — `m4_sievedDoorSq_of_sup_L` (:434) verbatim. -/
theorem m4_sievedDoorSq_of_sup_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {Braw Braw' : ℕ → ℝ}
    (hgrade : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * Braw' H) ≤ Braw H)
    (hsup : M4SievedDoorSqSup_L_gk K R M Braw') : M4SievedDoorSq_L_gk K R M Braw := by
  intro htr H _ hlo hhi α hα
  have hH : 0 < H := Nat.pos_of_ne_zero (NeZero.ne H)
  obtain ⟨b, q, hq, hqQ, hd⟩ := hα
  set c := memSCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC
    with hc
  set β : ℝ := (b : ℝ) / (q : ℝ) with hβ
  -- ⟦the pointwise drift bound, squared — THE `q`-GRADING KEPT (no `hden` demotion)⟧
  have hpt : ∀ n : ℕ, ‖absWindowSum c H n α‖ ^ 2
      ≤ (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * (subWindowSup c H n β) ^ 2 := by
    intro n
    have h := norm_absWindowSum_le_drift (B₅ := 12) (H := H) (q := q) (n := n)
      (β := β) (θ := α - β) hq hH hd c
    have he : β + (α - β) = α := by ring
    rw [he] at h
    calc ‖absWindowSum c H n α‖ ^ 2
        ≤ ((1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) * subWindowSup c H n β) ^ 2 := by
          gcongr
      _ = (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
            * (subWindowSup c H n β) ^ 2 := by ring
  -- ⟦the integral, and the grade⟧
  calc (∫ n, ‖absWindowSum c H n α‖ ^ 2 ∂(logMeasure R.x R.ω))
      ≤ ∫ n, (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * (subWindowSup c H n β) ^ 2
          ∂(logMeasure R.x R.ω) := integral_logMeasure_mono hpt
    _ = (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * ∫ n, (subWindowSup c H n β) ^ 2 ∂(logMeasure R.x R.ω) :=
        integral_logMeasure_const_mul _ _
    _ ≤ (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * (Braw' H * (q : ℝ) ^ 2 * (H : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hsup htr H hlo hhi b q hq hqQ) (sq_nonneg _)
    _ = ((1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * Braw' H))
          * (H : ℝ) ^ 2 := by ring
    _ ≤ Braw H * (H : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (hgrade H q hlo hhi hq hqQ) (sq_nonneg _)

theorem le_doorChiSup_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M H n : ℕ) {Kw : ℕ}
    (hK : Kw ≤ H) :
    ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖ ≤ doorChiSup_L_gk K χ M H n :=
  Finset.le_sup' (f := fun Kw => ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖)
    (Finset.mem_Icc.mpr ⟨Nat.zero_le Kw, hK⟩)

/-- **⟦R1⟧, STATED** (`M4ChiMaximalStep_L`).  The one inequality between §6's fixed-length
block bound and §3's input: the sub-window sup's block mean square against the fixed-length
one, at a grade factor `Cmax`.  A dyadic decomposition of the partial sums gives
`Cmax ≈ (log H)²`, which the exponent gap absorbs; the trivial route
`sup² ≤ ∑_{K ≤ H}` gives `Cmax = H + 1` and is fatal.  Named here so the S11 spine's
consumption list carries it explicitly rather than by implication. -/
def M4ChiMaximalStep_L (R : ChowlaRegime) (M k : ℕ) (Cmax : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup_L χ M H n) ^ 2
        ≤ Cmax H
          * ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
              ‖∑ m ∈ doorSievedWindow_L M H n, liouChi χ m‖ ^ 2

/-- **⟦R1⟧ AT THE LEVER** — `M4ChiMaximalStep_L` (:797). -/
def M4ChiMaximalStep_L_gk (K : ℕ) (R : ChowlaRegime) (M k : ℕ) (Cmax : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
    ∀ i < k, ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (doorChiSup_L_gk K χ M H n) ^ 2
        ≤ Cmax H
          * ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
              ‖∑ m ∈ doorSievedWindow_L_gk K M H n, liouChi χ m‖ ^ 2

/-- **⟦THE `E_binder` WIRE — UNCONDITIONAL⟧** (`m4_capE_at_door_L`).
`M4CapWire.DoorCapBase.E_binder` at the door datum, from `DoorCapErrWS_L` alone.

This is `m4_capE_at_door_of_hcoef_L` with its fatal hypothesis GONE: where that theorem asks
the GLOBAL block factorization — the contract `M4Assembly.doorRows_global_hcoef_kills_block`
refutes at a window-cut datum — this one asks only the STRICT relativized law, which the door
datum satisfies (`M4RowsChiZero.DoorRowZeroBase.coefWS` is a landed carried field of the
existing bundle). -/
theorem m4_capE_at_door_L {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ} {Tann E Mtail : ℝ}
    (h : DoorCapErrWS_L M Nd q Xd P Q b cf Tann E Mtail) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ E := by
  obtain ⟨hXd, hNd, hH2, hHle, hP1, hT, hb1, hcf1, hcoef, htail, hE⟩ := h
  subst hXd
  refine le_trans ?_ hE
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hasupp : ∀ n : ℕ, winCutH Xd (doorCoeffU_L M) n ≠ 0 →
      ((Xd : ℕ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    constructor
    · exact_mod_cast h1
    · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  exact ramErr_meanSq_all_chi_ws_priced q (H83 ((Xd : ℕ) : ℝ) theta293) hH2 (2 * Xd) Xd P Q
    hNd le_rfl hN2 hHle hP1 (winCutH Xd (doorCoeffU_L M)) b cf hcoef
    (fun n => norm_doorRowDatumU_le_one_L M Xd n) hb1 hcf1 hasupp Mtail htail Tann hT

/-- `m4_capE_at_door_L` (:466), at the lever. -/
theorem m4_capE_at_door_L_gk (K : ℕ) {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ}
    {Tann E Mtail : ℝ}
    (h : DoorCapErrWS_L_gk K M Nd q Xd P Q b cf Tann E Mtail) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU_L_gk K M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ E := by
  obtain ⟨hXd, hNd, hH2, hHle, hP1, hT, hb1, hcf1, hcoef, htail, hE⟩ := h
  subst hXd
  refine le_trans ?_ hE
  have hN2 : (((2 * Xd : ℕ)) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by push_cast; exact le_rfl
  have hasupp : ∀ n : ℕ, winCutH Xd (doorCoeffU_L_gk K M) n ≠ 0 →
      ((Xd : ℕ) : ℝ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    constructor
    · exact_mod_cast h1
    · have : ((n : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
  exact ramErr_meanSq_all_chi_ws_priced q (H83 ((Xd : ℕ) : ℝ) theta293) hH2 (2 * Xd) Xd P Q
    hNd le_rfl hN2 hHle hP1 (winCutH Xd (doorCoeffU_L_gk K M)) b cf hcoef
    (fun n => norm_doorRowDatumU_le_one_L_gk K M Xd n) hb1 hcf1 hasupp Mtail htail Tann hT

/-- **THE WAVE'S EXIT, SPLIT** (`m4_door_contradiction_of_live_split_L`) — the twin of
`m4_door_contradiction_of_live_L` (:537): `m4_exit_socket_split ∘ m4_hbd_of_live_split_L`.

⟦THE REGISTER, split form⟧ is the landed one with `C` deleted and the budget line re-cut:

* `M4DoorGates_L Cg R M k δ` — UNCHANGED (M4-8's own list; `doorCount_gates` is still the
  witness at `k := doorCount R.ω`);
* `0 ≤ Braw H` — UNCHANGED;
* `M4GradeGateSplit R δ₀ δ Braw k` — the budget line at the constant grade;
* `M4SievedDoorSq_L R M Braw` — UNCHANGED (the socket, at the band transport).

The conclusion `¬ logChowla2Fails R.eps R.x R.ω` is byte-identical to the landed one. -/
theorem m4_door_contradiction_of_live_split_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4SievedDoorSq_L R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_split_L
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  -- the socket's tower-law conjunct (⟦THE NAMED AMENDMENT⟧) is not consumed at this stage
  obtain ⟨R, hReps, hU1, hRg, -, hR⟩ := hexit U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R δ₀ δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **THE WAVE'S EXIT, SPLIT, AT THE LEVER** — `m4_door_contradiction_of_live_split_L`
(:771). -/
theorem m4_door_contradiction_of_live_split_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4SievedDoorSq_L_gk K R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_split_L_gk K
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket_split
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, -, hR⟩ := hexit U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R δ₀ δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **THE `q`-FREE READING** — `qgraded_drift_price_le` applied once, so a supplier with no
`q`-uniformity to spare still discharges the socket, at the ABSOLUTE drift price
`(1 + 2π)²·arcDen 12 H ²`.  This is the shape `M4Join.m4_wave_exit_sup` reads. -/
theorem m4_sievedDoorSq_of_sup_uniform_L {R : ChowlaRegime} {M : ℕ} {Braw Braw' : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Braw' H)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi) ^ 2 * (arcDen 12 H ^ 2 * Braw' H) ≤ Braw H)
    (hsup : M4SievedDoorSqSup_L R M Braw') : M4SievedDoorSq_L R M Braw :=
  m4_sievedDoorSq_of_sup_L
    (fun H _q hlo hhi hq hqQ =>
      le_trans (qgraded_drift_price_le hq hqQ (hB0 H)) (hgrade H hlo hhi)) hsup

/-- **THE `q`-FREE READING AT THE LEVER** — `m4_sievedDoorSq_of_sup_uniform_L` (:475). -/
theorem m4_sievedDoorSq_of_sup_uniform_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Braw Braw' : ℕ → ℝ}
    (hB0 : ∀ H : ℕ, 0 ≤ Braw' H)
    (hgrade : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      (1 + 2 * Real.pi) ^ 2 * (arcDen 12 H ^ 2 * Braw' H) ≤ Braw H)
    (hsup : M4SievedDoorSqSup_L_gk K R M Braw') : M4SievedDoorSq_L_gk K R M Braw :=
  m4_sievedDoorSq_of_sup_L_gk K
    (fun H _q hlo hhi hq hqQ =>
      le_trans (qgraded_drift_price_le hq hqQ (hB0 H)) (hgrade H hlo hhi)) hsup

/-- **⟦THE RATIFIED TARGET REGISTER⟧ — `m4_wave_exit_sup_split_L`**, the twin of
`m4_wave_exit_sup_L` (:467) and D-1 option (b) of the second-road freeze v2.

The same wave exit entered at B-2's carrier — `M4BlockMeanSqSup_L` → (§2) `M4SievedDoorSqSup_L` →
(B-2's `m4_sievedDoorSq_of_sup_uniform_L`) `M4SievedDoorSq_L` →
`M4Close.m4_door_contradiction_of_live_split` — with the door consumed at the head's own
constant `δ₀`.

⟦THE REGISTER, sup split form⟧

1. `M4DoorGates_L Cg R M k δ` — UNCHANGED, `hMδ` included (⟦UNTOUCHABLE⟧, `M4Exit` §7).
2. `∀ H, 0 ≤ Bblk H`, `∀ H, 0 ≤ Braw H` — UNCHANGED.
3. ~~`0 ≤ C`~~ — GONE.
4′. THE DRIFT PRICE, at B-2's `q`-free reading:
    `(1 + 2π)²·(arcDen 12 H)²·(3·B_blk H) ≤ Braw H` on the window range.  **Carried at its
    landed shape.**  Wave ④ re-cuts this one conjunct to the composed blocked-drift ×
    stratified-Gauss × χ-summed supply, under which the drift and both class `q`'s are `O(1)`
    together; nothing else in this register moves when it does.
5′. `M4GradeGateSplit R δ₀ δ Braw k` — the budget line at the constant grade.
6′. `M4BlockMeanSqSup_L R M k Bblk` — the per-block sup mean square at the rationals.
    **`q`-free**, which is the whole reason this register was chosen over `m4_wave_closed_L`'s
    (whose `hdrift` hard-wires `q²` and whose `Bcl` is woven into three conjuncts).

The conclusion `¬ logChowla2Fails R.eps R.x R.ω` is byte-identical to the landed one. -/
theorem m4_wave_exit_sup_split_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              (1 + 2 * Real.pi) ^ 2 * (arcDen 12 H ^ 2 * (3 * Bblk H)) ≤ Braw H) →
            M4GradeGateSplit R δ₀ δ Braw k →
            M4BlockMeanSqSup_L R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_split_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain U1floor g
  refine ⟨R, hReps, hU1, hRg,
    fun δ Braw Bblk M k hgates hB0 hBraw0 hdrift hgrade hblk => ?_⟩
  exact hR δ Braw M k hgates hBraw0 hgrade
    (m4_sievedDoorSq_of_sup_uniform_L (fun H => by have := hB0 H; linarith) hdrift
      (m4_cover_assembly_sup_L hgates hB0 hblk))

/-- **THE MAXIMAL STEP AT THE LEVER** — `m4_chiBlockMeanSq_of_shiftBlock_L` (:838). -/
theorem m4_chiBlockMeanSq_of_shiftBlock_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (htr : ∀ j H : ℕ, j < j₀ → F j H ≤ Ftr H)
    (hfix : M4ChiShiftBlockMeanSq_L_gk K R M k F) :
    M4ChiBlockMeanSq_L_gk K R M k (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  set L := Nat.log 2 H with hL
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set S : ℝ := ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j with hS
  have hS0 : (0 : ℝ) ≤ S := (geom_weight_sum_pos L).le
  -- ⟦STEP 1⟧ the pointwise maximal bound (§3), at the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M H n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, S
          * ∑ j ∈ Finset.range (L + 1),
              (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L_gk K χ M H n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, S
        * ∑ j ∈ Finset.range (L + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hjt : ∀ j ∈ Finset.range (L + 1), ∀ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
      ∑ n ∈ Finset.Ioc A B, X j t n ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    intro j hj t ht
    have hjL : j ≤ L := by
      have := Finset.mem_range.mp hj
      omega
    have ht' : t ≤ H / 2 ^ (j + 1) := by
      have := Finset.mem_range.mp ht
      omega
    have hs : 2 ^ (j + 1) * t ≤ H := by
      calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (H / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht'
        _ = H / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
        _ ≤ H := Nat.div_mul_le_self H (2 ^ (j + 1))
    have hre : ∑ n ∈ Finset.Ioc A B, X j t n
        = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 :=
      sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
    rw [hre]
    exact hfix H hlo hhi q hq hqQ i hik χ j hjL _ hs
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j => (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg H j
  have hj : ∀ j ∈ Finset.range (L + 1),
      (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hle : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (H / 2 ^ (j + 1) + 1), F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) :=
      Finset.sum_le_sum fun t ht => hjt j hjm t ht
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (F j H * (A : ℝ)) * W j := by
      calc ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
          ≤ (((H / 2 ^ (j + 1) : ℕ) + 1 : ℕ) : ℝ) * (F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)) :=
            hle
        _ = (F j H * (A : ℝ)) * W j := by
            simp only [hW]
            push_cast
            ring
    calc (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((F j H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT: the large lengths against the weighted full count, the small ones
  -- against the weighted head.  This is the only place the floor `j₀` is read.
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hlarge : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
    have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ := (Finset.mem_filter.mp hjm).2
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (han j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range (L + 1), (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hFanA (hWw0 j))
      _ = Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
    have hsub : (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
            (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ : j < j₀ := by have := (Finset.mem_filter.mp hjm).2; omega
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (htr j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range j₀, (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hFtrA (hWw0 j))
      _ = Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (L + 1),
        (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
        + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum hj) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (L + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, prefactor included (§4)
  have hHne : ((H : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
    exact ne_of_gt this
  have hfull : S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j ≤ 54 / 5 * (H : ℝ) ^ 2 := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_le hH0
  have hhead : S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀ := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_small_le hH0 j₀
  have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
  have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M H n) ^ 2
      ≤ S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ S * (Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
          + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hS0
    _ = Fan H * (A : ℝ) * (S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j)
          + Ftr H * (A : ℝ) * (S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ Fan H * (A : ℝ) * (54 / 5 * (H : ℝ) ^ 2)
          + Ftr H * (A : ℝ) * (9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hFanA
        have h2 := mul_le_mul_of_nonneg_left hhead hFtrA
        linarith
    _ = m4BclGraded j₀ Fan Ftr H * (H : ℝ) ^ 2 * (A : ℝ) := by
        unfold m4BclGraded m4Cmax
        rw [← hL]
        field_simp

/-- **⟦R1⟧, EXECUTED, LENGTH-GRADED** (`m4_chiBlockMeanSq_of_shiftBlock_L`) — the sub-window
sup's block mean square from the fixed dyadic lengths, at the SPLIT price `m4BclGraded`.

The trivial route `sup² ≤ ∑_{K ≤ H}` would cost `H+1` and is fatal; this route costs one
log, because the `≤ log₂H+1` dyadic pieces are paid once by Chebyshev and the offsets at
scale `j` number only `⌊H/2^{j+1}⌋+1`.

⟦THE SPLIT⟧ the length-graded input `F j H` is charged through TWO envelopes at the named
floor `j₀`: `Fan` on the lengths the capstone can actually speak about (`j₀ ≤ j`, where §4's
full count `3H²` applies) and `Ftr` on the lengths below it (`j < j₀`, where §4's small count
`2H·4^{j₀}` applies — linear in `H`).  Neither envelope is required to be small; the
arithmetic of the two counts is what makes the small half free (`m4SmallGradeFits`). -/
theorem m4_chiBlockMeanSq_of_shiftBlock_L {R : ChowlaRegime} {M k : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (htr : ∀ j H : ℕ, j < j₀ → F j H ≤ Ftr H)
    (hfix : M4ChiShiftBlockMeanSq_L R M k F) :
    M4ChiBlockMeanSq_L R M k (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi q hq hqQ i hik χ
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  set L := Nat.log 2 H with hL
  set A := doorLadder R.x H (i + 1) with hA
  set B := doorLadder R.x H i with hB
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set S : ℝ := ∑ j ∈ Finset.range (L + 1), (3 / 2 : ℝ) ^ j with hS
  have hS0 : (0 : ℝ) ≤ S := (geom_weight_sum_pos L).le
  -- ⟦STEP 1⟧ the pointwise maximal bound (§3), at the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M H n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, S
          * ∑ j ∈ Finset.range (L + 1),
              (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L χ M H n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, S
        * ∑ j ∈ Finset.range (L + 1),
            (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hjt : ∀ j ∈ Finset.range (L + 1), ∀ t ∈ Finset.range (H / 2 ^ (j + 1) + 1),
      ∑ n ∈ Finset.Ioc A B, X j t n ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) := by
    intro j hj t ht
    have hjL : j ≤ L := by
      have := Finset.mem_range.mp hj
      omega
    have ht' : t ≤ H / 2 ^ (j + 1) := by
      have := Finset.mem_range.mp ht
      omega
    have hs : 2 ^ (j + 1) * t ≤ H := by
      calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (H / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht'
        _ = H / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
        _ ≤ H := Nat.div_mul_le_self H (2 ^ (j + 1))
    have hre : ∑ n ∈ Finset.Ioc A B, X j t n
        = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2 :=
      sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
    rw [hre]
    exact hfix H hlo hhi q hq hqQ i hik χ j hjL _ hs
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j => (((H / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg H j
  have hj : ∀ j ∈ Finset.range (L + 1),
      (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hle : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (H / 2 ^ (j + 1) + 1), F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) :=
      Finset.sum_le_sum fun t ht => hjt j hjm t ht
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (F j H * (A : ℝ)) * W j := by
      calc ∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
          ≤ (((H / 2 ^ (j + 1) : ℕ) + 1 : ℕ) : ℝ) * (F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)) :=
            hle
        _ = (F j H * (A : ℝ)) * W j := by
            simp only [hW]
            push_cast
            ring
    calc (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((F j H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT: the large lengths against the weighted full count, the small ones
  -- against the weighted head.  This is the only place the floor `j₀` is read.
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hlarge : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
    have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ := (Finset.mem_filter.mp hjm).2
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (han j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range (L + 1), (Fan H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hFanA (hWw0 j))
      _ = Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
        (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
      ≤ Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
    have hsub : (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
          (F j H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j)
        ≤ ∑ j ∈ (Finset.range (L + 1)).filter (fun j => ¬ j₀ ≤ j),
            (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
          refine Finset.sum_le_sum fun j hjm => ?_
          have hj₀ : j < j₀ := by have := (Finset.mem_filter.mp hjm).2; omega
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (htr j H hj₀) hA0) (hWw0 j)
      _ ≤ ∑ j ∈ Finset.range j₀, (Ftr H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hFtrA (hWw0 j))
      _ = Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (L + 1),
        (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
        + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum hj) ?_
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (L + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, prefactor included (§4)
  have hHne : ((H : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
    exact ne_of_gt this
  have hfull : S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j ≤ 54 / 5 * (H : ℝ) ^ 2 := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_le hH0
  have hhead : S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀ := by
    rw [hS, hW, hL]
    exact dyadic_count_weight_geom_small_le hH0 j₀
  have hFanA : (0 : ℝ) ≤ Fan H * (A : ℝ) := mul_nonneg (hFan0 H) hA0
  have hFtrA : (0 : ℝ) ≤ Ftr H * (A : ℝ) := mul_nonneg (hFtr0 H) hA0
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M H n) ^ 2
      ≤ S * ∑ j ∈ Finset.range (L + 1),
          (∑ t ∈ Finset.range (H / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ S * (Fan H * (A : ℝ) * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j
          + Ftr H * (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hS0
    _ = Fan H * (A : ℝ) * (S * ∑ j ∈ Finset.range (L + 1), W j * (2 / 3 : ℝ) ^ j)
          + Ftr H * (A : ℝ) * (S * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ Fan H * (A : ℝ) * (54 / 5 * (H : ℝ) ^ 2)
          + Ftr H * (A : ℝ) * (9 / 2 * (H : ℝ) * (3 / 2 : ℝ) ^ L * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ L * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hFanA
        have h2 := mul_le_mul_of_nonneg_left hhead hFtrA
        linarith
    _ = m4BclGraded j₀ Fan Ftr H * (H : ℝ) ^ 2 * (A : ℝ) := by
        unfold m4BclGraded m4Cmax
        rw [← hL]
        field_simp

/-- **THE WAVE'S ANALYTIC ITEM, FROM THE GRADED ROW DATUM** — `M4ChiBlockMeanSq_L` at the grade
`m4BclGraded j₀ (2·MSan) (2·MStr) H`,
⟦R1⟧ discharged.  The bridge's own factor `2` (the harmonic→flat exchange) rides both
envelopes. -/
theorem m4_chiBlockMeanSq_of_dyadicRow_L {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (htr : ∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H)
    (hrow : M4ChiDyadicRowMeanSq_L R M k MS) :
    M4ChiBlockMeanSq_L R M k
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_chiBlockMeanSq_of_shiftBlock_L (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_
    (m4_chiShiftBlock_of_dyadicRow_L hrow)
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro j H hj; have := htr j H hj; linarith

/-- **THE SOCKET EXIT** (`m4_sievedDoorSq_of_classMeanSq_L`) — `M4ClassPrice` §7's steps 3–5,
entered at the mean-square datum:

3. `m4_blockMeanSqSupQ_of_classMeanSq_L` (§2) assembles `M4BlockMeanSqSupQ_L`;
4. `M4ClassPrice.m4_cover_assembly_supQ` covers, at the absolute factor `3`;
5. `M4BridgePhase.m4_sievedDoorSq_of_sup` discharges `M4Close.M4SievedDoorSq`, the split's
   `q²` meeting the drift's `1/q²` exactly.

This is `M4ClassPrice.m4_sievedDoorSq_of_classPrice` with its input re-cut, and nothing
else. -/
theorem m4_sievedDoorSq_of_classMeanSq_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {Bcl Braw : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
        ≤ Braw H)
    (hcl : M4ClassBlockMeanSq_L R M k Bcl) :
    M4SievedDoorSq_L R M Braw :=
  m4_sievedDoorSq_of_sup_L hdrift
    (m4_cover_assembly_supQ_L hgates hBcl0 (m4_blockMeanSqSupQ_of_classMeanSq_L hcl))

/-- **THE COMPOSE'S SHAPE, pinned once.**  The final compose is:

1. the un-phased row (`M4RowMeanSqUnphased_L`) supplies the χ-uniform sieved-window bounds;
2. `m4_class_price_L` (§3) prices every class at both branch windows;
3. `m4_blockMeanSqSupQ_of_classPrice_L` (§4) assembles them into `M4BlockMeanSqSupQ_L`;
4. `m4_cover_assembly_supQ_L` (§4) covers, at the absolute factor `3`;
5. `M4BridgePhase.m4_sievedDoorSq_of_sup` (the `q`-graded socket) discharges
   `M4Close.M4SievedDoorSq`, with the split's `q²` meeting the drift's `1/q²` exactly;
6. `m4_gradeGate_direct` (§6) supplies the budget line without spending the exponent gap.

Steps 3–5 are landed here as one statement, so only step 1's supply and step 2's two-window
instantiation remain for the compose. -/
theorem m4_sievedDoorSq_of_classPrice_L {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ} {δ : ℝ}
    {B : ℕ → ℝ} {Braw : ℕ → ℝ}
    (hgates : M4DoorGates_L Cg R M k δ)
    (hgrade : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
          * ((q : ℝ) ^ 2 * (3 * (B H ^ 2 / (H : ℝ) ^ 2))) ≤ Braw H)
    (hclass : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
        ∀ K, K ≤ H → ∀ r, r < q →
          ‖∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ ≤ B H) :
    M4SievedDoorSq_L R M Braw :=
  m4_sievedDoorSq_of_sup_L hgrade
    (m4_cover_assembly_supQ_L hgates (fun H => by positivity)
      (m4_blockMeanSqSupQ_of_classPrice_L hclass))

/-- **THE WAVE'S EXIT — `m4_door_contradiction_of_live_L`.**

`m4_exit_socket ∘ m4_hbd_of_live_L`: `ε` and `δ₀` are fixed first (the budget head's own honest
choice), then for every `C_MRT ≥ 0` and every extra floor / outer-scale demand there is a
regime `R` at which **log-Chowla-2 does not fail**, conditional on exactly this register:

* `M4DoorGates_L Cg R M k δ` — M4-8's door-glue list (the `24Cg/δ` `M`-gate, `log ω ≥ 4`, the
  ladder's three gates, HS-3 per block).  Owed by the regime/door numerology;
  `doorCount_gates` is the witness at `k := doorCount R.ω`.
* `0 ≤ Braw H` — the socket's grade is a grade.  Owed by the supplier.
* `M4GradeGate R C δ Braw k` — the budget line.  Owed to `m4_gradeGate_of_pricing` (§3)
  plus the pricing (§2).
* `M4SievedDoorSq_L R M Braw` — THE SOCKET: the sieved λ mean square at the door, at every
  tight-major `α`, given the band transport (⟦A2-5⟧).  Owed by ⟦THE FIVE OPEN BRIDGES⟧
  (module header).

Nothing else is open on the M4 road: `mrtUniformityXi_of_absWindowBound_twelve` (the arc),
`log_chowla_two_budget_head_g` (the head), `contradiction_of_mrtDoorXi` (the collision) and
`m4_door_glue` (the sieve insert) are all landed and consumed. -/
theorem m4_door_contradiction_of_live_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
            M4SievedDoorSq_L R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_L
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, _, _, _, hR⟩ := hexit C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R C δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **THE χ-DATUM, ASSEMBLED** (`m4_chiBlockMeanSq_of_row_L`).  §6's bridge composed with
⟦R1⟧: the wave's analytic item at the grade `Cmax H·2·MS H`, from the capstone's own
currency.  Every step between `ThmA2.thm_a2'_of_rows` and `M4ChiBlockMeanSq_L` is now either
landed or one of the three named residues. -/
theorem m4_chiBlockMeanSq_of_row_L {R : ChowlaRegime} {M k : ℕ} {MS Cmax : ℕ → ℝ}
    (hCmax0 : ∀ H : ℕ, 0 ≤ Cmax H) (hmax : M4ChiMaximalStep_L R M k Cmax)
    (hrow : M4ChiRowMeanSq_L R M k MS) :
    M4ChiBlockMeanSq_L R M k (fun H => Cmax H * (2 * MS H)) := by
  intro H hlo hhi q hq hqQ i hik χ
  refine le_trans (hmax H hlo hhi q hq hqQ i hik χ) ?_
  have hb := m4_chiBlock_fixed_of_chiRow_L hrow H hlo hhi q hq hqQ i hik χ
  have hle := mul_le_mul_of_nonneg_left hb (hCmax0 H)
  refine le_trans hle (le_of_eq ?_)
  ring

/-- **THE POINTWISE HALF** (`classSup_le_inv_totient_sum_doorChiSup_L`).  For a class coprime
to `q`, the class sup is under the χ-average of the twisted sups.  Route, at each length `K`:
`M4ClassPrice.sum_windowClass_memSCoeff` (the two filters commute) then
`M4BridgeResidue.norm_sum_residueClassOn_liou_le` (the decomposition, `χ(r)` unimodular). -/
theorem classSup_le_inv_totient_sum_doorChiSup_L {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (M H n : ℕ) :
    classSup (doorSievedCoeff_L M) H n q r
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L χ M H n := by
  refine classSup_le fun K hK => ?_
  have hfilt : ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
      = ∑ m ∈ residueClassOn q r (doorSievedWindow_L M K n), liouvilleC m := by
    simpa only [doorSievedCoeff_L, doorSievedWindow_L] using
      sum_windowClass_memSCoeff (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC K n q r
  rw [hfilt]
  refine le_trans (norm_sum_residueClassOn_liou_le hcop (doorSievedWindow_L M K n)) ?_
  have hφ : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun χ _ => le_doorChiSup_L χ M H n hK

/-- **THE WAVE'S EXIT AT THE LEVER** — `m4_door_contradiction_of_live_L` (:537). -/
theorem m4_door_contradiction_of_live_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Braw H) → M4GradeGate R C δ Braw k →
            M4SievedDoorSq_L_gk K R M Braw →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, hCg, hhbd⟩ := m4_hbd_of_live_L_gk K
  obtain ⟨ε, δ₀, hε, hδ₀, hexit⟩ := m4_exit_socket
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, _, _, _, hR⟩ := hexit C hC U1floor g
  exact ⟨R, hReps, hU1, hRg, fun δ Braw M k hgates hBraw0 hgrade hsock =>
    hR (hhbd R C δ Braw M k hgates hBraw0 hgrade hsock)⟩

/-- **THE SOCKET EXIT AT THE LEVER** — `m4_sievedDoorSq_of_classMeanSq_L` (:318). -/
theorem m4_sievedDoorSq_of_classMeanSq_L_gk (K : ℕ) {Cg : ℝ} {R : ChowlaRegime} {M k : ℕ}
    {δ : ℝ} {Bcl Braw : ℕ → ℝ}
    (hgates : M4DoorGates_L_gk K Cg R M k δ) (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hdrift : ∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
      (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
        ≤ Braw H)
    (hcl : M4ClassBlockMeanSq_L_gk K R M k Bcl) :
    M4SievedDoorSq_L_gk K R M Braw :=
  m4_sievedDoorSq_of_sup_L_gk K hdrift
    (m4_cover_assembly_supQ_L_gk K hgates hBcl0 (m4_blockMeanSqSupQ_of_classMeanSq_L_gk K hcl))

/-- **THE POINTWISE HALF AT THE LEVER** — `classSup_le_inv_totient_sum_doorChiSup_L`
(:395). -/
theorem classSup_le_inv_totient_sum_doorChiSup_L_gk (K : ℕ) {q : ℕ} [NeZero q] {r : ℕ}
    (hcop : Nat.Coprime q r) (M H n : ℕ) :
    classSup (doorSievedCoeff_L_gk K M) H n q r
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L_gk K χ M H n := by
  refine classSup_le fun Kw hKw => ?_
  have hfilt : ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
      = ∑ m ∈ residueClassOn q r (doorSievedWindow_L_gk K M Kw n), liouvilleC m := by
    simpa only [doorSievedCoeff_L_gk, doorSievedWindow_L_gk] using
      sum_windowClass_memSCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC Kw n q r
  rw [hfilt]
  refine le_trans (norm_sum_residueClassOn_liou_le hcop (doorSievedWindow_L_gk K M Kw n)) ?_
  have hφ : (0 : ℝ) < (q.totient : ℝ) := totient_cast_pos q
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Finset.sum_le_sum fun χ _ => le_doorChiSup_L_gk K χ M H n hKw

/-- **THE WAVE'S EXIT, AT THE PER-BLOCK HYPOTHESIS.**  `m4_door_contradiction_of_live_L` with
its socket replaced by `M4BlockMeanSq_L`: for every `C_MRT ≥ 0` and every floor/outer-scale
demand there is a regime at which log-Chowla-2 does not fail, conditional on

* `M4DoorGates_L Cg R M k δ` — M4-8's door list (unchanged; the assembly reads its ladder data),
* `0 ≤ B_blk H` — the block grade is a grade,
* `M4GradeGate R C δ (3·B_blk) k` — the budget line at the assembled grade
  (`m4_gradeGate_of_block_pricing`),
* `M4BlockMeanSq_L R M k B_blk` — **THE PER-BLOCK MEAN SQUARE**, owed by bridges 1–4.

Nothing on the covering side remains: the harmonic weight, the ladder sum, the `log ω`
absorption and the `L²→L¹` descent are all landed and consumed. -/
theorem m4_door_contradiction_of_blockMeanSq_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) →
            M4GradeGate R C δ (fun H => 3 * Bblk H) k →
            M4BlockMeanSq_L R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Bblk M k hgates hB0 hgrade hblk => ?_⟩
  exact hR δ (fun H => 3 * Bblk H) M k hgates
    (fun H => by have := hB0 H; linarith) hgrade (m4_cover_assembly_L hgates hB0 hblk)

/-- **THE WAVE'S EXIT AT THE PER-BLOCK HYPOTHESIS, AT THE LEVER** —
`m4_door_contradiction_of_blockMeanSq_L` (:488). -/
theorem m4_door_contradiction_of_blockMeanSq_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) →
            M4GradeGate R C δ (fun H => 3 * Bblk H) k →
            M4BlockMeanSq_L_gk K R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_L_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Bblk M k hgates hB0 hgrade hblk => ?_⟩
  exact hR δ (fun H => 3 * Bblk H) M k hgates
    (fun H => by have := hB0 H; linarith) hgrade (m4_cover_assembly_L_gk K hgates hB0 hblk)

/-- **`m4_wave_exit_L` — THE M4 WAVE'S CLOSE.**

For every `C_MRT ≥ 2` and every floor / outer-scale demand there is a regime `R` at which
**log-Chowla-2 does not fail**, conditional on exactly ⟦THE REGISTER⟧ below — and on nothing
else.  This list is what the S11 spine compose must clear.

⟦THE REGISTER⟧

1. **`M4DoorGates_L Cg R M k δ`** — M4-8's door-glue list at the regime: `1 ≤ M`, `0 < δ`, the
   `M`-gate `24·Cg/δ ≤ M`, the absorption floor `4 ≤ log ω`, the ladder's three gates
   (`2^{k+1} ≤ x`, the cover count `k ≤ log ω/log 2 + 2`, `hreach`), and HS-3's per-block
   sieve bundle.  Witness at `k := doorCount R.ω`: `M4Door.doorCount_gates`.
   *SCALE/REGIME data — owed by the door numerology, not by analysis.*
2. **`∀ H, 0 ≤ MS H`** — the row grade is a grade.  *DATA.*
3. **`2 ≤ C`** — the budget halving (`mrtDeliveredGrade` is linear in `C`). *SCALE.*
4. **`∀ H ∈ [Hlo, Hhi], 6·MS H ≤ m4Saving H`** — THE PRICING: the row grade, after the
   cover's `3` and the exchange's `2`, under the quality demand's `W^{−5/2}` saving.
   *REGIME — the analytic content of the whole wave, as one inequality.*
5. **`∀ H ∈ [Hlo, Hhi], δ/4 + 4·2^k/x ≤ mrtDeliveredGrade (C/2) H`** — the door's own two
   grades against the other half of the budget.  *SCALE/REGIME.*
6. **`M4RowMeanSq_L R M k MS`** — THE ROW INPUT: the per-block mean square of the phased sieved
   datum, in `thm_a2'_L`'s own currency.  *THE WAVE'S RESIDUE* (module header, ⟦THE RESIDUE⟧).

Nothing else: the arc, the budget head, the collision, the sieve insert, the harmonic cover,
the `log ω` absorption, the `L²→L¹` descent, the block exchange and the grade gate are all
landed and consumed. -/
theorem m4_wave_exit_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 2 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (MS : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ MS H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 6 * MS H ≤ m4Saving H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4RowMeanSq_L R M k MS →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_blockMeanSq_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C (by linarith) U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ MS M k hgates hMS0 hprice hrest hrow => ?_⟩
  exact hR δ (fun H => 2 * MS H) M k hgates (m4_blockGrade_nonneg hMS0)
    (m4_wave_gradeGate hC hprice hrest) (m4_blockMeanSq_of_rowMeanSq_L hrow)

/-- **THE SUP-ROUTE CLOSE** (`m4_wave_exit_sup_L`).  The same wave exit entered at B-2's
carrier: `M4BlockMeanSqSup_L` → (§2) `M4SievedDoorSqSup_L` → (B-2's `m4_sievedDoorSq_of_sup_L`)
`M4SievedDoorSq_L` → `M4Close.m4_door_contradiction_of_live`.

⟦THE REGISTER, sup form⟧ items 1–3 and 5 of `m4_wave_exit_L` unchanged; items 4 and 6 become

4′. `M4GradeGate R C δ Braw k` with the DRIFT PRICE paid explicitly at B-2's `q`-free
    reading: `(1 + 2π)²·(arcDen 12 H)²·(3·B_blk H) ≤ Braw H` on the window range
    (`hdrift`), and
6′. `M4BlockMeanSqSup_L R M k B_blk` — the per-block sup mean square at the rationals.

The drift price is B-2's and is charged here rather than folded into the grade, because the
sup route's whole point is that the frequency is rational when the mean square is taken.  It
is charged through `m4_sievedDoorSq_of_sup_uniform_L`, i.e. after the socket's `q`-grading has
been spent by `qgraded_drift_price_le` — this route hands the `q²` back and is therefore the
LOSSY reading; a supplier that produces its block bound with the class modulus attached
should read the socket at `m4_sievedDoorSq_of_sup_L` instead (`M4ClassPrice`). -/
theorem m4_wave_exit_sup_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bblk : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → (∀ H : ℕ, 0 ≤ Bblk H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              (1 + 2 * Real.pi) ^ 2 * (arcDen 12 H ^ 2 * (3 * Bblk H)) ≤ Braw H) →
            M4GradeGate R C δ Braw k →
            M4BlockMeanSqSup_L R M k Bblk →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg,
    fun δ Braw Bblk M k hgates hB0 hBraw0 hdrift hgrade hblk => ?_⟩
  exact hR δ Braw M k hgates hBraw0 hgrade
    (m4_sievedDoorSq_of_sup_uniform_L (fun H => by have := hB0 H; linarith) hdrift
      (m4_cover_assembly_sup_L hgates hB0 hblk))

/-- **THE χ-BLOCK STEP AT THE LEVER** — `m4_chiBlockMeanSq_of_dyadicRow_L` (:1134). -/
theorem m4_chiBlockMeanSq_of_dyadicRow_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (htr : ∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H)
    (hrow : M4ChiDyadicRowMeanSq_L_gk K R M k MS) :
    M4ChiBlockMeanSq_L_gk K R M k
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_chiBlockMeanSq_of_shiftBlock_L_gk K (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_
    (m4_chiShiftBlock_of_dyadicRow_L_gk K hrow)
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro j H hj; have := htr j H hj; linarith

/-- **`m4_wave_closed_L` — THE M4 WAVE'S CLOSED THEOREM.**

For every `C ≥ 0` and every floor / outer-scale demand there is a regime `R` at which
log-Chowla-2 does not fail, conditional on exactly ⟦THE FINAL REGISTER⟧ (the module header's
three classes) and on nothing else:

**(a) REGIME/SCALE** — `M4DoorGates_L Cg R M k δ` (witness `M4Door.doorCount_gates`);
`hdrift` (the `q`-graded drift price, absolute by `M4BridgePhase.qgraded_drift_price_le`);
`hdel` (`√(Braw H) ≤ mrtDeliveredGrade (C/2) H` — ⟦U3⟧, the exponent gap unspent);
`hrest` (the door's own two grades against the other half).

**(b) DATA** — `0 ≤ B_cl H`, `0 ≤ Braw H`, `0 ≤ C`.

**(c) THE ANALYTIC ITEM** — `M4ClassBlockMeanSq_L R M k B_cl`, the per-class block mean square
of the door's sieved `λ`.  §3 reduces its coprime half, LOSSLESSLY, to `M4ChiBlockMeanSq_L` —
the χ-uniform block mean square, i.e. the M4/MRT capstone's own currency.  The non-coprime
half and the capstone's row-datum binders are the module header's ⟦THE RESIDUE⟧.

Nothing else: the arc, the budget head, the collision, the sieve insert, the harmonic cover,
the `log ω` absorption, the `L²→L¹` descent, the residue split, the phase removal, the class
assembly and the grade gate are all landed and consumed. -/
theorem m4_wave_closed_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ClassBlockMeanSq_L R M k Bcl →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq_L hgates hBcl0 hdrift hcl)

/-- **THE χ-REDUCTION** (`m4_classMeanSq_of_chiMeanSq_L`) — the coprime half of
`M4ClassBlockMeanSq_L`, from `M4ChiBlockMeanSq_L`, at the SAME grade.  **No loss at all**: the
`1/φ(q)` of the decomposition cancels against the character count exactly
(`M4Close.inv_totient_sum_le`), and the only inequality spent is the square-of-average step,
which the χ-uniformity of the input makes free. -/
theorem m4_classMeanSq_of_chiMeanSq_L {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4ChiBlockMeanSq_L R M k Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ r, r < q → Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik r _ hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_L M) H n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M H n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_L hcop M H n
    have h0 := classSup_nonneg (doorSievedCoeff_L M) H n q r
    have hsq : (classSup (doorSievedCoeff_L M) H n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L χ M H n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_L χ M H n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff_L M) H n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M H n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M H n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (doorChiSup_L χ M H n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi q hq hqQ i hik χ)

/-- **THE M4 WAVE'S CLOSED THEOREM AT THE LEVER** — `m4_wave_closed_L` (:525). -/
theorem m4_wave_closed_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ClassBlockMeanSq_L_gk K R M k Bcl →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_door_contradiction_of_live_L_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hcl => ?_⟩
  exact hR δ Braw M k hgates hBraw0 (m4_gradeGate_direct hdel hrest)
    (m4_sievedDoorSq_of_classMeanSq_L_gk K hgates hBcl0 hdrift hcl)

/-- **THE χ-REDUCTION AT THE LEVER** — `m4_classMeanSq_of_chiMeanSq_L` (:416). -/
theorem m4_classMeanSq_of_chiMeanSq_L_gk (K : ℕ) {R : ChowlaRegime} {M k : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4ChiBlockMeanSq_L_gk K R M k Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ i < k, ∀ r, r < q → Nat.Coprime q r →
        ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
          ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ) := by
  intro H hlo hhi q hq hqQ i hik r _ hcop
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M H n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_L_gk K hcop M H n
    have h0 := classSup_nonneg (doorSievedCoeff_L_gk K M) H n q r
    have hsq : (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L_gk K χ M H n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_L_gk K χ M H n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
  have hstep1 : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M H n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M H n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
            (doorChiSup_L_gk K χ M H n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi q hq hqQ i hik χ)

/-- **THE CLOSE AT THE χ-UNIFORM DATUM** (`m4_wave_closed_of_chi_L`) — the same theorem with
class (c) read one layer further down, at the character-twisted block mean square.  The
`hnoncop` slot is the module header's ⟦THE RESIDUE⟧, first item: the non-coprime classes,
whose transport is `M4ClassPrice.norm_sum_windowClass_memS_dilate` (an EQUALITY) followed by
the same character expansion at the reduced modulus, and whose mean-square form re-indexes
the block `n ↦ n/d₀`.  It is carried here, not assumed away. -/
theorem m4_wave_closed_of_chi_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiBlockMeanSq_L R M k Bcl →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_L M) H n q r) ^ 2
                  ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hchi hnoncop => ?_⟩
  refine hR δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest ?_
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSq_L hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-- **THE CLOSE AT THE χ-UNIFORM DATUM, AT THE LEVER** — `m4_wave_closed_of_chi_L` (:583). -/
theorem m4_wave_closed_of_chi_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw Bcl : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ Bcl H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2 * ((q : ℝ) ^ 2 * (3 * Bcl H))
                ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiBlockMeanSq_L_gk K R M k Bcl →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
                  ≤ Bcl H * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_L_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest
    hchi hnoncop => ?_⟩
  refine hR δ Braw Bcl M k hgates hBcl0 hBraw0 hdrift hdel hrest ?_
  intro H hlo hhi q hq hqQ i hik r hr
  by_cases hcop : Nat.Coprime q r
  · exact m4_classMeanSq_of_chiMeanSq_L_gk K hchi H hlo hhi q hq hqQ i hik r hr hcop
  · exact hnoncop H hlo hhi q hq hqQ i hik r hr hcop

/-- **THE CLOSE AT THE GRADED DYADIC ROW DATUM, AT THE LEVER** —
`m4_wave_closed_of_dyadicRow_L` (:1181). -/
theorem m4_wave_closed_of_dyadicRow_L_gk (K : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (j₀ M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded j₀ (fun H => 2 * MSan H)
                      (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiDyadicRowMeanSq_L_gk K R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_L_gk K M) H n q r) ^ 2
                  ≤ m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                      * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_L_gk K
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS MSan MStr j₀ M k hgates hMSan0 hMStr0 hBraw0
    han htr hdrift hdel hrest hrow hnoncop => ?_⟩
  refine hR δ Braw (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) M k hgates
    (fun H => m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith))
    hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_dyadicRow_L_gk K j₀ hMSan0 hMStr0 han htr hrow) hnoncop

/-- **THE CLOSE AT THE GRADED DYADIC ROW DATUM** (`m4_wave_closed_of_dyadicRow_L`) —
`m4_wave_closed_L` with class (c) read down to the capstone's own currency, ⟦R1⟧ EXECUTED
rather than assumed.

The consumption list is `m4_wave_closed_of_row_L`'s with the maximal step removed: the
`M4ChiMaximalStep_L` slot is gone, `Cmax` is the explicit constant `m4Cmax H = 54/5`, and the row
datum is asked for at the dyadic window lengths `2^j ≤ H` and the shifted scales
`X_{i+1} + s`, `s ≤ H` — the instances the sub-windows' dyadic pieces actually need.  ⟦R2⟧
(the non-coprime classes) and ⟦R3⟧ (the capstone at the door's datum) are unchanged.

⟦THE REGISTER'S GRADED ITEMS⟧, the only change from the uniform version:

* the row grade is `MS : ℕ → ℕ → ℝ` and the nonnegativity slot is now TWO envelopes,
  `0 ≤ MSan H` and `0 ≤ MStr H`, plus the two envelope gates `MS j H ≤ MSan H` (`j₀ ≤ j`)
  and `MS j H ≤ MStr H` (`j < j₀`);
* the floor `j₀` is a BOUND PARAMETER of the register, supplied by the consumer (at the door
  it is `M·AdoorL M`), never a numeral;
* the drift line and the non-coprime line read the assembled
  `m4BclGraded j₀ (2·MSan) (2·MStr) H` in place of `m4Cmax H·(2·MS H)`.

The conclusion `¬ logChowla2Fails R.eps R.x R.ω` is untouched.

⟦THE CONSUMPTION NOTE, HONESTLY⟧ nothing here forces `j₀ ≤ log₂H`.  When `log₂H < j₀` the
large-`j` half of §5's split is EMPTY and every length is charged at `Ftr` — the bound is
then true and useless, exactly as it should be, and `m4SmallGradeFits` is what excludes that
regime: it needs `H ≳ 2^{j₀}` (⟦LEVER 1′⟧ halved the uniform route's `4^{j₀}`).  At the door
`j₀ = M·AdoorL M ≥ 2^18`, so the window floor must swallow `2^{M·AdoorL M}`.  The register
admits this: `U1floor ≤ R.Hlo` is chosen
BEFORE `R`, and `M` is constrained only through `Cg`/`δ` (`M4DoorGates_L.hMδ`), which are
available then — so a consumer fixes `M` first and asks for the matching floor.  The
ordering is workable; it is not free, and it is the item the supplier's threshold check must
carry. -/
theorem m4_wave_closed_of_dyadicRow_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (j₀ M k : ℕ),
            M4DoorGates_L Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < j₀ → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded j₀ (fun H => 2 * MSan H)
                      (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiDyadicRowMeanSq_L R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_L M) H n q r) ^ 2
                  ≤ m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H) H
                      * (H : ℝ) ^ 2 * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS MSan MStr j₀ M k hgates hMSan0 hMStr0 hBraw0
    han htr hdrift hdel hrest hrow hnoncop => ?_⟩
  refine hR δ Braw (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) M k hgates
    (fun H => m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith))
    hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_dyadicRow_L j₀ hMSan0 hMStr0 han htr hrow) hnoncop

/-- **THE CLOSE AT THE CAPSTONE'S OWN CURRENCY** (`m4_wave_closed_of_row_L`) — `m4_wave_closed_L`
with class (c) read all the way down to `M4ChiRowMeanSq_L`, the per-character block mean square
in `ThmA2.thm_a2'_of_rows`' currency.

⟦THE S11 CONSUMPTION LIST, final form⟧ — the hypotheses below, and nothing else:

* **(a) regime/scale** — `M4DoorGates_L` (witness `M4Door.doorCount_gates`), the `q`-graded
  drift price, the budget line `√Braw ≤ mrtDeliveredGrade (C/2)` (⟦U3⟧), the door's own two
  grades;
* **(b) data** — the three nonnegativity slots and `0 ≤ C`;
* **(c) the analytic residue, in THREE named pieces** —
  ⟦R1⟧ `M4ChiMaximalStep_L` (the sub-window sup against the fixed length),
  ⟦R2⟧ `hnoncop` (the non-coprime classes, whose transport is one loss-free dilation),
  ⟦R3⟧ `M4ChiRowMeanSq_L` (the capstone at the door's sieved, χ-twisted, un-phased datum).

Every other link of the M4/S9 chain — the arc, the budget head, the collision, the sieve
insert, the residue split, the phase removal, the character expansion, the class assembly,
the harmonic cover, the `log ω` absorption, the `L²→L¹` descent, the block exchange and the
grade gate — is landed and consumed. -/
theorem m4_wave_closed_of_row_L :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ : ℝ), 1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw MS Cmax : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ →
            (∀ H : ℕ, 0 ≤ MS H) → (∀ H : ℕ, 0 ≤ Cmax H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * (Cmax H * (2 * MS H)))) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            M4ChiMaximalStep_L R M k Cmax →
            M4ChiRowMeanSq_L R M k MS →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ r, r < q → ¬ Nat.Coprime q r →
                ∑ n ∈ Finset.Ioc (doorLadder R.x H (i + 1)) (doorLadder R.x H i),
                    (classSup (doorSievedCoeff_L M) H n q r) ^ 2
                  ≤ (Cmax H * (2 * MS H)) * (H : ℝ) ^ 2
                      * (doorLadder R.x H (i + 1) : ℝ)) →
              ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_chi_L
  refine ⟨Cg, ε, δ₀, hCg, hε, hδ₀, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, fun δ Braw MS Cmax M k hgates hMS0 hCmax0 hBraw0 hdrift hdel
    hrest hmax hrow hnoncop => ?_⟩
  refine hR δ Braw (fun H => Cmax H * (2 * MS H)) M k hgates
    (fun H => by have := hMS0 H; have := hCmax0 H; positivity) hBraw0 hdrift hdel hrest
    (m4_chiBlockMeanSq_of_row_L hCmax0 hmax hrow) hnoncop

end G2Scaffold

open G2Scaffold

/-! ## §1 — `M4CoprimeSupply` -/

/-- A sieved χ-twisted window sum is bounded by its window length. -/
theorem norm_sum_doorSievedWindow_le_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M K n : ℕ) :
    ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖ ≤ (K : ℝ) := by
  have hsub : doorSievedWindow_L M K n ⊆ Finset.Ioc n (n + K) := by
    simp only [doorSievedWindow_L, sievedWindow]
    exact Finset.filter_subset _ _
  have hcard : (doorSievedWindow_L M K n).card ≤ K := by
    calc (doorSievedWindow_L M K n).card ≤ (Finset.Ioc n (n + K)).card :=
          Finset.card_le_card hsub
      _ = K := by simp [Nat.card_Ioc]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ m ∈ doorSievedWindow_L M K n, ‖liouChi χ m‖
      ≤ ∑ _m ∈ doorSievedWindow_L M K n, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => norm_liouChi_le_one χ m
    _ = ((doorSievedWindow_L M K n).card : ℝ) := by simp
    _ ≤ (K : ℝ) := by exact_mod_cast hcard

/-- **THE χ-UNIFORM FREE BLOCK MEAN SQUARE, NARROWED** — `M4CoprimeBlockMeanSqN_L`'s χ-layer:
the same free half-open block `(A, B]`, the same free window length `L` with ⟦THE
NARROWING⟧, the same slack-`4` fit, with the sub-window sup `doorChiSup_L` in place of the
class sup. -/
def M4CoprimeChiBlockMeanSqN_L (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q,
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2 ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- **⟦W2⟧ THE χ-REDUCTION AT THE FREE BLOCK** (`m4_coprimeMeanSqN_of_chiMeanSqN_L`) — the
narrowed coprime family from its χ-layer, at the SAME grade.  The verbatim mirror of
`M4WaveClosed.m4_classMeanSq_of_chiMeanSq`: the two `doorLadder` literals are free, the
window length is free, ⟦THE NARROWING⟧ is carried through untouched, and nothing else
changes — every χ-layer stone is base- and length-generic already. -/
theorem m4_coprimeMeanSqN_of_chiMeanSqN_L {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4CoprimeChiBlockMeanSqN_L R M Bcl) : M4CoprimeBlockMeanSqN_L R M Bcl := by
  intro H hlo hhi L hLH hnar q hq hqQ r _ hcop A B hA hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M L n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_L hcop M L n
    have h0 := classSup_nonneg (doorSievedCoeff_L M) L n q r
    have hsq : (classSup (doorSievedCoeff_L M) L n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L χ M L n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_L χ M L n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L M) L n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B,
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M L n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc A B,
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M L n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi L hLH hnar q hq hqQ χ A B hA hfit)

/-- **THE FREE-BASE ROW INPUT** (`M4ChiFreeRowMeanSq_L`) — `M4Maximal.M4ChiDyadicRowMeanSq`
with the block bottom freed: the mean square of the door's sieved, χ-twisted, UN-PHASED
datum in `ThmA2.thm_a2'_of_rows`' own currency, at the window length `h = 2^j`
(`j ≤ log₂L`) and the scale `X = A + s` (`0 < A`, `s ≤ L`), with the capstone's two pins
`X_d = X` and `N = 2X_d` intact at every instance.

**LENGTH-GRADED**: the grade is `MS j H` — one per dyadic length, ⟦WALL 2⟧'s lesson
(`M4Maximal`'s header) carried verbatim. -/
def M4ChiFreeRowMeanSq_L (R : ChowlaRegime) (M : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L,
      ∀ A : ℕ, 0 < A → ∀ s ≤ L,
        1 / ((A + s : ℕ) : ℝ)
            * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
                ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                    * shortSum (doorChiCoeff_L χ M)
                        (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
          ≤ MS j H

/-- **THE FREE SHIFTED FIXED-LENGTH DATUM** (`M4ChiFreeShiftBlockMeanSq_L`) — the block mean
square of the sieved, χ-twisted window sums at the dyadic lengths `2^j ≤ L` and at every
shift `s ≤ L` of the FREE block `(A, B]`, LENGTH-GRADED.

⟦THE RESIDUE IS EXPLICIT⟧ the right-hand side carries, beside the block term
`F j H·(2^j)²·A`, the additive `(2·F j H + 8)·(2^j)²` the slack-`4` fit and the drop cost.
Neither term has a factor `A`; §3 charges them to the graded price's SECOND summand, where
`4^{j₀}` pays for them (⟦G2⟧). -/
def M4ChiFreeShiftBlockMeanSq_L (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- **⟦W3⟧ THE FREE SHIFTED BRIDGE** (`m4_chiFreeShiftBlock_of_freeRow_L`) — the free-base,
per-length row mean square becomes the shifted block sum of squared sieved-twisted window
sums, at the grade `2·MS` plus the explicit slack residue.

The route is `M4Maximal.m4_chiShiftBlock_of_dyadicRow`'s with its two ladder facts replaced:

* `M4ClassPrice.sum_Ioc_absWindowSum_sq_div_le_slack4` at the block `(A+s, B+s]`, the scale
  `X := A + s` and the frequency `0` — its fit is `(B+s) + 2^j ≤ 2(A+s) + 4`, which is the
  interface's `B + L ≤ 2A + 4` plus `2^j ≤ L`, and its coverage runs on `(A+s, B+s−4]`,
  where `M4BridgeIntegral.hcov_of_seamS0` discharges it;
* the harmonic→flat exchange against `B + s ≤ 2(A+s)`, which is `4 ≤ L` and nothing else.
-/
theorem m4_chiFreeShiftBlock_of_freeRow_L {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiFreeRowMeanSq_L R M MS) :
    M4ChiFreeShiftBlockMeanSq_L R M (fun j H => 2 * MS j H) := by
  intro H hlo hhi L hLH q hq hqQ χ j hjL s hsL A B hA hL4 hfit
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  -- (the fit `(B+s−4) + 2^j ≤ 2(A+s)` is available only when the dropped block is
  -- INHABITED — at `A = 1`, `L = 4`, `B = 2`, `s = 0` it fails and the block is empty, so
  -- the membership is read first and the fit derived from it)
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi L hLH q hq hqQ χ j hjL A hA s hsL
  have hMS0 : (0 : ℝ) ≤ MS j H :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff_L χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff_L χ M) (fun m => norm_doorChiCoeff_le_one_L χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := MS j H) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero_L] using hfinal

set_option maxHeartbeats 1600000 in
-- the dyadic assembly is `M4Maximal`'s at a free block: the triple-nested `Finset` sums
-- are re-elaborated against the free `(A, B]` and `L`, which is what costs the heartbeats
-- (no tactic search below is unbounded — every arithmetic step is `linarith` with hints)
/-- **⟦W4⟧ THE FREE MAXIMAL STEP** (`m4_coprimeChiN_of_freeShiftBlock_L`) — the χ-layer of the
narrowed coprime family, from the free shifted fixed-length datum, at the graded price
`m4BclGraded j₀ Fan Ftr`.

The three charges are the module header's ⟦THE LEDGER⟧, re-cut at ⟦LEVER 1′⟧'s two-summand
head: the analytic half lands on the nose against the CONSTANT first summand `54/5·Fan H`;
the trivial half's `(4/3)^{j₀}` piece and the slack-`4` residue share the head's first
summand (⟦G2⟧ is that comparison, now at `(4/3)^{j₀}`), and the trivial half's `(8/3)^{j₀}`
piece takes the head's second summand — which is what forces ⟦G1⟧ up to `arcDen²`. -/
theorem m4_coprimeChiN_of_freeShiftBlock_L {R : ChowlaRegime} {M : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ^ 2 ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 108 / 5 * Fan H + 432 / 5 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hfix : M4ChiFreeShiftBlockMeanSq_L R M F) :
    M4CoprimeChiBlockMeanSqN_L R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ χ A B hA hfit
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound, at the free length and the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L χ M L n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, SL
        * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshift : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2 := fun j t =>
    sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
  -- ⟦the analytic half: the datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshift j t]
    have hd := hfix H hlo hhi L hLH q hq hqQ χ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, no row datum consulted⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshift j t]
    have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
        ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro n _
      have h := norm_sum_doorSievedWindow_le_L χ M (2 ^ j) n
      have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
      have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
      exact_mod_cast hnat
    have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1), (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (A : ℝ) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((A : ℝ) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT: the weighted full count against the analytic half, the weighted head
  -- against the trivial one
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8) := by
    have := hFan0 H; nlinarith
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hA0R (hWw0 j))
      _ = (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ §4's two weighted counts, then the ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hg0 : (0 : ℝ) < (3 / 2 : ℝ) ^ (Nat.log 2 H) := by positivity
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, STRENGTHENED⟧ the two consequences the weighted head needs
  have harc2 : (1 : ℝ) ≤ arcDen 12 H ^ 2 := by nlinarith
  have hG1H := hG1 H hlo hhi
  have hFtrL : 2 * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have h2 : 2 * arcDen 12 H * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hL0R.le
    linarith [hnar]
  have hFtrL2 : (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    nlinarith [hsq, sq_nonneg ((L : ℝ))]
  -- ⟦the first budget line⟧ the trivial head's `(4/3)^{j₀}` half AND the slack residue
  have hEkey : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 :=
    by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (H : ℝ)
        ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ))
      nlinarith [h, hH0R.le]
    have hmain : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2 ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hg2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)) := by
      nlinarith [mul_le_mul_of_nonneg_left hgl1
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧ the trivial head's `(8/3)^{j₀}` half — ⟦G1⟧ at `arcDen²`
  have hres2 : (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (A : ℝ) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
          + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead hA0R
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- **THE COPRIME-SUPPLY ARM, SUPPLIED** (`m4_coprimeN_supplied_L`) — `M4CoprimeBlockMeanSqN_L`
at the grade `m4BclGraded j₀ (2·MSan) (2·MStr)`, from the free-base row datum and the
register's own envelopes.

⟦THE CONSUMPTION LIST⟧, beyond the row datum: the two envelope nonnegativities, the
analytic envelope gate `MS j H ≤ MSan H` at `j₀ ≤ j` (the trivial envelope gate is NOT
needed — the small lengths are charged at the absolute grade `1`), and the three
`H`-only class-(a) gates ⟦G1⟧, ⟦G2⟧, ⟦the regime fact⟧ of the module header. -/
theorem m4_coprimeN_supplied_L {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : M4ChiFreeRowMeanSq_L R M MS) :
    M4CoprimeBlockMeanSqN_L R M
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_coprimeMeanSqN_of_chiMeanSqN_L
    (m4_coprimeChiN_of_freeShiftBlock_L (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_ ?_ harc8
      (m4_chiFreeShiftBlock_of_freeRow_L hrow))
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi; have := hG2 H hlo hhi; have := hMSan0 H; linarith

/-- A sieved χ-twisted window sum at the lever is bounded by its window length —
`norm_sum_doorSievedWindow_le_L` (:105). -/
theorem norm_sum_doorSievedWindow_le_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Kw n : ℕ) :
    ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖ ≤ (Kw : ℝ) := by
  have hsub : doorSievedWindow_L_gk K M Kw n ⊆ Finset.Ioc n (n + Kw) := by
    simp only [doorSievedWindow_L_gk, sievedWindow]
    exact Finset.filter_subset _ _
  have hcard : (doorSievedWindow_L_gk K M Kw n).card ≤ Kw := by
    calc (doorSievedWindow_L_gk K M Kw n).card ≤ (Finset.Ioc n (n + Kw)).card :=
          Finset.card_le_card hsub
      _ = Kw := by simp [Nat.card_Ioc]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ m ∈ doorSievedWindow_L_gk K M Kw n, ‖liouChi χ m‖
      ≤ ∑ _m ∈ doorSievedWindow_L_gk K M Kw n, (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => norm_liouChi_le_one χ m
    _ = ((doorSievedWindow_L_gk K M Kw n).card : ℝ) := by simp
    _ ≤ (Kw : ℝ) := by exact_mod_cast hcard

/-- **THE χ-UNIFORM FREE BLOCK MEAN SQUARE, NARROWED, AT THE LEVER** —
`M4CoprimeChiBlockMeanSqN_L` (:142). -/
def M4CoprimeChiBlockMeanSqN_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q,
      ∀ A B : ℕ, 0 < A → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2 ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

/-- **⟦W2⟧ THE χ-REDUCTION AT THE FREE BLOCK, AT THE LEVER** —
`m4_coprimeMeanSqN_of_chiMeanSqN_L` (:178). -/
theorem m4_coprimeMeanSqN_of_chiMeanSqN_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ}
    (hchi : M4CoprimeChiBlockMeanSqN_L_gk K R M Bcl) : M4CoprimeBlockMeanSqN_L_gk K R M Bcl := by
  intro H hlo hhi L hLH hnar q hq hqQ r _ hcop A B hA hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦pointwise: the χ-average, squared⟧
  have hpt : ∀ n : ℕ, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M L n) ^ 2 := by
    intro n
    have hle := classSup_le_inv_totient_sum_doorChiSup_L_gk K hcop M L n
    have h0 := classSup_nonneg (doorSievedCoeff_L_gk K M) L n q r
    have hsq : (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
        ≤ ((q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, doorChiSup_L_gk K χ M L n) ^ 2 := by
      nlinarith
    exact hsq.trans (sq_inv_totient_sum_le_sum_sq (fun χ => doorChiSup_L_gk K χ M L n))
  -- ⟦the block sum, then the χ-average and the `n`-sum commute⟧
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (classSup (doorSievedCoeff_L_gk K M) L n q r) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B,
          (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M L n) ^ 2 :=
    Finset.sum_le_sum fun n _ => hpt n
  have hswap : ∑ n ∈ Finset.Ioc A B,
      (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M L n) ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hswap] at hstep1
  refine hstep1.trans ?_
  exact inv_totient_sum_le (fun χ => hchi H hlo hhi L hLH hnar q hq hqQ χ A B hA hfit)

/-- **THE FREE-BASE ROW INPUT AT THE LEVER** — `M4ChiFreeRowMeanSq_L` (:230). -/
def M4ChiFreeRowMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (MS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L,
      ∀ A : ℕ, 0 < A → ∀ s ≤ L,
        1 / ((A + s : ℕ) : ℝ)
            * (∫ y in ((A + s : ℕ) : ℝ)..(2 * ((A + s : ℕ) : ℝ)),
                ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                    * shortSum (doorChiCoeff_L_gk K χ M)
                        (seamS0 (2 * (A + s)) ((A + s : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
          ≤ MS j H

/-- **THE FREE SHIFTED FIXED-LENGTH DATUM AT THE LEVER** —
`M4ChiFreeShiftBlockMeanSq_L` (:249). -/
def M4ChiFreeShiftBlockMeanSq_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- **⟦W3⟧ THE FREE SHIFTED BRIDGE AT THE LEVER** —
`m4_chiFreeShiftBlock_of_freeRow_L` (:291). -/
theorem m4_chiFreeShiftBlock_of_freeRow_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    (hrow : M4ChiFreeRowMeanSq_L_gk K R M MS) :
    M4ChiFreeShiftBlockMeanSq_L_gk K R M (fun j H => 2 * MS j H) := by
  intro H hlo hhi L hLH q hq hqQ χ j hjL s hsL A B hA hL4 hfit
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  -- (the fit `(B+s−4) + 2^j ≤ 2(A+s)` is available only when the dropped block is
  -- INHABITED — at `A = 1`, `L = 4`, `B = 2`, `s = 0` it fails and the block is empty, so
  -- the membership is read first and the fit derived from it)
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L_gk K χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ MS j H := by
    rw [doorCoeffPhase_zero]
    exact hrow H hlo hhi L hLH q hq hqQ χ j hjL A hA s hsL
  have hMS0 : (0 : ℝ) ≤ MS j H :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff_L_gk K χ M) (fun m => norm_memSCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := MS j H) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * MS j H)
      = 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (2 * (2 * MS j H) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * MS j H * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero_L_gk K] using hfinal

set_option maxHeartbeats 1600000 in
-- the dyadic assembly is `M4Maximal`'s at a free block: the triple-nested `Finset` sums
-- are re-elaborated against the free `(A, B]` and `L`, which is what costs the heartbeats
-- (no tactic search below is unbounded — every arithmetic step is `linarith` with hints)
/-- **⟦W4⟧ THE FREE MAXIMAL STEP AT THE LEVER** —
`m4_coprimeChiN_of_freeShiftBlock_L` (:422). -/
theorem m4_coprimeChiN_of_freeShiftBlock_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ^ 2 ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 108 / 5 * Fan H + 432 / 5 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hfix : M4ChiFreeShiftBlockMeanSq_L_gk K R M F) :
    M4CoprimeChiBlockMeanSqN_L_gk K R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ χ A B hA hfit
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        arcDen 12 H * 8 ≤ arcDen 12 H * (L : ℝ)) harc0
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  set X : ℕ → ℕ → ℕ → ℝ := fun j t n =>
    ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound, at the free length and the geometric weights
  have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j :=
    Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L_gk K χ M L n
  -- ⟦STEP 2⟧ the sums commute (the weight rides the `j`-index only)
  have hswap : ∑ n ∈ Finset.Ioc A B, SL
        * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X j t n) * (2 / 3 : ℝ) ^ j
      = SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, X j t n) * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  -- ⟦STEP 3⟧ each (scale, offset) pair is a shifted fixed-length block sum
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshift : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n
      = ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 := fun j t =>
    sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2) A B _
  -- ⟦the analytic half: the datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshift j t]
    have hd := hfix H hlo hhi L hLH q hq hqQ χ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, no row datum consulted⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, X j t n ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshift j t]
    have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
        ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro n _
      have h := norm_sum_doorSievedWindow_le_L_gk K χ M (2 ^ j) n
      have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
      have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
      exact_mod_cast hnat
    have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
    nlinarith
  -- ⟦STEP 4⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1), (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n
        ≤ (A : ℝ) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((A : ℝ) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 5⟧ THE SPLIT: the weighted full count against the analytic half, the weighted head
  -- against the trivial one
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8) := by
    have := hFan0 H; nlinarith
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (A : ℝ) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg hA0R (hWw0 j))
      _ = (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ §4's two weighted counts, then the ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hg0 : (0 : ℝ) < (3 / 2 : ℝ) ^ (Nat.log 2 H) := by positivity
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, STRENGTHENED⟧ the two consequences the weighted head needs
  have harc2 : (1 : ℝ) ≤ arcDen 12 H ^ 2 := by nlinarith
  have hG1H := hG1 H hlo hhi
  have hFtrL : 2 * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have h2 : 2 * arcDen 12 H * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hL0R.le
    linarith [hnar]
  have hFtrL2 : (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    nlinarith [hsq, sq_nonneg ((L : ℝ))]
  -- ⟦the first budget line⟧ the trivial head's `(4/3)^{j₀}` half AND the slack residue
  have hEkey : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H * (L : ℝ) ^ 2 :=
    by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (H : ℝ)
        ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ))
      nlinarith [h, hH0R.le]
    have hmain : 9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8) * (L : ℝ) ^ 2 ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hg2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ) * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)) := by
      nlinarith [mul_le_mul_of_nonneg_left hgl1
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧ the trivial head's `(8/3)^{j₀}` half — ⟦G1⟧ at `arcDen²`
  have hres2 : (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
        + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, X j t n)
            * (2 / 3 : ℝ) ^ j := by
        rw [← hswap]; exact hstep1
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (A : ℝ) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (A : ℝ) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8)) * (54 / 5 * (L : ℝ) ^ 2)
          + (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead hA0R
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- **THE COPRIME-SUPPLY ARM, SUPPLIED, AT THE LEVER** — `m4_coprimeN_supplied_L` (:760). -/
theorem m4_coprimeN_supplied_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {MS : ℕ → ℕ → ℝ}
    {MSan MStr : ℕ → ℝ} (j₀ : ℕ)
    (hMSan0 : ∀ H : ℕ, 0 ≤ MSan H) (hMStr0 : ∀ H : ℕ, 0 ≤ MStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → MS j H ≤ MSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 2 ≤ MStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 44 * MSan H + 87 ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ≤ (H : ℝ))
    (hrow : M4ChiFreeRowMeanSq_L_gk K R M MS) :
    M4CoprimeBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * MSan H) (fun H => 2 * MStr H)) := by
  refine m4_coprimeMeanSqN_of_chiMeanSqN_L_gk K
    (m4_coprimeChiN_of_freeShiftBlock_L_gk K (F := fun j H => 2 * MS j H) j₀ ?_ ?_ ?_ ?_ ?_ harc8
      (m4_chiFreeShiftBlock_of_freeRow_L_gk K hrow))
  · intro H; have := hMSan0 H; linarith
  · intro H; have := hMStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi; have := hG2 H hlo hhi; have := hMSan0 H; linarith
/-! ## §2 — `M4T0Datum` -/

/-- **THE DOOR'S CUT DATUM, SPLIT** (`winCutH_doorChiCoeff_split_L`).  At every `n`,

  `winCutH X_d (1_𝒮·λχ̄) (n) = Σ_{𝒥 ⊆ [1,2]} (−1)^{|𝒥|}·g_𝒥(1) · winCutH X_d (λχ̄·g_𝒥) (n)`.

`CofactorSupplier.doorCofactor0_split` at the shift `Ps := 1` (which `M4DoorRow`'s
`doorCofactor0_door_eq_L` identifies with the door datum) composed with `winCutH_sum_finset`. -/
theorem winCutH_doorChiCoeff_split_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd n : ℕ) :
    winCutH Xd (doorChiCoeff_L χ M) n
      = ∑ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          pieceSign 𝒥 (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 1
            * winCutH Xd (pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
                (calQK (AdoorL M) (3072 * M) M)) n := by
  refine winCutH_sum_finset _ Xd _ _ (fun m => ?_) n
  rw [← doorCofactor0_door_eq_L χ M]
  exact doorCofactor0_split χ _ _ 2 1 le_rfl m

/-- **THE DOOR DATUM'S PER-FREQUENCY BAND SUP** (`m4_t0datum_sup_L`).  With the per-piece,
per-frequency centre bound `S₀` on `[X_d, N]`,

  `‖spolyA (winCutH X_d (doorChiCoeff_L χ M)) t m‖ ≤ 8·S₀·m`,  `|t| ≤ seamT0 X`, `m ≤ N`,

which is `M4Seam.cfb_t0band_supply_of_sup`'s `hsup` slot at the door datum.  The `8` is
`4 = #𝒫([1,2])` pieces times the half-open cut's factor `2`; no other constant appears. -/
theorem m4_t0datum_sup_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd N : ℕ} {X S₀ : ℝ}
    (hN : N ≤ 2 * Xd) (hS₀ : 0 ≤ S₀)
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ)) :
    ∀ t : ℝ, |t| ≤ seamT0 X → ∀ m : ℕ, m ≤ N →
      ‖spolyA (winCutH Xd (doorChiCoeff_L χ M)) t m‖ ≤ (8 * S₀) * (m : ℝ) := by
  intro t ht m hm
  have hb : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      ‖spolyA (winCutH Xd (pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M))) t m‖ ≤ 2 * S₀ * (m : ℝ) :=
    fun 𝒥 h𝒥 => cfb_sup_of_center_cut hS₀ hN (hpiece 𝒥 h𝒥 t ht) m hm
  have hmain := norm_spolyA_of_pieces
    (s := (Finset.Icc 1 2).powerset)
    (ε := fun 𝒥 => pieceSign 𝒥 (calP (AdoorL M) (3072 * M))
      (calQK (AdoorL M) (3072 * M) M) 1)
    (fun 𝒥 _ => norm_pieceSign_le_one 𝒥 _ _ 1)
    (winCutH_doorChiCoeff_split_L χ M Xd) hb
  rw [door_powerset_card] at hmain
  have h4 : ((4 : ℕ) : ℝ) * (2 * S₀ * (m : ℝ)) = (8 * S₀) * (m : ℝ) := by push_cast; ring
  linarith [hmain, h4.le, h4.ge]

/-- **THE `hT0band` SLOT AT THE DOOR DATUM** (`m4_hT0band_at_door_L`).

  `∫_{−T₀}^{T₀} ‖dpolyA (winCutH X_d (doorChiCoeff_L χ M)) (seamS0 N X) t‖² dt
     ≤ t0BandB X (cfbC₁ X C₁) M₀`,   `T₀ = seamT0 X = (log X)^{1/45}`,

i.e. `ThmA2Rows.thm_a2'_of_rows`'s (hence `M4MeanSq.m4_meansq_per_chi_gen`'s) `hT0band` slot at
`C₁′ := cfbC₁ X C₁`, AT THE DOOR'S SIEVED χ-TWISTED UN-PHASED DATUM.  This is the item
`M4DoorRow`'s ⟦THE `T₀`-BAND, NAMED⟧ recorded as open.

The support pin is free (`M4DoorRow.winCutH_supp0`); `hSle` and `hErr` are
`cfb_t0band_supply_of_sup`'s own binders at the grade `S = 8·S₀`. -/
theorem m4_hT0band_at_door_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd N : ℕ}
    {X C₁ M₀ S₀ : ℝ}
    (hX3 : (3 : ℝ) ≤ X) (hXd : ((Xd : ℕ) : ℝ) = X) (hXdN : Xd ≤ N) (hN : N ≤ 2 * Xd)
    (hC₁ : 1 ≤ C₁) (hS₀ : 0 ≤ S₀)
    (hSle : 8 * S₀ ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hXN : X ≤ (N : ℝ) := by
    rw [← hXd]; exact Nat.cast_le.mpr hXdN
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at this
    linarith
  refine cfb_t0band_supply_of_sup hX3 hXN hN2 hC₁ ?_ (by linarith) hSle ?_ hErr
  · intro n hn
    exact winCutH_supp0 _ (by rw [hXd]; exact hn)
  · exact m4_t0datum_sup_L χ M hN hS₀ hpiece

/-- **THE SLOT, FULLY REDUCED TO THE WIDE SUPPLY** (`m4_hT0band_at_door_of_wide_L`).  §5 ∘ §7:
the door datum's `hT0band` slot from the hoisted wide centre supply's OWN binders, with no
per-piece hand-off left in the middle.  This is the kernel witness that the two shapes fit —
§5 delivers its bound on `X−1 < k ≤ N`, §7 asks for it on `X_d ≤ k ≤ N`, and `(X_d : ℝ) = X`
is what identifies them.

The `∃X₀` is `center_halasz_supply_wideA`'s, hoisted through the whole composition: ONE
threshold for every character, every piece and every band frequency.  The grade gate
(`hgrade`) and `hErr` are the only arithmetic asked of the consumer; both are
`cfb_t0band_supply_of_sup`'s own shape, read at `S = 8·(cSq·(B + 4P) + cSq·D^{−1/4})`. -/
theorem m4_hT0band_at_door_of_wide_L (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd N D : ℕ) (X Xw B C₁ M₀ : ℝ),
        (3 : ℝ) ≤ X → ((Xd : ℕ) : ℝ) = X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B → 1 ≤ D →
        (D : ℝ) * (Xw + 1) ≤ X - 1 →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
                    (calQK (AdoorL M) (3072 * M) M) p
                  * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
        8 * (cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
              + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
            ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨X₀, hX₀0, hwide⟩ := piece_center_of_wide Y
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ M Xd N D X Xw B C₁ M₀ hX3 hXd hXdN hN hC₁ hXlb hXw hB0 hD hDgate hY10 hYsq
    hYlow hYlog hRHS hgrade hErr
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have h : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at h
    linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hcS : (0 : ℝ) ≤ cSq := by rw [cSq]; norm_num
  have hDp : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hS₀ : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
      + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) :=
      mul_nonneg hcS (by linarith)
    have h2 : (0 : ℝ) ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := mul_nonneg hcS hDp
    linarith
  refine m4_hT0band_at_door_L χ M hX3 hXd hXdN hN hC₁ hS₀ hgrade ?_ hErr
  intro 𝒥 h𝒥 t ht k hk1 hk2
  have hkX : X - 1 < (k : ℝ) := by
    have h : ((Xd : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
    rw [hXd] at h
    linarith
  exact hwide χ 𝒥 _ _ X Xw B N D t hXlb hXw hB0 hD hDgate hN2 hY10 hYsq hYlow hYlog
    (hRHS 𝒥 h𝒥 t ht) k hkX hk2

/-- The door's calibrated exponent ladder clears `2` at every index: `e_j = A·G^{j−1}·(j!)²`
with `A = AdoorL M ≥ 2^18`.  (`CofactorSupplier.blockWindow_calibrated_debit_sum`'s `hE`.) -/
theorem two_le_calE_door_L {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    2 ≤ calE (AdoorL M) (3072 * M) j := by
  have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
  have h1 : 1 ≤ (3072 * M) ^ (j - 1) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (Nat.factorial j) ^ 2 := Nat.one_le_pow _ _ (Nat.factorial_pos j)
  have hstep : AdoorL M ≤ AdoorL M * (3072 * M) ^ (j - 1) * (Nat.factorial j) ^ 2 := by
    calc AdoorL M = AdoorL M * 1 * 1 := by ring
      _ ≤ AdoorL M * (3072 * M) ^ (j - 1) * (Nat.factorial j) ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
  unfold calE
  omega

/-- **THE BAND FLOOR AT THE DOOR'S OWN PIECES** (`band_floor_M0_doorPiece_L`).  The masked band
floor at the door's calibrated ladder, with the debit EVALUATED: `X`-free, and at `J = 2` it
is `2·(log(4M) + 25)`.

The floor's constant is therefore `K + 2(log(4M)+25)` — still `X`-free, still `cfbM0`-shaped
(`cfbM0_add_debit`), which is what keeps the U1 pricing route reachable. -/
theorem band_floor_M0_doorPiece_L (Q : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M : ℕ)
      (𝒥 : Finset ℕ) (X v : ℝ), q ≤ Q → 1 ≤ M → 𝒥 ⊆ Finset.Icc 1 2 →
      Real.exp (Real.exp 1) ≤ X → |v| ≤ 2 * seamT0 X + 1 →
        cfbM0 (K + 2 * (Real.log (4 * (M : ℝ)) + 25)) q X
          ≤ pretDistSq (pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
              (calQK (AdoorL M) (3072 * M) M)) (costwist v) X := by
  obtain ⟨K, hK0, hK⟩ := band_floor_M0_pieceDatum Q
  refine ⟨K, hK0, ?_⟩
  intro q _ χ M 𝒥 X v hq hM h𝒥 hX hv
  have hdeb := blockWindow_calibrated_debit_sum (AdoorL M) (3072 * M) M 2 (𝒥 := 𝒥) X h𝒥 hM
    (two_le_calE_door_L hM)
  have hval : ((2 : ℕ) : ℝ) * (Real.log (((2 : ℕ) : ℝ) ^ 2 * (M : ℝ)) + 25)
      = 2 * (Real.log (4 * (M : ℝ)) + 25) := by norm_num
  rw [hval] at hdeb
  exact hK q χ _ _ 𝒥 X v _ hq hX hv hdeb

-- the levered K-family in the pieces, `doorCofactor0_door_eq_L_gk` in the middle. -/
theorem winCutH_doorChiCoeff_split_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (M Xd n : ℕ) :
    winCutH Xd (doorChiCoeff_L_gk K χ M) n
      = ∑ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          pieceSign 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 1
            * winCutH Xd (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
                (calQK (AdoorL M) (s13GK K M) M)) n := by
  refine winCutH_sum_finset _ Xd _ _ (fun m => ?_) n
  rw [← doorCofactor0_door_eq_L_gk K χ M]
  exact doorCofactor0_split χ _ _ 2 1 le_rfl m

/-- **THE DOOR DATUM'S PER-FREQUENCY BAND SUP, AT THE G-LEVER** (`m4_t0datum_sup_L_gk`).  The
`8` is `4 = #𝒫([1,2])` pieces times the half-open cut's factor `2`, exactly as landed. -/
theorem m4_t0datum_sup_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ)
    {Xd N : ℕ} {X S₀ : ℝ}
    (hN : N ≤ 2 * Xd) (hS₀ : 0 ≤ S₀)
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ)) :
    ∀ t : ℝ, |t| ≤ seamT0 X → ∀ m : ℕ, m ≤ N →
      ‖spolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) t m‖ ≤ (8 * S₀) * (m : ℝ) := by
  intro t ht m hm
  have hb : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      ‖spolyA (winCutH Xd (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M))) t m‖ ≤ 2 * S₀ * (m : ℝ) :=
    fun 𝒥 h𝒥 => cfb_sup_of_center_cut hS₀ hN (hpiece 𝒥 h𝒥 t ht) m hm
  have hmain := norm_spolyA_of_pieces
    (s := (Finset.Icc 1 2).powerset)
    (ε := fun 𝒥 => pieceSign 𝒥 (calP (AdoorL M) (s13GK K M))
      (calQK (AdoorL M) (s13GK K M) M) 1)
    (fun 𝒥 _ => norm_pieceSign_le_one 𝒥 _ _ 1)
    (winCutH_doorChiCoeff_split_L_gk K χ M Xd) hb
  rw [door_powerset_card] at hmain
  have h4 : ((4 : ℕ) : ℝ) * (2 * S₀ * (m : ℝ)) = (8 * S₀) * (m : ℝ) := by push_cast; ring
  linarith [hmain, h4.le, h4.ge]

/-- **THE `hT0band` SLOT AT THE DOOR DATUM, AT THE G-LEVER** (`m4_hT0band_at_door_L_gk`). -/
theorem m4_hT0band_at_door_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd N : ℕ}
    {X C₁ M₀ S₀ : ℝ}
    (hX3 : (3 : ℝ) ≤ X) (hXd : ((Xd : ℕ) : ℝ) = X) (hXdN : Xd ≤ N) (hN : N ≤ 2 * Xd)
    (hC₁ : 1 ≤ C₁) (hS₀ : 0 ≤ S₀)
    (hSle : 8 * S₀ ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)))
    (hpiece : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
      ∀ k : ℕ, Xd ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k,
            pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) n
              * eIu (-t) n‖ ≤ S₀ * (k : ℝ))
    (hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
        ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀)) :
    (∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 N X) t‖ ^ 2)
      ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  have hXN : X ≤ (N : ℝ) := by
    rw [← hXd]; exact Nat.cast_le.mpr hXdN
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at this
    linarith
  refine cfb_t0band_supply_of_sup hX3 hXN hN2 hC₁ ?_ (by linarith) hSle ?_ hErr
  · intro n hn
    exact winCutH_supp0 _ (by rw [hXd]; exact hn)
  · exact m4_t0datum_sup_L_gk K χ M hN hS₀ hpiece

/-- **THE SLOT, FULLY REDUCED TO THE WIDE SUPPLY, AT THE G-LEVER**
(`m4_hT0band_at_door_of_wide_L_gk`).  The `∃X₀` is `center_halasz_supply_wideA`'s, unmoved by
the lever: the wide centre supply never reads `G`. -/
theorem m4_hT0band_at_door_of_wide_L_gk (K : ℕ) (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd N D : ℕ) (X Xw B C₁ M₀ : ℝ),
        (3 : ℝ) ≤ X → ((Xd : ℕ) : ℝ) = X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        X₀ ≤ Real.sqrt X → Real.sqrt X ≤ Xw → 0 ≤ B → 1 ≤ D →
        (D : ℝ) * (Xw + 1) ≤ X - 1 →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xw ≤ (k : ℝ) → (k : ℝ) ≤ 2 * X →
            ‖prop21RHS (fun p => pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
                    (calQK (AdoorL M) (s13GK K M) M) p
                  * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * I)) (0 + t)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ B * (k : ℝ)) →
        8 * (cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
              + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
            ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
              + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨X₀, hX₀0, hwide⟩ := piece_center_of_wide Y
  refine ⟨X₀, hX₀0, ?_⟩
  intro q χ M Xd N D X Xw B C₁ M₀ hX3 hXd hXdN hN hC₁ hXlb hXw hB0 hD hDgate hY10 hYsq
    hYlow hYlog hRHS hgrade hErr
  have hN2 : (N : ℝ) ≤ 2 * X := by
    rw [← hXd]
    have h : (N : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := Nat.cast_le.mpr hN
    push_cast at h
    linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hcS : (0 : ℝ) ≤ cSq := by rw [cSq]; norm_num
  have hDp : (0 : ℝ) ≤ (D : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  have hS₀ : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
      + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have h1 : (0 : ℝ) ≤ cSq * (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) :=
      mul_nonneg hcS (by linarith)
    have h2 : (0 : ℝ) ≤ cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)) := mul_nonneg hcS hDp
    linarith
  refine m4_hT0band_at_door_L_gk K χ M hX3 hXd hXdN hN hC₁ hS₀ hgrade ?_ hErr
  intro 𝒥 h𝒥 t ht k hk1 hk2
  have hkX : X - 1 < (k : ℝ) := by
    have h : ((Xd : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
    rw [hXd] at h
    linarith
  exact hwide χ 𝒥 _ _ X Xw B N D t hXlb hXw hB0 hD hDgate hN2 hY10 hYsq hYlow hYlog
    (hRHS 𝒥 h𝒥 t ht) k hkX hk2
/-! ## §3 — `M4DoorClose` -/

/-- **THE DOOR ROW'S CARRIED REGISTER** (`DoorRowCarried_L`) — see the module header's three
classes.  The two analytic carries are `hend` (the endpoint) and the `T₀`-band integral; all
the rest is regime arithmetic at the block scale. -/
def DoorRowCarried_L (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
                (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
          (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ (ε ≤ theta293 - 1 / 500) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
          (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door_L`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    (5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    ((4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

/-- **THE TRIVIAL GRADE AT THE DOOR ROW** (`doorRow_trivial_grade_L`).  The door row's mean
square at ANY dyadic length is at most `4` — the bound `M4Maximal`'s graded split charges the
`j < j₀` half at, and the one `M4DoorRow.door_smallGrade_fits` is priced against. -/
theorem doorRow_trivial_grade_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ) {Xd : ℕ} (j : ℕ)
    (hXd : 0 < Xd) :
    1 / ((Xd : ℕ) : ℝ)
        * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                    ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ 4 := by
  have hXd0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by exact_mod_cast hXd
  have hhN : 0 < 2 ^ j := Nat.two_pow_pos j
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hhN
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  -- ⟦the pointwise bound⟧
  have hpt : ∀ y ∈ Set.Icc ((Xd : ℕ) : ℝ) (2 * ((Xd : ℕ) : ℝ)),
      ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
          * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
              ((2 ^ j : ℕ) : ℝ)‖ ^ 2 ≤ 4 := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_trans hXd0.le hy.1
    have hs := norm_shortSum_le (norm_doorChiCoeff_le_one_L χ M)
      (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) (x := y) (hlen := ((2 ^ j : ℕ) : ℝ)) hy0 hh0.le
    have hnm : ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
        * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖
        = 1 / ((2 ^ j : ℕ) : ℝ)
            * ‖shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
        * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
            ((2 ^ j : ℕ) : ℝ)‖ ≤ 2 := by
      rw [hnm]
      have h2h : ‖shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
          ((2 ^ j : ℕ) : ℝ)‖ ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by linarith
      calc 1 / ((2 ^ j : ℕ) : ℝ)
            * ‖shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖
          ≤ 1 / ((2 ^ j : ℕ) : ℝ) * (2 * ((2 ^ j : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h2h (by positivity)
        _ = 2 := by field_simp
    have h0 := norm_nonneg (((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
      * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ))
    nlinarith
  -- ⟦the mean⟧
  have hint := shortSum_sq_intervalIntegrable (doorChiCoeff_L χ M)
    (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) ((2 ^ j : ℕ) : ℝ) ((Xd : ℕ) : ℝ) (2 * ((Xd : ℕ) : ℝ))
  have hmono := intervalIntegral.integral_mono_on (a := ((Xd : ℕ) : ℝ))
    (b := 2 * ((Xd : ℕ) : ℝ)) (by linarith) hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hbound : (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
      ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
          * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
              ((2 ^ j : ℕ) : ℝ)‖ ^ 2) ≤ ((Xd : ℕ) : ℝ) * 4 := by
    calc _ ≤ (2 * ((Xd : ℕ) : ℝ) - ((Xd : ℕ) : ℝ)) * 4 := hmono
      _ = ((Xd : ℕ) : ℝ) * 4 := by ring
  calc 1 / ((Xd : ℕ) : ℝ)
        * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff_L χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                    ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ 1 / ((Xd : ℕ) : ℝ) * (((Xd : ℕ) : ℝ) * 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 4 := by field_simp

set_option maxHeartbeats 4000000 in
-- the ~90-binder instantiation: `DoorRowCarried_L`'s ~85-conjunct destructuring plus the
-- capstone's 86-argument application (four hoisted suppliers, one statement) is what costs
-- the heartbeats — no tactic search happens here, every step is `exact`-shaped
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED** (`m4_door_meansq_carried_L`).  At every door
instance meeting `DoorRowCarried_L`, the door's sieved, χ-twisted, UN-PHASED datum satisfies
the capstone's five-summand mean-square bound at the grade `B` — the datum binders
discharged, the register carried.

The `∃`-bound constants are the K6 discipline's: `Cq, cq, T₀, Xcap, Cs, Ccc, Kfl` are
`m4_meansq_per_chi_gen_L`'s; `Xsk` is `CaseAWide.m4_supplier_complete`'s wide threshold; `Kcf`
is `CofactorSupplier.capFreeFloor3_pieceDatum`'s masked-floor constant; `Ctail` is
`M4DoorRow.m4_door_tail_supply`'s coprime-tail mass constant.  All four suppliers are hoisted
ONCE, outside the instance quantifier. -/
theorem m4_door_meansq_carried_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloorL M ≤ j →
          DoorRowCarried_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_L
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, hεup, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hgP1, hgRows, hL4096, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    doorL_length_gate_iff.mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L χ M) n = doorChiCoeff_L χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L χ M)) (doorChiCoeff_L χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE CAPSTONE⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L χ M)) (liouChi χ)
    (doorChiCoeff_L χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 le_rfl
    (doorRow_ha1_L χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L χ M Xd n hn) (fun n hn => doorRow_hasupp_L χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L χ M) (fun i n => norm_doorPunctCoeff_le_one_L χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hgP1 hgRows hL4096
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- **THE DOOR'S DYADIC ROW, CARRIED** (`m4_dyadicRow_carried_L`).  `M4ChiDyadicRowMeanSq_L` at
the door datum, from THE FINAL CARRIED REGISTER: the per-instance `DoorRowCarried_L` (which
holds the `T₀`-band arm, the endpoint gate and every regime gate) plus the trivial grade at
the small lengths, plus the modulus cap `arcDen 12 H ≤ Qm` that puts the door's characters
inside `m4_meansq_per_chi_gen_L`'s range. -/
theorem m4_dyadicRow_carried_L :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarried_L Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_L
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · -- ⟦the capstone speaks: §3 at the carried register⟧
    have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · -- ⟦below the floor: the trivial grade⟧
    exact le_trans (doorRow_trivial_grade_L χ M j hApos) (htriv j H (not_le.mp hcase))

set_option maxHeartbeats 1600000 in
-- same cause as §3: elaborating the register (which mentions `DoorRowCarried_L` under six
-- binders) against `m4_wave_closed_of_dyadicRow_L`'s own list is the whole cost
/-- **THE M4 WAVE, STRUCTURALLY CLOSED** (`m4_wave_structurally_closed_L`).

  ⟦THE FINAL CARRIED REGISTER⟧ → `¬ logChowla2Fails R.eps R.x R.ω`,

with the register in the module header's three classes.  The two ANALYTIC arms are

* the `T₀`-band arm, inside `DoorRowCarried_L` (`M4T0Datum.m4_hT0band_at_door` is the plug),
* the coprime-supply arm `M4CoprimeBlockMeanSq_L R M (m4BclGraded j₀ (2·MSan) (2·MStr))`;

everything else is regime arithmetic (the `g`-arm/`U1floor` shapes of the outer register, the
drift and delivered lines, the two `M4NonCoprime` gates, the modulus cap) or witnessed here.

The floor is the door's own, `j₀ = doorRowFloorL M = M·AdoorL M`; `M4Maximal`'s ⟦THE
CONSUMPTION NOTE⟧ is the ordering that makes it workable (`M` fixed before `U1floor`). -/
theorem m4_wave_structurally_closed_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            -- ⟦the modulus cap: the door's characters inside the capstone's range⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            -- ⟦the small lengths' trivial grade⟧
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 + the regime gates: the per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarried_L Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            -- ⟦R2's two gates⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general⟧
            M4CoprimeBlockMeanSq_L R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_L
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  -- ⟦R2⟧ the wave asks only the NON-COPRIME classes; `m4_nonCoprime_classMeanSq_L` delivers all
  have hnc : M4ClassBlockMeanSq_L R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_L (k := k) hM hBcl0 hgate harc hcp
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq

/-- **THE DOOR ROW'S CARRIED REGISTER AT THE LEVER** — `DoorRowCarried_L` (:146). -/
def DoorRowCarried_L_gk (K : ℕ) (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε C₁' M₀ cqS cgS cW SW Rbar0 Dmask : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
                (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
          (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ (ε ≤ theta293 - 1 / 500) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L_gk K χ M Xd = 0) ∧
    -- ⟦THE CARRY: the `T₀`-band arm, at `m4_hT0band_at_door_L`'s own conclusion⟧
    ((∫ t in (-(seamT0 X))..(seamT0 X),
        ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
      ≤ t0BandB X C₁' M₀) ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    (5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    ((4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

/-- The lever's sieved, χ-twisted datum is `1`-bounded — the `_gk` reading of
`M4DoorRow.norm_doorChiCoeff_le_one` (`memSCoeff` only deletes terms, at any base). -/
theorem norm_doorChiCoeff_le_one_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M n : ℕ) :
    ‖doorChiCoeff_L_gk K χ M n‖ ≤ 1 :=
  norm_memSCoeff_le_one (norm_liouChi_le_one χ) _ _ 2 n

/-- **THE TRIVIAL GRADE AT THE DOOR ROW, AT THE LEVER** — `doorRow_trivial_grade_L`
(:301). -/
theorem doorRow_trivial_grade_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ)
    {Xd : ℕ} (j : ℕ) (hXd : 0 < Xd) :
    1 / ((Xd : ℕ) : ℝ)
        * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                    ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ 4 := by
  have hXd0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by exact_mod_cast hXd
  have hhN : 0 < 2 ^ j := Nat.two_pow_pos j
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by exact_mod_cast hhN
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  -- ⟦the pointwise bound⟧
  have hpt : ∀ y ∈ Set.Icc ((Xd : ℕ) : ℝ) (2 * ((Xd : ℕ) : ℝ)),
      ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
          * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
              ((2 ^ j : ℕ) : ℝ)‖ ^ 2 ≤ 4 := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ y := le_trans hXd0.le hy.1
    have hs := norm_shortSum_le (norm_doorChiCoeff_le_one_L_gk K χ M)
      (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) (x := y) (hlen := ((2 ^ j : ℕ) : ℝ)) hy0 hh0.le
    have hnm : ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
        * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
            ((2 ^ j : ℕ) : ℝ)‖
        = 1 / ((2 ^ j : ℕ) : ℝ)
            * ‖shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb : ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
        * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
            ((2 ^ j : ℕ) : ℝ)‖ ≤ 2 := by
      rw [hnm]
      have h2h : ‖shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
          ((2 ^ j : ℕ) : ℝ)‖ ≤ 2 * ((2 ^ j : ℕ) : ℝ) := by linarith
      calc 1 / ((2 ^ j : ℕ) : ℝ)
            * ‖shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖
          ≤ 1 / ((2 ^ j : ℕ) : ℝ) * (2 * ((2 ^ j : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h2h (by positivity)
        _ = 2 := by field_simp
    have h0 := norm_nonneg (((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
      * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
          ((2 ^ j : ℕ) : ℝ))
    nlinarith
  -- ⟦the mean⟧
  have hint := shortSum_sq_intervalIntegrable (doorChiCoeff_L_gk K χ M)
    (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) ((2 ^ j : ℕ) : ℝ) ((Xd : ℕ) : ℝ) (2 * ((Xd : ℕ) : ℝ))
  have hmono := intervalIntegral.integral_mono_on (a := ((Xd : ℕ) : ℝ))
    (b := 2 * ((Xd : ℕ) : ℝ)) (by linarith) hint intervalIntegrable_const hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hbound : (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
      ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
          * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
              ((2 ^ j : ℕ) : ℝ)‖ ^ 2) ≤ ((Xd : ℕ) : ℝ) * 4 := by
    calc _ ≤ (2 * ((Xd : ℕ) : ℝ) - ((Xd : ℕ) : ℝ)) * 4 := hmono
      _ = ((Xd : ℕ) : ℝ) * 4 := by ring
  calc 1 / ((Xd : ℕ) : ℝ)
        * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
            ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y
                    ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ 1 / ((Xd : ℕ) : ℝ) * (((Xd : ℕ) : ℝ) * 4) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 4 := by field_simp

set_option maxHeartbeats 4000000 in
-- same cause as the landed §3: the ~90-binder instantiation (`DoorRowCarried_L_gk`'s
-- ~85-conjunct destructuring plus the capstone's 86-argument application) is the whole
-- cost — no tactic search happens here, every step is `exact`-shaped
/-- **THE DOOR ROW'S MEAN SQUARE, CARRIED, AT THE LEVER** — `m4_door_meansq_carried_L`
(:389). -/
theorem m4_door_meansq_carried_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (Qm q : ℕ) (χ : DirichletCharacter ℂ q), 0 < q → q ≤ Qm →
        ∀ (M Xd j : ℕ) (B : ℝ), 1 ≤ M → doorRowFloorL M ≤ j →
          DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M Xd j B →
            1 / ((Xd : ℕ) : ℝ)
                * (∫ y in ((Xd : ℕ) : ℝ)..(2 * ((Xd : ℕ) : ℝ)),
                    ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
                        * shortSum (doorChiCoeff_L_gk K χ M)
                            (seamS0 (2 * Xd) ((Xd : ℕ) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
              ≤ B := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hgen⟩ :=
    m4_meansq_per_chi_gen_L_gk K hK
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  -- ⟦THE SKOLEM CUT⟧ the masked-floor constant, as a function of the modulus range
  choose Kcf hKcf0 hcfl using capFreeFloor3_pieceDatum
  obtain ⟨Ctail, hCtail0, htail⟩ := m4_door_tail_supply_L_gk K
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro Qm q χ hq hqQm M Xd j B hM hj0 hcar
  obtain ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, C₁', M₀,
    cqS, cgS, cW, SW, Rbar0, Dmask,
    hXdX, hhj, hXee, hlX2, hhX, hhceil, hTann, hceil5, hT₀le, hTbot, hLXL, hLe, hL256,
    hXdQ, hP3, hlogP2, hQbot, hQlog, hQL, hPlow, hQhigh, hPQ, hQ0, hHX, hH2, hPj1, hQXd,
    hXdbig, hdom, hW5, hkth, hMtX, hC16, hRradW, hthinpin, hMtpin, hkkg, hMtY,
    hRrad0, hV1, hVδ, hlogV, hδsq, hksthr, hVJg, hCb0, hCbound, hXthr,
    hX₀k, hMfl0k, hk2, hkX, hgateW, hYpin, hWY, hXY, hthrY,
    hcqgate, hCqgate, hε0, hεup, habs,
    hQlogXd, hdomband, hlogb, hPQratio, h2688,
    hDmask0, hdebit, hcfthr,
    hc0, hce, hc1, hblk, hbox, hD1, hDk, hX₀j, hsqXa, hpin,
    hXae, hMXa, hXaX, hMfl0, hboxw, hS0, hSbd, hendGen, hRbdU, hRbar00, hRgrade,
    hend, hT0band, hcff, hgP1, hgRows, hL4096, henv⟩ := hcar
  subst hXdX
  subst hhj
  haveI : NeZero q := ⟨hq.ne'⟩
  -- ⟦the scale's arithmetic⟧
  have hX0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXee
  have h1ee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.exp_pos 1
    linarith
  have hXd1 : 1 ≤ Xd := by
    have : (1 : ℝ) ≤ ((Xd : ℕ) : ℝ) := le_trans h1ee hXee
    exact_mod_cast this
  have hexp2 : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlog1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hLXe : Real.exp 1 ≤ Real.log ((Xd : ℕ) : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hP1 : 1 ≤ P := by omega
  have hP2 : 2 ≤ P := by omega
  -- ⟦THE LENGTH FLOOR IS FREE⟧: both `4 ≤ h` and the capstone's window gate
  have hj2 : 2 ≤ j := by
    have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
    have hAle : AdoorL M ≤ M * AdoorL M := Nat.le_mul_of_pos_left _ hM
    have hjf : M * AdoorL M ≤ j := hj0
    have h18 : (2 : ℕ) ≤ 2 ^ 18 := by norm_num
    omega
  have hh4 : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    have hN : (4 : ℕ) ≤ 2 ^ j := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    exact_mod_cast hN
  have hQ1h : ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) :=
    (door_length_gate_iff_L_gk K).mpr hj0
  -- ⟦THE DATUM SIDE (class (C)): the cut and its three S8 slots⟧
  have haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd →
      winCutH Xd (doorChiCoeff_L_gk K χ M) n = doorChiCoeff_L_gk K χ M n :=
    fun n h1 h2 => winCutH_of_mem _ h1 h2
  have ha0 : winCutH Xd (doorChiCoeff_L_gk K χ M) Xd = 0 := winCutH_supp0 _ le_rfl
  -- ⟦the pin chain and the per-block puncture law⟧
  have hcoefPin : SeamCoefW Xd P Q (winCutH Xd (doorChiCoeff_L_gk K χ M)) (doorChiCoeff_L_gk K χ M)
      (liouChi χ) :=
    doorChiCoeff_seamCoefW_at_door_H_L_gk K χ hM hlog1 hQXd hPlow haH ha0 hend
  have hcoefBand := doorChiCoeff_seamCoefW_punct_H_L_gk K χ hM haH ha0 hend
  -- ⟦the per-piece cap-free floor⟧
  have hfloor : ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) ((Xd : ℕ) : ℝ) := by
    intro 𝒥 h𝒥
    exact hcfl Qm q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥
      ((Xd : ℕ) : ℝ) Dmask hqQm hXee hDmask0 (hdebit 𝒥 h𝒥) hcfthr
  -- ⟦THE SOCKET⟧ at `Ps := 1`, `J := 2`, read at the door datum
  have hsock0 := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q 2 1 Mt kk Dd Xa cqS L cgS Cb
    ((Xd : ℕ) : ℝ) theta293 (seamRad ((Xd : ℕ) : ℝ)) ((Xd : ℕ) : ℝ) 0 Rbar0 cW SW
    hc0 hce hc1 hCb0 hCbound hP1 le_rfl hRrad0 theta293_pos theta293_lt_one_div_32.le
    hLXe hPlow hQhigh hPQ hfloor hblk hbox hD1 hDk hX₀j hsqXa hpin hXae hMXa hXaX hMfl0
    hboxw hS0 hSbd hendGen hRbdU
  have hsockR : CofactorSocket (H83 ((Xd : ℕ) : ℝ) theta293) (2 * Xd) Xd P Q
      ((Xd : ℕ) : ℝ) (seamRad ((Xd : ℕ) : ℝ)) 0 (4 * Rbar0) (doorChiCoeff_L_gk K χ M) := by
    have hs := cofactorSocket_doorChiCoeff_L_gk K χ hsock0
    have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by ring
    rwa [he] at hs
  -- ⟦THE COPRIME TAIL⟧: `Mtail` and `EP2` are computed, not carried
  have hNcast : (((2 * Xd : ℕ)) : ℝ) = 2 * ((Xd : ℕ) : ℝ) := by push_cast; ring
  obtain ⟨hMtail, hMtail0, hEP2⟩ := htail q χ M P Q Xd (2 * Xd) ((Xd : ℕ) : ℝ) ε
    rfl hNcast hX0 hL256 hP2 hPQ hXd1 hQlogXd hdomband hPlow hlogb habs hPQratio h2688
  -- ⟦THE ROW-SUM TRANSPORT⟧ the register carries the LANDED `a2RowsSum_L`, which is the
  -- STRONGER gate: the lever grows `𝒫ⱼ` and `𝒫ⱼ` sits in a denominator
  -- (`ThmA2.a2RowsSum_gk_le`), so the levered capstone's slot follows a fortiori
  have hgRowsK : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
    have hle := a2RowsSum_L_gk_le K M Xd
    linarith
  -- ⟦THE CAPSTONE⟧
  have hres := hgen Qm q χ hqQm (2 * Xd) Xd P Q M (winCutH Xd (doorChiCoeff_L_gk K χ M)) (liouChi χ)
    (doorChiCoeff_L_gk K χ M)
    (fun i => memSPunctCoeff (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 i
      (liouChi χ))
    ((Xd : ℕ) : ℝ) ((2 ^ j : ℕ) : ℝ) δ' V VJ L Cb (seamRad ((Xd : ℕ) : ℝ)) (4 * Rbar0)
    kmin Ymax ε _ _ C₁' M₀
    rfl rfl hXee hlX2 hh4 hhX hhceil hTann hceil5 hT₀le hTbot hLXL hLe hM hXdQ hQ1h hP3
    hlogP2 hQbot hQlog hQL hPlow hQhigh hPQ hQ0 hHX hH2 hPj1 hQXd hXdbig hdom
    hW5 hkth hMtX hC16 hRradW hthinpin hMtpin hkkg hMtY
    hRrad0 le_rfl le_rfl hV1 hVδ hlogV hδsq hksthr hVJg hCb0 hCbound hXthr
    hX₀k hMfl0k hk2 hkX hgateW hYpin hWY hXY hthrY hcqgate hCqgate
    hε0 hεup habs hEP2 le_rfl
    (doorRow_ha1_L_gk K χ M Xd) (norm_liouChi_le_one χ)
    (fun n hn => doorRow_hsupp0_L_gk K χ M Xd n hn) (fun n hn => doorRow_hasupp_L_gk K χ M Xd n hn)
    hMtail0 hMtail
    (norm_doorChiCoeff_le_one_L_gk K χ M) (fun i n => norm_doorPunctCoeff_le_one_L_gk K χ M i n)
    (by positivity) hRgrade hsockR hcoefBand hcoefPin hT0band hcff hgP1 hgRowsK hL4096
  -- ⟦THE DATUM BRIDGE⟧ the cut is invisible to the row's short sum
  simp only [shortSum_winCutH_seamS0] at hres
  exact le_trans hres henv

/-- **THE DOOR'S DYADIC ROW, CARRIED, AT THE LEVER** — `m4_dyadicRow_carried_L` (:523). -/
theorem m4_dyadicRow_carried_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ (Cq cq T₀ Xcap Cs Ccc : ℝ) (Kfl : ℕ → ℝ) (Xsk : ℝ) (Kcf : ℕ → ℝ) (Ctail : ℝ),
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ (∀ Qm : ℕ, 0 ≤ Kfl Qm) ∧
      0 < Xsk ∧ (∀ Qm : ℕ, 0 ≤ Kcf Qm) ∧ 0 < Ctail ∧
      ∀ (R : ChowlaRegime) (Qm M k : ℕ) (MS : ℕ → ℕ → ℝ), 1 ≤ M →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
        (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
        (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
          ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H, doorRowFloorL M ≤ j →
            ∀ s ≤ H,
              DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc (Kfl Qm) Xsk (Kcf Qm) Ctail χ M
                (doorLadder R.x H (i + 1) + s) j (MS j H)) →
        M4ChiDyadicRowMeanSq_L_gk K R M k MS := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_door_meansq_carried_L_gk K hK
  refine ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, ?_⟩
  intro R Qm M k MS hM hQm htriv hcar H hlo hhi q hq hqQ i hik χ j hjL s hsH
  have hxH : H + 1 ≤ R.x := regime_window_headroom R hhi
  have hApos : 0 < doorLadder R.x H (i + 1) + s := by
    have := doorLadder_floor hxH (i + 1); omega
  by_cases hcase : doorRowFloorL M ≤ j
  · -- ⟦the capstone speaks: §3 at the carried register⟧
    have hqQm : q ≤ Qm := by
      have hR : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
      exact_mod_cast hR
    exact hrow Qm q χ hq hqQm M (doorLadder R.x H (i + 1) + s) j (MS j H) hM hcase
      (hcar H hlo hhi q hq hqQ i hik χ j hjL hcase s hsH)
  · -- ⟦below the floor: the trivial grade⟧
    exact le_trans (doorRow_trivial_grade_L_gk K χ M j hApos) (htriv j H (not_le.mp hcase))

set_option maxHeartbeats 1600000 in
-- same cause as the landed §5: elaborating the register (which mentions `DoorRowCarried_L_gk`
-- under six binders) against `m4_wave_closed_of_dyadicRow_L_gk`'s own list is the whole cost
/-- **THE M4 WAVE, STRUCTURALLY CLOSED, AT THE LEVER** — `m4_wave_structurally_closed_L`
(:579).  The register is the landed one at `G := s13GK K M`; the two analytic arms and every
regime gate are unchanged in shape. -/
theorem m4_wave_structurally_closed_L_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            -- ⟦the modulus cap: the door's characters inside the capstone's range⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            -- ⟦the small lengths' trivial grade⟧
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 + the regime gates: the per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            -- ⟦R2's two gates⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general⟧
            M4CoprimeBlockMeanSq_L_gk K R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hrow⟩ :=
    m4_dyadicRow_carried_L_gk K hK
  obtain ⟨Cg, ε, δ₀, hCg, hε, hδ₀, hmain⟩ := m4_wave_closed_of_dyadicRow_L_gk K
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl Qm, Xsk, Kcf Qm, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl Qm, hXsk0, hKcf0 Qm, hCtail0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  have hBcl0 : ∀ H : ℕ, 0 ≤ m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H)
      (fun H => 2 * MStr H) H := fun H =>
    m4BclGraded_nonneg (Fan := fun H => 2 * MSan H) (Ftr := fun H => 2 * MStr H)
      (show (0 : ℝ) ≤ 2 * MSan H by have := hMSan0 H; linarith)
      (show (0 : ℝ) ≤ 2 * MStr H by have := hMStr0 H; linarith)
  -- ⟦R2⟧ the wave asks only the NON-COPRIME classes; `m4_nonCoprime_classMeanSq_L` delivers all
  have hnc : M4ClassBlockMeanSq_L_gk K R M k
      (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) :=
    m4_nonCoprime_classMeanSq_L_gk K (k := k) hM hBcl0 hgate harc hcp
  refine hR δ Braw MS MSan MStr (doorRowFloorL M) M k hgates hMSan0 hMStr0 hBraw0 han htr
    hdrift hdel hrest (hrow R Qm M k MS hM hQm htriv hcar) ?_
  intro H hlo hhi q hq hqQ i hik r hrq _hncop
  exact hnc H hlo hhi q hq hqQ i hik r hrq
/-! ## §4 — `M4T0DatumDischarge` -/

/-- **THE MASK'S ℓ¹(1/n) MASS**, from `RamareMassTail.ramTailWeight_mass_le` at a covering
window.  `z`-free, `y`-free, `X`-free. -/
theorem jMask_mass_le_L {𝒥 : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {P Q : ℕ} (z : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q)
    (hP : ∀ j ∈ 𝒥, P ≤ Pseq j) (hQ : ∀ j ∈ 𝒥, Qseq j ≤ Q) :
    ∑ b ∈ Finset.Icc 1 z, maskTailWeight (jMask 𝒥 Pseq Qseq) 0 b / (b : ℝ)
      ≤ windowMassConst P Q := by
  refine le_trans (Finset.sum_le_sum ?_) (ramTailWeight_mass_le P Q z hP4 hPQ le_rfl zero_le_one)
  intro b _
  exact div_le_div_of_nonneg_right
    (maskTailWeight_zero_le_ramTailWeight_zero (jMask_covered hP hQ) b) (Nat.cast_nonneg b)

/-- **⟦D3-DISCHARGE⟧ THE `hpiece` SLOT AT THE DOOR DATUM** (`m4_hpiece_at_door_L`).

The FROZEN binder of `M4T0Datum.m4_hT0band_at_door`, met exactly, at the grade
`S₀ = C'/(log X)^A`.  Every remaining hypothesis is carried and named:

* `x₀ ≤ X_d` — the carrier's own eventual threshold (`MlamGrChiMask_rate`);
* `400 ≤ X` — the HEIGHT fit's small-`k` corner (`seamT0_le_sqrt_sqrt`);
* `q ≤ (log X)^{10}` — the CONDUCTOR fit, transported up the range by `log k ≥ log X`;
* the three Rankin gates, per `k ∈ [X_d, N]` — `RamareMassTail`'s own, `y`-dependent, hence
  quantified inside (the honest quantifier move);
* `∀ j ∈ [1,2], P ≤ P_j` and `Q_j ≤ Q` — the covering window for the mass/tail rows. -/
theorem m4_hpiece_at_door_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (3072 * M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j ≤ Q) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ A) →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xd ≤ k → k ≤ N →
            ‖∑ n ∈ Finset.Icc 1 k,
                pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) n
                  * eIu (-t) n‖
              ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨C', x₀, hC'pos, hrate⟩ := piece_partial_sum_rate hMmu A hA P Q hP4 hPQ
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  -- the conductor fit, transported up the range
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  -- the height fit, through the small-`k` corner and `√√` monotonicity
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT⟧** (`m4_hT0band_at_door_discharged_L`).  `m4_hpiece_at_door_L`
composed with `M4T0Datum.m4_hT0band_at_door`:

  `∫_{−T₀}^{T₀} ‖dpolyA (winCutH X_d (doorChiCoeff_L χ M)) (seamS0 N X) t‖² dt`
  `   ≤ t0BandB X (cfbC₁ X C₁) M₀`,   `T₀ = seamT0 X = (log X)^{1/45}`,

i.e. `M4MeanSq.m4_meansq_per_chi_gen`'s `hT0band` slot at the door's sieved χ-twisted un-phased
datum, WITHOUT any per-piece hand-off left in the middle.  The `hpiece` binder that
`M4T0Datum` carried is gone; what remains are the named gates of `m4_hpiece_at_door_L`, the
grade fit `C' ≤ (log X)^{A−1/2+1/1000}` (reduced by `t0datum_grade_of_fit`) and
`cfb_t0band_supply_of_sup`'s own `hErr`. -/
theorem m4_hT0band_at_door_discharged_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (3072 * M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j ≤ Q) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ A) →
        8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨C', x₀, hC'pos, hpiece⟩ := m4_hpiece_at_door_L hMmu A hA P Q hP4 hPQ
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-- **THE DOOR'S COVERING WINDOW** (`door_cover_L`): `[calP A G 1, calQK A G M 2]` contains every
block the door's `𝒥 ⊆ [1,2]` names. -/
theorem door_cover_L (M : ℕ) (hM : 1 ≤ M) :
    (∀ j ∈ Finset.Icc 1 2, calP (AdoorL M) (3072 * M) 1 ≤ calP (AdoorL M) (3072 * M) j)
      ∧ (∀ j ∈ Finset.Icc 1 2,
          calQK (AdoorL M) (3072 * M) M j ≤ calQK (AdoorL M) (3072 * M) M 2) := by
  have hG : 1 ≤ 3072 * M := by omega
  constructor
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact calP_door_ge hG hj.1 hj.2
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact calQK_door_le hG hj.1 hj.2

/-- **THE DOOR'S COVERING WINDOW IS ADMISSIBLE** (`door_window_bounds_L`): `4 ≤ P₁` and
`P₁ ≤ Q₂`, the two side conditions `m4_hpiece_at_door_L` reads on `[P,Q]`.  Both come from the
door's own ladder: `P₁ = 2^{AdoorL M}` with `AdoorL M ≥ 2^{18}` (`DoorFrame.Adoor_ge_old`), and
`Q₂ ≥ Q₁ = 2^{M·AdoorL M} ≥ P₁`.  With `door_cover_L` this closes the door instantiation: no
window hypothesis of the exit is left for the consumer. -/
theorem door_window_bounds_L (M : ℕ) (hM : 1 ≤ M) :
    4 ≤ calP (AdoorL M) (3072 * M) 1
      ∧ calP (AdoorL M) (3072 * M) 1 ≤ calQK (AdoorL M) (3072 * M) M 2 := by
  have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
  have hPeq : calP (AdoorL M) (3072 * M) 1 = 2 ^ (AdoorL M) := by rw [calP, calE_one]
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (AdoorL M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · refine le_trans ?_ (calQK_door_le (j := 1) (by omega : 1 ≤ 3072 * M) le_rfl (by norm_num))
    rw [hPeq, calQK, calE_one]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 : 1 ≤ 1 ^ 2 * M := by simpa using hM
    calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
      _ ≤ (1 ^ 2 * M) * AdoorL M := Nat.mul_le_mul h1 le_rfl

/-- **⟦D3-DISCHARGE, SPLIT-HOISTED⟧ THE `hpiece` SLOT** (`m4_hpiece_at_door_split_L`) —
`m4_hpiece_at_door_L` at the window-free threshold. -/
theorem m4_hpiece_at_door_split_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (3072 * M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
            ∀ k : ℕ, Xd ≤ k → k ≤ N →
              ‖∑ n ∈ Finset.Icc 1 k,
                  pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) n
                    * eIu (-t) n‖
                ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨x₀, hsplit⟩ := piece_partial_sum_rate_split hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hrate⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT, SPLIT-HOISTED⟧** (`m4_hT0band_at_door_discharged_split_L`) —
`m4_hT0band_at_door_discharged_L` at the window-free threshold.  This is the link the door's
band slot consumes: `x₀` is fixed once and for all, and only the grade constant `C'` is
allowed to read the door's `M`-dependent window. -/
theorem m4_hT0band_at_door_discharged_split_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
          x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (3072 * M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
          4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
              ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 N X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨x₀, hsplit⟩ := m4_hpiece_at_door_split_L hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hpiece⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-- **⟦D3, SPLIT-HOISTED + GRADED⟧ THE PIECE'S PARTIAL SUM**
(`piece_partial_sum_rate_split_graded_L`)
— §7's link 2 with `C` in the top block and the window-explicit cap on `C'` carried. -/
theorem piece_partial_sum_rate_split_graded_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ C * (4 : ℝ) ^ A * windowMassConst P Q + 1 ∧
        ∀ k : ℕ, x₀ ≤ k → 16 ≤ k →
        16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) →
        8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ) →
        Real.exp (2 * Real.exp 1
            * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
          ≤ (Real.log (k : ℝ)) ^ A →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          (q : ℝ) ≤ (Real.log k) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) →
          ∀ (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ),
            (∀ j ∈ 𝒥, P ≤ Pseq j) → (∀ j ∈ 𝒥, Qseq j ≤ Q) →
            ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n‖
              ≤ C' * k / (Real.log k) ^ A := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := MlamGrChiMask_rate_split_graded hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hC'le, hrate⟩ := hsplit (windowMassConst P Q) (Real.exp_pos _).le
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro k hk hk16 hgHalf hgO1 hgWin q _ χ hq t ht 𝒥 Pseq Qseq hP hQ
  rw [piece_partial_sum_eq]
  have hts : |(-t)| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by rwa [abs_neg]
  exact hrate k hk q χ hq (-t) hts (jMask 𝒥 Pseq Qseq) 0 le_rfl zero_le_one
    (jMask_mass_le_L _ hP4 hPQ hP hQ)
    (jMask_htail_le k A hA hP4 hPQ hk16 hgHalf hgO1 hgWin hP hQ)

/-- **⟦D3-DISCHARGE, SPLIT-HOISTED + GRADED⟧ THE `hpiece` SLOT**
(`m4_hpiece_at_door_split_graded_L`)
— §7's link 3 carrying the window-explicit cap. -/
theorem m4_hpiece_at_door_split_graded_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ C * (4 : ℝ) ^ A * windowMassConst P Q + 1 ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (3072 * M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
            ∀ k : ℕ, Xd ≤ k → k ≤ N →
              ‖∑ n ∈ Finset.Icc 1 k,
                  pieceDatum χ 𝒥 (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) n
                    * eIu (-t) n‖
                ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := piece_partial_sum_rate_split_graded_L hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hC'le, hrate⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT, SPLIT-HOISTED + GRADED⟧**
(`m4_hT0band_at_door_discharged_split_graded_L`) — §7's link 4 carrying the window-explicit cap.
This is the link the door's band slot consumes: `x₀` and `C` are fixed once and for all, and
the band constant `C'` is now bounded by an EXPLICIT function of the door's window. -/
theorem m4_hT0band_at_door_discharged_split_graded_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ C * (4 : ℝ) ^ A * windowMassConst P Q + 1 ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
          x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (3072 * M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (3072 * M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
          4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
              ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 N X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := m4_hpiece_at_door_split_graded_L hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hC'le, hpiece⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-- **⟦D3-DISCHARGE — THE `hpiece` SLOT⟧ AT THE G-LEVER** (`m4_hpiece_at_door_L_gk`). -/
theorem m4_hpiece_at_door_L_gk (K : ℕ) (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ A) →
        ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
          ∀ k : ℕ, Xd ≤ k → k ≤ N →
            ‖∑ n ∈ Finset.Icc 1 k,
                pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) n
                  * eIu (-t) n‖
              ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨C', x₀, hC'pos, hrate⟩ := piece_partial_sum_rate hMmu A hA P Q hP4 hPQ
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  -- the conductor fit, transported up the range
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  -- the height fit, through the small-`k` corner and `√√` monotonicity
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT⟧ AT THE G-LEVER**
(`m4_hT0band_at_door_discharged_L_gk`). -/
theorem m4_hT0band_at_door_discharged_L_gk (K : ℕ) (hMmu : MmuChiRate) (A : ℝ)
    (hA : 0 < A) (P Q : ℕ)
    (hP4 : 4 ≤ P) (hPQ : P ≤ Q) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
        ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
        x₀ ≤ Xd → 16 ≤ Xd →
        (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
        (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
        (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
        (∀ k : ℕ, Xd ≤ k → k ≤ N →
          Real.exp (2 * Real.exp 1
              * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
            ≤ (Real.log (k : ℝ)) ^ A) →
        8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
        4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
            ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
        (∫ t in (-(seamT0 X))..(seamT0 X),
            ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨C', x₀, hC'pos, hpiece⟩ := m4_hpiece_at_door_L_gk K hMmu A hA P Q hP4 hPQ
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L_gk K χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-- **THE DOOR'S COVERING WINDOW, AT THE G-LEVER** (`door_cover_L_gk`) — the ladder
monotonicity is `G`-generic; only `1 ≤ G` is used, supplied by `GLever.one_le_s13GK`. -/
theorem door_cover_L_gk (K : ℕ) (M : ℕ) (hM : 1 ≤ M) :
    (∀ j ∈ Finset.Icc 1 2, calP (AdoorL M) (s13GK K M) 1 ≤ calP (AdoorL M) (s13GK K M) j)
      ∧ (∀ j ∈ Finset.Icc 1 2,
          calQK (AdoorL M) (s13GK K M) M j ≤ calQK (AdoorL M) (s13GK K M) M 2) := by
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hM
  constructor
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact calP_door_ge hG hj.1 hj.2
  · intro j hj
    rw [Finset.mem_Icc] at hj
    exact calQK_door_le hG hj.1 hj.2

/-- **THE DOOR'S COVERING WINDOW IS ADMISSIBLE, AT THE G-LEVER**
(`door_window_bounds_L_gk`).  `P₁ = 2^{AdoorL M}` is LEVEL 1 and unmoved; the upper leg goes
through `calQK_door_le` at `1 ≤ s13GK K M`. -/
theorem door_window_bounds_L_gk (K : ℕ) (M : ℕ) (hM : 1 ≤ M) :
    4 ≤ calP (AdoorL M) (s13GK K M) 1
      ∧ calP (AdoorL M) (s13GK K M) 1 ≤ calQK (AdoorL M) (s13GK K M) M 2 := by
  have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
  have hPeq : calP (AdoorL M) (s13GK K M) 1 = 2 ^ (AdoorL M) := by rw [calP, calE_one]
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (AdoorL M) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · refine le_trans ?_ (calQK_door_le (j := 1) (one_le_s13GK K hM) le_rfl (by norm_num))
    rw [hPeq, calQK, calE_one]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 : 1 ≤ 1 ^ 2 * M := by simpa using hM
    calc AdoorL M = 1 * AdoorL M := (one_mul _).symm
      _ ≤ (1 ^ 2 * M) * AdoorL M := Nat.mul_le_mul h1 le_rfl

/-- **⟦D3-DISCHARGE, SPLIT-HOISTED⟧ THE `hpiece` SLOT, AT THE G-LEVER**
(`m4_hpiece_at_door_split_L_gk`).  `piece_partial_sum_rate_split` is `G`-FREE and is reused. -/
theorem m4_hpiece_at_door_split_L_gk (K : ℕ) (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
            ∀ k : ℕ, Xd ≤ k → k ≤ N →
              ‖∑ n ∈ Finset.Icc 1 k,
                  pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) n
                    * eIu (-t) n‖
                ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨x₀, hsplit⟩ := piece_partial_sum_rate_split hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hrate⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT, SPLIT-HOISTED⟧ AT THE G-LEVER**
(`m4_hT0band_at_door_discharged_split_L_gk`). -/
theorem m4_hT0band_at_door_discharged_split_L_gk (K : ℕ) (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ x₀ : ℕ, ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
          x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
          4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
              ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 N X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨x₀, hsplit⟩ := m4_hpiece_at_door_split_L_gk K hMmu A hA
  refine ⟨x₀, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hpiece⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L_gk K χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-- **⟦D3-DISCHARGE, SPLIT-HOISTED + GRADED⟧ THE `hpiece` SLOT, AT THE G-LEVER**
(`m4_hpiece_at_door_split_graded_L_gk`). -/
theorem m4_hpiece_at_door_split_graded_L_gk (K : ℕ) (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ C * (4 : ℝ) ^ A * windowMassConst P Q + 1 ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
            ∀ k : ℕ, Xd ≤ k → k ≤ N →
              ‖∑ n ∈ Finset.Icc 1 k,
                  pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) n
                    * eIu (-t) n‖
                ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := piece_partial_sum_rate_split_graded_L hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hC'le, hrate⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT, SPLIT-HOISTED + GRADED⟧ AT THE G-LEVER**
(`m4_hT0band_at_door_discharged_split_graded_L_gk`). -/
theorem m4_hT0band_at_door_discharged_split_graded_L_gk (K : ℕ) (hMmu : MmuChiRate)
    (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q : ℕ), 4 ≤ P → P ≤ Q →
      ∃ C' : ℝ, 0 < C' ∧ C' ≤ C * (4 : ℝ) ^ A * windowMassConst P Q + 1 ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
          x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
          4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
              ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 N X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := m4_hpiece_at_door_split_graded_L_gk K hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q hP4 hPQ
  obtain ⟨C', hC'pos, hC'le, hpiece⟩ := hsplit P Q hP4 hPQ
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin
    hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L_gk K χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hgHalf hgO1 hgWin) hErr

/-- **THE MASK'S ℓ¹(1/n) MASS, PER BLOCK** (`jMask_mass_le_prod_L`) — every block the mask
names sits in ONE of two windows, and the mass is at most the PRODUCT of the two window mass
constants.  The `z`-free, `y`-free, `X`-free twin of `jMask_mass_le_L`. -/
theorem jMask_mass_le_prod_L {𝒥 : Finset ℕ} {Pseq Qseq : ℕ → ℕ} {P₁ Q₁ P₂ Q₂ : ℕ} (z : ℕ)
    (h₁4 : 4 ≤ P₁) (h₁ : P₁ ≤ Q₁) (h₂4 : 4 ≤ P₂) (h₂ : P₂ ≤ Q₂)
    (hcov : ∀ j ∈ 𝒥, (P₁ ≤ Pseq j ∧ Qseq j ≤ Q₁) ∨ (P₂ ≤ Pseq j ∧ Qseq j ≤ Q₂)) :
    ∑ b ∈ Finset.Icc 1 z, maskTailWeight (jMask 𝒥 Pseq Qseq) 0 b / (b : ℝ)
      ≤ windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂ := by
  classical
  set S : Finset ℕ := primeBand P₁ Q₁ ∪ primeBand P₂ Q₂ with hSdef
  have hcovS : ∀ p : ℕ, p.Prime → jMask 𝒥 Pseq Qseq p = true → p ∈ S := by
    intro p hp hmask
    obtain ⟨j, hj, hpj⟩ := jMask_iff.mp hmask
    rw [hSdef, Finset.mem_union, primeBand, primeBand, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Icc]
    rcases hcov j hj with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact Or.inl ⟨⟨le_trans hA hpj.1, le_trans hpj.2 hB⟩, hp⟩
    · exact Or.inr ⟨⟨le_trans hA hpj.1, le_trans hpj.2 hB⟩, hp⟩
  have hstep : ∑ b ∈ Finset.Icc 1 z, maskTailWeight (jMask 𝒥 Pseq Qseq) 0 b / (b : ℝ)
      ≤ ∑ b ∈ (Finset.Icc 1 z).filter (fun b => b.primeFactors ⊆ S), 1 / (b : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum ?_
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    rw [maskTailWeight_zero_param]
    by_cases hsm : b ≠ 0 ∧ MaskSmooth (jMask 𝒥 Pseq Qseq) b
    · have hsub : b.primeFactors ⊆ S := by
        intro p hpm
        exact hcovS p (Nat.prime_of_mem_primeFactors hpm) (hsm.2 p hpm)
      rw [if_pos hsm, if_pos hsub]
    · rw [if_neg hsm, zero_div]
      split_ifs
      · positivity
      · exact le_rfl
  exact le_trans hstep (twoWindow_mass_le P₁ Q₁ P₂ Q₂ z h₁4 h₁ h₂4 h₂)

/-- **THE DOOR'S PER-BLOCK WINDOWS ARE ADMISSIBLE, AT THE G-LEVER**
(`door_block_bounds_L_gk`): `4 ≤ 𝒫_j` and `𝒫_j ≤ 𝒬_j` at each block `j ∈ {1,2}` — the two
side conditions the per-block mass reads. -/
theorem door_block_bounds_L_gk (K M : ℕ) (hM : 1 ≤ M) {j : ℕ} (hj : 1 ≤ j) :
    4 ≤ calP (AdoorL M) (s13GK K M) j
      ∧ calP (AdoorL M) (s13GK K M) j ≤ calQK (AdoorL M) (s13GK K M) M j := by
  have hG : 1 ≤ s13GK K M := one_le_s13GK K hM
  have hE1 : AdoorL M ≤ calE (AdoorL M) (s13GK K M) j := by
    have := calE_mono (AdoorL M) hG hj
    rwa [calE_one] at this
  have hA : 2 ^ 18 ≤ AdoorL M := AdoorL_ge_old hM
  refine ⟨?_, ?_⟩
  · rw [calP]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (calE (AdoorL M) (s13GK K M) j) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [calP, calQK]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have h1 : 1 ≤ j ^ 2 * M := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by positivity) (by omega))
    calc calE (AdoorL M) (s13GK K M) j = 1 * calE (AdoorL M) (s13GK K M) j := (one_mul _).symm
      _ ≤ (j ^ 2 * M) * calE (AdoorL M) (s13GK K M) j := Nat.mul_le_mul_right _ h1

/-- **THE DOOR'S BLOCKS SIT ONE PER WINDOW, AT THE G-LEVER** (`door_block_cover_L_gk`) — the
per-block coverage the product mass reads, at the ladder's own two blocks. -/
theorem door_block_cover_L_gk (K M : ℕ) :
    ∀ j ∈ Finset.Icc 1 2,
      (calP (AdoorL M) (s13GK K M) 1 ≤ calP (AdoorL M) (s13GK K M) j
          ∧ calQK (AdoorL M) (s13GK K M) M j ≤ calQK (AdoorL M) (s13GK K M) M 1)
        ∨ (calP (AdoorL M) (s13GK K M) 2 ≤ calP (AdoorL M) (s13GK K M) j
          ∧ calQK (AdoorL M) (s13GK K M) M j ≤ calQK (AdoorL M) (s13GK K M) M 2) := by
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.mp hj
  interval_cases j
  · exact Or.inl ⟨le_rfl, le_rfl⟩
  · exact Or.inr ⟨le_rfl, le_rfl⟩

/-- **⟦D3, SPLIT-HOISTED + GRADED, PER BLOCK⟧** (`piece_partial_sum_rate_split_graded_prod_L`)
— `piece_partial_sum_rate_split_graded_L` with the mass budget priced PER BLOCK.  The covering
window `[P,Q]` and its three tail gates are UNCHANGED (they are what the Rankin row reads);
only the `C'`-cap moves from `windowMassConst P Q` to the product form. -/
theorem piece_partial_sum_rate_split_graded_prod_L (hMmu : MmuChiRate) (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q P₁ Q₁ P₂ Q₂ : ℕ), 4 ≤ P → P ≤ Q →
      4 ≤ P₁ → P₁ ≤ Q₁ → 4 ≤ P₂ → P₂ ≤ Q₂ →
      ∃ C' : ℝ, 0 < C' ∧
        C' ≤ C * (4 : ℝ) ^ A * (windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂) + 1 ∧
        ∀ k : ℕ, x₀ ≤ k → 16 ≤ k →
        16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ) →
        8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ) →
        Real.exp (2 * Real.exp 1
            * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
          ≤ (Real.log (k : ℝ)) ^ A →
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          (q : ℝ) ≤ (Real.log k) ^ (10 : ℕ) →
          ∀ t : ℝ, |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) →
          ∀ (𝒥 : Finset ℕ) (Pseq Qseq : ℕ → ℕ),
            (∀ j ∈ 𝒥, P ≤ Pseq j) → (∀ j ∈ 𝒥, Qseq j ≤ Q) →
            (∀ j ∈ 𝒥, (P₁ ≤ Pseq j ∧ Qseq j ≤ Q₁) ∨ (P₂ ≤ Pseq j ∧ Qseq j ≤ Q₂)) →
            ‖∑ n ∈ Finset.Icc 1 k, pieceDatum χ 𝒥 Pseq Qseq n * eIu (-t) n‖
              ≤ C' * k / (Real.log k) ^ A := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := MlamGrChiMask_rate_split_graded hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q P₁ Q₁ P₂ Q₂ hP4 hPQ h₁4 h₁ h₂4 h₂
  obtain ⟨C', hC'pos, hC'le, hrate⟩ := hsplit
    (windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂)
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro k hk hk16 hgHalf hgO1 hgWin q _ χ hq t ht 𝒥 Pseq Qseq hP hQ hblk
  rw [piece_partial_sum_eq]
  have hts : |(-t)| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by rwa [abs_neg]
  exact hrate k hk q χ hq (-t) hts (jMask 𝒥 Pseq Qseq) 0 le_rfl zero_le_one
    (jMask_mass_le_prod_L _ h₁4 h₁ h₂4 h₂ hblk)
    (jMask_htail_le k A hA hP4 hPQ hk16 hgHalf hgO1 hgWin hP hQ)

/-- **⟦D3-DISCHARGE, SPLIT-HOISTED + GRADED, PER BLOCK⟧ THE `hpiece` SLOT, AT THE G-LEVER**
(`m4_hpiece_at_door_split_graded_prod_L_gk`). -/
theorem m4_hpiece_at_door_split_graded_prod_L_gk (K : ℕ) (hMmu : MmuChiRate) (A : ℝ)
    (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q P₁ Q₁ P₂ Q₂ : ℕ), 4 ≤ P → P ≤ Q →
      4 ≤ P₁ → P₁ ≤ Q₁ → 4 ≤ P₂ → P₂ ≤ Q₂ →
      ∃ C' : ℝ, 0 < C' ∧
        C' ≤ C * (4 : ℝ) ^ A * (windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂) + 1 ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
          (∀ j ∈ Finset.Icc 1 2,
              (P₁ ≤ calP (AdoorL M) (s13GK K M) j
                  ∧ calQK (AdoorL M) (s13GK K M) M j ≤ Q₁)
                ∨ (P₂ ≤ calP (AdoorL M) (s13GK K M) j
                  ∧ calQK (AdoorL M) (s13GK K M) M j ≤ Q₂)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset, ∀ t : ℝ, |t| ≤ seamT0 X →
            ∀ k : ℕ, Xd ≤ k → k ≤ N →
              ‖∑ n ∈ Finset.Icc 1 k,
                  pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) n
                    * eIu (-t) n‖
                ≤ (C' / (Real.log X) ^ A) * (k : ℝ) := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := piece_partial_sum_rate_split_graded_prod_L hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q P₁ Q₁ P₂ Q₂ hP4 hPQ h₁4 h₁ h₂4 h₂
  obtain ⟨C', hC'pos, hC'le, hrate⟩ := hsplit P Q P₁ Q₁ P₂ Q₂ hP4 hPQ h₁4 h₁ h₂4 h₂
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro q _ χ M Xd N X hXd hX400 hx₀ h16 hq hcovP hcovQ hcovB hgHalf hgO1 hgWin 𝒥 h𝒥 t ht k
    hk1 hk2
  have h𝒥sub : 𝒥 ⊆ Finset.Icc 1 2 := Finset.mem_powerset.mp h𝒥
  have hX0 : (0 : ℝ) < X := by linarith
  have hXk : X ≤ (k : ℝ) := by
    rw [← hXd]
    exact_mod_cast hk1
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLk : Real.log X ≤ Real.log (k : ℝ) := Real.log_le_log hX0 hXk
  have hLkpos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le hLXpos hLk
  have hk16 : 16 ≤ k := le_trans h16 hk1
  have hkx₀ : x₀ ≤ k := le_trans hx₀ hk1
  have hqk : (q : ℝ) ≤ (Real.log (k : ℝ)) ^ (10 : ℕ) := by
    refine le_trans hq ?_
    gcongr
  have hth : |t| ≤ (Nat.sqrt (Nat.sqrt k) : ℝ) := by
    refine le_trans ht (le_trans (seamT0_le_sqrt_sqrt hXd hX400) ?_)
    exact_mod_cast Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt hk1)
  have hmain := hrate k hkx₀ hk16 (hgHalf k hk1 hk2) (hgO1 k hk1 hk2) (hgWin k hk1 hk2)
    q χ hqk t hth 𝒥 _ _ (fun j hj => hcovP j (h𝒥sub hj)) (fun j hj => hcovQ j (h𝒥sub hj))
    (fun j hj => hcovB j (h𝒥sub hj))
  refine le_trans hmain ?_
  have hLAX : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hLAk : (Real.log X) ^ A ≤ (Real.log (k : ℝ)) ^ A :=
    Real.rpow_le_rpow hLXpos.le hLk hA.le
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [show C' / (Real.log X) ^ A * (k : ℝ) = C' * (k : ℝ) / (Real.log X) ^ A from by ring]
  exact div_le_div_of_nonneg_left (mul_nonneg hC'pos.le hk0) hLAX hLAk

/-- **⟦D3-DISCHARGE — THE EXIT, SPLIT-HOISTED + GRADED, PER BLOCK⟧ AT THE G-LEVER**
(`m4_hT0band_at_door_discharged_split_graded_prod_L_gk`). -/
theorem m4_hT0band_at_door_discharged_split_graded_prod_L_gk (K : ℕ) (hMmu : MmuChiRate)
    (A : ℝ) (hA : 0 < A) :
    ∃ (x₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ (P Q P₁ Q₁ P₂ Q₂ : ℕ), 4 ≤ P → P ≤ Q →
      4 ≤ P₁ → P₁ ≤ Q₁ → 4 ≤ P₂ → P₂ ≤ Q₂ →
      ∃ C' : ℝ, 0 < C' ∧
        C' ≤ C * (4 : ℝ) ^ A * (windowMassConst P₁ Q₁ * windowMassConst P₂ Q₂) + 1 ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd N : ℕ) {X C₁ M₀ : ℝ},
          ((Xd : ℕ) : ℝ) = X → (400 : ℝ) ≤ X → Xd ≤ N → N ≤ 2 * Xd → 1 ≤ C₁ →
          x₀ ≤ Xd → 16 ≤ Xd →
          (q : ℝ) ≤ (Real.log X) ^ (10 : ℕ) →
          (∀ j ∈ Finset.Icc 1 2, P ≤ calP (AdoorL M) (s13GK K M) j) →
          (∀ j ∈ Finset.Icc 1 2, calQK (AdoorL M) (s13GK K M) M j ≤ Q) →
          (∀ j ∈ Finset.Icc 1 2,
              (P₁ ≤ calP (AdoorL M) (s13GK K M) j
                  ∧ calQK (AdoorL M) (s13GK K M) M j ≤ Q₁)
                ∨ (P₂ ≤ calP (AdoorL M) (s13GK K M) j
                  ∧ calQK (AdoorL M) (s13GK K M) M j ≤ Q₂)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            16 * A * Real.log (Real.log (k : ℝ)) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            8 * A * Real.log (Real.log (k : ℝ)) * Real.log (Q : ℝ) ≤ Real.log (k : ℝ)) →
          (∀ k : ℕ, Xd ≤ k → k ≤ N →
            Real.exp (2 * Real.exp 1
                * (Real.log (Real.log (Q : ℝ)) - Real.log (Real.log (P : ℝ)) + 25))
              ≤ (Real.log (k : ℝ)) ^ A) →
          8 * C' ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) →
          4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
              ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M₀) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 N X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X C₁) M₀ := by
  obtain ⟨x₀, C, hCpos, hsplit⟩ := m4_hpiece_at_door_split_graded_prod_L_gk K hMmu A hA
  refine ⟨x₀, C, hCpos, ?_⟩
  intro P Q P₁ Q₁ P₂ Q₂ hP4 hPQ h₁4 h₁ h₂4 h₂
  obtain ⟨C', hC'pos, hC'le, hpiece⟩ := hsplit P Q P₁ Q₁ P₂ Q₂ hP4 hPQ h₁4 h₁ h₂4 h₂
  refine ⟨C', hC'pos, hC'le, ?_⟩
  intro q _ χ M Xd N X C₁ M₀ hXd hX400 hXdN hN hC₁ hx₀ h16 hq hcovP hcovQ hcovB hgHalf hgO1
    hgWin hgrade hErr
  have hX3 : (3 : ℝ) ≤ X := by linarith
  have hLXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hLA : (0 : ℝ) < (Real.log X) ^ A := Real.rpow_pos_of_pos hLXpos A
  have hS₀ : (0 : ℝ) ≤ C' / (Real.log X) ^ A := le_of_lt (div_pos hC'pos hLA)
  have hSle : 8 * (C' / (Real.log X) ^ A)
      ≤ 2 * (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M₀)
          + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    refine t0datum_grade_of_fit hX3 hC₁ ?_
    calc C' ≤ 8 * C' := by linarith
      _ ≤ (Real.log X) ^ (A + (-(1 : ℝ) / 2 + 1 / 1000)) := hgrade
  exact m4_hT0band_at_door_L_gk K χ M hX3 hXd hXdN hN hC₁ hS₀ hSle
    (hpiece q χ M Xd N hXd hX400 hx₀ h16 hq hcovP hcovQ hcovB hgHalf hgO1 hgWin) hErr
/-! ## §5 — `M4ChiSummed` -/

/-- The row mean square is nonnegative (`M4BridgeIntegral.meanSq_nonneg`). -/
theorem chiFreeRowSq_nonneg_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M j : ℕ) {X : ℕ}
    (hX : 0 < X) : 0 ≤ chiFreeRowSq_L χ M j X := by
  have hX0 : (0 : ℝ) < ((X : ℕ) : ℝ) := by exact_mod_cast hX
  exact meanSq_nonneg (doorChiCoeff_L χ M) (seamS0 (2 * X) ((X : ℕ) : ℝ)) ((2 ^ j : ℕ) : ℝ) hX0

/-- **THE ABSOLUTE GRADE `4`** — `M4DoorClose.doorRow_trivial_grade`, re-read at the name.
This is what makes the socket's anti-vacuity witness `q`-free. -/
theorem chiFreeRowSq_le_four_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M j : ℕ) {X : ℕ}
    (hX : 0 < X) : chiFreeRowSq_L χ M j X ≤ 4 :=
  doorRow_trivial_grade_L χ M j hX

/-- **⟦A-C1⟧ THE χ-SUMMED FREE-BASE ROW SOCKET** (`M4ChiSummedFreeRow_L R M RS`).

The second road's ONE analytic input.  Read at:

* a FREE base `A` (`0 < A`) and a FREE shift `s ≤ L` — the strata's dilated bases
  `⌊A/d⌋` are named by no ladder, which is what killed freeze v1's socket;
* CAP-GENERAL `∀ L ≤ H` and WINDOW-DYADIC `2^j`, `j ≤ log₂ L` — non-dyadic lengths never
  reach the row;
* EVERY modulus `0 < q ≤ arcDen 12 H`, with `RS : ℕ → ℕ → ℝ` **`q`-free** (length-graded
  `j`, ambient `H`) — the reduced moduli `q/d` of the strata are covered by the same `RS`;
* the SUM over `χ : DirichletCharacter ℂ q`, not a per-χ bound (⟦WHY A `Σ_χ` SOCKET⟧).

⟦NO ENDPOINT ANTECEDENT⟧ (`D-5`, R-E confirmed): `seamS0` is strict at the bottom, the
tiling is half-open, and no consumer reads the closed endpoint — the endpoint obligation
belongs to whatever SUPPLIES this socket, not to the socket.

⟦THE BASE CAP⟧ (`(A : ℝ) ≤ 2·R.x`) — **the (α) base-cap surgery, JYH-granted 2026-07-30**.
The FOURTH base antecedent, and the only one that bounds the base from ABOVE.  See the
module header's ⟦THE (α) BASE-CAP SURGERY⟧ for the defect it closes and for the byte
verification of every read. -/
def M4ChiSummedFreeRow_L (R : ChowlaRegime) (M : ℕ) (RS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s) ≤ RS j H

/-- **THE SOCKET IS INHABITED** (the house's anti-vacuity duty) — at
`RS j H := 4·arcDen 12 H` the socket holds outright: each of the `φ(q)` terms is at most the
absolute grade `4` (`chiFreeRowSq_le_four_L`), and `φ(q) ≤ q ≤ arcDen 12 H` is the modulus
range's own gate.  So ALL of the socket's content is the grade, and the anti-vacuity witness
is `q`-FREE — which is what the `q`-free `RS` demands.

⟦the (α) base-cap surgery, JYH-granted 2026-07-30⟧ the new base cap is UNUSED here (as are
the other three base antecedents): the absolute grade holds at every base, so the witness
survives the weakening untouched. -/
theorem m4_chiSummedFreeRow_trivial_L (R : ChowlaRegime) (M : ℕ) :
    M4ChiSummedFreeRow_L R M (fun _ H => 4 * arcDen 12 H) := by
  intro H _ _ L _ q hq hqQ j _ A hA _ _ _ _ s _
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hterm : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      chiFreeRowSq_L χ M j (A + s) ≤ 4 := fun χ _ => chiFreeRowSq_le_four_L χ M j hAs
  have hsum : ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
      ≤ ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
    calc ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
        ≤ ∑ _χ : DirichletCharacter ℂ q, (4 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  linarith

/-- **THE POINTWISE SHIFTED BRIDGE** (`chiFreeShift_pointwise_L`) — `⟦W3⟧` at a per-χ constant
`c` in place of the χ-uniform grade `MS j H`.

Byte-for-byte `M4CoprimeSupply.m4_chiFreeShiftBlock_of_freeRow`'s proof with the row datum
read at `c`: the slack-`4` block bound at the shifted block, the harmonic→flat exchange
against `B + s ≤ 2(A+s)` (which is `4 ≤ L`), and the two comparisons the free block affords.
Nothing new is estimated. -/
theorem chiFreeShift_pointwise_L {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ)
    {L j s A B : ℕ} {c : ℝ} (hjL : j ≤ Nat.log 2 L) (hsL : s ≤ L) (hA : 0 < A) (hL4 : 4 ≤ L)
    (hfit : B + L ≤ 2 * A + 4) (hc : chiFreeRowSq_L χ M j (A + s) ≤ c) :
    ∑ n ∈ Finset.Ioc (A + s) (B + s),
        ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
      ≤ 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum at the constant `c`, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ c := by
    rw [doorCoeffPhase_zero]
    exact hc
  have hc0 : (0 : ℝ) ≤ c :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff_L χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff_L χ M) (fun m => norm_doorChiCoeff_le_one_L χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := c) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
      = 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * c * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero_L] using hfinal

/-- **THE χ-SUMMED SHIFTED FIXED-LENGTH DATUM** (`M4ChiSummedFreeShiftBlock_L`) — the `Σ_χ`
twin of `M4CoprimeSupply.M4ChiFreeShiftBlockMeanSq`.

⟦THE φ(q) LEDGER, first entry⟧ the drop residue `8·(2^j)²` is charged at the ABSOLUTE grade
per character, so under `∑_χ` it is `8·φ(q)·(2^j)²`; it is carried at `8·arcDen 12 H·(2^j)²`,
which keeps the predicate `q`-free.

⟦the (α) base-cap surgery, JYH-granted 2026-07-30⟧ the base cap `(A : ℝ) ≤ 2·R.x` rides here
because `m4_chiSummedShiftBlock_of_freeRow_L` reads the socket at THIS `A` — the propagation is
forced, and the module header's verification covers it. -/
def M4ChiSummedFreeShiftBlock_L (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- **⟦S-2a⟧ THE SHIFTED BRIDGE, MIRRORED** (`m4_chiSummedShiftBlock_of_freeRow_L`) — the
χ-summed socket becomes the χ-summed shifted block datum at the grade `2·RS`.

The step IS genuinely pointwise-in-χ (⟦the mechanicalness spot-check⟧ of the freeze's
residual-risk list): `chiFreeShift_pointwise_L` is applied at each `χ` with the constant
`c := chiFreeRowSq_L χ M j (A+s)` — the character's OWN row datum — and only then summed.
There is no cross-χ coupling anywhere in the step; the only character-dependent charge is
the absolute drop residue, which is the ⟦φ(q) LEDGER⟧'s first entry. -/
theorem m4_chiSummedShiftBlock_of_freeRow_L {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    (hrow : M4ChiSummedFreeRow_L R M RS) :
    M4ChiSummedFreeShiftBlock_L R M (fun j H => 2 * RS j H) := by
  intro H hlo hhi L hLH q hq hqQ j hjL s hsL A B hA hAj hAsq hAx hAcap hL4 hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  -- ⟦the pointwise bound at each character's OWN row datum⟧
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * chiFreeRowSq_L χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (4 * chiFreeRowSq_L χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := fun χ _ =>
    chiFreeShift_pointwise_L χ M hjL hsL hA hL4 hfit le_rfl
  refine le_trans (Finset.sum_le_sum hper) ?_
  -- ⟦the sum splits into the row sum and the absolute residue⟧
  have hsplit : ∑ χ : DirichletCharacter ℂ q,
      (2 * chiFreeRowSq_L χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * chiFreeRowSq_L χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
      = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s))
          * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
        + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
            * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    calc ∑ χ : DirichletCharacter ℂ q,
          (2 * chiFreeRowSq_L χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (4 * chiFreeRowSq_L χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        = ∑ χ : DirichletCharacter ℂ q,
            (chiFreeRowSq_L χ M j (A + s)
                * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
              + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
          Finset.sum_congr rfl fun χ _ => by ring
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s)
              * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2))
            + ∑ _χ : DirichletCharacter ℂ q, 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s))
            * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
          + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
              * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
          rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsplit, card_dirichletCharacter_nat q]
  have hrowsum := hrow H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  have hrow0 : (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s) :=
    Finset.sum_nonneg fun χ _ => chiFreeRowSq_nonneg_L χ M j hAs
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  have hfac0 : (0 : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    positivity
  have h1 : (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s))
        * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ RS j H * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hrowsum hfac0
  have h2 : (q.totient : ℝ) * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ arcDen 12 H * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right hφarc ?_
    positivity
  nlinarith [h1, h2]

/-- **THE χ-SUMMED NARROWED BLOCK MEAN SQUARE** (`M4ChiSummedBlockMeanSqN_L`) — the `Σ_χ` twin
of `M4CoprimeSupply.M4CoprimeChiBlockMeanSqN`: the same free half-open block `(A, B]`, the
same free length `L` with ⟦THE NARROWING⟧ `H ≤ arcDen·L`, the same slack-`4` fit, with the
sum over characters on the left instead of a χ-uniform bound.

This is what the stratified Gauss consumer reads: the Cauchy–Schwarz against the Gauss sum's
second moment leaves exactly `∑_χ (per-χ sup)²` and no `φ(q)`.

⟦the (α) base-cap surgery, JYH-granted 2026-07-30⟧ the base cap `(A : ℝ) ≤ 2·R.x` rides here
because `m4_chiSummedBlockN_of_shiftBlock_L` reads the shifted family at THIS `A`.  Its
consumer `M4Gauss.m4_freeBlockSup_of_chiSummed` supplies it at the DILATED base
`⌊A/d⌋ − 1 ≤ A` by monotonicity — the only base antecedent that costs no `arcDen` power. -/
def M4ChiSummedBlockMeanSqN_L (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 3 * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ A B : ℕ, 0 < A → L ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

set_option maxHeartbeats 3200000 in
-- the dyadic assembly is `M4CoprimeSupply`'s at a free block with ONE further summation
-- layer (the character sum), so the triple-nested `Finset` sums are re-elaborated against
-- `∑_χ` as well as the free `(A, B]` and `L` — that re-elaboration is what costs the
-- heartbeats (no tactic search below is unbounded: every arithmetic step is `linarith` or
-- `nlinarith` with explicit hints)
/-- **⟦S-2b⟧ THE MAXIMAL STEP, MIRRORED** (`m4_chiSummedBlockN_of_shiftBlock_L`) — the χ-summed
block mean square from the χ-summed shifted fixed-length datum, at the graded price
`m4BclGraded j₀ Fan Ftr`.

⟦THE LEDGER, mirrored⟧ — the three charges of `M4CoprimeSupply`'s header, each read under
`∑_χ`:

1. the analytic half (`j₀ ≤ j`) reads the χ-SUMMED datum, so it lands on the grade's first
   summand exactly as before — **no `φ(q)` appears**, which is the whole point of the socket;
2. the trivial half (`j < j₀`) reads no datum and is charged `φ(q)` times the absolute grade
   `1`; bounded by `arcDen 12 H`, it is what raises ⟦G1⟧ to `2·arcDen³ ≤ Ftr`;
3. the slack-`4` residue arrives from the shifted datum already carrying its `8·arcDen`
   (⟦φ(q) LEDGER⟧ entry 1) and is charged, with the trivial half's `(4/3)^{j₀}` piece,
   against the head's first summand — ⟦G2⟧ at `108/5·Fan + 432/5·arcDen`.

Both gates are thresholds on WITNESSED envelopes, `H`-only and one-sided. -/
theorem m4_chiSummedBlockN_of_shiftBlock_L {R : ChowlaRegime} {M : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ^ 7 ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      108 / 5 * Fan H + 432 / 5 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ))
    (hfix : M4ChiSummedFreeShiftBlock_L R M F) :
    M4ChiSummedBlockMeanSqN_L R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ A B hA hAL hAsq hAx hAcap hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have harc30 : (0 : ℝ) < arcDen 12 H ^ 3 := by positivity
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        arcDen 12 H ^ 3 * 8 ≤ arcDen 12 H ^ 3 * (L : ℝ)) harc30
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    have hzero : ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2 = 0 := by
      intro χ
      rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    rw [Finset.sum_congr rfl (fun χ _ => hzero χ), Finset.sum_const, smul_zero]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  -- ⟦R-P5, THE LENGTH ANTECEDENT PROPAGATED⟧ every dyadic window of the assembly is at most
  -- the free length (`2^j ≤ 2^{log₂L} ≤ L`), so the block's own `L ≤ A` supplies the shifted
  -- family's `2^j ≤ A` at every scale the analytic half reads
  have h2jL : ∀ j : ℕ, j ≤ Lg → 2 ^ j ≤ A := by
    intro j hj
    have h1 : 2 ^ j ≤ 2 ^ Lg := Nat.pow_le_pow_right (by norm_num) hj
    have h2 : 2 ^ Lg ≤ L := by rw [hLg]; exact Nat.pow_log_le_self 2 hL0.ne'
    omega
  set X : DirichletCharacter ℂ q → ℕ → ℕ → ℕ → ℝ := fun χ j t n =>
    ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set Y : ℕ → ℕ → ℕ → ℝ := fun j t n => ∑ χ : DirichletCharacter ℂ q, X χ j t n with hY
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound per character, with the sums already commuted
  have hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
        ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
    intro χ
    have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
        ≤ ∑ n ∈ Finset.Ioc A B, SL
            * ∑ j ∈ Finset.range (Lg + 1),
                (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j :=
      Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L χ M L n
    have hswap : ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm
    exact hswap ▸ hstep1
  -- ⟦STEP 1′⟧ the character sum, taken through the assembly
  have hsummed : ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum fun χ _ => hchi χ) (le_of_eq ?_)
    calc ∑ χ : DirichletCharacter ℂ q, SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1), ∑ χ : DirichletCharacter ℂ q,
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.sum_comm]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_comm]
  -- ⟦STEP 2⟧ each (scale, offset) pair is a shifted fixed-length block sum, summed over χ
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshiftY : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      = ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2 := by
    intro j t
    rw [hY, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => ?_
    exact sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2)
      A B _
  -- ⟦the analytic half: the χ-summed datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshiftY j t]
    have hd := hfix H hlo hhi L hLH q hq hqQ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (h2jL j hjLg) hAsq hAx hAcap (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, φ(q) times⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      ≤ arcDen 12 H * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshiftY j t]
    have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro χ _
      have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ ^ 2
            ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
        intro n _
        have h := norm_sum_doorSievedWindow_le_L χ M (2 ^ j) n
        have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L M (2 ^ j) n, liouChi χ m‖ := norm_nonneg _
        nlinarith
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
        exact_mod_cast hnat
      have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletCharacter_nat q] at hsum
    have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hmid : (q.totient : ℝ) * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        ≤ arcDen 12 H * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_right hφarc ?_
      positivity
    nlinarith [hsum, hmid]
  -- ⟦STEP 3⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) := by
          ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            arcDen 12 H * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (arcDen 12 H * (A : ℝ)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((arcDen 12 H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 4⟧ THE SPLIT
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H) := by
    have := hFan0 H; nlinarith
  have harcA0 : (0 : ℝ) ≤ arcDen 12 H * (A : ℝ) := by positivity
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg harcA0 (hWw0 j))
      _ = (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, then the mirrored ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hg0 : (0 : ℝ) < (3 / 2 : ℝ) ^ (Nat.log 2 H) := by positivity
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, at `arcDen³`⟧ the two consequences the mirrored weighted head needs
  have harc2 : (1 : ℝ) ≤ arcDen 12 H ^ 2 := by nlinarith
  have harc3 : (1 : ℝ) ≤ arcDen 12 H ^ 3 := by nlinarith
  have hG1H := hG1 H hlo hhi
  have hFtrL : 2 * arcDen 12 H * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have hchain : 2 * arcDen 12 H * (H : ℝ) ≤ 2 * arcDen 12 H ^ 4 * (L : ℝ) := by
      have h1 : 2 * arcDen 12 H * (H : ℝ)
          ≤ 2 * arcDen 12 H * (arcDen 12 H ^ 3 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hnar (by positivity)
      nlinarith [h1]
    have hle47 : arcDen 12 H ^ 4 ≤ arcDen 12 H ^ 7 := by
      calc arcDen 12 H ^ 4 = arcDen 12 H ^ 4 * 1 := by ring
        _ ≤ arcDen 12 H ^ 4 * arcDen 12 H ^ 3 :=
            mul_le_mul_of_nonneg_left harc3 (by positivity)
        _ = arcDen 12 H ^ 7 := by ring
    have hle : 2 * arcDen 12 H ^ 4 ≤ 2 * arcDen 12 H ^ 7 := by linarith
    have hstep : 2 * arcDen 12 H ^ 4 * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hle hG1H) hL0R.le
    linarith
  have hFtrL2 : arcDen 12 H * (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H ^ 3 * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    have hstep : arcDen 12 H * (H : ℝ) ^ 2 ≤ arcDen 12 H ^ 7 * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq harc0.le]
    have hstep2 : arcDen 12 H ^ 7 * (L : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hG1H (sq_nonneg ((L : ℝ)))]
    linarith
  -- ⟦the first budget line⟧
  have hEkey : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg) * (H : ℝ)
        ≤ arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
            * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ)))
      nlinarith [h, hH0R.le]
    have hmain : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
          * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
        + arcDen 12 H * (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
          ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hg2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ)
            * (arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg))) := by
      have hbig : (1 : ℝ) ≤ arcDen 12 H * (3 / 2 : ℝ) ^ Lg := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbig
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧
  have hres2 : arcDen 12 H * (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
              * (arcDen 12 H * (H : ℝ) ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * arcDen 12 H * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
            * (arcDen 12 H * (H : ℝ) ^ 2)
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (54 / 5 * (L : ℝ) ^ 2)
        + (arcDen 12 H * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := hsummed
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (arcDen 12 H * (A : ℝ)) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by
        ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (54 / 5 * (L : ℝ) ^ 2)
          + (arcDen 12 H * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead harcA0
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- **THE χ-SUMMED SUPPLY, ASSEMBLED** (`m4_chiSummedN_supplied_L`).

⟦THE CONSUMPTION LIST⟧, beyond the socket: the two envelope nonnegativities, the analytic
envelope gate `RS j H ≤ RSan H` at `j₀ ≤ j`, and the three `H`-only class-(a) gates — ⟦G1⟧
at `arcDen³` (the mirror's price, `M4CoprimeSupply`'s `arcDen²` plus one character-count
power), ⟦G2⟧ at `44·RSan + 87·arcDen`, and the regime fact `8·arcDen ≤ H`. -/
theorem m4_chiSummedN_supplied_L {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    {RSan RStr : ℕ → ℝ} (j₀ : ℕ)
    (hRSan0 : ∀ H : ℕ, 0 ≤ RSan H) (hRStr0 : ∀ H : ℕ, 0 ≤ RStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ))
    (hrow : M4ChiSummedFreeRow_L R M RS) :
    M4ChiSummedBlockMeanSqN_L R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) := by
  refine m4_chiSummedBlockN_of_shiftBlock_L (F := fun j H => 2 * RS j H) j₀ ?_ ?_ ?_ ?_ ?_ harc8
    (m4_chiSummedShiftBlock_of_freeRow_L hrow)
  · intro H; have := hRSan0 H; linarith
  · intro H; have := hRStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi
    have hg2 := hG2 H hlo hhi
    have h0 := hRSan0 H
    have harc := arcDen_nonneg 12 H
    linarith

/-- `chiFreeRowSq_L` (:154), at the lever. -/
def chiFreeRowSq_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M j X : ℕ) : ℝ :=
  1 / ((X : ℕ) : ℝ)
    * (∫ y in ((X : ℕ) : ℝ)..(2 * ((X : ℕ) : ℝ)),
        ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
            * shortSum (doorChiCoeff_L_gk K χ M) (seamS0 (2 * X) ((X : ℕ) : ℝ)) y
                ((2 ^ j : ℕ) : ℝ)‖ ^ 2)

/-- `chiFreeRowSq_nonneg_L` (:162), at the lever. -/
theorem chiFreeRowSq_nonneg_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M j : ℕ) {X : ℕ}
    (hX : 0 < X) : 0 ≤ chiFreeRowSq_L_gk K χ M j X := by
  have hX0 : (0 : ℝ) < ((X : ℕ) : ℝ) := by exact_mod_cast hX
  exact meanSq_nonneg (doorChiCoeff_L_gk K χ M) (seamS0 (2 * X) ((X : ℕ) : ℝ)) ((2 ^ j : ℕ) : ℝ) hX0

/-- `chiFreeRowSq_le_four_L` (:169), at the lever. -/
theorem chiFreeRowSq_le_four_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M j : ℕ) {X : ℕ}
    (hX : 0 < X) : chiFreeRowSq_L_gk K χ M j X ≤ 4 :=
  doorRow_trivial_grade_L_gk K χ M j hX

/-- `M4ChiSummedFreeRow_L` (:199), at the lever. -/
def M4ChiSummedFreeRow_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (RS : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s) ≤ RS j H

/-- `m4_chiSummedFreeRow_trivial_L` (:216), at the lever. -/
theorem m4_chiSummedFreeRow_trivial_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) :
    M4ChiSummedFreeRow_L_gk K R M (fun _ H => 4 * arcDen 12 H) := by
  intro H _ _ L _ q hq hqQ j _ A hA _ _ _ _ s _
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hterm : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      chiFreeRowSq_L_gk K χ M j (A + s) ≤ 4 := fun χ _ => chiFreeRowSq_le_four_L_gk K χ M j hAs
  have hsum : ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
      ≤ ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
    calc ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
        ≤ ∑ _χ : DirichletCharacter ℂ q, (4 : ℝ) := Finset.sum_le_sum hterm
      _ = ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ) * 4 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [card_dirichletCharacter_nat q] at hsum
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  linarith

/-- `chiFreeShift_pointwise_L` (:278), at the lever. -/
theorem chiFreeShift_pointwise_L_gk (K : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (M : ℕ)
    {L j s A B : ℕ} {c : ℝ} (hjL : j ≤ Nat.log 2 L) (hsL : s ≤ L) (hA : 0 < A) (hL4 : 4 ≤ L)
    (hfit : B + L ≤ 2 * A + 4) (hc : chiFreeRowSq_L_gk K χ M j (A + s) ≤ c) :
    ∑ n ∈ Finset.Ioc (A + s) (B + s),
        ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
      ≤ 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
  have hL0 : 0 < L := by omega
  have h2j : 2 ^ j ≤ L :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjL) (Nat.pow_log_le_self 2 hL0.ne')
  have hh0 : 0 < 2 ^ j := Nat.two_pow_pos _
  have hAs : 0 < A + s := by omega
  have hAsR : (0 : ℝ) < ((A + s : ℕ) : ℝ) := by exact_mod_cast hAs
  -- ⟦the fit, at the interface's slack⟧
  have hfitS : (B + s) + 2 ^ j ≤ 2 * (A + s) + 4 := by omega
  -- ⟦the coverage, on the DROPPED block⟧
  have hcov : ∀ n ∈ Finset.Ioc (A + s) (B + s - 4), ∀ m ∈ Finset.Ioc n (n + 2 ^ j),
      m ∉ seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ) → doorChiCoeff_L_gk K χ M m = 0 := by
    intro n hn m hm hns
    have hn' := Finset.mem_Ioc.mp hn
    have hne : A + s < B + s - 4 := lt_of_lt_of_le hn'.1 hn'.2
    exact absurd (mem_seamS0_of_block_window (X := (((A + s : ℕ)) : ℝ))
      (N := 2 * (A + s)) le_rfl (by omega) hn hm) hns
  -- ⟦the row datum at the constant `c`, read at the removed phase⟧
  have hMSrow : 1 / (((A + s : ℕ)) : ℝ)
      * (∫ y in (((A + s : ℕ)) : ℝ)..(2 * (((A + s : ℕ)) : ℝ)),
          ‖((1 / ((2 ^ j : ℕ) : ℝ) : ℝ) : ℂ)
              * shortSum (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
                  (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) y ((2 ^ j : ℕ) : ℝ)‖ ^ 2)
      ≤ c := by
    rw [doorCoeffPhase_zero]
    exact hc
  have hc0 : (0 : ℝ) ≤ c :=
    le_trans (meanSq_nonneg (doorCoeffPhase (doorChiCoeff_L_gk K χ M) 0)
      (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) ((2 ^ j : ℕ) : ℝ) hAsR) hMSrow
  -- ⟦the slack-`4` block bound⟧
  have hslack := sum_Ioc_absWindowSum_sq_div_le_slack4
    (c := doorChiCoeff_L_gk K χ M) (fun m => norm_doorChiCoeff_le_one_L_gk K χ M m)
    (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) 0 (H := 2 ^ j) (A := A + s) (B := B + s)
    (MS := c) hh0 hAs hfitS hcov hMSrow
  -- ⟦the exchange at the shifted block⟧
  have hterm : ∀ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hnB : (n : ℝ) ≤ (((B + s : ℕ)) : ℝ) := by exact_mod_cast hn2
    have hvnn : (0 : ℝ) ≤ ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ) := by
      positivity
    calc ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
        = (n : ℝ) * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) := by
          field_simp
      _ ≤ (((B + s : ℕ)) : ℝ)
            * (‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnB hvnn
  have hex : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c
          + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg _)
  -- ⟦the two comparisons the free block affords⟧
  have hBs2 : (((B + s : ℕ)) : ℝ) ≤ 2 * (A : ℝ) + 4 := by
    have hnat : B + s ≤ 2 * A + 4 := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hBAs : (((B + s : ℕ)) : ℝ) ≤ 2 * (((A + s : ℕ)) : ℝ) := by
    have hnat : B + s ≤ 2 * (A + s) := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ) := by positivity
  have h1 : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
      ≤ (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c) :=
    mul_le_mul_of_nonneg_right hBs2 (by positivity)
  have h2 : (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      ≤ 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) :=
    mul_le_mul_of_nonneg_right hBAs (by positivity)
  have h3 : 2 * (((A + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    field_simp
    ring
  have hsplit : (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c
        + 4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ)))
      = (((B + s : ℕ)) : ℝ) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
        + (((B + s : ℕ)) : ℝ) * (4 * (((2 ^ j : ℕ) : ℝ) ^ 2 / (((A + s : ℕ)) : ℝ))) := by
    ring
  have hr : (2 * (A : ℝ) + 4) * (((2 ^ j : ℕ) : ℝ) ^ 2 * c)
      = 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + 4 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
  have hfinal : ∑ n ∈ Finset.Ioc (A + s) (B + s),
      ‖absWindowSum (doorChiCoeff_L_gk K χ M) (2 ^ j) n 0‖ ^ 2
      ≤ 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    rw [hsplit] at hex
    have hgoal : 2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * c + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2
        = (2 * c * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + 4 * c * ((2 ^ j : ℕ) : ℝ) ^ 2) + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by ring
    rw [hgoal, ← hr, ← h3]
    linarith
  simpa only [absWindowSum_doorChiCoeff_zero_L_gk K] using hfinal

/-- `M4ChiSummedFreeShiftBlock_L` (:397), at the lever. -/
def M4ChiSummedFreeShiftBlock_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (F : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, ∀ s ≤ L,
      ∀ A B : ℕ, 0 < A → 2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      4 ≤ L → B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc (A + s) (B + s),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ F j H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (2 * F j H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2

/-- `m4_chiSummedShiftBlock_of_freeRow_L` (:454), at the lever. -/
theorem m4_chiSummedShiftBlock_of_freeRow_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    (hrow : M4ChiSummedFreeRow_L_gk K R M RS) :
    M4ChiSummedFreeShiftBlock_L_gk K R M (fun j H => 2 * RS j H) := by
  intro H hlo hhi L hLH q hq hqQ j hjL s hsL A B hA hAj hAsq hAx hAcap hL4 hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hAs : 0 < A + s := by omega
  have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  -- ⟦the pointwise bound at each character's OWN row datum⟧
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      ∑ n ∈ Finset.Ioc (A + s) (B + s),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
        ≤ 2 * chiFreeRowSq_L_gk K χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (4 * chiFreeRowSq_L_gk K χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2 := fun χ _ =>
    chiFreeShift_pointwise_L_gk K χ M hjL hsL hA hL4 hfit le_rfl
  refine le_trans (Finset.sum_le_sum hper) ?_
  -- ⟦the sum splits into the row sum and the absolute residue⟧
  have hsplit : ∑ χ : DirichletCharacter ℂ q,
      (2 * chiFreeRowSq_L_gk K χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
        + (4 * chiFreeRowSq_L_gk K χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
      = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s))
          * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
        + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
            * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    calc ∑ χ : DirichletCharacter ℂ q,
          (2 * chiFreeRowSq_L_gk K χ M j (A + s) * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
            + (4 * chiFreeRowSq_L_gk K χ M j (A + s) + 8) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        = ∑ χ : DirichletCharacter ℂ q,
            (chiFreeRowSq_L_gk K χ M j (A + s)
                * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
              + 8 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
          Finset.sum_congr rfl fun χ _ => by ring
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s)
              * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2))
            + ∑ _χ : DirichletCharacter ℂ q, 8 * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
          Finset.sum_add_distrib
      _ = (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s))
            * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
          + ((Fintype.card (DirichletCharacter ℂ q) : ℕ) : ℝ)
              * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
          rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsplit, card_dirichletCharacter_nat q]
  have hrowsum := hrow H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  have hrow0 : (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s) :=
    Finset.sum_nonneg fun χ _ => chiFreeRowSq_nonneg_L_gk K χ M j hAs
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  have hfac0 : (0 : ℝ) ≤ 2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    positivity
  have h1 : (∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s))
        * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ RS j H * (2 * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ) + 4 * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hrowsum hfac0
  have h2 : (q.totient : ℝ) * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2)
      ≤ arcDen 12 H * (8 * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right hφarc ?_
    positivity
  nlinarith [h1, h2]

/-- `M4ChiSummedBlockMeanSqN_L` (:535), at the lever. -/
def M4ChiSummedBlockMeanSqN_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (Bcl : ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → (H : ℝ) ≤ arcDen 12 H ^ 3 * (L : ℝ) →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
      ∀ A B : ℕ, 0 < A → L ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      B + L ≤ 2 * A + 4 →
        ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
          ≤ Bcl H * (L : ℝ) ^ 2 * (A : ℝ)

set_option maxHeartbeats 3200000 in
-- the dyadic assembly is `M4CoprimeSupply`'s at a free block with ONE further summation
-- layer (the character sum), so the triple-nested `Finset` sums are re-elaborated against
-- `∑_χ` as well as the free `(A, B]` and `L` — that re-elaboration is what costs the
-- heartbeats (no tactic search below is unbounded: every arithmetic step is `linarith` or
-- `nlinarith` with explicit hints)
/-- `m4_chiSummedBlockN_of_shiftBlock_L` (:605), at the lever. -/
theorem m4_chiSummedBlockN_of_shiftBlock_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {F : ℕ → ℕ → ℝ}
    {Fan Ftr : ℕ → ℝ} (j₀ : ℕ)
    (hFan0 : ∀ H : ℕ, 0 ≤ Fan H) (hFtr0 : ∀ H : ℕ, 0 ≤ Ftr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → F j H ≤ Fan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ^ 7 ≤ Ftr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      108 / 5 * Fan H + 432 / 5 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ))
    (hfix : M4ChiSummedFreeShiftBlock_L_gk K R M F) :
    M4ChiSummedBlockMeanSqN_L_gk K R M (m4BclGraded j₀ Fan Ftr) := by
  classical
  intro H hlo hhi L hLH hnar q hq hqQ A B hA hAL hAsq hAx hAcap hfit
  haveI : NeZero q := ⟨hq.ne'⟩
  have hH0 : 0 < H := by have := R.hHlo_floor; omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hBcl0 : (0 : ℝ) ≤ m4BclGraded j₀ Fan Ftr H :=
    m4BclGraded_nonneg (hFan0 H) (hFtr0 H)
  -- ⟦THE NARROWING, read against the arc gate: the free length cannot be short⟧
  have harc30 : (0 : ℝ) < arcDen 12 H ^ 3 := by positivity
  have hL8R : (8 : ℝ) ≤ (L : ℝ) :=
    le_of_mul_le_mul_left
      (by have := harc8 H hlo hhi; linarith :
        arcDen 12 H ^ 3 * 8 ≤ arcDen 12 H ^ 3 * (L : ℝ)) harc30
  have hL8 : 8 ≤ L := by exact_mod_cast hL8R
  have hL0 : 0 < L := by omega
  have hL0R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL0
  by_cases hAB : B < A
  · -- ⟦the empty block⟧
    have hzero : ∀ χ : DirichletCharacter ℂ q,
        ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2 = 0 := by
      intro χ
      rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    rw [Finset.sum_congr rfl (fun χ _ => hzero χ), Finset.sum_const, smul_zero]
    exact mul_nonneg (mul_nonneg hBcl0 (sq_nonneg _)) (Nat.cast_nonneg _)
  rw [Nat.not_lt] at hAB
  -- ⟦the non-empty block: the fit's three consequences⟧
  have hA4 : 4 ≤ A := by omega
  have hB2A : B ≤ 2 * A := by omega
  have hL2A : (L : ℝ) ≤ 2 * (A : ℝ) := by
    have hnat : L ≤ 2 * A := by omega
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  set Lg := Nat.log 2 L with hLg
  -- ⟦R-P5, THE LENGTH ANTECEDENT PROPAGATED⟧ every dyadic window of the assembly is at most
  -- the free length (`2^j ≤ 2^{log₂L} ≤ L`), so the block's own `L ≤ A` supplies the shifted
  -- family's `2^j ≤ A` at every scale the analytic half reads
  have h2jL : ∀ j : ℕ, j ≤ Lg → 2 ^ j ≤ A := by
    intro j hj
    have h1 : 2 ^ j ≤ 2 ^ Lg := Nat.pow_le_pow_right (by norm_num) hj
    have h2 : 2 ^ Lg ≤ L := by rw [hLg]; exact Nat.pow_log_le_self 2 hL0.ne'
    omega
  set X : DirichletCharacter ℂ q → ℕ → ℕ → ℕ → ℝ := fun χ j t n =>
    ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) (n + 2 ^ (j + 1) * t), liouChi χ m‖ ^ 2 with hX
  set Y : ℕ → ℕ → ℕ → ℝ := fun j t n => ∑ χ : DirichletCharacter ℂ q, X χ j t n with hY
  set SL : ℝ := ∑ j ∈ Finset.range (Lg + 1), (3 / 2 : ℝ) ^ j with hSL
  have hSL0 : (0 : ℝ) ≤ SL := (geom_weight_sum_pos Lg).le
  -- ⟦STEP 1⟧ the pointwise maximal bound per character, with the sums already commuted
  have hchi : ∀ χ : DirichletCharacter ℂ q,
      ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
        ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
    intro χ
    have hstep1 : ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
        ≤ ∑ n ∈ Finset.Ioc A B, SL
            * ∑ j ∈ Finset.range (Lg + 1),
                (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j :=
      Finset.sum_le_sum fun n _ => doorChiSup_sq_le_dyadic_L_gk K χ M L n
    have hswap : ∑ n ∈ Finset.Ioc A B, SL
          * ∑ j ∈ Finset.range (Lg + 1),
              (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm
    exact hswap ▸ hstep1
  -- ⟦STEP 1′⟧ the character sum, taken through the assembly
  have hsummed : ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
    refine le_trans (Finset.sum_le_sum fun χ _ => hchi χ) (le_of_eq ?_)
    calc ∑ χ : DirichletCharacter ℂ q, SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j
        = SL * ∑ χ : DirichletCharacter ℂ q, ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1), ∑ χ : DirichletCharacter ℂ q,
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, X χ j t n) * (2 / 3 : ℝ) ^ j := by
          rw [Finset.sum_comm]
      _ = SL * ∑ j ∈ Finset.range (Lg + 1),
            (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
              ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := by
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_comm]
  -- ⟦STEP 2⟧ each (scale, offset) pair is a shifted fixed-length block sum, summed over χ
  have hsle : ∀ j t : ℕ, t ≤ L / 2 ^ (j + 1) → 2 ^ (j + 1) * t ≤ L := by
    intro j t ht
    calc 2 ^ (j + 1) * t ≤ 2 ^ (j + 1) * (L / 2 ^ (j + 1)) := Nat.mul_le_mul_left _ ht
      _ = L / 2 ^ (j + 1) * 2 ^ (j + 1) := Nat.mul_comm _ _
      _ ≤ L := Nat.div_mul_le_self L (2 ^ (j + 1))
  have hshiftY : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      = ∑ χ : DirichletCharacter ℂ q,
          ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2 := by
    intro j t
    rw [hY, Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => ?_
    exact sum_Ioc_shift (fun n => ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2)
      A B _
  -- ⟦the analytic half: the χ-summed datum, read through the envelope⟧
  have hjtL : ∀ j t : ℕ, j ≤ Lg → j₀ ≤ j → t ≤ L / 2 ^ (j + 1) →
      ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
          + (2 * Fan H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t hjLg hj₀ ht
    rw [hshiftY j t]
    have hd := hfix H hlo hhi L hLH q hq hqQ j hjLg (2 ^ (j + 1) * t) (hsle j t ht) A B hA
      (h2jL j hjLg) hAsq hAx hAcap (by omega) hfit
    have hFle := han j H hj₀
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hP0 hA0R]
  -- ⟦the trivial half: the ABSOLUTE grade `1`, φ(q) times⟧
  have hjtS : ∀ j t : ℕ, ∑ n ∈ Finset.Ioc A B, Y j t n
      ≤ arcDen 12 H * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
    intro j t
    rw [hshiftY j t]
    have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ∑ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
            ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
          ≤ (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 := by
      intro χ _
      have hterm : ∀ n ∈ Finset.Ioc (A + 2 ^ (j + 1) * t) (B + 2 ^ (j + 1) * t),
          ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ ^ 2
            ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by
        intro n _
        have h := norm_sum_doorSievedWindow_le_L_gk K χ M (2 ^ j) n
        have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L_gk K M (2 ^ j) n, liouChi χ m‖ :=
          norm_nonneg _
        nlinarith
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      have hcast : ((B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : B + 2 ^ (j + 1) * t - (A + 2 ^ (j + 1) * t) ≤ A := by omega
        exact_mod_cast hnat
      have h2j : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := by positivity
      nlinarith
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletCharacter_nat q] at hsum
    have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
    have hP0 : (0 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hmid : (q.totient : ℝ) * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2)
        ≤ arcDen 12 H * ((A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_right hφarc ?_
      positivity
    nlinarith [hsum, hmid]
  -- ⟦STEP 3⟧ the per-scale count × weight
  set W : ℕ → ℝ := fun j =>
    (((L / 2 ^ (j + 1) : ℕ) : ℝ) + 1) * (((2 ^ j : ℕ) : ℝ)) ^ 2 with hW
  have hW0 : ∀ j, (0 : ℝ) ≤ W j := fun j => dyadic_count_weight_term_nonneg L j
  have hWw0 : ∀ j, (0 : ℝ) ≤ W j * (2 / 3 : ℝ) ^ j := fun j =>
    mul_nonneg (hW0 j) (by positivity)
  have hjL : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j hjm
    have hjmem := Finset.mem_filter.mp hjm
    have hjLg : j ≤ Lg := by have := Finset.mem_range.mp hjmem.1; omega
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            (Fan H * ((2 ^ j : ℕ) : ℝ) ^ 2 * (A : ℝ)
              + (2 * Fan H + 8 * arcDen 12 H) * ((2 ^ j : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum fun t ht =>
        hjtL j t hjLg hjmem.2 (by have := Finset.mem_range.mp ht; omega)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) := by
          ring
  have hjS : ∀ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
      (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by
    intro j _
    have hle : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ ∑ _t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            arcDen 12 H * (A : ℝ) * ((2 ^ j : ℕ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun t _ => hjtS j t
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    have hstep : ∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n
        ≤ (arcDen 12 H * (A : ℝ)) * W j := by
      refine hle.trans (le_of_eq ?_)
      simp only [hW]
      push_cast
      ring
    calc (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
        ≤ ((arcDen 12 H * (A : ℝ)) * W j) * (2 / 3 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := by ring
  -- ⟦STEP 4⟧ THE SPLIT
  have hCan0 : (0 : ℝ) ≤ Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H) := by
    have := hFan0 H; nlinarith
  have harcA0 : (0 : ℝ) ≤ arcDen 12 H * (A : ℝ) := by positivity
  have hlarge : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
          * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => j₀ ≤ j),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum hjL
      _ ≤ ∑ j ∈ Finset.range (Lg + 1),
            (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => mul_nonneg hCan0 (hWw0 j))
      _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hsmall : ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    have hsub : (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j) ⊆ Finset.range j₀ := by
      intro j hjm
      have := (Finset.mem_filter.mp hjm).2
      exact Finset.mem_range.mpr (by omega)
    calc ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
            * (2 / 3 : ℝ) ^ j
        ≤ ∑ j ∈ (Finset.range (Lg + 1)).filter (fun j => ¬ j₀ ≤ j),
            (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) := Finset.sum_le_sum hjS
      _ ≤ ∑ j ∈ Finset.range j₀, (arcDen 12 H * (A : ℝ)) * (W j * (2 / 3 : ℝ) ^ j) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j _ _ => mul_nonneg harcA0 (hWw0 j))
      _ = (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
          rw [Finset.mul_sum]
  have hcount : ∑ j ∈ Finset.range (Lg + 1),
        (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1), ∑ n ∈ Finset.Ioc A B, Y j t n)
          * (2 / 3 : ℝ) ^ j
      ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
        + (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (Lg + 1)) (fun j => j₀ ≤ j)]
    linarith
  -- ⟦THE ASSEMBLY⟧ the two weighted counts, then the mirrored ledger
  have hLgN : Nat.log 2 L ≤ Nat.log 2 H := Nat.log_mono_right hLH
  have hgl1 : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ Lg := one_le_pow₀ (by norm_num)
  have hglg : (3 / 2 : ℝ) ^ Lg ≤ (3 / 2 : ℝ) ^ (Nat.log 2 H) := by
    rw [hLg]; gcongr; norm_num
  have hg0 : (0 : ℝ) < (3 / 2 : ℝ) ^ (Nat.log 2 H) := by positivity
  have hfull : SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
      ≤ 54 / 5 * (L : ℝ) ^ 2 := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_le hL0
  have hhead : SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j
      ≤ 9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
        + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀ := by
    rw [hSL, hW, hLg]
    exact dyadic_count_weight_geom_small_le hL0 j₀
  -- ⟦G1, at `arcDen³`⟧ the two consequences the mirrored weighted head needs
  have harc2 : (1 : ℝ) ≤ arcDen 12 H ^ 2 := by nlinarith
  have harc3 : (1 : ℝ) ≤ arcDen 12 H ^ 3 := by nlinarith
  have hG1H := hG1 H hlo hhi
  have hFtrL : 2 * arcDen 12 H * (H : ℝ) ≤ Ftr H * (L : ℝ) := by
    have hchain : 2 * arcDen 12 H * (H : ℝ) ≤ 2 * arcDen 12 H ^ 4 * (L : ℝ) := by
      have h1 : 2 * arcDen 12 H * (H : ℝ)
          ≤ 2 * arcDen 12 H * (arcDen 12 H ^ 3 * (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hnar (by positivity)
      nlinarith [h1]
    have hle47 : arcDen 12 H ^ 4 ≤ arcDen 12 H ^ 7 := by
      calc arcDen 12 H ^ 4 = arcDen 12 H ^ 4 * 1 := by ring
        _ ≤ arcDen 12 H ^ 4 * arcDen 12 H ^ 3 :=
            mul_le_mul_of_nonneg_left harc3 (by positivity)
        _ = arcDen 12 H ^ 7 := by ring
    have hle : 2 * arcDen 12 H ^ 4 ≤ 2 * arcDen 12 H ^ 7 := by linarith
    have hstep : 2 * arcDen 12 H ^ 4 * (L : ℝ) ≤ Ftr H * (L : ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hle hG1H) hL0R.le
    linarith
  have hFtrL2 : arcDen 12 H * (H : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
    have hsq : (H : ℝ) ^ 2 ≤ (arcDen 12 H ^ 3 * (L : ℝ)) ^ 2 := by nlinarith [hnar, hH0R.le]
    have hstep : arcDen 12 H * (H : ℝ) ^ 2 ≤ arcDen 12 H ^ 7 * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq harc0.le]
    have hstep2 : arcDen 12 H ^ 7 * (L : ℝ) ^ 2 ≤ Ftr H * (L : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hG1H (sq_nonneg ((L : ℝ)))]
    linarith
  -- ⟦the first budget line⟧
  have hEkey : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hH0R]
    have hstep : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg) * (H : ℝ)
        ≤ arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
            * (H : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hglg
        (by positivity : (0 : ℝ) ≤ arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ)))
      nlinarith [h, hH0R.le]
    have hmain : arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ (Nat.log 2 H))
          * (H : ℝ)
        ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ * Ftr H * (L : ℝ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hFtrL
        (by positivity : (0 : ℝ) ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀
          * (L : ℝ))
      nlinarith [h]
    linarith
  have hres : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
        + arcDen 12 H * (A : ℝ) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀)
      ≤ 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hg2 := hG2 H hlo hhi
    have hstep : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
        ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ)) := by
      have h1 : 54 / 5 * (2 * Fan H + 8 * arcDen 12 H) * (L : ℝ) ^ 2
          ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hg2 (sq_nonneg ((L : ℝ)))
        nlinarith [this]
      nlinarith [mul_le_mul_of_nonneg_left hL2A
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ))]
    have hgl : (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (2 * (A : ℝ))
        ≤ (2 / 9) * ((A : ℝ)
            * (arcDen 12 H * (9 * (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (3 / 2 : ℝ) ^ Lg))) := by
      have hbig : (1 : ℝ) ≤ arcDen 12 H * (3 / 2 : ℝ) ^ Lg := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hbig
        (by positivity : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ j₀ * (L : ℝ) * (A : ℝ))]
    have hbud := mul_le_mul_of_nonneg_left hEkey hA0R
    nlinarith [hstep, hgl, hbud]
  -- ⟦the second budget line⟧
  have hres2 : arcDen 12 H * (A : ℝ) * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
          * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hH2 : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
    have hkey : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ) ^ 2
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) := by
      have h1 : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) * (H : ℝ) ^ 2
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
              * (arcDen 12 H * (H : ℝ) ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hglg
          (by positivity : (0 : ℝ) ≤ 9 / 5 * (8 / 3 : ℝ) ^ j₀ * arcDen 12 H * (H : ℝ) ^ 2)
        nlinarith [h]
      have h2 : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀
            * (arcDen 12 H * (H : ℝ) ^ 2)
          ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hFtrL2 (by positivity)
      linarith
    have hdiv : arcDen 12 H * (9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
        ≤ 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2) := by
      have hrw : 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2
            * (Ftr H * (L : ℝ) ^ 2)
          = (9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ * (Ftr H * (L : ℝ) ^ 2))
              / (H : ℝ) ^ 2 := by
        field_simp
      rw [hrw, le_div_iff₀ hH2]
      linarith [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hdiv hA0R]
  have hfinal : (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (54 / 5 * (L : ℝ) ^ 2)
        + (arcDen 12 H * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
          + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀)
      ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := by
    have hexp : m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ)
        = 54 / 5 * Fan H * (A : ℝ) * (L : ℝ) ^ 2
          + 9 / 2 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (4 / 3 : ℝ) ^ j₀ / (H : ℝ) * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ)
          + 9 / 5 * (3 / 2 : ℝ) ^ (Nat.log 2 H) * (8 / 3 : ℝ) ^ j₀ / (H : ℝ) ^ 2 * Ftr H
              * (L : ℝ) ^ 2 * (A : ℝ) := by
      unfold m4BclGraded m4Cmax
      ring
    rw [hexp]
    nlinarith [hres, hres2]
  calc ∑ χ : DirichletCharacter ℂ q, ∑ n ∈ Finset.Ioc A B, (doorChiSup_L_gk K χ M L n) ^ 2
      ≤ SL * ∑ j ∈ Finset.range (Lg + 1),
          (∑ t ∈ Finset.range (L / 2 ^ (j + 1) + 1),
            ∑ n ∈ Finset.Ioc A B, Y j t n) * (2 / 3 : ℝ) ^ j := hsummed
    _ ≤ SL * ((Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j
          + (arcDen 12 H * (A : ℝ)) * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left hcount hSL0
    _ = (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H))
            * (SL * ∑ j ∈ Finset.range (Lg + 1), W j * (2 / 3 : ℝ) ^ j)
          + (arcDen 12 H * (A : ℝ)) * (SL * ∑ j ∈ Finset.range j₀, W j * (2 / 3 : ℝ) ^ j) := by
        ring
    _ ≤ (Fan H * (A : ℝ) + (2 * Fan H + 8 * arcDen 12 H)) * (54 / 5 * (L : ℝ) ^ 2)
          + (arcDen 12 H * (A : ℝ)) * (9 / 2 * (L : ℝ) * (3 / 2 : ℝ) ^ Lg * (4 / 3 : ℝ) ^ j₀
            + 9 / 5 * (3 / 2 : ℝ) ^ Lg * (8 / 3 : ℝ) ^ j₀) := by
        have h1 := mul_le_mul_of_nonneg_left hfull hCan0
        have h2 := mul_le_mul_of_nonneg_left hhead harcA0
        linarith
    _ ≤ m4BclGraded j₀ Fan Ftr H * (L : ℝ) ^ 2 * (A : ℝ) := hfinal

/-- `m4_chiSummedN_supplied_L` (:1036), at the lever. -/
theorem m4_chiSummedN_supplied_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {RS : ℕ → ℕ → ℝ}
    {RSan RStr : ℕ → ℝ} (j₀ : ℕ)
    (hRSan0 : ∀ H : ℕ, 0 ≤ RSan H) (hRStr0 : ∀ H : ℕ, 0 ≤ RStr H)
    (han : ∀ j H : ℕ, j₀ ≤ j → RS j H ≤ RSan H)
    (hG1 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ^ 7 ≤ RStr H)
    (hG2 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      44 * RSan H + 87 * arcDen 12 H ≤ (4 / 3 : ℝ) ^ j₀)
    (harc8 : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 8 * arcDen 12 H ^ 3 ≤ (H : ℝ))
    (hrow : M4ChiSummedFreeRow_L_gk K R M RS) :
    M4ChiSummedBlockMeanSqN_L_gk K R M
      (m4BclGraded j₀ (fun H => 2 * RSan H) (fun H => 2 * RStr H)) := by
  refine m4_chiSummedBlockN_of_shiftBlock_L_gk K (F := fun j H => 2 * RS j H) j₀
    ?_ ?_ ?_ ?_ ?_ harc8
    (m4_chiSummedShiftBlock_of_freeRow_L_gk K hrow)
  · intro H; have := hRSan0 H; linarith
  · intro H; have := hRStr0 H; linarith
  · intro j H hj; have := han j H hj; linarith
  · intro H hlo hhi; have := hG1 H hlo hhi; linarith
  · intro H hlo hhi
    have hg2 := hG2 H hlo hhi
    have h0 := hRSan0 H
    have harc := arcDen_nonneg 12 H
    linarith
/-! ## §6 — `M4RowsChi` -/

/-- The Lemma-12 row sum is a sum of nonnegative terms (`1 ≤ X_d`, `2 ≤ H₁`, `1 ≤ P_j`) —
`ThmA2Rows.a2RowsSum_nonneg` at the free ladder. -/
private lemma m4_rowsSum_nonneg {A G Jb Xd : ℕ} {H1 : ℝ} (hXd : 1 ≤ Xd) (hH1 : 2 ≤ H1) :
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

/-- **THE DOOR BRIDGE** (`m4MrowChi_le_a2Mrow_L`).  At the door family and the vacuous ball,
the per-`χ` row number sits inside the frozen interface's `a2Mrow_L`. -/
theorem m4MrowChi_le_a2Mrow_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChi Ct Cp (AdoorL M) (3072 * M) M 2 Xd (H1doorL M) (1 / 12) X ε 0
      ≤ a2Mrow_L Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_L (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [m4_rowsSum_nonneg (A := AdoorL M) (G := 3072 * M) (Jb := 2) (Xd := Xd)
      (H1 := H1doorL M) hXd (H1door_two_L hM)]
  unfold m4MrowChi a2Mrow_L a2Level1_L a2RowsSum_L
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

/-- **⟦THE D2 DELIVERABLE AT THE DOOR⟧ THE `a2Mrow_L`-GENRE ROW FAMILY**
(`m4_hrowsSum_chi_door_L`).  §9 at the door family and the vacuous ball, landed inside the
FROZEN interface's row constant: this is `thm_a2'_of_rows_chiSummed_L`'s `hrowsSum` slot at the
constant families `Cs χ := Ct`, `Ccc χ := Cp`, `ε χ := ε`.

The frame `CalFrameK (1/12) (H1doorL M) (AdoorL M) (3072M) M 2 X_d` is the LANDED
`ThmA2.calFrameK_doorH1_at`, so only `1 ≤ M` and the cutoff `Q₂ ≤ X_d` are asked for. -/
theorem m4_hrowsSum_chi_door_L :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = bfam j m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → c p * bfam j m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
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
            ≤ a2Mrow_L Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoef hwin hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (3072 * M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L M Xd hM hXdQ) hNXd hN4 hcoef hwin
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChi_le_a2Mrow_L hM hXd1 hCp.le

/-- **THE DOOR BRIDGE, AT THE G-LEVER** (`m4MrowChi_le_a2Mrow_L_gk`).  The
landed proof at `G := s13GK K M`: `level1_term_door_decays_L_gk` supplies the level-1 leg
(K-INVARIANT, `ThmA2.a2Level1_gk_eq` puts it back as `a2Level1_L M`), and the Lemma-12 rows land
in `a2RowsSum_L_gk`.  NOTE THE POLARITY: this is NOT `a2Mrow_L_gk_le` composed with the landed
bridge — the target `a2Mrow_L_gk` is the SMALLER number, so the estimate is re-derived, not
weakened through. -/
theorem m4MrowChi_le_a2Mrow_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) {Ct Cp X ε : ℝ}
    (hCp : 0 ≤ Cp) :
    m4MrowChi Ct Cp (AdoorL M) (s13GK K M) M 2 Xd (H1doorL M) (1 / 12) X ε 0
      ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hlvl := level1_term_door_decays_L_gk K (M := M) hM (R := 9) (by norm_num)
  have hRS0 : (0 : ℝ) ≤ (∑ j ∈ Finset.Icc 1 2,
      ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
          * (Real.exp 1 / (Xd : ℝ) ^ 2))
        + 16 * Real.logb 2 (2 * (Xd : ℝ))
            / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
        + 1 / (Xd : ℝ))) + Cp * (2 / (M : ℝ)) := by
    have h2 : (0 : ℝ) ≤ Cp * (2 / (M : ℝ)) := by positivity
    linarith [m4_rowsSum_nonneg (A := AdoorL M) (G := s13GK K M) (Jb := 2) (Xd := Xd)
      (H1 := H1doorL M) hXd (H1door_two_L hM)]
  unfold m4MrowChi a2Mrow_L_gk a2RowsSum_L_gk
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

/-- **⟦THE D2 DELIVERABLE AT THE DOOR⟧ THE `a2Mrow_L`-GENRE ROW FAMILY, AT THE
G-LEVER** (`m4_hrowsSum_chi_door_L_gk`).  `m4_hrowsSum_chi` is `G`-generic and is fired at
`G := s13GK K M`; the frame is `ThmA2.calFrameK_doorH1_at_gk`, whence the side condition
`K ≤ 1.7·10⁸`. -/
theorem m4_hrowsSum_chi_door_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Ct Cp : ℝ, 0 < Ct ∧ 0 < Cp ∧
      ∀ (q : ℕ) [NeZero q] (c a : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ),
        (∀ n : ℕ, ‖a n‖ ≤ 1) → (∀ j m : ℕ, ‖bfam j m‖ ≤ 1) → (∀ p : ℕ, ‖c p‖ ≤ 1) →
      ∀ (N Xd M : ℕ) (X h ε : ℝ) (t₁ : DirichletCharacter ℂ q → ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        2 * Xd ≤ N → (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = bfam j m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → c p * bfam j m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
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
            ≤ a2Mrow_L_gk K Ct Cp M Xd X ε := by
  obtain ⟨Ct, Cp, hCt, hCp, hrows⟩ := m4_hrowsSum_chi
  refine ⟨Ct, Cp, hCt, hCp, ?_⟩
  intro q _ c a bfam ha1 hb1 hc1 N Xd M X h ε t₁ hM hXdQ hNXd hN4 hcoef hwin hasupp hQXd
    hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  refine (hrows q c a bfam ha1 hb1 hc1 N Xd (AdoorL M) (s13GK K M) M 2 (H1doorL M) X h
    (1 / 12) ε t₁ (fun _ => 0) (calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ) hNXd hN4 hcoef hwin
    hasupp hQXd hXdbig hdom hh4 hX0 hL0 hX4Xd hQ1h hcap χ T hT hTX2 hTgate hTll).trans ?_
  exact m4MrowChi_le_a2Mrow_L_gk K hM hXd1 hCp.le
/-! ## §7 — `M4ChiSocketWire` -/

/-- **THE `Σ_χ` FREE-BASE ROW SOCKET, ABOVE THE DOOR'S FLOOR** (`M4ChiSummedFreeRowBig_L`).

Byte-for-byte `M4ChiSummedFreeRow_L R M RSbig` with `doorRowFloorL M ≤ j` inserted immediately
after the window index — the shape a supplier can actually meet, because
`M4DoorClose.m4_door_meansq_carried` is itself stated only above that floor.

⟦the (α) base-cap surgery, JYH-granted 2026-07-30⟧ the socket's fourth base antecedent
`(A : ℝ) ≤ 2·R.x` is carried here verbatim, so `m4_chiSummedFreeRow_of_big_L` still meets the
socket byte for byte and every supplier below serves only the BOUNDED base range — which is
what makes `M4Assembly.DoorFuseFrame`'s decaying upper caps satisfiable at all. -/
def M4ChiSummedFreeRowBig_L (R : ChowlaRegime) (M : ℕ) (RSbig : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L χ M j (A + s) ≤ RSbig j H

/-- **THE SPLICED GRADE** (`m4ChiRowGraded_L M RSbig`) — the analytic grade above the door's
floor, the landed absolute grade `4·arcDen 12 H` below it.  `q`-FREE, as the socket demands
(the `arcDen` is the ⟦φ(q) LEDGER⟧'s character count, never the modulus). -/
def m4ChiRowGraded_L (M : ℕ) (RSbig : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ :=
  fun j H => if doorRowFloorL M ≤ j then RSbig j H else 4 * arcDen 12 H

/-- Above the floor the spliced grade IS the analytic grade — this is what ⟦gate 4⟧ reads. -/
theorem m4ChiRowGraded_big_L (M : ℕ) (RSbig : ℕ → ℕ → ℝ) {j : ℕ} (H : ℕ)
    (hj : doorRowFloorL M ≤ j) : m4ChiRowGraded_L M RSbig j H = RSbig j H := if_pos hj

/-- Below the floor the spliced grade is the absolute one — the half no consumer reads. -/
theorem m4ChiRowGraded_small_L (M : ℕ) (RSbig : ℕ → ℕ → ℝ) {j : ℕ} (H : ℕ)
    (hj : ¬ doorRowFloorL M ≤ j) : m4ChiRowGraded_L M RSbig j H = 4 * arcDen 12 H := if_neg hj

/-- **⟦GATE 4, READ⟧** — `m4_second_road_L`'s analytic-envelope gate at `j₀ := doorRowFloorL M`
sees only the `RSbig` branch, so an envelope for `RSbig` is an envelope for the splice.  This
is the whole reason the `else` branch costs nothing. -/
theorem m4ChiRowGraded_an_L {M : ℕ} {RSbig : ℕ → ℕ → ℝ} {RSan : ℕ → ℝ}
    (han : ∀ j H : ℕ, doorRowFloorL M ≤ j → RSbig j H ≤ RSan H) :
    ∀ j H : ℕ, doorRowFloorL M ≤ j → m4ChiRowGraded_L M RSbig j H ≤ RSan H := by
  intro j H hj
  rw [m4ChiRowGraded_big_L M RSbig H hj]
  exact han j H hj

/-- **⟦A4-D4a⟧ THE GRADED SPLICE** (`m4_chiSummedFreeRow_of_big_L`).  An ABSTRACT large-`j`
`Σ_χ` grade inhabits `m4_second_road_L`'s ⟦item 11⟧ at the spliced grade: above the door's
floor the hypothesis fires verbatim, below it the landed anti-vacuity witness
`m4_chiSummedFreeRow_trivial_L` carries the socket at `4·arcDen 12 H` (the `φ(q) ≤ arcDen`
count against `M4DoorClose.doorRow_trivial_grade`'s absolute `4`).

No supplier is named and no fork is entered: `RSbig` is a parameter. -/
theorem m4_chiSummedFreeRow_of_big_L {R : ChowlaRegime} {M : ℕ} {RSbig : ℕ → ℕ → ℝ}
    (hbig : M4ChiSummedFreeRowBig_L R M RSbig) :
    M4ChiSummedFreeRow_L R M (m4ChiRowGraded_L M RSbig) := by
  intro H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  by_cases hcase : doorRowFloorL M ≤ j
  · rw [m4ChiRowGraded_big_L M RSbig H hcase]
    exact hbig H hlo hhi L hLH q hq hqQ j hjL hcase A hA hAj hAsq hAx hAcap s hsL
  · rw [m4ChiRowGraded_small_L M RSbig H hcase]
    exact m4_chiSummedFreeRow_trivial_L R M H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx
      hAcap s hsL

/-- `M4ChiSummedFreeRowBig_L` (:96), at the lever. -/
def M4ChiSummedFreeRowBig_L_gk (K : ℕ) (R : ChowlaRegime) (M : ℕ) (RSbig : ℕ → ℕ → ℝ) : Prop :=
  ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H → ∀ q : ℕ, 0 < q →
    (q : ℝ) ≤ arcDen 12 H → ∀ j ≤ Nat.log 2 L, doorRowFloorL M ≤ j → ∀ A : ℕ, 0 < A →
      2 ^ j ≤ A → Real.sqrt (H : ℝ) ≤ (A : ℝ) →
      (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) →
      ∀ s ≤ L,
        ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq_L_gk K χ M j (A + s) ≤ RSbig j H

/-- `m4_chiSummedFreeRow_of_big_L` (:137), at the lever. -/
theorem m4_chiSummedFreeRow_of_big_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {RSbig : ℕ → ℕ → ℝ}
    (hbig : M4ChiSummedFreeRowBig_L_gk K R M RSbig) :
    M4ChiSummedFreeRow_L_gk K R M (m4ChiRowGraded_L M RSbig) := by
  intro H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx hAcap s hsL
  by_cases hcase : doorRowFloorL M ≤ j
  · rw [m4ChiRowGraded_big_L M RSbig H hcase]
    exact hbig H hlo hhi L hLH q hq hqQ j hjL hcase A hA hAj hAsq hAx hAcap s hsL
  · rw [m4ChiRowGraded_small_L M RSbig H hcase]
    exact m4_chiSummedFreeRow_trivial_L_gk K R M H hlo hhi L hLH q hq hqQ j hjL A hA hAj hAsq hAx
      hAcap s hsL
/-! ## §8 — `M4Gauss` -/

/-- **THE COPRIME EXPANSION** — the coprime residues of the door's sieved window at the
rational `b/q`, folded into the Gauss sums and the χ-twisted window sums.

`M4ClassPrice.sum_windowClass_memSCoeff` (the two filters commute) then
`M4BridgeResidue.sum_residueClassOn_liou_eq` (the character decomposition), then the two
sums exchanged.  An EQUALITY — nothing is estimated. -/
theorem coprime_window_expansion_L {q : ℕ} [NeZero q] (M K n : ℕ) (b : ℤ) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
      = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m := by
  classical
  have hclass : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
      ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
        = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m := by
    intro r hr
    have hcop : Nat.Coprime q r := (Finset.mem_filter.mp hr).2
    have hfilt : ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
        = ∑ m ∈ residueClassOn q r (doorSievedWindow_L M K n), liouvilleC m := by
      simpa only [doorSievedCoeff_L, doorSievedWindow_L] using
        sum_windowClass_memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC K n q r
    rw [hfilt]
    exact sum_residueClassOn_liou_eq hcop (doorSievedWindow_L M K n)
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
          ratPhase b q r * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m) :=
    Finset.sum_congr rfl fun r hr => by rw [hclass r hr]
  rw [hstep]
  calc ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m)
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
          ∑ χ : DirichletCharacter ℂ q, ((q.totient : ℕ) : ℂ)⁻¹
            * ((ratPhase b q r * χ ((r : ℕ) : ZMod q))
              * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by ring
    _ = ∑ χ : DirichletCharacter ℂ q,
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ((q.totient : ℕ) : ℂ)⁻¹
              * ((ratPhase b q r * χ ((r : ℕ) : ZMod q))
                * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m) := Finset.sum_comm
    _ = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [chiGaussSum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- **THE COPRIME PART OF A WINDOW, SQUARED** (`norm_sq_coprime_window_le_L`) — §2's headline:
the coprime residues of the door's sieved window at `b/q`, squared, are under the χ-SUM of
the twisted sub-window sups at any cap `Lw ≥ K`.  **Prefactor `1`.** -/
theorem norm_sq_coprime_window_le_L {q : ℕ} [NeZero q] (M : ℕ) {K Lw : ℕ} (hK : K ≤ Lw)
    (n : ℕ) (b : ℤ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L χ M Lw n) ^ 2 := by
  rw [coprime_window_expansion_L M K n b]
  refine le_trans (norm_sq_inv_totient_gauss_le b
    (fun χ => ∑ m ∈ doorSievedWindow_L M K n, liouChi χ m)) ?_
  refine Finset.sum_le_sum fun χ _ => ?_
  have h := le_doorChiSup_L χ M Lw n hK
  have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L M K n, liouChi χ m‖ := norm_nonneg _
  nlinarith

/-- **ONE CLASS, DILATED** (`class_rat_dilate_L`) — the bare class sum of the door's sieved
datum at `(q, r)` IS `λ(d)` times the bare class sum at the reduced pair `(q/d, r/d)` on the
dilated window, `d = gcd(r,q)`.

`M4BridgeDilate.classWindowSum_dilate` (an equality, the change of variables) then
`absWindowSum_dilCoeff_memS_door_L` (the `λ(d)` factorisation under the `M`-RELATIVE door gate
`gcd(r,q) ≤ W < calP (AdoorL M) (3072M) 1`).  ⟦NO NUMERAL⟧ — the ceiling `W` is free; the
retired `log H ≤ 2^{21845}` (an H-upper) is never demanded.

⟦THE GATE SITS AT `d`, NOT AT `q`⟧ (wave ⑤, ⟦D0-TEST⟧'s structural fact) — the door side
(`door_gate_blocks_L`, `dilCoeff_memS_door_L`, `absWindowSum_dilCoeff_memS_door_L`) carries `q` and
`W` as PURE INTERMEDIATES: neither occurs in the conclusion, so the whole chain is
instantiable at `q := d` with `hdq := le_rfl` and ZERO new bytes.  The hypothesis here is
therefore the strictly weaker `(gcd r q : ℝ) ≤ W`; every landed caller supplies it from
`gcd r q ≤ q ≤ W`. -/
theorem class_rat_dilate_L {M K n q r : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hdW : ((Nat.gcd r q : ℕ) : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) :
    ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
      = liouvilleC (Nat.gcd r q)
        * ∑ m ∈ windowClass (dilLen K n (Nat.gcd r q)) (n / Nat.gcd r q)
            (q / Nat.gcd r q) (r / Nat.gcd r q), doorSievedCoeff_L M m := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  simp only [doorSievedCoeff_L]
  calc ∑ m ∈ windowClass K n q r, memSCoeff (calP (AdoorL M) (3072 * M))
        (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC m
      = classWindowSum (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) K n q r 0 := by
        rw [classWindowSum_eq_classPhaseSum, classPhaseSum_zero]
    _ = absWindowSum (dilCoeff (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) (Nat.gcd r q) (q / Nat.gcd r q)
            (r / Nat.gcd r q)) (dilLen K n (Nat.gcd r q)) (n / Nat.gcd r q) 0 := by
        have h := classWindowSum_dilate (memSCoeff (calP (AdoorL M) (3072 * M))
          (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC) hq r K n 0
        rwa [mul_zero] at h
    _ = liouvilleC (Nat.gcd r q) * absWindowSum (classCoeff (memSCoeff
          (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC)
            (q / Nat.gcd r q) (r / Nat.gcd r q)) (dilLen K n (Nat.gcd r q))
              (n / Nat.gcd r q) 0 :=
        absWindowSum_dilCoeff_memS_door_L (J := 2) (q := Nat.gcd r q) hM hd.ne' le_rfl hdW hW 0
    _ = liouvilleC (Nat.gcd r q) * ∑ m ∈ windowClass (dilLen K n (Nat.gcd r q))
          (n / Nat.gcd r q) (q / Nat.gcd r q) (r / Nat.gcd r q),
            memSCoeff (calP (AdoorL M) (3072 * M))
              (calQK (AdoorL M) (3072 * M) M) 2 liouvilleC m := by
        rw [absWindowSum_classCoeff_zero]

set_option maxHeartbeats 1600000 in
-- the linear anchor puts `M` (not `⌊log₂ M⌋ + 1`) in the exponent slot, so the
-- stratified assembly re-elaborates `calP`/`calQK` against a bigger term; no tactic search
-- below is unbounded
/-- **THE STRATUM `d`, SQUARED** (`stratum_sq_le_chiSummed_L`) — the classes with
`gcd(r,q) = d`, phased and summed, are under the χ-SUM at the reduced modulus `q/d` on the
dilated window.  Prefactor `1` (§2), `λ(d)` invisible (`‖λ‖ = 1`).

The cap `Lw` is a parameter with the single hypothesis `dilLen K n d ≤ Lw`, so the consumer
chooses `L` at `d = 1` and `⌊L/d⌋ + 1` at `d ≥ 2` — the two caps that keep the length under
the ambient `H`.

⟦THE GATE SITS AT `d`⟧ (wave ⑤) — `hdW : (d : ℝ) ≤ W`, NOT `(q : ℝ) ≤ W`: the door gate is
demanded at the dilation factor alone (`class_rat_dilate_L`'s header).  A consumer that
truncates the strata at a ceiling `D₀` reads this at `W := D₀`, so the analytic strata never
demand a gate above `D₀`. -/
theorem stratum_sq_le_chiSummed_L {M K n q d Lw : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hd0 : 0 < d) (hdq : d ∣ q) (hdW : (d : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen K n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L χ M Lw (n / d)) ^ 2 := by
  classical
  have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  haveI : NeZero (q / d) := ⟨hq0.ne'⟩
  -- ⟦each class of the fibre, dilated⟧
  have hterm : ∀ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
      ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m
        = liouvilleC d * (ratPhase b (q / d) (r / d)
          * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) (r / d),
              doorSievedCoeff_L M m) := by
    intro r hr
    have hgcd : Nat.gcd r q = d := (Finset.mem_filter.mp hr).2
    have hdr : d ∣ r := hgcd ▸ Nat.gcd_dvd_left r q
    have hdil := class_rat_dilate_L (M := M) (K := K) (n := n) (q := q) (r := r) hM hq
      (by rw [hgcd]; exact hdW) hW
    rw [hgcd] at hdil
    rw [hdil, ratPhase_dilate hd0 hq hdq hdr b]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_fibre_eq_coprime hq hd0 hdq
      (fun r => ratPhase b (q / d) (r / d)
        * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) (r / d), doorSievedCoeff_L M m)]
  -- ⟦the `λ(d)` is unimodular⟧
  have hround : ∀ r₀ ∈ (Finset.range (q / d)).filter (fun r₀ => Nat.Coprime (q / d) r₀),
      ratPhase b (q / d) ((d * r₀) / d)
          * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) ((d * r₀) / d),
              doorSievedCoeff_L M m
        = ratPhase b (q / d) r₀
          * ∑ m ∈ windowClass (dilLen K n d) (n / d) (q / d) r₀, doorSievedCoeff_L M m := by
    intro r₀ _
    rw [Nat.mul_div_cancel_left r₀ hd0]
  rw [Finset.sum_congr rfl hround, norm_mul, liouvilleC_norm hd0.ne', one_mul]
  exact norm_sq_coprime_window_le_L M hlen (n / d) b

/-- **THE STRATUM'S BUDGET AT ONE BASE** — the χ-SUM at the reduced modulus `q/d`, read at
the stratum's own cap and dilated base.  Named so §5's recombination and wave ⑤'s
truncation speak the same object. -/
def strataTerm_L (M q L d n : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L χ M (capL L d) (n / d)) ^ 2

theorem strataTerm_nonneg_L (M q L d n : ℕ) : 0 ≤ strataTerm_L M q L d n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **THE STRATIFIED SUP BOUND AT ONE BASE** (`subWindowSup_sq_le_strata_L`) — the door's
sieved sub-window sup at the rational `b/q`, squared, against the weighted stratum budgets.

The weights are `1/d` (the Cauchy–Schwarz side) and `d` (the budget side); their product's
`(∑_{d ∣ q} 1/d)²` is the ONLY `q`-dependence that survives the whole road, and it is
bounded `H`-only by `(1 + log arcDen)²`. -/
theorem subWindowSup_sq_le_strata_L {M n q L : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) (b : ℤ) :
    (subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L M q L d n := by
  classical
  set T := ∑ d ∈ q.divisors, Real.sqrt (strataTerm_L M q L d n) with hT
  -- ⟦every sub-window is under the sum of the strata's square roots⟧
  have hstrat : ∀ K, K ≤ L →
      ‖absWindowSum (doorSievedCoeff_L M) K n ((b : ℝ) / (q : ℝ))‖ ≤ T := by
    intro K hK
    have hsplit : absWindowSum (doorSievedCoeff_L M) K n ((b : ℝ) / (q : ℝ))
        = ∑ r ∈ Finset.range q,
            ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m := by
      have h := absWindowSum_residue_split (doorSievedCoeff_L M) K n hq b 0
      rw [add_zero] at h
      simpa only [classPhaseSum_zero] using h
    have hmaps : ∀ r ∈ Finset.range q, Nat.gcd r q ∈ q.divisors := fun r _ =>
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r q, hq.ne'⟩
    rw [hsplit, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun r => ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m)]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdW : (d : ℝ) ≤ W :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqW
    have hsq := stratum_sq_le_chiSummed_L (M := M) (K := K) (n := n) (q := q) (d := d)
      (Lw := capL L d) hM hq hd0 hdq hdW hW b (dilLen_le_capL hd0 hK)
    have h0 : (0 : ℝ) ≤ ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ := norm_nonneg _
    calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖
        = Real.sqrt (‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
            ratPhase b q r * ∑ m ∈ windowClass K n q r, doorSievedCoeff_L M m‖ ^ 2) :=
          (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (strataTerm_L M q L d n) := Real.sqrt_le_sqrt hsq
  have hsup : subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ)) ≤ T :=
    subWindowSup_le hstrat
  have hsup0 : (0 : ℝ) ≤ subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ)) :=
    subWindowSup_nonneg _ _ _ _
  -- ⟦the weighted Cauchy–Schwarz over the strata⟧
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq q.divisors
    (fun d => (Real.sqrt (d : ℝ))⁻¹)
    (fun d => Real.sqrt (d : ℝ) * Real.sqrt (strataTerm_L M q L d n))
  have hprod : ∀ d ∈ q.divisors,
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * Real.sqrt (strataTerm_L M q L d n))
        = Real.sqrt (strataTerm_L M q L d n) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hs : Real.sqrt (d : ℝ) ≠ 0 := by positivity
    field_simp
  have hf2 : ∀ d ∈ q.divisors,
      ((Real.sqrt (d : ℝ))⁻¹) ^ 2 = (1 : ℝ) / (d : ℝ) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [inv_pow, Real.sq_sqrt hd0R.le, one_div]
  have hg2 : ∀ d ∈ q.divisors,
      (Real.sqrt (d : ℝ) * Real.sqrt (strataTerm_L M q L d n)) ^ 2
        = (d : ℝ) * strataTerm_L M q L d n := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [mul_pow, Real.sq_sqrt hd0R.le, Real.sq_sqrt (strataTerm_nonneg_L M q L d n)]
  rw [Finset.sum_congr rfl hprod, Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2] at hcs
  calc (subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ T ^ 2 := by nlinarith
    _ ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L M q L d n := hcs

set_option maxHeartbeats 1600000 in
-- the stratified assembly re-elaborates the divisor sum, the fibre count, the χ-datum and
-- the ledger at every stratum, and each step carries the full `strataTerm_L` expansion; the
-- arithmetic steps are all `linarith`/`nlinarith` with explicit hints (no unbounded search)
/-- **⟦S-3⟧ THE STRATIFIED CONSUMER, IN BLOCK FORM** (`m4_freeBlockSup_of_chiSummed_L`).

The door's sieved sub-window sup at ANY rational `b/q` of the arc range, mean-squared over a
free half-open block `(A, B]` with the TIGHT fit `B + L ≤ 2A`, priced by the χ-summed supply
at the composed constant

```
      4 · (1 + log arcDen 12 H)² · B_cl H .
```

⟦WHAT IS NOT IN THE PRICE⟧ no `q`, no `q²`, no `arcDen` power: the class count died at §2's
prefactor `1`, and the strata's `1/d²` ledger paid the fibre factor.  The only survivor is
the divisor residual `(∑_{d ∣ q} 1/d)² ≤ (1 + log arcDen)²` — `H`-only and `loglog`-scale.

⟦THE GATES⟧ two, both `H`-only, one-sided and regime-absorbable: the `M`-RELATIVE dilation
gate `arcDen 12 H < calP (AdoorL M) (3072M) 1` (never the retired numeral), and the window
floor `32·arcDen 12 H² ≤ H`.  The latter is what makes every stratum's re-indexed block
non-degenerate (`2d ≤ A`) and every dilated cap admissible.

⟦R-P5, THE BASE ANTECEDENTS SWAPPED⟧ the crude base floor `32·arcDen 12 H ≤ A` is replaced
by the two x-scale-ladder facts `2H ≤ A` and `R.x ≤ 8·R.ω·A`, and the window floor is read
at its square (`16·arcDen 12 H ² ≤ H`).  All three are strictly what the socket's three base
antecedents cost at the ONE dilation this file performs: the re-indexed block
`(⌊A/d⌋ − 1, ⌊B/d⌋]` must satisfy `capL L d ≤ ⌊A/d⌋ − 1`, `√H ≤ ⌊A/d⌋ − 1` and
`R.x ≤ 16·R.ω·arcDen 12 H·(⌊A/d⌋ − 1)`, and each is derived below by the same pattern as
`hcapnar` (the narrowing at the dilated cap): one power of `arcDen 12 H` is spent because
`d ≤ arcDen 12 H`.  `32·arcDen 12 H ≤ A` still follows (`2H ≥ 2·32·arcDen`), so nothing
downstream of the old floor is weakened.

⟦THE BASE CAP — the (α) base-cap surgery, JYH-granted 2026-07-30⟧ the supply predicate now
also asks `(A : ℝ) ≤ 2·R.x` from ABOVE, and this file passes it to the dilated base for
FREE: `⌊A/d⌋ − 1 ≤ A`, so no `arcDen` power is spent on it (unlike the three lower
antecedents).  The consumer `M4SecondRoad.m4_blockMeanSqBlk2_of_chiSummed` discharges it at
the door ladder's own top rung. -/
theorem m4_freeBlockSup_of_chiSummed_L {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ} (hM : 1 ≤ M)
    (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    (hchi : M4ChiSummedBlockMeanSqN_L R M Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (L : ℝ) → 32 * arcDen 12 H ≤ (L : ℝ) →
      16 * arcDen 12 H ^ 2 ≤ (H : ℝ) →
      ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
        ∀ A B : ℕ, 0 < A → 2 * (H : ℝ) ≤ (A : ℝ) →
          (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) → B + L ≤ 2 * A →
          ∑ n ∈ Finset.Ioc A B,
              (subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ))) ^ 2
            ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  intro H hlo hhi L hLH hnar hLarc harcsq b q hq hqQ A B hA hAH hAx hAcap hfit
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hAarc : 32 * arcDen 12 H ≤ (A : ℝ) := by
    have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
    linarith
  have hres0 : (0 : ℝ) ≤ strataResidual H := strataResidual_nonneg harc1
  have hB0 := hBcl0 H
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hL0R : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hdiv0 : (0 : ℝ) ≤ ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => by positivity
  have hdivres : ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) ≤ strataResidual H := by
    refine le_trans (sum_inv_divisors_le hq) ?_
    unfold strataResidual
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have := Real.log_le_log (by linarith) hqQ
    linarith
  by_cases hAB : B < A
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  rw [Nat.not_lt] at hAB
  -- ⟦the block's own consequences: the tight fit and the two arc floors⟧
  have hLA : L ≤ A := by omega
  have hLAR : (L : ℝ) ≤ (A : ℝ) := by exact_mod_cast hLA
  have hL32 : (32 : ℝ) ≤ (L : ℝ) := by nlinarith
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  -- ⟦R-P5, THE THREE ANTECEDENTS AT THE UNDILATED BASE⟧ the two arithmetic facts every
  -- dilated instance below re-reads: `4·arcDen 12 H ≤ √H` (the window floor at its square)
  -- and `2L ≤ A` (the length antecedent with the two units of `ℕ`-division slack)
  have hH0 : 0 < H := by omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt hH0R.le
  have harcsqrt : 4 * arcDen 12 H ≤ Real.sqrt (H : ℝ) := by
    have h1 : Real.sqrt ((4 * arcDen 12 H) ^ 2) ≤ Real.sqrt (H : ℝ) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hsqrtle : Real.sqrt (H : ℝ) ≤ (H : ℝ) := by nlinarith [harcsqrt, harc1]
  have h2LA : 2 * L ≤ A := by
    have h : (2 : ℝ) * (L : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast h
  -- ⟦the per-base stratified bound, summed⟧
  have hpt : ∀ n ∈ Finset.Ioc A B,
      (subWindowSup (doorSievedCoeff_L M) L n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L M q L d n := fun n _ =>
    subWindowSup_sq_le_strata_L hM hq hqQ (hgate H hlo hhi) b
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hswap : ∑ n ∈ Finset.Ioc A B,
        ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L M q L d n)
      = (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
  rw [hswap]
  -- ⟦THE PER-STRATUM BUDGET⟧ the fibre count, the χ-datum, the sharp ledger
  have hstr : ∀ d ∈ q.divisors,
      (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n
        ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdarc : (d : ℝ) ≤ arcDen 12 H :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqQ
    have hdA2R : 2 * (d : ℝ) ≤ (A : ℝ) := by nlinarith
    have hdA2 : 2 * d ≤ A := by exact_mod_cast hdA2R
    have hdA : d ≤ A := by omega
    have hdL : (d : ℝ) ≤ (L : ℝ) := by nlinarith
    have h32dL : 32 * d ≤ L := by
      have h : (32 : ℝ) * (d : ℝ) ≤ (L : ℝ) := by linarith
      exact_mod_cast h
    have hdA3 : 3 * d ≤ A := by
      have h : (3 : ℝ) * (d : ℝ) ≤ (A : ℝ) := by linarith
      exact_mod_cast h
    -- ⟦the reduced modulus⟧
    have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
    have hq0Q : ((q / d : ℕ) : ℝ) ≤ arcDen 12 H :=
      le_trans (by exact_mod_cast Nat.div_le_self q d) hqQ
    -- ⟦the dilated cap is admissible⟧
    have hcapL : capL L d ≤ L := capL_le hd0 hL2
    have hcapH : capL L d ≤ H := le_trans hcapL hLH
    have hcapmul : (L : ℝ) ≤ (d : ℝ) * ((capL L d : ℕ) : ℝ) := by
      exact_mod_cast le_mul_capL (L := L) (d := d) hd0
    have hcap0 : (0 : ℝ) ≤ ((capL L d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcapnar : (H : ℝ) ≤ arcDen 12 H ^ 3 * ((capL L d : ℕ) : ℝ) := by
      have h1 : (L : ℝ) ≤ arcDen 12 H * ((capL L d : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hdarc hcap0
        linarith [hcapmul]
      have h2 : arcDen 12 H ^ 2 * (L : ℝ)
          ≤ arcDen 12 H ^ 2 * (arcDen 12 H * ((capL L d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have heq : arcDen 12 H ^ 2 * (arcDen 12 H * ((capL L d : ℕ) : ℝ))
          = arcDen 12 H ^ 3 * ((capL L d : ℕ) : ℝ) := by ring
      rw [heq] at h2
      linarith [hnar]
    -- ⟦the re-indexed block⟧
    have hA'2 : 2 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    have hA'pos : 0 < A / d - 1 := by omega
    have hA'3 : 3 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    -- ⟦R-P5, THE THREE ANTECEDENTS AT THE DILATED BASE⟧ each spends exactly one power of
    -- `arcDen 12 H` (because `d ≤ arcDen 12 H`) and the two `ℕ`-division units the `⌊·⌋` and
    -- the `−1` cost — the same pattern as `hcapnar` above
    have hA'cast : ((A / d - 1 : ℕ) : ℝ) = ((A / d : ℕ) : ℝ) - 1 := by
      have h1 : 1 ≤ A / d := by omega
      rw [Nat.cast_sub h1, Nat.cast_one]
    have hAdiv : (A : ℝ) ≤ (d : ℝ) * ((A / d : ℕ) : ℝ) + (d : ℝ) := by
      have h' := (Nat.cast_le (α := ℝ)).mpr (le_mul_div_add (A := A) (d := d) hd0)
      push_cast at h'
      linarith
    have hA'0 : (0 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hA'2R : (2 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      have h : (2 : ℕ) ≤ A / d - 1 := by omega
      exact_mod_cast h
    -- (i) THE LENGTH ANTECEDENT `capL L d ≤ ⌊A/d⌋ − 1`
    have hcapA : capL L d ≤ A / d - 1 := capL_le_dilated_base hd0 h32dL h2LA
    -- (ii) THE `√H` ANTECEDENT
    have hsqA' : Real.sqrt (H : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      rw [hA'cast]
      have hd4 : 4 * (d : ℝ) ≤ Real.sqrt (H : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hd4
        (by positivity : (0 : ℝ) ≤ Real.sqrt (H : ℝ) + 2)
      have hkey : (d : ℝ) * (Real.sqrt (H : ℝ) + 2) ≤ (A : ℝ) := by
        nlinarith [hmul, hsqsq, hsqrtle, hAH, hH0R, hA0R]
      have hstep : (d : ℝ) * Real.sqrt (H : ℝ)
          ≤ (d : ℝ) * (((A / d : ℕ) : ℝ) - 1) := by nlinarith [hAdiv, hkey]
      exact le_of_mul_le_mul_left hstep hd0R
    -- (iii) THE x-SCALE ANTECEDENT
    have hxA' : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) := by
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have hAd2 : (A : ℝ) ≤ (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ) := by
        rw [hA'cast]; linarith [hAdiv]
      have s1 : (R.x : ℝ)
          ≤ 8 * (R.ω : ℝ) * ((d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hAd2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
        linarith [hAx]
      have s2 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)
          ≤ 2 * (arcDen 12 H * ((A / d - 1 : ℕ) : ℝ)) := by
        have h1 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ)
            ≤ arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdarc hA'0
        have h2 : 2 * arcDen 12 H ≤ arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) := by
          nlinarith [hA'2R, harc0]
        linarith
      have s3 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
      nlinarith [s1, s3]
    -- (iv) THE BASE CAP, INHERITED (the (α) base-cap surgery, JYH-granted 2026-07-30):
    -- `⌊A/d⌋ − 1 ≤ A`, so the cap passes to the dilated base with NO `arcDen` power spent
    have hcapA' : ((A / d - 1 : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hle : ((A / d - 1 : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : A / d - 1 ≤ A := le_trans (Nat.sub_le _ _) (Nat.div_le_self A d)
        exact_mod_cast hnat
      linarith
    have hfit' : B / d + capL L d ≤ 2 * (A / d - 1) + 4 := by
      have h := dilBlock_reindex_fit (A := A) (B := B) (H := L) (d := d) hd0 hdA hfit
      have hc := capL_le_div_succ (L := L) (d := d) hd0
      omega
    -- ⟦the fibre count⟧
    have hf0 : ∀ n' : ℕ, (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ (q / d),
        (doorChiSup_L χ M (capL L d) n') ^ 2 := fun n' =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmaps : ∀ n ∈ Finset.Ioc A B, n / d ∈ Finset.Ioc (A / d - 1) (B / d) := fun n hn =>
      div_mem_reindexed hd0 hdA hn
    have hfib := sum_Ioc_comp_div_le (f := fun n' => ∑ χ : DirichletCharacter ℂ (q / d),
      (doorChiSup_L χ M (capL L d) n') ^ 2) hf0 hd0 hmaps
    -- ⟦the χ-summed datum at the reduced modulus⟧
    have hdatum := hchi H hlo hhi (capL L d) hcapH hcapnar (q / d) hq0 hq0Q
      (A / d - 1) (B / d) hA'pos hcapA hsqA' hxA' hcapA' hfit'
    -- ⟦the sharp ledger⟧
    have hled := capL_ledger (A := A) (L := L) (d := d) hd0 hB0
    have hdatum' : ∑ n' ∈ Finset.Ioc (A / d - 1) (B / d),
          ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L χ M (capL L d) n') ^ 2
        ≤ Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      exact hdatum
    have hchain : ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n
        ≤ (d : ℝ) * (Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ)) := by
      refine le_trans hfib ?_
      exact mul_le_mul_of_nonneg_left hdatum' hd0R.le
    have hfinal : ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n
        ≤ Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := le_trans hchain hled
    have hLd : ((L : ℝ) + (d : ℝ)) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
    have hstep : (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n
        ≤ (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hfinal hd0R.le
    have hdne : ((d : ℝ)) ≠ 0 := ne_of_gt hd0R
    have hrw : (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2)
        = (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
      field_simp
    refine le_trans hstep ?_
    rw [hrw]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hLd (mul_nonneg hB0 hA0R)]
  -- ⟦the recombination⟧
  have hsum : ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n
      ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstr
  have hbig0 : (0 : ℝ) ≤ 4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by positivity
  calc (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L M q L d n
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
            * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hdiv0
    _ ≤ strataResidual H * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H) := by
        have h1 : (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
              * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)
            ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H :=
          mul_le_mul_of_nonneg_left hdivres hbig0
        have h2 : (0 : ℝ) ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H := by
          positivity
        nlinarith [hdivres, hdiv0]
    _ = 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by ring

/-- `coprime_window_expansion_L` (:214), at the lever. -/
theorem coprime_window_expansion_L_gk (K : ℕ) {q : ℕ} [NeZero q] (M Kw n : ℕ) (b : ℤ) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
      = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m := by
  classical
  have hclass : ∀ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
      ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
        = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m := by
    intro r hr
    have hcop : Nat.Coprime q r := (Finset.mem_filter.mp hr).2
    have hfilt : ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
        = ∑ m ∈ residueClassOn q r (doorSievedWindow_L_gk K M Kw n), liouvilleC m := by
      simpa only [doorSievedCoeff_L_gk, doorSievedWindow_L_gk] using
        sum_windowClass_memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC Kw n q r
    rw [hfilt]
    exact sum_residueClassOn_liou_eq hcop (doorSievedWindow_L_gk K M Kw n)
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
          ratPhase b q r * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m) :=
    Finset.sum_congr rfl fun r hr => by rw [hclass r hr]
  rw [hstep]
  calc ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * (((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          χ ((r : ℕ) : ZMod q) * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m)
      = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
          ∑ χ : DirichletCharacter ℂ q, ((q.totient : ℕ) : ℂ)⁻¹
            * ((ratPhase b q r * χ ((r : ℕ) : ZMod q))
              * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun χ _ => by ring
    _ = ∑ χ : DirichletCharacter ℂ q,
          ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
            ((q.totient : ℕ) : ℂ)⁻¹
              * ((ratPhase b q r * χ ((r : ℕ) : ZMod q))
                * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m) := Finset.sum_comm
    _ = ((q.totient : ℕ) : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          chiGaussSum χ b * ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [chiGaussSum, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- `norm_sq_coprime_window_le_L` (:302), at the lever. -/
theorem norm_sq_coprime_window_le_L_gk (K : ℕ) {q : ℕ} [NeZero q] (M : ℕ) {Kw Lw : ℕ} (hK : Kw ≤ Lw)
    (n : ℕ) (b : ℤ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime q r),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, (doorChiSup_L_gk K χ M Lw n) ^ 2 := by
  rw [coprime_window_expansion_L_gk K M Kw n b]
  refine le_trans (norm_sq_inv_totient_gauss_le b
    (fun χ => ∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m)) ?_
  refine Finset.sum_le_sum fun χ _ => ?_
  have h := le_doorChiSup_L_gk K χ M Lw n hK
  have h0 : (0 : ℝ) ≤ ‖∑ m ∈ doorSievedWindow_L_gk K M Kw n, liouChi χ m‖ := norm_nonneg _
  nlinarith

/-- `class_rat_dilate_L` (:398), at the lever. -/
theorem class_rat_dilate_L_gk (K : ℕ) {M Kw n q r : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hdW : ((Nat.gcd r q : ℕ) : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) :
    ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
      = liouvilleC (Nat.gcd r q)
        * ∑ m ∈ windowClass (dilLen Kw n (Nat.gcd r q)) (n / Nat.gcd r q)
            (q / Nat.gcd r q) (r / Nat.gcd r q), doorSievedCoeff_L_gk K M m := by
  have hd : 0 < Nat.gcd r q := Nat.gcd_pos_of_pos_right r hq
  simp only [doorSievedCoeff_L_gk]
  calc ∑ m ∈ windowClass Kw n q r, memSCoeff (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m
      = classWindowSum (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) Kw n q r 0 := by
        rw [classWindowSum_eq_classPhaseSum, classPhaseSum_zero]
    _ = absWindowSum (dilCoeff (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) (Nat.gcd r q) (q / Nat.gcd r q)
            (r / Nat.gcd r q)) (dilLen Kw n (Nat.gcd r q)) (n / Nat.gcd r q) 0 := by
        have h := classWindowSum_dilate (memSCoeff (calP (AdoorL M) (s13GK K M))
          (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC) hq r Kw n 0
        rwa [mul_zero] at h
    _ = liouvilleC (Nat.gcd r q) * absWindowSum (classCoeff (memSCoeff
          (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC)
            (q / Nat.gcd r q) (r / Nat.gcd r q)) (dilLen Kw n (Nat.gcd r q))
              (n / Nat.gcd r q) 0 :=
        absWindowSum_dilCoeff_memS_door_L_gk K (J := 2) (q := Nat.gcd r q) hM hd.ne' le_rfl hdW hW 0
    _ = liouvilleC (Nat.gcd r q) * ∑ m ∈ windowClass (dilLen Kw n (Nat.gcd r q))
          (n / Nat.gcd r q) (q / Nat.gcd r q) (r / Nat.gcd r q),
            memSCoeff (calP (AdoorL M) (s13GK K M))
              (calQK (AdoorL M) (s13GK K M) M) 2 liouvilleC m := by
        rw [absWindowSum_classCoeff_zero]

set_option maxHeartbeats 1600000 in
-- same cause as the un-levered twin above
/-- `stratum_sq_le_chiSummed_L` (:448), at the lever. -/
theorem stratum_sq_le_chiSummed_L_gk (K : ℕ) {M Kw n q d Lw : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hd0 : 0 < d) (hdq : d ∣ q) (hdW : (d : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) (b : ℤ)
    (hlen : dilLen Kw n d ≤ Lw) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L_gk K χ M Lw (n / d)) ^ 2 := by
  classical
  have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
  haveI : NeZero (q / d) := ⟨hq0.ne'⟩
  -- ⟦each class of the fibre, dilated⟧
  have hterm : ∀ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
      ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m
        = liouvilleC d * (ratPhase b (q / d) (r / d)
          * ∑ m ∈ windowClass (dilLen Kw n d) (n / d) (q / d) (r / d),
              doorSievedCoeff_L_gk K M m) := by
    intro r hr
    have hgcd : Nat.gcd r q = d := (Finset.mem_filter.mp hr).2
    have hdr : d ∣ r := hgcd ▸ Nat.gcd_dvd_left r q
    have hdil := class_rat_dilate_L_gk K (M := M) (Kw := Kw) (n := n) (q := q) (r := r) hM hq
      (by rw [hgcd]; exact hdW) hW
    rw [hgcd] at hdil
    rw [hdil, ratPhase_dilate hd0 hq hdq hdr b]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_fibre_eq_coprime hq hd0 hdq
      (fun r => ratPhase b (q / d) (r / d)
        * ∑ m ∈ windowClass (dilLen Kw n d) (n / d) (q / d) (r / d), doorSievedCoeff_L_gk K M m)]
  -- ⟦the `λ(d)` is unimodular⟧
  have hround : ∀ r₀ ∈ (Finset.range (q / d)).filter (fun r₀ => Nat.Coprime (q / d) r₀),
      ratPhase b (q / d) ((d * r₀) / d)
          * ∑ m ∈ windowClass (dilLen Kw n d) (n / d) (q / d) ((d * r₀) / d),
              doorSievedCoeff_L_gk K M m
        = ratPhase b (q / d) r₀
          * ∑ m ∈ windowClass (dilLen Kw n d) (n / d) (q / d) r₀, doorSievedCoeff_L_gk K M m := by
    intro r₀ _
    rw [Nat.mul_div_cancel_left r₀ hd0]
  rw [Finset.sum_congr rfl hround, norm_mul, liouvilleC_norm hd0.ne', one_mul]
  exact norm_sq_coprime_window_le_L_gk K M hlen (n / d) b

/-- `strataTerm_L` (:565), at the lever. -/
def strataTerm_L_gk (K : ℕ) (M q L d n : ℕ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L_gk K χ M (capL L d) (n / d)) ^ 2

/-- `strataTerm_nonneg_L` (:568), at the lever. -/
theorem strataTerm_nonneg_L_gk (K : ℕ) (M q L d n : ℕ) : 0 ≤ strataTerm_L_gk K M q L d n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `subWindowSup_sq_le_strata_L` (:577), at the lever. -/
theorem subWindowSup_sq_le_strata_L_gk (K : ℕ) {M n q L : ℕ} {W : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (hqW : (q : ℝ) ≤ W) (hW : W < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) (b : ℤ) :
    (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L_gk K M q L d n := by
  classical
  set T := ∑ d ∈ q.divisors, Real.sqrt (strataTerm_L_gk K M q L d n) with hT
  -- ⟦every sub-window is under the sum of the strata's square roots⟧
  have hstrat : ∀ Kw, Kw ≤ L →
      ‖absWindowSum (doorSievedCoeff_L_gk K M) Kw n ((b : ℝ) / (q : ℝ))‖ ≤ T := by
    intro Kw hK
    have hsplit : absWindowSum (doorSievedCoeff_L_gk K M) Kw n ((b : ℝ) / (q : ℝ))
        = ∑ r ∈ Finset.range q,
            ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m := by
      have h := absWindowSum_residue_split (doorSievedCoeff_L_gk K M) Kw n hq b 0
      rw [add_zero] at h
      simpa only [classPhaseSum_zero] using h
    have hmaps : ∀ r ∈ Finset.range q, Nat.gcd r q ∈ q.divisors := fun r _ =>
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r q, hq.ne'⟩
    rw [hsplit, ← Finset.sum_fiberwise_of_maps_to hmaps
      (fun r => ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m)]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdW : (d : ℝ) ≤ W :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqW
    have hsq := stratum_sq_le_chiSummed_L_gk K (M := M) (Kw := Kw) (n := n) (q := q) (d := d)
      (Lw := capL L d) hM hq hd0 hdq hdW hW b (dilLen_le_capL hd0 hK)
    have h0 : (0 : ℝ) ≤ ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
        ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m‖ := norm_nonneg _
    calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
            ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m‖
        = Real.sqrt (‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = d),
            ratPhase b q r * ∑ m ∈ windowClass Kw n q r, doorSievedCoeff_L_gk K M m‖ ^ 2) :=
          (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (strataTerm_L_gk K M q L d n) := Real.sqrt_le_sqrt hsq
  have hsup : subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ)) ≤ T :=
    subWindowSup_le hstrat
  have hsup0 : (0 : ℝ) ≤ subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ)) :=
    subWindowSup_nonneg _ _ _ _
  -- ⟦the weighted Cauchy–Schwarz over the strata⟧
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq q.divisors
    (fun d => (Real.sqrt (d : ℝ))⁻¹)
    (fun d => Real.sqrt (d : ℝ) * Real.sqrt (strataTerm_L_gk K M q L d n))
  have hprod : ∀ d ∈ q.divisors,
      (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * Real.sqrt (strataTerm_L_gk K M q L d n))
        = Real.sqrt (strataTerm_L_gk K M q L d n) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hs : Real.sqrt (d : ℝ) ≠ 0 := by positivity
    field_simp
  have hf2 : ∀ d ∈ q.divisors,
      ((Real.sqrt (d : ℝ))⁻¹) ^ 2 = (1 : ℝ) / (d : ℝ) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [inv_pow, Real.sq_sqrt hd0R.le, one_div]
  have hg2 : ∀ d ∈ q.divisors,
      (Real.sqrt (d : ℝ) * Real.sqrt (strataTerm_L_gk K M q L d n)) ^ 2
        = (d : ℝ) * strataTerm_L_gk K M q L d n := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    rw [mul_pow, Real.sq_sqrt hd0R.le, Real.sq_sqrt (strataTerm_nonneg_L_gk K M q L d n)]
  rw [Finset.sum_congr rfl hprod, Finset.sum_congr rfl hf2, Finset.sum_congr rfl hg2] at hcs
  calc (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2
      ≤ T ^ 2 := by nlinarith
    _ ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L_gk K M q L d n := hcs

set_option maxHeartbeats 1600000 in
-- the stratified assembly re-elaborates the divisor sum, the fibre count, the χ-datum and
-- the ledger at every stratum, and each step carries the full `strataTerm_L_gk K` expansion; the
-- arithmetic steps are all `linarith`/`nlinarith` with explicit hints (no unbounded search)
/-- `m4_freeBlockSup_of_chiSummed_L` (:760), at the lever. -/
theorem m4_freeBlockSup_of_chiSummed_L_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {Bcl : ℕ → ℝ}
    (hM : 1 ≤ M)
    (hBcl0 : ∀ H : ℕ, 0 ≤ Bcl H)
    (hgate : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    (hchi : M4ChiSummedBlockMeanSqN_L_gk K R M Bcl) :
    ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ L : ℕ, L ≤ H →
      (H : ℝ) ≤ arcDen 12 H ^ 2 * (L : ℝ) → 32 * arcDen 12 H ≤ (L : ℝ) →
      16 * arcDen 12 H ^ 2 ≤ (H : ℝ) →
      ∀ (b : ℤ) (q : ℕ), 0 < q → (q : ℝ) ≤ arcDen 12 H →
        ∀ A B : ℕ, 0 < A → 2 * (H : ℝ) ≤ (A : ℝ) →
          (R.x : ℝ) ≤ 8 * (R.ω : ℝ) * (A : ℝ) → (A : ℝ) ≤ 2 * (R.x : ℝ) → B + L ≤ 2 * A →
          ∑ n ∈ Finset.Ioc A B,
              (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2
            ≤ 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by
  classical
  intro H hlo hhi L hLH hnar hLarc harcsq b q hq hqQ A B hA hAH hAx hAcap hfit
  have harc1 : (1 : ℝ) ≤ arcDen 12 H := one_le_arcDen_of_regime (R := R) hlo
  have harc0 : (0 : ℝ) < arcDen 12 H := by linarith
  have hAarc : 32 * arcDen 12 H ≤ (A : ℝ) := by
    have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
    linarith
  have hres0 : (0 : ℝ) ≤ strataResidual H := strataResidual_nonneg harc1
  have hB0 := hBcl0 H
  have hA0R : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
  have hL0R : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  have hdiv0 : (0 : ℝ) ≤ ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) :=
    Finset.sum_nonneg fun d _ => by positivity
  have hdivres : ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) ≤ strataResidual H := by
    refine le_trans (sum_inv_divisors_le hq) ?_
    unfold strataResidual
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have := Real.log_le_log (by linarith) hqQ
    linarith
  by_cases hAB : B < A
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  rw [Nat.not_lt] at hAB
  -- ⟦the block's own consequences: the tight fit and the two arc floors⟧
  have hLA : L ≤ A := by omega
  have hLAR : (L : ℝ) ≤ (A : ℝ) := by exact_mod_cast hLA
  have hL32 : (32 : ℝ) ≤ (L : ℝ) := by nlinarith
  have hL2 : 2 ≤ L := by
    have : (2 : ℝ) ≤ (L : ℝ) := by linarith
    exact_mod_cast this
  -- ⟦R-P5, THE THREE ANTECEDENTS AT THE UNDILATED BASE⟧ the two arithmetic facts every
  -- dilated instance below re-reads: `4·arcDen 12 H ≤ √H` (the window floor at its square)
  -- and `2L ≤ A` (the length antecedent with the two units of `ℕ`-division slack)
  have hH0 : 0 < H := by omega
  have hH0R : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH0
  have hLHR : (L : ℝ) ≤ (H : ℝ) := by exact_mod_cast hLH
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (H : ℝ) := Real.sqrt_nonneg _
  have hsqsq : Real.sqrt (H : ℝ) ^ 2 = (H : ℝ) := Real.sq_sqrt hH0R.le
  have harcsqrt : 4 * arcDen 12 H ≤ Real.sqrt (H : ℝ) := by
    have h1 : Real.sqrt ((4 * arcDen 12 H) ^ 2) ≤ Real.sqrt (H : ℝ) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by positivity)] at h1
  have hsqrtle : Real.sqrt (H : ℝ) ≤ (H : ℝ) := by nlinarith [harcsqrt, harc1]
  have h2LA : 2 * L ≤ A := by
    have h : (2 : ℝ) * (L : ℝ) ≤ (A : ℝ) := by linarith
    exact_mod_cast h
  -- ⟦the per-base stratified bound, summed⟧
  have hpt : ∀ n ∈ Finset.Ioc A B,
      (subWindowSup (doorSievedCoeff_L_gk K M) L n ((b : ℝ) / (q : ℝ))) ^ 2
        ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L_gk K M q L d n := fun n _ =>
    subWindowSup_sq_le_strata_L_gk K hM hq hqQ (hgate H hlo hhi) b
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hswap : ∑ n ∈ Finset.Ioc A B,
        ((∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ∑ d ∈ q.divisors, (d : ℝ) * strataTerm_L_gk K M q L d n)
      = (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
  rw [hswap]
  -- ⟦THE PER-STRATUM BUDGET⟧ the fibre count, the χ-datum, the sharp ledger
  have hstr : ∀ d ∈ q.divisors,
      (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hd0R : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hdq : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hdarc : (d : ℝ) ≤ arcDen 12 H :=
      le_trans (by exact_mod_cast Nat.le_of_dvd hq hdq) hqQ
    have hdA2R : 2 * (d : ℝ) ≤ (A : ℝ) := by nlinarith
    have hdA2 : 2 * d ≤ A := by exact_mod_cast hdA2R
    have hdA : d ≤ A := by omega
    have hdL : (d : ℝ) ≤ (L : ℝ) := by nlinarith
    have h32dL : 32 * d ≤ L := by
      have h : (32 : ℝ) * (d : ℝ) ≤ (L : ℝ) := by linarith
      exact_mod_cast h
    have hdA3 : 3 * d ≤ A := by
      have h : (3 : ℝ) * (d : ℝ) ≤ (A : ℝ) := by linarith
      exact_mod_cast h
    -- ⟦the reduced modulus⟧
    have hq0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdq) hd0
    have hq0Q : ((q / d : ℕ) : ℝ) ≤ arcDen 12 H :=
      le_trans (by exact_mod_cast Nat.div_le_self q d) hqQ
    -- ⟦the dilated cap is admissible⟧
    have hcapL : capL L d ≤ L := capL_le hd0 hL2
    have hcapH : capL L d ≤ H := le_trans hcapL hLH
    have hcapmul : (L : ℝ) ≤ (d : ℝ) * ((capL L d : ℕ) : ℝ) := by
      exact_mod_cast le_mul_capL (L := L) (d := d) hd0
    have hcap0 : (0 : ℝ) ≤ ((capL L d : ℕ) : ℝ) := Nat.cast_nonneg _
    have hcapnar : (H : ℝ) ≤ arcDen 12 H ^ 3 * ((capL L d : ℕ) : ℝ) := by
      have h1 : (L : ℝ) ≤ arcDen 12 H * ((capL L d : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hdarc hcap0
        linarith [hcapmul]
      have h2 : arcDen 12 H ^ 2 * (L : ℝ)
          ≤ arcDen 12 H ^ 2 * (arcDen 12 H * ((capL L d : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have heq : arcDen 12 H ^ 2 * (arcDen 12 H * ((capL L d : ℕ) : ℝ))
          = arcDen 12 H ^ 3 * ((capL L d : ℕ) : ℝ) := by ring
      rw [heq] at h2
      linarith [hnar]
    -- ⟦the re-indexed block⟧
    have hA'2 : 2 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    have hA'pos : 0 < A / d - 1 := by omega
    have hA'3 : 3 ≤ A / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    -- ⟦R-P5, THE THREE ANTECEDENTS AT THE DILATED BASE⟧ each spends exactly one power of
    -- `arcDen 12 H` (because `d ≤ arcDen 12 H`) and the two `ℕ`-division units the `⌊·⌋` and
    -- the `−1` cost — the same pattern as `hcapnar` above
    have hA'cast : ((A / d - 1 : ℕ) : ℝ) = ((A / d : ℕ) : ℝ) - 1 := by
      have h1 : 1 ≤ A / d := by omega
      rw [Nat.cast_sub h1, Nat.cast_one]
    have hAdiv : (A : ℝ) ≤ (d : ℝ) * ((A / d : ℕ) : ℝ) + (d : ℝ) := by
      have h' := (Nat.cast_le (α := ℝ)).mpr (le_mul_div_add (A := A) (d := d) hd0)
      push_cast at h'
      linarith
    have hA'0 : (0 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hA'2R : (2 : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      have h : (2 : ℕ) ≤ A / d - 1 := by omega
      exact_mod_cast h
    -- (i) THE LENGTH ANTECEDENT `capL L d ≤ ⌊A/d⌋ − 1`
    have hcapA : capL L d ≤ A / d - 1 := capL_le_dilated_base hd0 h32dL h2LA
    -- (ii) THE `√H` ANTECEDENT
    have hsqA' : Real.sqrt (H : ℝ) ≤ ((A / d - 1 : ℕ) : ℝ) := by
      rw [hA'cast]
      have hd4 : 4 * (d : ℝ) ≤ Real.sqrt (H : ℝ) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hd4
        (by positivity : (0 : ℝ) ≤ Real.sqrt (H : ℝ) + 2)
      have hkey : (d : ℝ) * (Real.sqrt (H : ℝ) + 2) ≤ (A : ℝ) := by
        nlinarith [hmul, hsqsq, hsqrtle, hAH, hH0R, hA0R]
      have hstep : (d : ℝ) * Real.sqrt (H : ℝ)
          ≤ (d : ℝ) * (((A / d : ℕ) : ℝ) - 1) := by nlinarith [hAdiv, hkey]
      exact le_of_mul_le_mul_left hstep hd0R
    -- (iii) THE x-SCALE ANTECEDENT
    have hxA' : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) := by
      have hω0 : (0 : ℝ) ≤ (R.ω : ℝ) := Nat.cast_nonneg _
      have hAd2 : (A : ℝ) ≤ (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ) := by
        rw [hA'cast]; linarith [hAdiv]
      have s1 : (R.x : ℝ)
          ≤ 8 * (R.ω : ℝ) * ((d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hAd2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
        linarith [hAx]
      have s2 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ) + 2 * (d : ℝ)
          ≤ 2 * (arcDen 12 H * ((A / d - 1 : ℕ) : ℝ)) := by
        have h1 : (d : ℝ) * ((A / d - 1 : ℕ) : ℝ)
            ≤ arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hdarc hA'0
        have h2 : 2 * arcDen 12 H ≤ arcDen 12 H * ((A / d - 1 : ℕ) : ℝ) := by
          nlinarith [hA'2R, harc0]
        linarith
      have s3 := mul_le_mul_of_nonneg_left s2 (by positivity : (0 : ℝ) ≤ 8 * (R.ω : ℝ))
      nlinarith [s1, s3]
    -- (iv) THE BASE CAP, INHERITED (the (α) base-cap surgery, JYH-granted 2026-07-30):
    -- `⌊A/d⌋ − 1 ≤ A`, so the cap passes to the dilated base with NO `arcDen` power spent
    have hcapA' : ((A / d - 1 : ℕ) : ℝ) ≤ 2 * (R.x : ℝ) := by
      have hle : ((A / d - 1 : ℕ) : ℝ) ≤ (A : ℝ) := by
        have hnat : A / d - 1 ≤ A := le_trans (Nat.sub_le _ _) (Nat.div_le_self A d)
        exact_mod_cast hnat
      linarith
    have hfit' : B / d + capL L d ≤ 2 * (A / d - 1) + 4 := by
      have h := dilBlock_reindex_fit (A := A) (B := B) (H := L) (d := d) hd0 hdA hfit
      have hc := capL_le_div_succ (L := L) (d := d) hd0
      omega
    -- ⟦the fibre count⟧
    have hf0 : ∀ n' : ℕ, (0 : ℝ) ≤ ∑ χ : DirichletCharacter ℂ (q / d),
        (doorChiSup_L_gk K χ M (capL L d) n') ^ 2 := fun n' =>
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hmaps : ∀ n ∈ Finset.Ioc A B, n / d ∈ Finset.Ioc (A / d - 1) (B / d) := fun n hn =>
      div_mem_reindexed hd0 hdA hn
    have hfib := sum_Ioc_comp_div_le (f := fun n' => ∑ χ : DirichletCharacter ℂ (q / d),
      (doorChiSup_L_gk K χ M (capL L d) n') ^ 2) hf0 hd0 hmaps
    -- ⟦the χ-summed datum at the reduced modulus⟧
    have hdatum := hchi H hlo hhi (capL L d) hcapH hcapnar (q / d) hq0 hq0Q
      (A / d - 1) (B / d) hA'pos hcapA hsqA' hxA' hcapA' hfit'
    -- ⟦the sharp ledger⟧
    have hled := capL_ledger (A := A) (L := L) (d := d) hd0 hB0
    have hdatum' : ∑ n' ∈ Finset.Ioc (A / d - 1) (B / d),
          ∑ χ : DirichletCharacter ℂ (q / d), (doorChiSup_L_gk K χ M (capL L d) n') ^ 2
        ≤ Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      exact hdatum
    have hchain : ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ (d : ℝ) * (Bcl H * ((capL L d : ℕ) : ℝ) ^ 2 * ((A / d - 1 : ℕ) : ℝ)) := by
      refine le_trans hfib ?_
      exact mul_le_mul_of_nonneg_left hdatum' hd0R.le
    have hfinal : ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2 := le_trans hchain hled
    have hLd : ((L : ℝ) + (d : ℝ)) ^ 2 ≤ 4 * (L : ℝ) ^ 2 := by nlinarith
    have hstep : (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
        ≤ (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hfinal hd0R.le
    have hdne : ((d : ℝ)) ≠ 0 := ne_of_gt hd0R
    have hrw : (d : ℝ) * (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ) / (d : ℝ) ^ 2)
        = (Bcl H * ((L : ℝ) + (d : ℝ)) ^ 2 * (A : ℝ)) * ((1 : ℝ) / (d : ℝ)) := by
      field_simp
    refine le_trans hstep ?_
    rw [hrw]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    linarith [mul_le_mul_of_nonneg_left hLd (mul_nonneg hB0 hA0R)]
  -- ⟦the recombination⟧
  have hsum : ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
      ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hstr
  have hbig0 : (0 : ℝ) ≤ 4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by positivity
  calc (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
        * ∑ d ∈ q.divisors, (d : ℝ) * ∑ n ∈ Finset.Ioc A B, strataTerm_L_gk K M q L d n
      ≤ (∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ))
          * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
            * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hdiv0
    _ ≤ strataResidual H * ((4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H) := by
        have h1 : (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ))
              * ∑ d ∈ q.divisors, (1 : ℝ) / (d : ℝ)
            ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H :=
          mul_le_mul_of_nonneg_left hdivres hbig0
        have h2 : (0 : ℝ) ≤ (4 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ)) * strataResidual H := by
          positivity
        nlinarith [hdivres, hdiv0]
    _ = 4 * strataResidual H ^ 2 * Bcl H * (L : ℝ) ^ 2 * (A : ℝ) := by ring
/-! ## §9 — `M4T0Discharge` -/

private lemma eight_log_le_self_t0d {Lv : ℝ} (h : 64 ≤ Lv) : 8 * Real.log Lv ≤ Lv := by
  have hL0 : (0 : ℝ) < Lv := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt Lv := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt Lv := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hsq : Real.sqrt Lv * Real.sqrt Lv = Lv := Real.mul_self_sqrt hL0.le
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hlog : Real.log (Real.sqrt Lv) ≤ Real.sqrt Lv / Real.exp 1 := by
    have h1 : Real.log (Real.sqrt Lv / Real.exp 1) ≤ Real.sqrt Lv / Real.exp 1 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hs0.ne' (Real.exp_ne_zero 1), Real.log_exp] at h1
    linarith
  have hhalf : Real.log (Real.sqrt Lv) = Real.log Lv / 2 := Real.log_sqrt hL0.le
  have hdiv : Real.sqrt Lv / Real.exp 1 ≤ Real.sqrt Lv / 2 :=
    div_le_div_of_nonneg_left hs0.le (by norm_num) he2
  rw [hhalf] at hlog
  nlinarith

private lemma ypin4_gates_t0d {k : ℝ} (hk : Real.exp 4096 ≤ k) :
    10 ≤ Real.log k ^ 4 ∧ Real.log k ^ 4 ≤ Real.sqrt k
      ∧ Real.sqrt (Real.log k) ≤ Real.log k ^ 4
      ∧ Real.log (Real.log k ^ 4) ≤ Real.sqrt (Real.log k) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos _) hk
  have hL : (4096 : ℝ) ≤ Real.log k := by
    rw [← Real.log_exp 4096]; exact Real.log_le_log (Real.exp_pos _) hk
  have hL0 : (0 : ℝ) < Real.log k := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log k := by linarith
  have hL4 : Real.log k ≤ Real.log k ^ 4 := le_self_pow₀ hL1 (by norm_num)
  have hsqL0 : (0 : ℝ) < Real.sqrt (Real.log k) := Real.sqrt_pos.mpr hL0
  have hsqLsq : Real.sqrt (Real.log k) * Real.sqrt (Real.log k) = Real.log k :=
    Real.mul_self_sqrt hL0.le
  have hsqL64 : (64 : ℝ) ≤ Real.sqrt (Real.log k) := by
    have h64 : Real.sqrt 4096 = 64 := by
      rw [show (4096 : ℝ) = 64 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt hL
  have hsqLle : Real.sqrt (Real.log k) ≤ Real.log k := by nlinarith
  have hlogpow : Real.log (Real.log k ^ 4) = 4 * Real.log (Real.log k) := by
    rw [Real.log_pow]; push_cast; ring
  have hbind : 4 * Real.log (Real.log k) ≤ Real.sqrt (Real.log k) := by
    have h8 := eight_log_le_self_t0d hsqL64
    have hhalf : Real.log (Real.sqrt (Real.log k)) = Real.log (Real.log k) / 2 :=
      Real.log_sqrt hL0.le
    rw [hhalf] at h8
    linarith
  have hg2 : Real.log k ^ 4 ≤ Real.sqrt k := by
    have hsk : Real.sqrt k = Real.exp (Real.log k * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hk0]
    have hp4 : Real.log k ^ 4 = Real.exp (4 * Real.log (Real.log k)) := by
      rw [← hlogpow]
      exact (Real.exp_log (by positivity)).symm
    rw [hsk, hp4]
    refine Real.exp_le_exp.mpr ?_
    have h8 := eight_log_le_self_t0d (le_trans (by norm_num) hL)
    linarith
  refine ⟨by nlinarith, hg2, le_trans hsqLle hL4, ?_⟩
  rw [hlogpow]
  exact hbind

/-- **THE DISCHARGE'S GRADE CONSTANT** (`t0dC1_L`).  `X`-free and `q`-free; `1 ≤ t0dC1_L Cb`
outright (`one_le_t0dC1_L`), which is `m4_hT0band_at_door_of_wide_L`'s `hC₁`. -/
def t0dC1_L (Cb : ℝ) : ℝ :=
  4 * cSq * (gradeAbsConstC (1 / (2 * Real.exp 1)) Cb + 2 * farCStar + 5)

/-- `1 ≤ t0dC1_L Cb` — `m4_hT0band_at_door_of_wide_L`'s `hC₁`, from `cSq = 20736` alone. -/
theorem one_le_t0dC1_L {Cb : ℝ} (hc1 : 2 * (1 / (2 * Real.exp 1)) < 1) (hCb0 : 0 ≤ Cb) :
    1 ≤ t0dC1_L Cb := by
  have hG : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hF : (0 : ℝ) ≤ farCStar := farCStar_nonneg
  have hcs : cSq = 20736 := rfl
  unfold t0dC1_L
  rw [hcs]
  linarith

set_option maxHeartbeats 1600000 in
-- `m4_hT0band_at_door_of_wide_L`'s ~20-binder application, with the grade expression carried
-- three times (`hgrade`, `hErr`, the conclusion) — elaboration cost only
/-- **THE `T₀`-BAND ARM OF `DoorRowCarried_L`, DISCHARGED** (`m4_t0band_discharged_L`).

  `⟦the discharge's gate list⟧ →
     ∫_{−seamT0 X}^{seamT0 X} ‖dpolyA (winCutH X_d (doorChiCoeff_L χ M)) (seamS0 (2X_d) X) t‖² dt
       ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X)`

— the RAW slot `M4MeanSq.m4_meansq_per_chi_gen` reads, at the door's sieved, χ-twisted,
UN-PHASED datum, with `(C₁′, M₀)` no longer existential but PINNED at
`(cfbC₁ X (t0dC1_L Cb), (1009/45000)·e·loglog X)`.

⟦K6⟧ the two suppliers' constants — `K` (`FarL2.box_floor_M0_pieceDatum`'s masked box floor)
and `X₀` (`CaseAWide.center_halasz_supply_wideA`'s hoisted threshold, maxed with `e^{4096}`) —
are bound OUTSIDE the instance quantifier; every gate that mentions them is INSIDE. -/
theorem m4_t0band_discharged_L (Q : ℕ) :
    ∃ K X₀ : ℝ, 0 ≤ K ∧ 0 < X₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd D : ℕ)
        (X Xw Cb Dmask : ℝ), q ≤ Q →
        X₀ ≤ Real.sqrt X → ((Xd : ℕ) : ℝ) = X →
        Real.sqrt X ≤ Xw → Xw ≤ X → 1 ≤ D → (D : ℝ) * (Xw + 1) ≤ X - 1 →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
              (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) →
        700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log (q : ℝ)
                + (q : ℝ) + (K + (Dmask + 4))) ≤ Real.log (Real.log X) →
        seamT0 X + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X →
        (D : ℝ) ^ (-(1 / 4 : ℝ)) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) := by
  obtain ⟨X₀, hX₀0, hwide⟩ := m4_hT0band_at_door_of_wide_L (fun x => Real.log x ^ 4)
  obtain ⟨K, hK0, hpiece⟩ := t0d_piece_hRHS Q
  refine ⟨K, max X₀ (Real.exp 4096), hK0,
    lt_of_lt_of_le (Real.exp_pos 4096) (le_max_right _ _), ?_⟩
  intro q _ χ M Xd D X Xw Cb Dmask hq hX0lb hXd hsqXw hXwX hD hDgate hCb0 hCbound hdebit
    hthr hgateT hDdec
  have hX₀ : X₀ ≤ Real.sqrt X := le_trans (le_max_left _ _) hX0lb
  have hsq4096 : Real.exp 4096 ≤ Real.sqrt X := le_trans (le_max_right _ _) hX0lb
  -- ⟦the scale page⟧
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos _) hsq4096
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hexp4097 : (4097 : ℝ) ≤ Real.exp 4096 := by linarith [Real.add_one_le_exp (4096 : ℝ)]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := by linarith
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hXexp : Real.exp 8192 ≤ X := by
    have hsplit : Real.exp 8192 = Real.exp 4096 * Real.exp 4096 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (4096 : ℝ)]
  have hLX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hXexp
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hX3 : (3 : ℝ) ≤ X := by
    have : (4097 : ℝ) ≤ X := le_trans (le_trans hexp4097 hsq4096) hsqX
    linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / (2 * Real.exp 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hG0 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb :=
    gradeAbsConstC_nonneg hc1 hCb0
  -- ⟦the four `Y`-gates⟧
  have hk4096 : ∀ k : ℕ, Xw ≤ (k : ℝ) → Real.exp 4096 ≤ (k : ℝ) :=
    fun k h => le_trans (le_trans hsq4096 hsqXw) h
  -- ⟦the numerals⟧
  have hE0 : (0 : ℝ) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := Real.rpow_nonneg hL0.le _
  have hQ0 : (0 : ℝ) ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_nonneg (by linarith) _
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hL0.le _
  have hB0 : (0 : ℝ) ≤ t0dB X Cb := by
    unfold t0dB
    have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
        * Real.log X ^ (-(1009 : ℝ) / 90000) := mul_nonneg hG0 hE0
    have h2 : (0 : ℝ) ≤ farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      mul_nonneg farCStar_nonneg hQ0
    linarith
  have hEdef : Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
      = Real.log X ^ (-(1009 : ℝ) / 90000) := t0d_decay_eq hL0
  -- ⟦hErr⟧
  have hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X) := by
    rw [hEdef]; exact t0d_err_le (by linarith)
  -- ⟦hgrade⟧: the four residues charged against the gate value
  have hFle : farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
      ≤ 2 * farCStar * Real.log X ^ (-(1009 : ℝ) / 90000) := by
    have h := t0d_far_le (X := X) (by linarith)
    nlinarith [farCStar_nonneg]
  have hPle : Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := t0d_P_le (by linarith)
  have hcs : cSq = 20736 := rfl
  have hgrade : 8 * (cSq * (t0dB X Cb + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
        + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
      ≤ 2 * (t0dC1_L Cb * Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    rw [hEdef]
    unfold t0dB t0dC1_L
    rw [hcs]
    linarith
  refine hwide χ M Xd (2 * Xd) D X Xw (t0dB X Cb) (t0dC1_L Cb) (t0dM0 X)
    hX3 hXd (by omega) le_rfl (one_le_t0dC1_L hc1 hCb0) hX₀ hsqXw hB0 hD hDgate
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.2.1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.2.2)
    ?_ hgrade hErr
  intro 𝒥 h𝒥 t ht k hkXw hk2X
  have hgt : |t| + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X := by linarith
  exact hpiece q χ (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) 𝒥 X Xw Cb
    Dmask t k hq hsq4096 hsqXw hXwX hCb0 hCbound (hdebit 𝒥 h𝒥) hthr hgt hkXw hk2X

/-- **THE DOOR ROW'S CARRIED REGISTER, ARM 1 DISCHARGED** (`DoorRowCarriedT0_L`).  See §4's
header for the exact diff against `M4DoorClose.DoorRowCarried`. -/
def DoorRowCarriedT0_L (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) i)
                (calQK (AdoorL M) (3072 * M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (3072 * M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (3072 * M) 2)
          (calQK (AdoorL M) (3072 * M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ (ε ≤ theta293 - 1 / 500) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (3072 * M) i)
          (calQK (AdoorL M) (3072 * M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    (5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    ((4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1_L Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

set_option maxHeartbeats 4000000 in
-- the same cause as `M4DoorClose` §3: two ~98-conjunct registers are elaborated against each
-- other; no tactic search happens, every step is a projection
/-- **THE BRIDGE** (`doorRowCarried_of_t0free_L`).  The T₀-free register implies the carried one:
every conjunct transports verbatim, and the ONE that does not — the `T₀`-band integral — is
supplied by `m4_t0band_discharged_L` from `DoorRowT0Gates` plus the register's own `(X_d : ℝ) = X`,
`0 ≤ Cb`, `ShortIntervalDatum Cb` and mask-debit conjuncts.

⟦K6⟧ `Kbox` and `X₀w` are hoisted OUTSIDE every quantifier, exactly as the register's other
eight opaque constants are. -/
theorem doorRowCarried_of_t0free_L (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarried_L Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged_L Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW, SW,
    Rbar0, Dmask, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17,
    d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35,
    d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53,
    d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71,
    d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89,
    d90, d91, d92, d93, d94, d95, d96, d97, d98⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d93
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff_L χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d69 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1_L Cb), t0dM0 X,
    cqS, cgS, cW, SW, Rbar0, Dmask, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
    d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49,
    d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67,
    d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85,
    d86, d87, d88, d89, d90, d91, d92, hT0, d94, d95, d96, d97, d98⟩

set_option maxHeartbeats 1600000 in
-- `m4_wave_structurally_closed_L`'s own budget: its register mentions `DoorRowCarriedT0_L`
-- under six binders, and that is the whole cost
/-- **THE M4 WAVE, `T₀`-ARM DISCHARGED** (`m4_wave_closed_T0_discharged_L`).
`M4DoorClose.m4_wave_structurally_closed` composed with §4's bridge: the register's ARM-1 line
now reads `DoorRowCarriedT0_L`, i.e. the `T₀`-band integral is DERIVED, not assumed.  What remains
carried is ONE analytic arm — the coprime supply `M4CoprimeBlockMeanSq_L` — plus regime
arithmetic. -/
theorem m4_wave_closed_T0_discharged_L (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general — the ONLY analytic carry left⟧
            M4CoprimeBlockMeanSq_L R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_L Qm
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmain⟩ :=
    m4_wave_structurally_closed_L Qm
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  refine hR δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv ?_ hgate harc hcp
  intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
  haveI : NeZero q := ⟨by omega⟩
  have hqQm : q ≤ Qm := by
    have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
    exact_mod_cast hRq
  exact hbridge Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q χ M
    (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
    (hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)

/-- **THE DOOR ROW'S CARRIED REGISTER, ARM 1 DISCHARGED, AT THE G-LEVER**
(`DoorRowCarriedT0_L_gk`) — `DoorRowCarriedT0_L` (:581) with `(K : ℕ)` first and every
`3072·M` at `s13GK K M`.  `a2RowsSum_L M Xd`, `a2Level1_L M`, `calH (H1doorL M)` and
`doorRowFloorL M` are LEVEL 1, hence K-INVARIANT, and keep their landed names — the same
convention `M4DoorClose.DoorRowCarried_gk` fixes.  `DoorRowT0Gates` is `G`-FREE (it names no
`M` at all) and is NOT twinned. -/
def DoorRowCarriedT0_L_gk (K : ℕ) (Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ) : Prop :=
  ∃ (P Q Ddis : ℕ) (Mt kk Dd : ℕ → ℕ) (Xa : ℕ → ℝ)
    (X h δ' V VJ L Cb kmin Ymax ε Xw cqS cgS cW SW Rbar0 Dmask : ℝ),
    -- ⟦the two pins⟧
    ((Xd : ℝ) = X) ∧ (((2 ^ j : ℕ) : ℝ) = h) ∧
    -- ⟦the scale page, at the BLOCK scale⟧
    (Real.exp (Real.exp 1) ≤ X) ∧ (Real.exp 2 ≤ Real.log X) ∧
    (h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ))) ∧
    (Real.log h + 30 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X) ∧
    TannGate X (2 * (X / h)) ∧ (5 ≤ Real.log (Real.log (2 * (X / h)))) ∧
    (T₀ ≤ 2 * (X / h)) ∧ (Real.exp 1 ≤ 2 * (X / h)) ∧
    (Real.log X ≤ L) ∧ (Real.exp 1 ≤ L) ∧ ((256 : ℝ) ≤ Real.log X) ∧
    -- ⟦the door and the band⟧
    (calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) ∧
    (3 ≤ P) ∧ ((2 : ℝ) ≤ Real.log (P : ℝ)) ∧ ((Q : ℝ) ≤ 2 * (X / h)) ∧
    (Real.log (Q : ℝ) ≤ Real.log X / Real.log (Real.log X)) ∧
    (Real.log (Q : ℝ) ≤ L) ∧
    (P83 X theta293 ≤ (P : ℝ)) ∧ ((Q : ℝ) ≤ Q83 X) ∧ (P ≤ Q) ∧ (0 < Q) ∧
    (H83 X theta293 ≤ (Xd : ℝ)) ∧ ((2 : ℝ) ≤ H83 X theta293) ∧
    ((1 : ℝ) < ((calP (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)) ∧
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    ((100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ))) ∧
    (∀ i ∈ Finset.Icc 1 2,
      ((Nat.sqrt Xd : ℝ) + 1)
          * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) i)
                (calQK (AdoorL M) (s13GK K M) M i), (1 + 3 / (p : ℝ))
        ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) i : ℕ) : ℝ)
            / Real.log ((calQK (AdoorL M) (s13GK K M) M i : ℕ) : ℝ))) ∧
    -- ⟦the window floors at the witness ladder⟧
    (∀ v ∈ ramI (H83 X theta293) P Q, (5 : ℝ) ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      ballQuarterThreshold + 1 ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * ramRbot (H83 X theta293) Xd v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      18 + Real.log (Real.log X)
          - Real.log (Real.log (ramRbot (H83 X theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log X)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      seamRad X ≤ Real.sqrt 2 * ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      thinBundleG X VJ (calH (H1doorL M) 2) (calP (AdoorL M) (s13GK K M) 2)
          (calQK (AdoorL M) (s13GK K M) M 2) * X ^ (1 - 2 * (1 / 12 : ℝ))
        ≤ ramRbot (H83 X theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      pin2Gate ≤ ((witMt (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, kmin ≤ ((witKk (H83 X theta293) Xd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((witMt (H83 X theta293) Xd v : ℕ) : ℝ) ≤ Ymax) ∧
    -- ⟦the calibration, the radius, the short-interval datum⟧
    ((0 : ℝ) < seamRad X) ∧
    ((1 : ℝ) ≤ V) ∧ (V⁻¹ ≤ δ') ∧ (Real.log V ≤ 100 * Real.log L) ∧
    (δ' ^ 2 ≤ (Real.log X) ^ (-(6 : ℝ))) ∧
    (656384 * (1 + Real.log (2 * X)) ≤ (Real.log X) ^ (4 - 3 * theta293)) ∧
    (Real.exp (mrAlpha (1 / 12) 2
        * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ) ∧
    ((0 : ℝ) ≤ Cb) ∧ ShortIntervalDatum Cb ∧
    (2 * (Real.log X) ^ ((3 : ℝ) / 5) ≤ Real.log X) ∧
    -- ⟦the `kmin`/`Ymax` ladder⟧
    (Xcap ≤ kmin) ∧ ((0 : ℝ) ≤ cofactorMfl X theta293 kmin) ∧
    ((2 : ℝ) ≤ kmin) ∧ (kmin ≤ X) ∧
    ((1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin) ∧
    (pin2Gate ≤ Ymax) ∧ (Real.log Ymax ≤ 2 * Real.log kmin) ∧
    (Real.log X ≤ Real.log Ymax) ∧
    (32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) ∧
    -- ⟦THE TWO OPAQUE CAPSTONE GATES (K6)⟧
    (420 * L * L ^ ((3 : ℝ) / 4) * (Real.log L) ^ 5 ≤ cq * (Real.log (P : ℝ)) ^ 2) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293)) ∧
    -- ⟦the ε-window⟧
    ((0 : ℝ) ≤ ε) ∧ (ε ≤ theta293 - 1 / 500) ∧ ((8640 : ℝ) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the coprime-tail page (⟦THE K6 PATTERN⟧: the threshold where `Ctail` is bound)⟧
    (100 * Real.log (Q : ℝ) ≤ Real.log (Xd : ℝ)) ∧
    (((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
      ≤ (Xd : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))) ∧
    (10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ)) ∧
    (Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) ∧
    (2688 * Ctail * Real.log (Real.log X) ≤ (Real.log X) ^ ε) ∧
    -- ⟦the per-piece cap-free floor: only the Mertens mask debit is carried⟧
    ((0 : ℝ) ≤ Dmask) ∧
    (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
          (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) ∧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kcf + 25
            + Dmask)
      < Real.log (Real.log X)) ∧
    -- ⟦THE SOCKET'S GATES⟧ (`m4_supplier_complete` at `Ps := 1`, `J := 2`)
    ((0 : ℝ) < cW) ∧ (cW ≤ 1 / Real.exp 1) ∧ (2 * cW < 1) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      TLBlockGates34 cqS (H83 X theta293) P (2 * Xd) Xd Mt kk X L cgS Cb X theta293
        (seamRad X) v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X →
      |t| + Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ)) ≤ 3 * X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 1 ≤ Dd v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Dd v ≤ kk v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Xsk ≤ Real.sqrt (Xa v)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.sqrt (Xa v) ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, Real.exp 1 ≤ Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ((Mt v : ℕ) : ℝ) ≤ 2 * Xa v) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 * Xa v ≤ X) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      (0 : ℝ) ≤ cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ)) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ X → ∀ i : ℕ,
      ((kk v / Dd v : ℕ) : ℝ) ≤ (i : ℝ) → (i : ℝ) ≤ 2 * Xa v →
        |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * X) ∧
    ((0 : ℝ) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cSq * caseASwide cW Cb (cofactorMfl X theta293 ((kk v / Dd v : ℕ) : ℝ))
          ((kk v / Dd v : ℕ) : ℝ) (Xa v)
        + cSq * ((Dd v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ SW) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q, 2 / ramRbot (H83 X theta293) Xd v
      ≤ cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) / 3) ∧
    (∀ v ∈ ramI (H83 X theta293) P Q,
      cofactorRbdGen SW ((kk v : ℕ) : ℝ) ((Mt v : ℕ) : ℝ)
          (Tstar2 ((Mt v : ℕ) : ℝ) (Real.log ((Mt v : ℕ) : ℝ))) (seamRad X) ≤ Rbar0) ∧
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293)) ∧
    -- ⟦THE ENDPOINT⟧ (`M4Band.memSCoeff_endpoint_zero_of_seamCoefW` is the converse)
    (doorChiCoeff_L_gk K χ M Xd = 0) ∧
    -- ⟦ARM 1 DISCHARGED: the T₀-band gates, not the T₀-band integral⟧
    DoorRowT0Gates Kbox X₀w q Ddis X Xw Dmask ∧
    -- ⟦the assembled floor's threshold and the interface's grading gates⟧
    (40 * Real.log (Real.log (Real.log X))
        + 32 * ((1 / 8) * Real.log q + (1 / 4) * (q : ℝ)
            + vkDebitConst (vkEulerCorr q * vkTwistConst q) + vkMidDebit q + Kfl + 25)
      < Real.log (Real.log X)) ∧
    (374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    (5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500)) ∧
    ((4096 : ℝ) ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) ∧
    -- ⟦THE ENVELOPE: the five-summand right-hand side at this instance⟧
    (8448 * (cfbC₁ X (t0dC1_L Cb)) ^ 2 * Real.exp (-(1 / Real.exp 1) * t0dM0 X)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h
      ≤ B)

/-- **⟦D3 — THE `T₀`-BAND, DISCHARGED⟧ AT THE G-LEVER** (`m4_t0band_discharged_L_gk`).  The
landed existential `∃K` is α-renamed `Kb` here, since `K` is now the lever's binder.
`t0d_piece_hRHS` is stated at an ABSTRACT `(Pseq, Qseq)` and is `G`-FREE, so only the door
instantiation moves; the composition is `m4_hT0band_at_door_of_wide_L_gk`. -/
theorem m4_t0band_discharged_L_gk (K : ℕ) (Q : ℕ) :
    ∃ Kb X₀ : ℝ, 0 ≤ Kb ∧ 0 < X₀ ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (M Xd D : ℕ)
        (X Xw Cb Dmask : ℝ), q ≤ Q →
        X₀ ≤ Real.sqrt X → ((Xd : ℕ) : ℝ) = X →
        Real.sqrt X ≤ Xw → Xw ≤ X → 1 ≤ D → (D : ℝ) * (Xw + 1) ≤ X - 1 →
        0 ≤ Cb → ShortIntervalDatum Cb →
        (∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
          (∑ i ∈ 𝒥, ∑ p ∈ blockWindowPrimes (calP (AdoorL M) (s13GK K M) i)
              (calQK (AdoorL M) (s13GK K M) M i) X, (1 : ℝ) / (p : ℝ)) ≤ Dmask) →
        700 * ((5 / 4) * Real.log (Real.log (Real.log X)) + (3 / 4) * Real.log (q : ℝ)
                + (q : ℝ) + (Kb + (Dmask + 4))) ≤ Real.log (Real.log X) →
        seamT0 X + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X →
        (D : ℝ) ^ (-(1 / 4 : ℝ)) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) →
          (∫ t in (-(seamT0 X))..(seamT0 X),
              ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
            ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) := by
  obtain ⟨X₀, hX₀0, hwide⟩ := m4_hT0band_at_door_of_wide_L_gk K (fun x => Real.log x ^ 4)
  obtain ⟨Kb, hK0, hpiece⟩ := t0d_piece_hRHS Q
  refine ⟨Kb, max X₀ (Real.exp 4096), hK0,
    lt_of_lt_of_le (Real.exp_pos 4096) (le_max_right _ _), ?_⟩
  intro q _ χ M Xd D X Xw Cb Dmask hq hX0lb hXd hsqXw hXwX hD hDgate hCb0 hCbound hdebit
    hthr hgateT hDdec
  have hX₀ : X₀ ≤ Real.sqrt X := le_trans (le_max_left _ _) hX0lb
  have hsq4096 : Real.exp 4096 ≤ Real.sqrt X := le_trans (le_max_right _ _) hX0lb
  -- ⟦the scale page⟧
  have hsq0 : (0 : ℝ) < Real.sqrt X := lt_of_lt_of_le (Real.exp_pos _) hsq4096
  have hX0 : (0 : ℝ) < X := Real.sqrt_pos.mp hsq0
  have hsqsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hexp4097 : (4097 : ℝ) ≤ Real.exp 4096 := by linarith [Real.add_one_le_exp (4096 : ℝ)]
  have hsq1 : (1 : ℝ) ≤ Real.sqrt X := by linarith
  have hsqX : Real.sqrt X ≤ X := by nlinarith
  have hXexp : Real.exp 8192 ≤ X := by
    have hsplit : Real.exp 8192 = Real.exp 4096 * Real.exp 4096 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (4096 : ℝ)]
  have hLX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hXexp
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hX3 : (3 : ℝ) ≤ X := by
    have : (4097 : ℝ) ≤ X := le_trans (le_trans hexp4097 hsq4096) hsqX
    linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc1 : 2 * (1 / (2 * Real.exp 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by positivity)]; linarith
  have hG0 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb :=
    gradeAbsConstC_nonneg hc1 hCb0
  -- ⟦the four `Y`-gates⟧
  have hk4096 : ∀ k : ℕ, Xw ≤ (k : ℝ) → Real.exp 4096 ≤ (k : ℝ) :=
    fun k h => le_trans (le_trans hsq4096 hsqXw) h
  -- ⟦the numerals⟧
  have hE0 : (0 : ℝ) ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := Real.rpow_nonneg hL0.le _
  have hQ0 : (0 : ℝ) ≤ (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_nonneg (by linarith) _
  have hP0 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hL0.le _
  have hB0 : (0 : ℝ) ≤ t0dB X Cb := by
    unfold t0dB
    have h1 : (0 : ℝ) ≤ gradeAbsConstC (1 / (2 * Real.exp 1)) Cb
        * Real.log X ^ (-(1009 : ℝ) / 90000) := mul_nonneg hG0 hE0
    have h2 : (0 : ℝ) ≤ farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1))) :=
      mul_nonneg farCStar_nonneg hQ0
    linarith
  have hEdef : Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
      = Real.log X ^ (-(1009 : ℝ) / 90000) := t0d_decay_eq hL0
  -- ⟦hErr⟧
  have hErr : 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X) := by
    rw [hEdef]; exact t0d_err_le (by linarith)
  -- ⟦hgrade⟧: the four residues charged against the gate value
  have hFle : farCStar * (Real.log X / 2) ^ (-(1 / (32 * Real.exp 1)))
      ≤ 2 * farCStar * Real.log X ^ (-(1009 : ℝ) / 90000) := by
    have h := t0d_far_le (X := X) (by linarith)
    nlinarith [farCStar_nonneg]
  have hPle : Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.log X ^ (-(1009 : ℝ) / 90000) := t0d_P_le (by linarith)
  have hcs : cSq = 20736 := rfl
  have hgrade : 8 * (cSq * (t0dB X Cb + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))
        + cSq * (D : ℝ) ^ (-(1 / 4 : ℝ)))
      ≤ 2 * (t0dC1_L Cb * Real.exp (-(1 / (2 * Real.exp 1)) * t0dM0 X)
        + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
    rw [hEdef]
    unfold t0dB t0dC1_L
    rw [hcs]
    linarith
  refine hwide χ M Xd (2 * Xd) D X Xw (t0dB X Cb) (t0dC1_L Cb) (t0dM0 X)
    hX3 hXd (by omega) le_rfl (one_le_t0dC1_L hc1 hCb0) hX₀ hsqXw hB0 hD hDgate
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.2.1)
    (fun k h _ => (ypin4_gates_t0d (hk4096 k h)).2.2.2)
    ?_ hgrade hErr
  intro 𝒥 h𝒥 t ht k hkXw hk2X
  have hgt : |t| + Tstar (2 * X) (Real.log (2 * X)) ≤ 3 * X := by linarith
  exact hpiece q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) 𝒥 X Xw Cb
    Dmask t k hq hsq4096 hsqXw hXwX hCb0 hCbound (hdebit 𝒥 h𝒥) hthr hgt hkXw hk2X

set_option maxHeartbeats 4000000 in
/-- **THE BRIDGE, AT THE G-LEVER** (`doorRowCarried_of_t0free_L_gk`) — the
levered `T₀`-free register implies `M4DoorClose.DoorRowCarried_gk`, conjunct by conjunct. -/
theorem doorRowCarried_of_t0free_L_gk (K : ℕ) (Qm : ℕ) :
    ∃ Kbox X₀w : ℝ, 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail : ℝ) (q : ℕ) [NeZero q]
        (χ : DirichletCharacter ℂ q) (M Xd j : ℕ) (B : ℝ), q ≤ Qm →
        DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B →
          DoorRowCarried_L_gk K Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M Xd j B := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hdis⟩ := m4_t0band_discharged_L_gk K Qm
  refine ⟨Kbox, X₀w, hK0, hX₀0, ?_⟩
  intro Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q _ χ M Xd j B hq hfree
  obtain ⟨P, Q, Ddis, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, Xw, cqS, cgS, cW, SW,
    Rbar0, Dmask, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17,
    d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35,
    d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49, d50, d51, d52, d53,
    d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67, d68, d69, d70, d71,
    d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85, d86, d87, d88, d89,
    d90, d91, d92, d93, d94, d95, d96, d97, d98⟩ := hfree
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := d93
  have hT0 : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA (winCutH Xd (doorChiCoeff_L_gk K χ M)) (seamS0 (2 * Xd) X) t‖ ^ 2)
        ≤ t0BandB X (cfbC₁ X (t0dC1_L Cb)) (t0dM0 X) :=
    hdis q χ M Xd Ddis X Xw Cb Dmask hq g1 d1 g2 g3 g4 g5 d46 d47 d69 g6 g7 g8
  exact ⟨P, Q, Mt, kk, Dd, Xa, X, h, δ', V, VJ, L, Cb, kmin, Ymax, ε, cfbC₁ X (t0dC1_L Cb), t0dM0 X,
    cqS, cgS, cW, SW, Rbar0, Dmask, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
    d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, d42, d43, d44, d45, d46, d47, d48, d49,
    d50, d51, d52, d53, d54, d55, d56, d57, d58, d59, d60, d61, d62, d63, d64, d65, d66, d67,
    d68, d69, d70, d71, d72, d73, d74, d75, d76, d77, d78, d79, d80, d81, d82, d83, d84, d85,
    d86, d87, d88, d89, d90, d91, d92, hT0, d94, d95, d96, d97, d98⟩

set_option maxHeartbeats 1600000 in
-- `m4_wave_structurally_closed_L_gk`'s own budget: the register mentions `DoorRowCarriedT0_L_gk`
-- under six binders, and that is the whole cost
/-- **THE M4 WAVE, `T₀`-ARM DISCHARGED, AT THE LEVER** — `m4_wave_closed_T0_discharged_L`
(:776). -/
theorem m4_wave_closed_T0_discharged_L_gk (K : ℕ) (hK : K ≤ 170000000) (Qm : ℕ) :
    ∃ (Cg : ℝ) (ε : ℚ) (δ₀ Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail Kbox X₀w : ℝ),
      1 ≤ Cg ∧ 0 < ε ∧ 0 < δ₀ ∧
      0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < Xcap ∧ 0 < Cs ∧ 0 < Ccc ∧ 0 ≤ Kfl ∧
      0 < Xsk ∧ 0 ≤ Kcf ∧ 0 < Ctail ∧ 0 ≤ Kbox ∧ 0 < X₀w ∧
      ∀ (C : ℝ), 0 ≤ C → ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
        ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
          ∀ (δ : ℝ) (Braw : ℕ → ℝ) (MS : ℕ → ℕ → ℝ) (MSan MStr : ℕ → ℝ) (M k : ℕ),
            M4DoorGates_L_gk K Cg R M k δ → 1 ≤ M →
            (∀ H : ℕ, 0 ≤ MSan H) → (∀ H : ℕ, 0 ≤ MStr H) → (∀ H : ℕ, 0 ≤ Braw H) →
            (∀ j H : ℕ, doorRowFloorL M ≤ j → MS j H ≤ MSan H) →
            (∀ j H : ℕ, j < doorRowFloorL M → MS j H ≤ MStr H) →
            (∀ (H q : ℕ), R.Hlo ≤ H → H ≤ R.Hhi → 0 < q → (q : ℝ) ≤ arcDen 12 H →
              (1 + 2 * Real.pi * (arcDen 12 H / (q : ℝ))) ^ 2
                  * ((q : ℝ) ^ 2 * (3 * m4BclGraded (doorRowFloorL M)
                      (fun H => 2 * MSan H) (fun H => 2 * MStr H) H)) ≤ Braw H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              Real.sqrt (Braw H) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              δ / 4 + 4 * 2 ^ k / (R.x : ℝ) ≤ mrtDeliveredGrade (C / 2) H) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → arcDen 12 H ≤ (Qm : ℝ)) →
            (∀ j H : ℕ, j < doorRowFloorL M → 4 ≤ MS j H) →
            -- ⟦ARM 1 DISCHARGED: the T₀-free per-instance register⟧
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ arcDen 12 H →
              ∀ i < k, ∀ χ : DirichletCharacter ℂ q, ∀ j ≤ Nat.log 2 H,
                doorRowFloorL M ≤ j → ∀ s ≤ H,
                  DoorRowCarriedT0_L_gk K Kbox X₀w Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail χ M
                    (doorLadder R.x H (i + 1) + s) j (MS j H)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              arcDen 12 H < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → 2 * arcDen 12 H ≤ (H : ℝ)) →
            -- ⟦ARM 2: the coprime supply, interval/length-general — the ONLY analytic carry left⟧
            M4CoprimeBlockMeanSq_L_gk K R M
              (m4BclGraded (doorRowFloorL M) (fun H => 2 * MSan H) (fun H => 2 * MStr H)) →
            ¬ logChowla2Fails R.eps R.x R.ω := by
  obtain ⟨Kbox, X₀w, hK0, hX₀0, hbridge⟩ := doorRowCarried_of_t0free_L_gk K Qm
  obtain ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0, hmain⟩ :=
    m4_wave_structurally_closed_L_gk K hK Qm
  refine ⟨Cg, ε, δ₀, Cq, cq, T₀, Xcap, Cs, Ccc, Kfl, Xsk, Kcf, Ctail, Kbox, X₀w,
    hCg, hε, hδ₀, hCq, hcq, hT₀, hXcap, hCs, hCcc, hKfl, hXsk0, hKcf0, hCtail0,
    hK0, hX₀0, ?_⟩
  intro C hC U1floor g
  obtain ⟨R, hReps, hU1, hRg, hR⟩ := hmain C hC U1floor g
  refine ⟨R, hReps, hU1, hRg, ?_⟩
  intro δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv hcar hgate harc hcp
  refine hR δ Braw MS MSan MStr M k hgates hM hMSan0 hMStr0 hBraw0 han htr hdrift hdel hrest
    hQm htriv ?_ hgate harc hcp
  intro H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH
  haveI : NeZero q := ⟨by omega⟩
  have hqQm : q ≤ Qm := by
    have hRq : (q : ℝ) ≤ (Qm : ℝ) := le_trans hqQ (hQm H hlo hhi)
    exact_mod_cast hRq
  exact hbridge Cq cq T₀ Xcap Cs Ccc Kfl Xsk Kcf Ctail q χ M
    (doorLadder R.x H (i + 1) + s) j (MS j H) hqQm
    (hcar H hlo hhi q hq hqQ i hik χ j hjL hj0 s hsH)
end Salt.MR

end
