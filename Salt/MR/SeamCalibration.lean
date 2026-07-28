/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TLegExit
import Salt.MR.GradedCapstone

/-!
# `SeamCalibration` — the station calibration: ONE frame for BOTH halves of the seam row

`GradedCapstone.hUG34_unconditional` (the `𝒰`-leg, socket-free) and `TLegExit.TLeg_bound`
(the graded `𝒯`-leg) are the seam row's two halves.  `TLegExit.TLeg_feeds_capstone` fits their
SHAPES; its own docstring records what it does **not** certify — that the two hypothesis
families are simultaneously satisfiable, because they live in different parameter families:

* the `𝒰`-side gates on the §8.3 station pins `H₈₃ X θ₂₉₃ = (log X)^θ`,
  `P₈₃ X θ₂₉₃ = exp((log X)^{1−θ})`, `Q₈₃ X = exp(log X/loglog X)`;
* the `𝒯`-side gates on the graded ladder `Hseq/Pseq/Qseq` through
  `TLegExit.LevelGates … j` for every `2 ≤ j ≤ J`.

This file closes that residual.  It defines the calibrated ladder, DERIVES `LevelGates` at
every level from one bundle of scalar station gates (`CalFrame`), exhibits an inhabitant of
that bundle (`calFrame_satisfiable` — no vacuity), and composes the two halves into one
theorem with no integral on the right and no ladder hypothesis left standing.

## The honest correspondence — which level talks to the §8.3 pins?  **None does.**

The natural reading ("the ladder's top rung IS the §8.3 window") is WRONG, and the corpus
already knows why: `USetPins.pin_Pii` is the ratified pin `Q_j < P₈₃` for every `j ≤ Jb`.
The whole ladder sits **strictly below** the station window:

  `log Q_J ≤ (log X)^{1/2} < (log X)^{1−θ} = log P₈₃`     (`θ = θ₂₉₃ < 1/2`),

so the `𝒯`-partition's primes and the `𝒰`-row's Lemma-12 window never overlap.  The two
families touch at exactly ONE place: the cutoff index `Jb`, at which the capstone reads the
ladder (`1 < Q_{Jb}`, `log Q_{Jb} ≤ (log X)^{1/2}`, `3 ≤ P_{Jb} ≤ Q_{Jb} ≤ Tann`,
`2 ≤ H_{Jb}`, the `α`-pins).  `ladder_below_station` records the separation; every one of the
capstone's `Jb`-reads is discharged here from `CalFrame`.  `Jset := Jb` throughout (MR runs
one `J`; the capstone's `Jb ≤ Jset` is then `le_rfl`).

## The calibrated ladder

MR §2 (4), p.6 fixes `P_j = exp(j^{4j}(log Q₁)^{j−1}log P₁)`, `Q_j = exp(j^{4j+2}(log Q₁)^j)`.
That ladder is one *witness* for MR's conditions `(2)`/`(3)`; the corpus' `CellGates`
transcribes `(2)`/`(3)` themselves, so any ladder clearing them is a legitimate calibration.
`P_j` and `Q_j` must be NATURAL numbers here (`Pseq Qseq : ℕ → ℕ`), which MR's `exp(…)` is
not, so the calibration is carried in a ℕ-valued exponent to base `2`:

  `e_j := A·G^{j−1}·(j!)²`,  `P_j := 2^{e_j}`,  `Q_j := 2^{2e_j}`,  `H_j := j²·H₁`.

`e_j/e_{j−1} = G·j²` reproduces exactly the growth MR's `j^{4j}` supplies (`P_j ≥ P₁^{j²}`),
and `H_j = j²H₁` is ⟦V6⟧'s shape — chosen because it makes `LevelGates.Hj_pin` collapse
EXACTLY: `(j²H₁)³ ≤ j⁶P₁^{1/2} ⟺ H₁³ ≤ P₁^{1/2}`, one `j`-free gate (MR's own
`H_j = j²P₁^{1/6−η}/(log Q₁)^{1/3}` clears it with `H₁ ≤ P₁^{1/6}`).

## The station gates, and why they are the honest ones (law #253)

Four of the eleven fields are MR's own ranges (`0 < η < 1/6`, `1 ≤ Jb`, `1 ≤ G`); the seven
that do work are these.

`CalFrame η H₁ A G Jb Xd` carries no hypothesis of the form "the gate holds"; every field is
a scalar threshold on the frame, and the `∀ j ∈ [2,Jb]` families are DERIVED:

* `G_gate : 64 ≤ η·G` — MR `(3)` at the halved `η` (`LevelGates.cell` runs at `η/2`).  The
  `j²` on both sides cancels against `e_j/e_{j−1} = Gj²`, so ONE numeral covers every level.
* `A_gate_lin : 2Jb ≤ A` — pays `(3)`'s `16 log j` term (`log j ≤ j ≤ Jb ≤ A/2 ≤ e_{j−1}log2`).
* `A_gate_log : 4Jb²(log e_{Jb} + 1) ≤ (η/2)(A log 2 − 1)` — MR `(2)` at the halved `η`, read
  at the TOP of the ladder: `loglog Q_j ≤ log e_j + 1 ≤ log e_{Jb} + 1` and `j ≤ Jb`, while
  the right-hand side only grows (`A ≤ e_{j−1}`).  This is the genuinely binding gate; it says
  `log P₁ ≳ Jb³ log Jb`, i.e. the anchor is chosen AFTER the cutoff — which is MR's own order
  of quantifiers (`P₁,Q₁` first, then `J = J(X)`, then `X > X(η)`).
* `A_floor : 24 ≤ A` — the block bottoms `16 ≤ log Q_j`, `2 ≤ log P_j`, `1 < log P_{j−1}`.
* `H1_two`/`H1_pin`/`Q_le_Xd` — §8.2's width gates and the sharp-`M` gate `Q_{Jb} ≤ X_d`.

`calFrame_satisfiable` exhibits `η = 1/12`, `H₁ = 2`, `A = 65536`, `G = 768`, `Jb = 2`,
`Xd = Q_{Jb}` — a genuine inhabitant, so `levelGates_calibrated` is not vacuously true, and
`calibrated_block_nonempty` shows the level blocks `I_j` carry points.

## The stones

* `calE`/`calP`/`calQ`/`calH` — the calibrated sequences, and their log identities.
* `CalFrame` — the station frame (eleven scalar gates).
* `levelGates_calibrated` — **`∀ j ∈ [2,Jb], LevelGates (calP A G) (calQ A G) (calH H₁) η
  (calP A G 1) Xd j`**, every field derived.
* `calFrame_satisfiable`, `calibrated_block_nonempty` — the non-vacuity certificates.
* `ladder_below_station` — `Q_j < P₈₃` for `j ≤ Jb` (the correspondence).
* `seam_row_calibrated` — **THE SEAM ROW, CLOSED**: `hUG34_unconditional`'s exit composed
  with `TLeg_bound` at ONE parameter family, no integral on the right, no ladder gate left.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 pp.6 (`S`, `(2)`, `(3)`, `(4)`, `J`),
p.24 (eq (20), the `H_j` table), §8.2 pp.25–27, §8.3 p.27; `docs/sources/mr_extract.md` §1,
§2.7; `docs/exploration/hsup-design.md` ⟦V6⟧.
-/

namespace Salt.MR

/-! ## §0 — the calibrated sequences -/

/-- **The calibrated exponent ladder** `e_j := A·G^{j−1}·(j!)²` (MR §2 (4)'s growth, in the
ℕ-valued form base-`2` exponentiation needs).  `e_1 = A`, and `e_j = e_{j−1}·G·j²`. -/
def calE (A G j : ℕ) : ℕ := A * G ^ (j - 1) * (Nat.factorial j) ^ 2

/-- **The calibrated `P`-ladder** `P_j := 2^{e_j}` (MR §2's `P_j`, in ℕ). -/
def calP (A G j : ℕ) : ℕ := 2 ^ calE A G j

/-- **The calibrated `Q`-ladder** `Q_j := 2^{2e_j} = P_j²` (MR §2's `Q_j`, in ℕ). -/
def calQ (A G j : ℕ) : ℕ := 2 ^ (2 * calE A G j)

/-- **The calibrated width ladder** `H_j := j²·H₁` (⟦V6⟧'s shape; MR p.24's table). -/
noncomputable def calH (H1 : ℝ) (j : ℕ) : ℝ := (j : ℝ) ^ 2 * H1

lemma calE_one (A G : ℕ) : calE A G 1 = A := by
  simp [calE, Nat.factorial]

lemma calE_mono (A : ℕ) {G : ℕ} (hG : 1 ≤ G) : Monotone (calE A G) := by
  intro i j hij
  refine Nat.mul_le_mul (Nat.mul_le_mul (le_refl A) (Nat.pow_le_pow_right hG (by omega))) ?_
  exact Nat.pow_le_pow_left (Nat.factorial_le hij) 2

/-- **The ladder's one-step ratio** `e_j = e_{j−1}·(G j²)` — the growth MR's `j^{4j}` gives,
and the reason gate `(3)`'s `j²` cancels at every level. -/
lemma calE_step (A G : ℕ) {j : ℕ} (hj : 2 ≤ j) :
    calE A G j = calE A G (j - 1) * (G * j ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have h1 : k + 2 - 1 = k + 1 := by omega
  simp only [calE, h1, Nat.add_sub_cancel, Nat.factorial_succ]
  ring

lemma calQ_mono (A : ℕ) {G : ℕ} (hG : 1 ≤ G) : Monotone (calQ A G) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (by have := calE_mono A hG hij; omega)

lemma log_calP (A G j : ℕ) :
    Real.log ((calP A G j : ℕ) : ℝ) = (calE A G j : ℝ) * Real.log 2 := by
  rw [calP]
  push_cast
  rw [Real.log_pow]

lemma log_calQ (A G j : ℕ) :
    Real.log ((calQ A G j : ℕ) : ℝ) = 2 * (calE A G j : ℝ) * Real.log 2 := by
  rw [calQ]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- The `1/2`-rpow, from the square — the form `LevelGates.Hj_pin` asks for. -/
lemma le_rpow_half_of_sq_le {x y : ℝ} (hx : 0 ≤ x) (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) :=
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ ≤ Real.sqrt y := Real.sqrt_le_sqrt h
    _ = y ^ ((1 : ℝ) / 2) := (rpow_half_eq_sqrt y).symm

/-- The block bottoms, from `24 ≤ e`. -/
private lemma calE_floor_bounds {E : ℝ} (h : (24 : ℝ) ≤ E) :
    (16 : ℝ) ≤ 2 * E * Real.log 2 ∧ (2 : ℝ) ≤ E * Real.log 2 := by
  have h1 : (24 : ℝ) * 0.6931471803 ≤ E * Real.log 2 :=
    mul_le_mul h Real.log_two_gt_d9.le (by norm_num) (by linarith)
  constructor <;> linarith

/-! ## §1 — the station frame -/

/-- **THE STATION FRAME** (law #253: every threshold the calibration spends, in-statement).
Eleven scalar gates on `(η, H₁, A, G, Jb, X_d)`; no `∀ j` hypothesis, no "for `X` large".
See the module docstring for what each one pays. -/
structure CalFrame (η H1 : ℝ) (A G Jb Xd : ℕ) : Prop where
  /-- MR's `η ∈ (0,1/6)`, lower end. -/
  eta_pos : 0 < η
  /-- MR's `η ∈ (0,1/6)`, upper end. -/
  eta_lt : η < 1 / 6
  /-- The cutoff is a genuine level. -/
  one_le_Jb : 1 ≤ Jb
  /-- The ladder's growth base is a genuine multiplier. -/
  one_le_G : 1 ≤ G
  /-- **MR `(3)` at the halved `η`**: `e_j/e_{j−1} = Gj²` beats `8log Q_{j−1}` uniformly. -/
  G_gate : 64 ≤ η * (G : ℝ)
  /-- `(3)`'s `16 log j` term, paid at the top: `log j ≤ j ≤ Jb ≤ A/2`. -/
  A_gate_lin : 2 * (Jb : ℝ) ≤ (A : ℝ)
  /-- **MR `(2)` at the halved `η`**, read at the top of the ladder. -/
  A_gate_log : 4 * (Jb : ℝ) ^ 2 * (Real.log ((calE A G Jb : ℕ) : ℝ) + 1)
      ≤ (η / 2) * ((A : ℝ) * Real.log 2 - 1)
  /-- The block bottoms `16 ≤ log Q_j`, `2 ≤ log P_j`, `1 < log P_{j−1}`. -/
  A_floor : 24 ≤ A
  /-- Lemma 12's width gate at level 1 (hence at every level, `H_j = j²H₁`). -/
  H1_two : 2 ≤ H1
  /-- MR p.24's `H`-pin, `j`-free after the `j⁶` cancels: `H₁³ ≤ P₁^{1/2}`. -/
  H1_pin : H1 ^ 3 ≤ ((calP A G 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)
  /-- The SHARP-`M` gate at the top of the ladder (hence at every level). -/
  Q_le_Xd : calQ A G Jb ≤ Xd

/-! ## §2 — `LevelGates` at the calibrated sequences -/

set_option maxHeartbeats 1000000 in
-- `LevelGates`' twelve fields — nineteen leaf obligations, eight of them inside `cell` —
-- are derived one by one from the eleven scalar frame gates; `LevelGates.cell`'s `η/2` is
-- carried explicitly
/-- **THE CALIBRATION** (`levelGates_calibrated`).  Every field of `TLegExit.LevelGates` —
including all eight of `TLegKill.CellGates` at the HALVED `η` — holds at the calibrated
sequences `P_j = 2^{e_j}`, `Q_j = 2^{2e_j}`, `H_j = j²H₁`, `P₁ = 2^A`, for every level
`2 ≤ j ≤ Jb`, derived from `CalFrame`'s eleven scalar gates alone.

The two MR conditions are where the design bites:

* `(3)` `8 log Q_{j−1} + 16 log j ≤ ((η/2)/j²)log P_j`: `log P_j = e_j log 2` and
  `e_j = e_{j−1}Gj²`, so the `j²` cancels EXACTLY and the gate becomes `32 ≤ (η/2)G`
  (`G_gate`) plus `log j ≤ e_{j−1}log 2` (`A_gate_lin`).
* `(2)` `loglog Q_j/(log P_{j−1} − 1) ≤ (η/2)/(4j²)`: `loglog Q_j = log(2e_j log 2)
  ≤ log e_j + 1` is monotone up the ladder and `j ≤ Jb`, while `log P_{j−1} − 1 ≥ A log2 − 1`
  is monotone down it — so ONE gate at the top (`A_gate_log`) covers every level. -/
theorem levelGates_calibrated {η H1 : ℝ} {A G Jb Xd : ℕ} (hF : CalFrame η H1 A G Jb Xd) :
    ∀ j ∈ Finset.Icc 2 Jb,
      LevelGates (calP A G) (calQ A G) (calH H1) η ((calP A G) 1) Xd j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj2, hjJ⟩ := hj
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hmono := calE_mono A hF.one_le_G
  -- ⟦THE THREE RUNGS⟧
  have hEp : A ≤ calE A G (j - 1) := by
    have h := hmono (show 1 ≤ j - 1 by omega)
    rwa [calE_one] at h
  have hEpj : calE A G (j - 1) ≤ calE A G j := hmono (by omega)
  have hEjJ : calE A G j ≤ calE A G Jb := hmono hjJ
  have hEpR : (24 : ℝ) ≤ ((calE A G (j - 1) : ℕ) : ℝ) := by
    have h : (24 : ℕ) ≤ calE A G (j - 1) := le_trans hF.A_floor hEp
    exact_mod_cast h
  have hEjR : (24 : ℝ) ≤ ((calE A G j : ℕ) : ℝ) := by
    have h : (24 : ℕ) ≤ calE A G j := le_trans (le_trans hF.A_floor hEp) hEpj
    exact_mod_cast h
  have hAER : ((A : ℕ) : ℝ) ≤ ((calE A G (j - 1) : ℕ) : ℝ) := by exact_mod_cast hEp
  have hEjJR : ((calE A G j : ℕ) : ℝ) ≤ ((calE A G Jb : ℕ) : ℝ) := by exact_mod_cast hEjJ
  obtain ⟨hQfl, hPfl⟩ := calE_floor_bounds hEpR
  obtain ⟨hQfl', hPfl'⟩ := calE_floor_bounds hEjR
  -- ⟦THE WIDTH LADDER⟧
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hpR : (1 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ j - 1 := by omega
    exact_mod_cast h
  have hpjR : ((j - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    have h : j - 1 ≤ j := by omega
    exact_mod_cast h
  have hH1 := hF.H1_two
  refine
    { cell := ?_, eta_lt6 := hη6, two_le_Hj := ?_, two_le_Hp := ?_, Hp_le_Hj := ?_,
      Hj_pin := ?_, logQj_ge := ?_, logPp_ge := ?_, logPj_ge := ?_, P1_le_Qp := ?_,
      one_le_P1 := ?_, Qj_le_Xd := ?_ }
  · -- ⟦MR's `(2)`/`(3)` AT THE HALVED `η`⟧
    refine
      { eta_pos := by linarith, eta_lt := by linarith, two_le_j := hj2,
        one_lt_logP := ?_, logP_le_logQ := ?_, one_le_logQ := ?_, gate2 := ?_, gate3 := ?_ }
    · rw [log_calP]; linarith
    · rw [log_calP, log_calQ]; linarith
    · rw [log_calQ]; linarith
    · -- MR `(2)`
      rw [log_calQ, log_calP]
      have hden : (0 : ℝ) < ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 - 1 := by linarith
      rw [div_le_iff₀ hden, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (j : ℝ) ^ 2)]
      -- `loglog Q_j ≤ log e_{Jb} + 1`
      have hl20 : (0 : ℝ) < Real.log 2 := by linarith
      have hprod : (0 : ℝ) < 2 * ((calE A G j : ℕ) : ℝ) * Real.log 2 :=
        mul_pos (by linarith) hl20
      have hle1 : 2 * ((calE A G j : ℕ) : ℝ) * Real.log 2 ≤ 2 * ((calE A G j : ℕ) : ℝ) :=
        mul_le_of_le_one_right (by linarith) (by linarith)
      have hs1 : Real.log (2 * ((calE A G j : ℕ) : ℝ) * Real.log 2)
          ≤ Real.log (2 * ((calE A G j : ℕ) : ℝ)) := Real.log_le_log hprod hle1
      have hs2 : Real.log (2 * ((calE A G j : ℕ) : ℝ))
          = Real.log 2 + Real.log ((calE A G j : ℕ) : ℝ) :=
        Real.log_mul (by norm_num) (by linarith)
      have hs3 : Real.log ((calE A G j : ℕ) : ℝ) ≤ Real.log ((calE A G Jb : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) hEjJR
      have hlogb : Real.log (2 * ((calE A G j : ℕ) : ℝ) * Real.log 2)
          ≤ Real.log ((calE A G Jb : ℕ) : ℝ) + 1 := by linarith
      -- `j ≤ Jb`, and the top gate
      have hjJR : (j : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hjJ
      have hJb1R : (1 : ℝ) ≤ (Jb : ℝ) := by linarith
      have hlogb0 : (0 : ℝ) ≤ Real.log ((calE A G Jb : ℕ) : ℝ) + 1 := by
        have := Real.log_nonneg (show (1 : ℝ) ≤ ((calE A G Jb : ℕ) : ℝ) by
          exact le_trans (by norm_num) (le_trans hEjR hEjJR))
        linarith
      have hsq : 4 * (j : ℝ) ^ 2 ≤ 4 * (Jb : ℝ) ^ 2 := by nlinarith
      have hmul : Real.log (2 * ((calE A G j : ℕ) : ℝ) * Real.log 2) * (4 * (j : ℝ) ^ 2)
          ≤ (Real.log ((calE A G Jb : ℕ) : ℝ) + 1) * (4 * (Jb : ℝ) ^ 2) :=
        mul_le_mul hlogb hsq (by positivity) hlogb0
      have hstep : (A : ℝ) * Real.log 2 ≤ ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hAER (by linarith)
      have hfin : (η / 2) * ((A : ℝ) * Real.log 2 - 1)
          ≤ (η / 2) * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith [hF.A_gate_log]
    · -- MR `(3)`
      rw [log_calQ, log_calP]
      have hstepR : ((calE A G j : ℕ) : ℝ)
          = ((calE A G (j - 1) : ℕ) : ℝ) * ((G : ℝ) * (j : ℝ) ^ 2) := by
        rw [calE_step A G hj2]; push_cast; ring
      rw [hstepR]
      have hjne : (j : ℝ) ≠ 0 := ne_of_gt hj0
      have hcollapse : η / 2 / (j : ℝ) ^ 2
            * ((((calE A G (j - 1) : ℕ) : ℝ) * ((G : ℝ) * (j : ℝ) ^ 2)) * Real.log 2)
          = η / 2 * (G : ℝ) * ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 := by
        field_simp
      rw [hcollapse]
      have hGb : (32 : ℝ) ≤ η / 2 * (G : ℝ) := by linarith [hF.G_gate]
      have hmul : 32 * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2)
          ≤ (η / 2 * (G : ℝ)) * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right hGb (by linarith)
      have hlogj : Real.log (j : ℝ) ≤ (j : ℝ) := by
        have := Real.log_le_sub_one_of_pos hj0; linarith
      have hjA : (j : ℝ) ≤ (A : ℝ) / 2 := by
        have hjJR : (j : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hjJ
        linarith [hF.A_gate_lin]
      have hhalf : ((calE A G (j - 1) : ℕ) : ℝ) * (1 / 2)
          ≤ ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
  · simp only [calH]; nlinarith
  · simp only [calH]; nlinarith
  · simp only [calH]
    have hsq : ((j - 1 : ℕ) : ℝ) ^ 2 ≤ (j : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (by linarith)
  · simp only [calH]
    have hid : ((j : ℝ) ^ 2 * H1) ^ 3 = (j : ℝ) ^ 6 * H1 ^ 3 := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left hF.H1_pin (by positivity)
  · rw [log_calQ]; linarith
  · rw [log_calP]; linarith
  · rw [log_calP]; linarith
  · have h : calP A G 1 ≤ calQ A G (j - 1) := by
      simp only [calP, calQ, calE_one]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h
  · exact Nat.one_le_two_pow
  · exact le_trans (calQ_mono A hF.one_le_G hjJ) hF.Q_le_Xd

/-! ## §3 — the calibration is INHABITED, and its blocks carry points -/

/-- **NO VACUITY** (`calFrame_satisfiable`).  A genuine inhabitant of `CalFrame`:
`η = 1/12`, `H₁ = 2`, `A = 65536`, `G = 768`, `Jb = 2`, `X_d = Q₂`.  The two binding gates
clear with room: `G_gate` is `64 ≤ (1/12)·768 = 64` (EXACT — `G = 64·12` is the smallest
admissible base at this `η`), and `A_gate_log` is `16(log e₂ + 1) ≤ (1/24)(65536 log 2 − 1)`,
i.e. `336 ≤ 1892` (`e₂ = 65536·768·4 = 201326592 ≤ 2^{28}`, so `log e₂ ≤ 28 log 2 < 19.41`).
`levelGates_calibrated` therefore genuinely produces `LevelGates … 2`. -/
theorem calFrame_satisfiable :
    CalFrame (1 / 12) 2 65536 768 2 (calQ 65536 768 2) := by
  have hval : calE 65536 768 2 = 201326592 := by
    norm_num [calE, Nat.factorial]
  have hlog : Real.log ((calE 65536 768 2 : ℕ) : ℝ) ≤ 20 := by
    rw [hval]
    have h1 : ((201326592 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (28 : ℕ) := by norm_num
    calc Real.log ((201326592 : ℕ) : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (28 : ℕ)) := Real.log_le_log (by norm_num) h1
      _ = 28 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 20 := by linarith [Real.log_two_lt_d9]
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by norm_num, G_gate := by norm_num, A_gate_lin := by norm_num,
      A_gate_log := ?_, A_floor := by norm_num, H1_two := by norm_num,
      H1_pin := ?_, Q_le_Xd := le_rfl }
  · push_cast
    linarith [hlog, Real.log_two_gt_d9]
  · refine le_rpow_half_of_sq_le (by norm_num) ?_
    -- `2^A` is never evaluated: the exponent stays the symbol `calE 65536 768 1`
    have h64 : (64 : ℕ) ≤ calP 65536 768 1 := by
      have hE : (6 : ℕ) ≤ calE 65536 768 1 := by rw [calE_one]; norm_num
      have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
      rw [calP, h6]
      exact Nat.pow_le_pow_right (by norm_num) hE
    have h64R : (64 : ℝ) ≤ ((calP 65536 768 1 : ℕ) : ℝ) := by exact_mod_cast h64
    calc ((2 : ℝ) ^ 3) ^ 2 = 64 := by norm_num
      _ ≤ ((calP 65536 768 1 : ℕ) : ℝ) := h64R

/-- **The calibrated blocks carry points.**  `Q_j = P_j²` makes `I_j = [⌊H_j log P_j⌋,
⌊H_j log Q_j⌋]` nonempty at every level — the `(v,r)`-sums `Ej_bound` prices are not
sums over `∅`. -/
lemma calibrated_block_nonempty {H1 : ℝ} {A G j : ℕ} (hH1 : 0 ≤ H1) :
    (ramI (calH H1 j) (calP A G j) (calQ A G j)).Nonempty := by
  rw [ramI, Finset.nonempty_Icc]
  refine Nat.floor_le_floor ?_
  rw [log_calP, log_calQ]
  have h0 : (0 : ℝ) ≤ calH H1 j := by simp only [calH]; positivity
  have hE : (0 : ℝ) ≤ ((calE A G j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg (mul_nonneg h0 hE) hl2]

/-- **THE CORRESPONDENCE** (`ladder_below_station`): no level of the `𝒯`-ladder is the §8.3
window — the WHOLE ladder sits strictly below it, `Q_j < P₈₃ X θ₂₉₃` for every `j ≤ Jb`.
`USetPins.pin_Pii` at the calibrated `Q`-ladder, whose only input is MR's own definition of
the cutoff (`log Q_{Jb} ≤ (log X)^{1/2}`) and `θ₂₉₃ < 1/2`. -/
theorem ladder_below_station {A G Jb : ℕ} {X : ℝ} (hG : 1 ≤ G) (hX : 1 < Real.log X)
    (hJdef : ((calQ A G Jb : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2))) :
    ∀ j : ℕ, j ≤ Jb → ((calQ A G j : ℕ) : ℝ) < P83 X theta293 :=
  pin_Pii X theta293 (calQ A G) Jb Jb theta293_lt_half hX hJdef
    (fun _ _ hij => calQ_mono A hG hij) le_rfl

/-! ## §4 — THE SEAM ROW, CLOSED -/

set_option maxHeartbeats 1000000 in
-- the two halves are composed at ONE parameter family; the statement is
-- `hUG34_unconditional`'s verbatim with the eleven ladder-reads deleted and `CalFrame`
-- put in their place, and `TLeg_feeds_capstone`'s bound on the right
/-- **THE SEAM ROW, CLOSED END TO END** (`seam_row_calibrated`).

`GradedCapstone.hUG34_unconditional` (the `𝒰`-leg, socket-free) and `TLegExit.TLeg_bound`
(the graded `𝒯`-leg) composed at ONE parameter family — the calibrated ladder — with NO
integral on the right and NO ladder hypothesis left standing:

  `∫_{Ann}‖F(1+it)‖² ≤ 8S² + (§8.1's level-1 term + 1536·C·e³(2T/X_d+240)/P₁ + Σ_j E_j)`
  `                        + 2(T/X + 1)(log X)^{−θ₂₉₃+ε}`.

**What is discharged here** (the eleven reads `hUG34_unconditional` makes of the ladder, all
from `CalFrame` alone): `1 < Q_{Jb}`, `1 ≤ Jb`, `Jb ≤ Jset` (`Jset := Jb`), `2 ≤ H_{Jb}`,
`0 ≤ α_{Jb}`, `3 ≤ P_{Jb}`, `P_{Jb} ≤ Q_{Jb}`, `Q_{Jb} ≤ Tann` (DERIVED from `TannGate`
and the cutoff, not assumed), the `VJ`-family (from `ramI_top_le`, replaced by the single
scalar `exp(α_{Jb} log Q_{Jb}) ≤ VJ`), `α_{Jb} ≤ 1/4 − η` and `2η ≤ 1` (eq (20)); plus
`TLeg_bound`'s ENTIRE hypothesis family — `LevelGates` at every level
(`levelGates_calibrated`), `1 ≤ X_d`, `0 ≤ Tann`, `0 < P₁`, and level 1's four
(`2 ≤ H₁`, `1 ≤ P₁`, `P₁ ≤ Q₁`, the sharp-`M` floor on all of `I₁`).

**The surviving frame** is exactly: `CalFrame` (eleven scalar station gates), MR's cutoff
`log Q_{Jb} ≤ (log X)^{1/2}`, the `𝒰`-side analytic gates of `hUG34_unconditional` that
never mention the ladder (the `X`/`Tann`/`L` frame, the §8.3 window `P83 ≤ P ≤ Q ≤ Q83`,
the pretentious-distance and collision gates, `TLBlockGates34`, the CASE-A transplant's
three, the `kmin`/`Ymax` block geometry, the two block gates and Lemma 12's rows, the
graded row's own `X ≤ N ≤ 2X`/support/sup frame), and the `𝒯`-side's dyadic frame
`2X_d ≤ N` with Lemma 12's coefficient contract on `[1,Jb]`.  Nothing else. -/
theorem seam_row_calibrated :
    ∃ Cq cq T₀ Ccol X₀ Cs : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        -- ⟦THE STATION FRAME⟧ the eleven scalar gates, in place of every ladder hypothesis
        CalFrame η H1 A G Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        -- MR §2's cutoff, at the calibrated ladder
        Real.log ((calQ A G Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the `VJ`-family, collapsed to its worst corner
        Real.exp (mrAlpha η Jb * Real.log ((calQ A G Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQ A G Jb)
            * X ^ (1 - 2 * η) ≤ ((Ms j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q → |t₁| ≤ X →
        pretDistSq (ellLin g) (costwist t₁) X ≤ (1 / 16) * Real.log (Real.log X) →
        collisionGate X 25 Ccol → 0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        (∀ j ∈ ramI (H83 X theta293) P Q, TLBlockGates34 cq (H83 X theta293) P N Xd Mt kk
          Tann L (1 / Real.exp 1) Cb X theta293 Rrad j) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ∀ t : ℝ, |t| ≤ Tann →
          |t| + Tstar2 ((Mt j : ℕ) : ℝ) (Real.log ((Mt j : ℕ) : ℝ)) ≤ 3 * X) →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin →
        0 ≤ cofactorMfl X theta293 kmin →
        2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        32 * (Real.log X) ^ (2 + 2 * theta293)
            * (20512 * δ' ^ 2 * (1 + Real.log (2 * Tann))) ≤ (Real.log X) ^ (-theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        E ≤ 3 * (720 * (Tann / X + 1) / H83 X theta293 + EP2) →
        (∫ t in (-Tann)..Tann,
            ‖ramErr (H83 X theta293) N Xd P Q a (ellLin g) cf t‖ ^ 2) ≤ E →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tann → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|)) →
        -- ⟦THE `𝒯`-SIDE FRAME⟧ the dyadic length and Lemma 12's coefficient contract
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQ A G j → ¬ p ∣ m →
          a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQ A G j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQ A G 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQ A G 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + ∑ j ∈ Finset.Icc 1 Jb,
                    lemma12Rows N Xd (calP A G j) (calQ A G j) (calH H1 j) Tann a b c)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, Ccol, X₀, hCq, hcq, hT₀, hX₀0, hcap⟩ := hUG34_unconditional
  obtain ⟨Cs, hCs, hfeed⟩ := TLeg_feeds_capstone
  refine ⟨Cq, cq, T₀, Ccol, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
  -- ⟦THE LADDER, READ FROM THE FRAME⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hEJbN : 24 ≤ calE A G Jb := by
    have h := calE_mono A hG1 hJb1
    rw [calE_one] at h
    exact le_trans hF.A_floor h
  have hJbR : (1 : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hJb1
  -- the top of the ladder
  have hQnat : 1 < calQ A G Jb := by
    simp only [calQ]
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * calE A G Jb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hQ1 : (1 : ℝ) < ((calQ A G Jb : ℕ) : ℝ) := by exact_mod_cast hQnat
  have hQpos : (0 : ℝ) < ((calQ A G Jb : ℕ) : ℝ) := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (by omega) hF.Q_le_Xd
  have hHb2 : (2 : ℝ) ≤ calH H1 Jb := by
    simp only [calH]; nlinarith [hF.H1_two]
  have hHb0 : (0 : ℝ) < calH H1 Jb := by linarith
  have hα0 : (0 : ℝ) ≤ mrAlpha η Jb := (mrAlpha_pos η hη hη6 hJb1).le
  have hP3 : 3 ≤ calP A G Jb := by
    simp only [calP]
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ calE A G Jb := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPQ : calP A G Jb ≤ calQ A G Jb :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `Q_{Jb} ≤ Tann`, DERIVED from `TannGate` and the cutoff
  have hlogX0 : (0 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hQT : ((calQ A G Jb : ℕ) : ℝ) ≤ Tann := by
    calc ((calQ A G Jb : ℕ) : ℝ) = Real.exp (Real.log ((calQ A G Jb : ℕ) : ℝ)) :=
          (Real.exp_log hQpos).symm
      _ ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_le_exp.mpr hJdef
      _ ≤ Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ Tann := hTgate
  -- the `VJ`-family, from the block top
  have hVJ : ∀ v ∈ ramI (calH H1 Jb) (calP A G Jb) (calQ A G Jb),
      Real.exp (mrAlpha η Jb * (v : ℝ) / calH H1 Jb) ≤ VJ := by
    intro v hv
    have htop := ramI_top_le hHb0 hQ1.le hv
    have hstep : mrAlpha η Jb * (v : ℝ) / calH H1 Jb
        ≤ mrAlpha η Jb * Real.log ((calQ A G Jb : ℕ) : ℝ) := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left htop hα0
    exact le_trans (Real.exp_le_exp.mpr hstep) hVJg
  have hα : mrAlpha η Jb ≤ 1 / 4 - η := by
    have hinv : (0 : ℝ) ≤ 1 / (2 * (Jb : ℝ)) := by positivity
    rw [mrAlpha]
    nlinarith
  -- ⟦LEVEL 1⟧ the `𝒯`-leg's own four
  have hcalH1 : calH H1 1 = H1 := by simp [calH]
  have hH1two : (2 : ℝ) ≤ calH H1 1 := by rw [hcalH1]; exact hF.H1_two
  have hQ1Xd : calQ A G 1 ≤ Xd := le_trans (calQ_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQ A G 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith)
      (by simp only [calQ]; exact Nat.one_le_two_pow) hQ1Xd hv
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  -- ⟦THE 𝒰-LEG AT THE CALIBRATED LADDER⟧
  have hcapinst := hcap g c a cf hg hc1 hcf1 N Xd P Q Jb Jb (calP A G) (calQ A G) m₀ Ms Mt kk
    (calH H1) (mrAlpha η) X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 le_rfl hHb2 hα0 hP3 hPQ hQT hVJ hα (by linarith) hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  -- ⟦THE 𝒯-LEG, AND THE COMPOSITION⟧
  exact hfeed c a b (calP A G) (calQ A G) (calH H1) η Jb N Xd (calP A G 1) X Tann t₁ S ε
    hη hη6 hJb1 hXd1 hNXd (by linarith) hP1pos (levelGates_calibrated hF) hH1two
    (by simp only [calP]; exact Nat.one_le_two_pow)
    (Nat.pow_le_pow_right (by norm_num) (by omega)) hbot1 hcoef hb1 (fun p => hc1 p) hwin
    hcapinst

end Salt.MR
