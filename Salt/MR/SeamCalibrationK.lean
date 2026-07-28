/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TypicalPrice

/-!
# `SeamCalibrationK` — the K-ladder: the re-pinned calibration that MEETS MR eq (28)

`TypicalPrice`'s verdict quartet (`log_calP_div_log_calQ`, `sum_calibrated_ratio_eq`,
`calibrated_ratio_not_MR_shape`, `calibrated_sum_ratio_ge_half`) is a kernel-certified
REFUTATION of the landed calibration as a supplier for MR §9 eq (28): `SeamCalibration.calQ`
is `calP²`, so `log P_j/log Q_j = 1/2` at every level and the `j`-collection is `Jb/2` — never
`o(1)`, while eq (28) needs it below `δ`.

This file is the repair, built as a **parallel family** (`docs/exploration/hsup-design.md`
⟦V9b⟧'s ruling): nothing in `SeamCalibration` or `TypicalPrice` is touched, and every landed
theorem there still holds of the landed ladder.  What changes is one exponent.

## The K-ladder

The `P`-ladder is UNCHANGED — `calP A G j = 2^{e_j}`, `e_j = A·G^{j−1}(j!)²`, and every
landed `calE`/`calP` lemma is reused verbatim (this is why there is no `calEK`: the exponent
ladder never needed `M`; `M` enters only through the `Q`-exponent and through two frame
gates).  The `Q`-ladder is re-pinned by the **K-exponent** `K_j := j²·M`:

  `calQK A G M j := 2^{(j²M)·e_j} = (calP A G j)^{K_j}`,   so   `log P_j/log Q_j = 1/(j²M)`.

That is exactly MR (4)'s shape (`log P_j/log Q_j = log P₁/(j² log Q₁)`, `mr_extract` §6.4),
with `1/M` in the role of `log P₁/log Q₁ = δ/4`.  The `j²`-decay is restored, so

  `Σ_{j=1}^{Jb} log P_j/log Q_j ≤ (Σ_{j≥1} j^{−2})/M ≤ 2/M`   (`sum_ratioK_le`),

uniformly in the cutoff (the true constant is `π²/6 = 1.6449… ≤ 2`; mathlib's elementary
`sum_Ioo_inv_sq_le` gives the `2` without the Basel value, and `2` is what the demand is
checked against below — no slack is borrowed).

## The demand side, run honestly (law #253, and the TYPDEN lesson)

MR p.31's small-`h` accounting is `(28) ≤ δ/50 + (2 + 1/50)·Σ_j log P_j/log Q_j ≤ δ`.  At the
K-ladder this is a THEOREM about `M`, not a hope: `eq28_clears_of_M` proves

  `0 < δ → 8/δ ≤ M → δ/50 + (2 + 1/50)·Σ_j log P_j/log Q_j ≤ δ`,

the arithmetic being `Σ ≤ 2/M ≤ δ/4` and `1/50 + (2+1/50)/4 = 0.525 ≤ 1`.  The pin taken by
`calFrameK_satisfiable` is `M = 800`, i.e. `δ = 1/100`, and `sum_ratioK_pinned_clears` runs
the numbers AT THAT PIN.  (MR's own `M` is `4/δ`; the factor-2 loss is the price of the
elementary `Σ j^{−2} ≤ 2` in place of `π²/6`, and is paid in the pin, not in the statement.)

## What the re-pin costs the calibration — the per-field re-derivation

`CalFrameK` is `SeamCalibration.CalFrame` with two gates re-read and one added (`one_le_M`):

* `G_gateK : 64·(Jb²M) ≤ η·G` — MR `(3)` now carries `8 log Q_{j−1} = 8(j−1)²M·e_{j−1}log2`,
  so the `j²`-cancellation against `e_j/e_{j−1} = Gj²` leaves the K-factor behind; the frame
  absorbs it at the top of the ladder (`(j−1)² ≤ Jb²`).  ⟦V9b⟧'s "`64K ≤ ηG`", with
  `K := Jb²M`.  The true demand is `24(Jb²M) ≤ (η/2)G`; `64` leaves a factor `4/3`.
* `A_gate_logK : 4Jb²(log(Jb²M) + log e_{Jb}) ≤ (η/2)(A log2 − 1)` — MR `(2)`'s
  `loglog Q_j = log(j²M·e_j·log2) ≤ log(Jb²M) + log e_{Jb}`.  ⟦V9b⟧'s "`A_gate_log` gains
  only `log K`": the anchor pays a LOGARITHM of the re-pin.
* every other field is `CalFrame`'s verbatim: `eta_pos`/`eta_lt`/`one_le_Jb`/`one_le_G`
  (MR's ranges), `A_gate_lin` (`(3)`'s `16 log j`), `A_floor` (the block bottoms),
  `H1_two`/`H1_pin` (§8.2's width gates), `Q_le_Xd` (the sharp-`M` gate).

The twelve `LevelGates` fields re-derive at the K-family (`levelGates_calibratedK`); the ones
that MOVE are `cell.logP_le_logQ`, `cell.one_le_logQ`, `cell.gate2`, `cell.gate3`,
`logQj_ge`, `P1_le_Qp`, `Qj_le_Xd` (all now carrying `K_j ≥ 1`), while the width block
(`two_le_Hj`, `two_le_Hp`, `Hp_le_Hj`, `Hj_pin`) and the `P`-side floors
(`one_lt_logP`, `logPp_ge`, `logPj_ge`, `one_le_P1`) are untouched — `calH` and `calP` did
not move.

## The inhabitant (K-3: the better `H₁`)

`calFrameK_satisfiable`: `η = 1/12`, `A = 65536`, `G = 2457600`, `M = 800`, `Jb = 2`,
`X_d = Q_{Jb}`, and — the ⟦V9b⟧ finding (iii) repair — `H₁ := P₁^{1/6}` instead of `2`.
`H1_pin` (`H₁³ ≤ P₁^{1/2}`) then holds with EQUALITY, which is the largest width `CalFrame`
permits, and the window row `480(T/X_d+1)·2e²/H_j` becomes negligible rather than `O(1)`.
`G_gateK` is exact (`64·4·800 = 204800 = (1/12)·2457600`); `A_gate_logK` is certified
at `16(9 + 28) = 592 ≤ 1892` (the true value is `16·35.26 = 564`).
No numeral `2^{big}` is ever formed: `P₁` stays the symbol `calP 65536 2457600 1`.

## The two pricing repairs

* **K-2** (`ramP2mass_direct`): ⟦V9b⟧ finding (ii).  `TypicalPrice.ramP2mass_win_le`'s
  `Σf² ≤ (Σf)²` returns `64/P²`, which is USELESS at the seam's scales (`X_d ≥ Q_j ≥ P_j²`
  makes every level's row `≥ 64`).  The direct route `Σf² ≤ (max f)(Σf)` with
  `max_n ‖coeff_n‖/n ≤ 2ω(n)/X_d` and `2^{ω(n)} ≤ n ≤ 2X_d` returns
  `16·log₂(2X_d)/(X_d·P)` — MR's own `(T/X+1)/P` grade.
* **K-3** (above): the inhabitant now takes `H₁ = P₁^{1/6}`.

## The stones

* `calQK`, `log_calQK`, `calQK_mono`, `calP_le_calQK` — the re-pinned ladder.
* `CalFrameK`, `levelGates_calibratedK` — the frame and the twelve-field re-derivation.
* `calFrameK_satisfiable`, `calibrated_block_nonemptyK`, `ladder_below_stationK` — non-vacuity
  and the correspondence.
* `log_calP_div_log_calQK`, `sum_ratioK_le`, `eq28_clears_of_M`, `sum_ratioK_pinned_clears` —
  **the number the seam row needs**, and the demand-side gate.
* `ramP2mass_direct` — the p²-row repair.
* `seam_row_calibratedK` — the seam row at the K-family.
* `sum_lemma12Rows_priced_calibratedK` — **the seam row's `Σ_j lemma12Rows` AS A NUMBER**,
  with the density collection now `C·(2/M)` instead of `C·Jb/2`.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6 ((2), (3), (4)), p.24, §8.2 pp.25–27,
§9 p.31 (eq (28), the small-`h` parameter set); `docs/sources/mr_extract.md` §1, §6.4, §6.7;
`docs/exploration/hsup-design.md` ⟦V8⟧, ⟦V9⟧, ⟦V9b⟧.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §0 — the re-pinned `Q`-ladder -/

/-- **The K-exponent's `Q`-ladder** `Q_j := 2^{(j²M)e_j} = P_j^{j²M}` (MR §2 (4)'s
`log P_j/log Q_j = log P₁/(j² log Q₁)`, with `1/M` in the role of `log P₁/log Q₁`).
The `P`-ladder is `SeamCalibration.calP`, unchanged. -/
def calQK (A G M j : ℕ) : ℕ := 2 ^ ((j ^ 2 * M) * calE A G j)

lemma log_calQK (A G M j : ℕ) :
    Real.log ((calQK A G M j : ℕ) : ℝ)
      = ((j : ℝ) ^ 2 * (M : ℝ)) * ((calE A G j : ℕ) : ℝ) * Real.log 2 := by
  rw [calQK]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

lemma calQK_mono (A : ℕ) {G M : ℕ} (hG : 1 ≤ G) : Monotone (calQK A G M) := by
  intro i j hij
  refine Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul ?_ (calE_mono A hG hij))
  exact Nat.mul_le_mul_right M (Nat.pow_le_pow_left hij 2)

lemma one_le_calQK (A G M j : ℕ) : 1 ≤ calQK A G M j := Nat.one_le_two_pow

/-- `K_j ≥ 1` is all it takes for the re-pin to be a genuine widening: `P_j ≤ Q_j`. -/
lemma calP_le_calQK {A G M j : ℕ} (hM : 1 ≤ M) (hj : 1 ≤ j) :
    calP A G j ≤ calQK A G M j := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.pow_pos hj) hM)

/-- The block bottoms, from `24 ≤ e` (`SeamCalibration`'s private helper, re-derived: the
corpus copy is not exported). -/
private lemma calEK_floor_bounds {E : ℝ} (h : (24 : ℝ) ≤ E) :
    (16 : ℝ) ≤ 2 * E * Real.log 2 ∧ (2 : ℝ) ≤ E * Real.log 2 := by
  have h1 : (24 : ℝ) * 0.6931471803 ≤ E * Real.log 2 :=
    mul_le_mul h Real.log_two_gt_d9.le (by norm_num) (by linarith)
  constructor <;> linarith

/-! ## §1 — the station frame at the K-ladder -/

/-- **THE K-STATION FRAME** (law #253).  `SeamCalibration.CalFrame` with the two MR-condition
gates re-read at the K-exponent (`G_gateK` gains the factor `Jb²M`; `A_gate_logK` gains
`log(Jb²M)`) and `one_le_M` added.  See the module docstring for the per-field account. -/
structure CalFrameK (η H1 : ℝ) (A G M Jb Xd : ℕ) : Prop where
  /-- MR's `η ∈ (0,1/6)`, lower end. -/
  eta_pos : 0 < η
  /-- MR's `η ∈ (0,1/6)`, upper end. -/
  eta_lt : η < 1 / 6
  /-- The cutoff is a genuine level. -/
  one_le_Jb : 1 ≤ Jb
  /-- The ladder's growth base is a genuine multiplier. -/
  one_le_G : 1 ≤ G
  /-- The re-pin is a genuine widening (`K_j = j²M ≥ 1`). -/
  one_le_M : 1 ≤ M
  /-- **MR `(3)` at the halved `η`, with the K-exponent absorbed** (⟦V9b⟧'s `64K ≤ ηG`). -/
  G_gateK : 64 * ((Jb : ℝ) ^ 2 * (M : ℝ)) ≤ η * (G : ℝ)
  /-- `(3)`'s `16 log j` term, paid at the top: `log j ≤ j ≤ Jb ≤ A/2`. -/
  A_gate_lin : 2 * (Jb : ℝ) ≤ (A : ℝ)
  /-- **MR `(2)` at the halved `η`**, read at the top of the ladder; the re-pin costs
  `log(Jb²M)` and nothing more. -/
  A_gate_logK : 4 * (Jb : ℝ) ^ 2
      * (Real.log ((Jb : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE A G Jb : ℕ) : ℝ))
      ≤ (η / 2) * ((A : ℝ) * Real.log 2 - 1)
  /-- The block bottoms `16 ≤ log Q_j`, `2 ≤ log P_j`, `1 < log P_{j−1}`. -/
  A_floor : 24 ≤ A
  /-- Lemma 12's width gate at level 1 (hence at every level, `H_j = j²H₁`). -/
  H1_two : 2 ≤ H1
  /-- MR p.24's `H`-pin, `j`-free after the `j⁶` cancels: `H₁³ ≤ P₁^{1/2}`. -/
  H1_pin : H1 ^ 3 ≤ ((calP A G 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)
  /-- The SHARP-`M` gate at the top of the ladder (hence at every level). -/
  Q_le_Xd : calQK A G M Jb ≤ Xd

/-! ## §2 — `LevelGates` at the K-ladder -/

set_option maxHeartbeats 1000000 in
-- the twelve `LevelGates` fields, re-derived at `Q_j = P_j^{j²M}`; the seven that move are
-- the ones carrying `K_j`, the five width/`P`-floor fields are `SeamCalibration`'s verbatim
/-- **THE K-CALIBRATION** (`levelGates_calibratedK`).  Every field of `TLegExit.LevelGates` —
including all eight of `TLegKill.CellGates` at the HALVED `η` — holds at the re-pinned
sequences `P_j = 2^{e_j}`, `Q_j = 2^{(j²M)e_j}`, `H_j = j²H₁`, `P₁ = 2^A`, for every level
`2 ≤ j ≤ Jb`, derived from `CalFrameK`'s twelve scalar gates alone.

The two MR conditions, at the K-exponent:

* `(3)` `8 log Q_{j−1} + 16 log j ≤ ((η/2)/j²)log P_j`: now `log Q_{j−1} =
  (j−1)²M·e_{j−1}log2`, so after `e_j = e_{j−1}Gj²` cancels the `j²` the residue is
  `8(j−1)²M + (the log j term) ≤ 24Jb²M ≤ (η/2)G` — `G_gateK`.
* `(2)` `loglog Q_j/(log P_{j−1} − 1) ≤ (η/2)/(4j²)`: `loglog Q_j =
  log(j²M·e_j·log2) ≤ log(Jb²M) + log e_{Jb}` is monotone up the ladder — `A_gate_logK`. -/
theorem levelGates_calibratedK {η H1 : ℝ} {A G M Jb Xd : ℕ}
    (hF : CalFrameK η H1 A G M Jb Xd) :
    ∀ j ∈ Finset.Icc 2 Jb,
      LevelGates (calP A G) (calQK A G M) (calH H1) η ((calP A G) 1) Xd j := by
  intro j hj
  rw [Finset.mem_Icc] at hj
  obtain ⟨hj2, hjJ⟩ := hj
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hmono := calE_mono A hF.one_le_G
  -- ⟦THE THREE RUNGS⟧ (verbatim from `SeamCalibration.levelGates_calibrated`)
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
  obtain ⟨hQfl, hPfl⟩ := calEK_floor_bounds hEpR
  obtain ⟨hQfl', hPfl'⟩ := calEK_floor_bounds hEjR
  -- ⟦THE WIDTH LADDER⟧ (verbatim: `calH` did not move)
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hpR : (1 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ j - 1 := by omega
    exact_mod_cast h
  have hpjR : ((j - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    have h : j - 1 ≤ j := by omega
    exact_mod_cast h
  have hH1 := hF.H1_two
  -- ⟦THE K-FACTORS⟧ the only genuinely new arithmetic
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hF.one_le_M
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by linarith
  have hjJR : (j : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hjJ
  have hjsq : (j : ℝ) ^ 2 ≤ (Jb : ℝ) ^ 2 := by nlinarith
  have hpsq : ((j - 1 : ℕ) : ℝ) ^ 2 ≤ (Jb : ℝ) ^ 2 := by nlinarith
  have hKj4 : (4 : ℝ) ≤ (j : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  have hKj1 : (1 : ℝ) ≤ (j : ℝ) ^ 2 * (M : ℝ) := by linarith
  have hKp1 : (1 : ℝ) ≤ ((j - 1 : ℕ) : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  have hKJb1 : (1 : ℝ) ≤ (Jb : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  have hKjJb : (j : ℝ) ^ 2 * (M : ℝ) ≤ (Jb : ℝ) ^ 2 * (M : ℝ) :=
    mul_le_mul_of_nonneg_right hjsq hM0
  have hKpJb : ((j - 1 : ℕ) : ℝ) ^ 2 * (M : ℝ) ≤ (Jb : ℝ) ^ 2 * (M : ℝ) :=
    mul_le_mul_of_nonneg_right hpsq hM0
  refine
    { cell := ?_, eta_lt6 := hη6, two_le_Hj := ?_, two_le_Hp := ?_, Hp_le_Hj := ?_,
      Hj_pin := ?_, logQj_ge := ?_, logPp_ge := ?_, logPj_ge := ?_, P1_le_Qp := ?_,
      one_le_P1 := ?_, Qj_le_Xd := ?_ }
  · -- ⟦MR's `(2)`/`(3)` AT THE HALVED `η`, AT THE K-EXPONENT⟧
    refine
      { eta_pos := by linarith, eta_lt := by linarith, two_le_j := hj2,
        one_lt_logP := ?_, logP_le_logQ := ?_, one_le_logQ := ?_, gate2 := ?_, gate3 := ?_ }
    · rw [log_calP]; linarith
    · rw [log_calP, log_calQK]; nlinarith
    · rw [log_calQK]; nlinarith
    · -- MR `(2)` at `loglog Q_j = log(j²M·e_j·log2)`
      rw [log_calQK, log_calP]
      have hden : (0 : ℝ) < ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 - 1 := by linarith
      rw [div_le_iff₀ hden, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (j : ℝ) ^ 2)]
      have hl20 : (0 : ℝ) < Real.log 2 := by linarith
      have hprod : (0 : ℝ) < (j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * Real.log 2 := by
        have : (0 : ℝ) < (j : ℝ) ^ 2 * (M : ℝ) := by linarith
        positivity
      have hKJbpos : (0 : ℝ) < (Jb : ℝ) ^ 2 * (M : ℝ) := by linarith
      have hEJbpos : (0 : ℝ) < ((calE A G Jb : ℕ) : ℝ) := by linarith
      have hle1 : (j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * Real.log 2
          ≤ (Jb : ℝ) ^ 2 * (M : ℝ) * ((calE A G Jb : ℕ) : ℝ) :=
        calc (j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * Real.log 2
            ≤ (j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = (j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) := by ring
          _ ≤ (Jb : ℝ) ^ 2 * (M : ℝ) * ((calE A G Jb : ℕ) : ℝ) :=
              mul_le_mul hKjJb hEjJR (by linarith) (by linarith)
      have hs1 : Real.log ((j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * Real.log 2)
          ≤ Real.log ((Jb : ℝ) ^ 2 * (M : ℝ) * ((calE A G Jb : ℕ) : ℝ)) :=
        Real.log_le_log hprod hle1
      have hs2 : Real.log ((Jb : ℝ) ^ 2 * (M : ℝ) * ((calE A G Jb : ℕ) : ℝ))
          = Real.log ((Jb : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE A G Jb : ℕ) : ℝ) :=
        Real.log_mul (ne_of_gt hKJbpos) (ne_of_gt hEJbpos)
      have hlogb : Real.log ((j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * Real.log 2)
          ≤ Real.log ((Jb : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE A G Jb : ℕ) : ℝ) := by
        linarith
      have hlogb0 : (0 : ℝ)
          ≤ Real.log ((Jb : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE A G Jb : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ Real.log ((Jb : ℝ) ^ 2 * (M : ℝ)) := Real.log_nonneg hKJb1
        have h2 : (0 : ℝ) ≤ Real.log ((calE A G Jb : ℕ) : ℝ) :=
          Real.log_nonneg (by linarith)
        linarith
      have hJb1R : (1 : ℝ) ≤ (Jb : ℝ) := by linarith
      have hsq : 4 * (j : ℝ) ^ 2 ≤ 4 * (Jb : ℝ) ^ 2 := by nlinarith
      have hmul : Real.log ((j : ℝ) ^ 2 * (M : ℝ) * ((calE A G j : ℕ) : ℝ) * Real.log 2)
            * (4 * (j : ℝ) ^ 2)
          ≤ (Real.log ((Jb : ℝ) ^ 2 * (M : ℝ)) + Real.log ((calE A G Jb : ℕ) : ℝ))
            * (4 * (Jb : ℝ) ^ 2) :=
        mul_le_mul hlogb hsq (by positivity) hlogb0
      have hstep : (A : ℝ) * Real.log 2 ≤ ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hAER (by linarith)
      have hfin : (η / 2) * ((A : ℝ) * Real.log 2 - 1)
          ≤ (η / 2) * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith [hF.A_gate_logK]
    · -- MR `(3)` at `log Q_{j−1} = (j−1)²M·e_{j−1}log2`
      rw [log_calQK, log_calP]
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
      have hElog0 : (0 : ℝ) ≤ ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 := by linarith
      have hGb : 32 * ((Jb : ℝ) ^ 2 * (M : ℝ)) ≤ η / 2 * (G : ℝ) := by
        linarith [hF.G_gateK]
      have hmulG : 32 * ((Jb : ℝ) ^ 2 * (M : ℝ))
            * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2)
          ≤ (η / 2 * (G : ℝ)) * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right hGb hElog0
      have hA1 : 8 * (((j - 1 : ℕ) : ℝ) ^ 2 * (M : ℝ))
            * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2)
          ≤ 8 * ((Jb : ℝ) ^ 2 * (M : ℝ))
            * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2) := by
        nlinarith
      have hlogj : Real.log (j : ℝ) ≤ (j : ℝ) := by
        have := Real.log_le_sub_one_of_pos hj0; linarith
      have hjA : (j : ℝ) ≤ (A : ℝ) / 2 := by linarith [hF.A_gate_lin]
      have hhalf : ((calE A G (j - 1) : ℕ) : ℝ) * (1 / 2)
          ≤ ((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have hA2 : 16 * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2)
          ≤ 16 * ((Jb : ℝ) ^ 2 * (M : ℝ))
            * (((calE A G (j - 1) : ℕ) : ℝ) * Real.log 2) := by
        nlinarith
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
  · rw [log_calQK]; nlinarith
  · rw [log_calP]; linarith
  · rw [log_calP]; linarith
  · have h : calP A G 1 ≤ calQK A G M (j - 1) := by
      simp only [calP, calQK, calE_one]
      refine Nat.pow_le_pow_right (by norm_num) ?_
      refine le_trans hEp ?_
      exact Nat.le_mul_of_pos_left _
        (Nat.mul_pos (Nat.pow_pos (by omega)) hF.one_le_M)
    exact_mod_cast h
  · exact Nat.one_le_two_pow
  · exact le_trans (calQK_mono A hF.one_le_G hjJ) hF.Q_le_Xd

/-! ## §3 — the K-calibration is INHABITED (and K-3: the better `H₁`) -/

/-- **NO VACUITY, AND THE BETTER WIDTH** (`calFrameK_satisfiable`).  A genuine inhabitant of
`CalFrameK`: `η = 1/12`, `H₁ = P₁^{1/6}`, `A = 65536`, `G = 2457600`, `M = 800`, `Jb = 2`,
`X_d = Q_{Jb}`.

Three things are being certified at once.

* **The K-gate closes.**  `G_gateK` is `64·(2²·800) = 204800 ≤ (1/12)·2457600 = 204800`
  — EXACT, so `G = 768·Jb²M` is the smallest admissible base at this `η`, exactly as
  `G = 768` was in the landed frame at `M = Jb = 1`.  The re-pin's whole cost to the ladder
  is this one linear factor.
* **The anchor pays only a logarithm.**  `A_gate_logK` is
  `16(log 3200 + log e₂) ≤ (1/24)(65536 log 2 − 1)`, certified at `16(9 + 28) = 592 ≤ 1892`
  (`e₂ = 65536·2457600·4 = 644245094400 ≤ 2^{40}`, `3200 ≤ 2^{12}`).  Room to spare: the
  gate would still close at `M` up to about `e^{48}`.
* **⟦V9b⟧ finding (iii), repaired** (K-3).  The landed inhabitant took `H₁ = 2`, which leaves
  Lemma 12's window row at `≈ 480(T/X_d+1)·2e²/H_j = O(1)` per level.  `CalFrame.H1_pin`
  permits `H₁` up to `P₁^{1/6}`, and that is what is taken here — `H1_pin` holds with
  EQUALITY (`(P₁^{1/6})³ = P₁^{1/2}`), and `H1_two` holds because `P₁ ≥ 64`.

`P₁ = 2^{65536}` is never evaluated: it stays the symbol `calP 65536 2457600 1` throughout,
and `X_d = calQK 65536 2457600 800 2` stays a symbol as well. -/
theorem calFrameK_satisfiable :
    CalFrameK (1 / 12) (((calP 65536 2457600 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      65536 2457600 800 2 (calQK 65536 2457600 800 2) := by
  -- `P₁ ≥ 64`, symbolically (the exponent is never expanded)
  have h64 : (64 : ℕ) ≤ calP 65536 2457600 1 := by
    have hE : (6 : ℕ) ≤ calE 65536 2457600 1 := by rw [calE_one]; norm_num
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP 65536 2457600 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP 65536 2457600 1 : ℕ) : ℝ) := by linarith
  -- `e₂`, and its logarithm
  have hval : calE 65536 2457600 2 = 644245094400 := by
    norm_num [calE, Nat.factorial]
  have hEpos : (0 : ℝ) < ((calE 65536 2457600 2 : ℕ) : ℝ) := by
    rw [hval]; norm_num
  have hlogE : Real.log ((calE 65536 2457600 2 : ℕ) : ℝ) ≤ 28 := by
    have hle : ((calE 65536 2457600 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (40 : ℕ) := by
      rw [hval]; norm_num
    calc Real.log ((calE 65536 2457600 2 : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (40 : ℕ)) :=
          Real.log_le_log hEpos hle
      _ = 40 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 28 := by linarith [Real.log_two_lt_d9]
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by norm_num, one_le_M := by norm_num, G_gateK := by norm_num,
      A_gate_lin := by norm_num, A_gate_logK := ?_, A_floor := by norm_num,
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · -- `A_gate_logK`: `16(log 3200 + log e₂) ≤ (1/24)(65536 log 2 − 1)`
    have hlogK : Real.log ((2 : ℝ) ^ 2 * 800) ≤ 9 := by
      have hc : (2 : ℝ) ^ 2 * 800 = 3200 := by norm_num
      rw [hc]
      calc Real.log (3200 : ℝ) ≤ Real.log ((2 : ℝ) ^ (12 : ℕ)) :=
            Real.log_le_log (by norm_num) (by norm_num)
        _ = 12 * Real.log 2 := by rw [Real.log_pow]; norm_num
        _ ≤ 9 := by linarith [Real.log_two_lt_d9]
    push_cast
    refine le_trans (mul_le_mul_of_nonneg_left (add_le_add hlogK hlogE) (by norm_num)) ?_
    linarith [Real.log_two_gt_d9]
  · -- `H1_two`: `2 = 64^{1/6} ≤ P₁^{1/6}`
    calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP 65536 2457600 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · -- `H1_pin`: `(P₁^{1/6})³ = P₁^{1/2}` — equality, the largest width the frame allows
    have hid : (((calP 65536 2457600 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ)
        = ((calP 65536 2457600 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP 65536 2457600 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-- **The K-calibrated blocks carry points.**  `K_j ≥ 1` makes `I_j = [⌊H_j log P_j⌋,
⌊H_j log Q_j⌋]` nonempty at every level — the `(v,r)`-sums `Ej_bound` prices are not sums
over `∅`. -/
lemma calibrated_block_nonemptyK {H1 : ℝ} {A G M j : ℕ} (hH1 : 0 ≤ H1) (hM : 1 ≤ M)
    (hj : 1 ≤ j) :
    (ramI (calH H1 j) (calP A G j) (calQK A G M j)).Nonempty := by
  rw [ramI, Finset.nonempty_Icc]
  refine Nat.floor_le_floor ?_
  rw [log_calP, log_calQK]
  have h0 : (0 : ℝ) ≤ calH H1 j := by simp only [calH]; positivity
  have hE : (0 : ℝ) ≤ ((calE A G j : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hK : (1 : ℝ) ≤ (j : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg h0 hE) hl2]

/-- **THE CORRESPONDENCE AT THE K-LADDER** (`ladder_below_stationK`).  The re-pin does not
move the ladder into the §8.3 window: `Q_j < P₈₃ X θ₂₉₃` for every `j ≤ Jb`, from MR's own
cutoff and `θ₂₉₃ < 1/2` (`USetPins.pin_Pii`, exactly as in `SeamCalibration`). -/
theorem ladder_below_stationK {A G M Jb : ℕ} {X : ℝ} (hG : 1 ≤ G) (hX : 1 < Real.log X)
    (hJdef : ((calQK A G M Jb : ℕ) : ℝ) ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2))) :
    ∀ j : ℕ, j ≤ Jb → ((calQK A G M j : ℕ) : ℝ) < P83 X theta293 :=
  pin_Pii X theta293 (calQK A G M) Jb Jb theta293_lt_half hX hJdef
    (fun _ _ hij => calQK_mono A hG hij) le_rfl

/-! ## §4 — THE NUMBER: `Σ_j log P_j/log Q_j` at the K-ladder, and the eq-(28) demand -/

/-- **THE RATIO AT THE K-LADDER IS `1/(j²M)`, EXACTLY, AT EVERY LEVEL** — MR (4)'s own shape
(`log P_j/log Q_j = log P₁/(j² log Q₁)`), with `1/M` in the role of `log P₁/log Q₁`.
Contrast `TypicalPrice.log_calP_div_log_calQ`, which is the constant `1/2`. -/
theorem log_calP_div_log_calQK {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) {j : ℕ}
    (hj : 1 ≤ j) :
    Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
      = 1 / ((j : ℝ) ^ 2 * (M : ℝ)) := by
  have hE : 0 < calE A G j := by
    rw [calE]
    exact Nat.mul_pos (Nat.mul_pos hA (pow_pos hG (j - 1)))
      (pow_pos (Nat.factorial_pos j) 2)
  have hER : (0 : ℝ) < ((calE A G j : ℕ) : ℝ) := by exact_mod_cast hE
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hK : (0 : ℝ) < (j : ℝ) ^ 2 * (M : ℝ) := by nlinarith
  rw [log_calP, log_calQK]
  field_simp

/-- `Σ_{j=1}^{Jb} j^{−2} ≤ 2`, uniformly in the cutoff (mathlib's `sum_Ioo_inv_sq_le`; the
true value is `π²/6 = 1.6449…`, which is not needed — the demand below is checked against
the `2`). -/
private lemma sum_invsq_Icc_le_two (Jb : ℕ) :
    ∑ j ∈ Finset.Icc 1 Jb, ((j : ℝ) ^ 2)⁻¹ ≤ 2 := by
  have hset : Finset.Ioo 0 (Jb + 1) = Finset.Icc 1 Jb := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  have h := sum_Ioo_inv_sq_le (α := ℝ) 0 (Jb + 1)
  rw [hset] at h
  simpa using h

/-- **THE `j`-COLLECTION IS `≤ 2/M` — THE NUMBER THE SEAM ROW NEEDS** (`sum_ratioK_le`).
The `j²`-decay MR's eq (28) demands is restored by the re-pin, and the bound is UNIFORM in
the cutoff `Jb` — the exact failure `TypicalPrice.sum_calibrated_ratio_eq` (`= Jb/2`) and
`calibrated_ratio_not_MR_shape` diagnosed. -/
theorem sum_ratioK_le {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (Jb : ℕ) :
    ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
      ≤ 2 / (M : ℝ) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcongr : ∀ j ∈ Finset.Icc 1 Jb,
      Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
        = (M : ℝ)⁻¹ * ((j : ℝ) ^ 2)⁻¹ := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [log_calP_div_log_calQK hA hG hM hj.1]
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
    field_simp
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  have hstep : (M : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 Jb, ((j : ℝ) ^ 2)⁻¹ ≤ (M : ℝ)⁻¹ * 2 :=
    mul_le_mul_of_nonneg_left (sum_invsq_Icc_le_two Jb) (by positivity)
  calc (M : ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 Jb, ((j : ℝ) ^ 2)⁻¹ ≤ (M : ℝ)⁻¹ * 2 := hstep
    _ = 2 / (M : ℝ) := by field_simp

/-- **THE DEMAND SIDE, RUN** (`eq28_clears_of_M`).  MR p.31's small-`h` accounting is
`(28) ≤ δ/50 + (2 + 1/50)·Σ_j log P_j/log Q_j`, and Theorem 1 needs that `≤ δ`
(`docs/sources/mr_extract.md` §6.4).  At the K-ladder this is a theorem about the re-pin
scale: `M ≥ 8/δ` suffices, because `Σ_j ≤ 2/M ≤ δ/4` and `1/50 + (2 + 1/50)/4 = 0.525 ≤ 1`.

This is the gate the landed calibration CANNOT meet at any `Jb` (`TypicalPrice`'s
`calibrated_sum_ratio_ge_half`: the sum is `≥ 1/2` there, so the accounting returns `≈ 1.02`,
which exceeds `δ` for every `δ < 1`).  MR's own scale is `M = 4/δ`; the factor `2` here is
the price of `Σ j^{−2} ≤ 2` in place of `π²/6 = 1.6449…`, and it is paid in `M`. -/
theorem eq28_clears_of_M {A G M : ℕ} (hA : 1 ≤ A) (hG : 1 ≤ G) (hM : 1 ≤ M) (Jb : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hMδ : 8 / δ ≤ (M : ℝ)) :
    δ / 50 + (2 + 1 / 50) * ∑ j ∈ Finset.Icc 1 Jb,
        Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ)
      ≤ δ := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hsum := sum_ratioK_le hA hG hM Jb
  have hMδ' : (8 : ℝ) ≤ (M : ℝ) * δ := by
    rw [div_le_iff₀ hδ] at hMδ; linarith
  have h2M : 2 / (M : ℝ) ≤ δ / 4 := by
    rw [div_le_div_iff₀ hM0 (by norm_num)]
    linarith
  linarith

/-- **THE DEMAND, AT THE PIN TAKEN** (`sum_ratioK_pinned_clears`).  `calFrameK_satisfiable`'s
own numerals — `A = 65536`, `G = 2457600`, `M = 800` — run against MR eq (28) at `δ = 1/100`
(`M = 8/δ`).  The TYPDEN lesson: the inhabitant's `M` slot is checked here, not assumed. -/
theorem sum_ratioK_pinned_clears (Jb : ℕ) :
    (1 : ℝ) / 100 / 50
        + (2 + 1 / 50) * ∑ j ∈ Finset.Icc 1 Jb,
            Real.log ((calP 65536 2457600 j : ℕ) : ℝ)
              / Real.log ((calQK 65536 2457600 800 j : ℕ) : ℝ)
      ≤ 1 / 100 :=
  eq28_clears_of_M (by norm_num) (by norm_num) (by norm_num) Jb (by norm_num) (by norm_num)

/-! ## §5 — K-2: the `p²` row by the DIRECT route -/

/-- **The windowed cofactor count** (`TypicalPrice`'s private helper, re-derived verbatim:
the corpus copy is not exported).  Cofactors `m` with `p ∣ m`, `m ≥ 1`, `pm ≤ 2X_d` inject
into `[1, 2X_d/p²]` via `m ↦ m/p`. -/
private lemma card_dvd_window_leK {p Xd : ℕ} (hp : 0 < p) (S : Finset ℕ)
    (hS : ∀ m ∈ S, p ∣ m ∧ 1 ≤ m ∧ p * m ≤ 2 * Xd) :
    (S.card : ℝ) ≤ 2 * (Xd : ℝ) / (p : ℝ) ^ 2 := by
  classical
  have hcard : S.card ≤ (Finset.Icc 1 (2 * Xd / (p * p))).card := by
    refine Finset.card_le_card_of_injOn (fun m => m / p) ?_ ?_
    · intro m hm
      obtain ⟨hdvd, hm1, hpm⟩ := hS m hm
      obtain ⟨k, hk⟩ := hdvd
      have hk0 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · rw [h0, Nat.mul_zero] at hk; omega
        · exact h0
      have hkdiv : m / p = k := by rw [hk]; exact Nat.mul_div_cancel_left k hp
      have hkle : k ≤ 2 * Xd / (p * p) := by
        rw [Nat.le_div_iff_mul_le (by positivity)]
        calc k * (p * p) = p * (p * k) := by ring
          _ = p * m := by rw [hk]
          _ ≤ 2 * Xd := hpm
      simp only [Finset.coe_Icc, Set.mem_Icc, hkdiv]
      exact ⟨hk0, hkle⟩
    · intro m₁ hm₁ m₂ hm₂ heq
      have h1 : m₁ / p * p = m₁ := Nat.div_mul_cancel (hS m₁ hm₁).1
      have h2 : m₂ / p * p = m₂ := Nat.div_mul_cancel (hS m₂ hm₂).1
      have h3 : m₁ / p = m₂ / p := heq
      rw [← h1, ← h2, h3]
  have hIcc : (Finset.Icc 1 (2 * Xd / (p * p))).card = 2 * Xd / (p * p) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  rw [hIcc] at hcard
  have hstep : (((2 * Xd / (p * p) : ℕ)) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hcast : ((2 * Xd : ℕ) : ℝ) / ((p * p : ℕ) : ℝ) = 2 * (Xd : ℝ) / (p : ℝ) ^ 2 := by
    push_cast; ring
  have hleft : (S.card : ℝ) ≤ (((2 * Xd / (p * p) : ℕ)) : ℝ) := by exact_mod_cast hcard
  rw [hcast] at hstep
  linarith

/-- **The windowed inner row** `Σ_m winTerm ≤ 4/p²` (`TypicalPrice`'s private helper,
re-derived verbatim). -/
private lemma winTerm_inner_row_leK {p Xd : ℕ} (hp : 0 < p) (hXd : 1 ≤ Xd) (S : Finset ℕ)
    (hS : ∀ m ∈ S, p ∣ m ∧ 1 ≤ m) :
    ∑ m ∈ S, winTerm Xd p m ≤ 4 / (p : ℝ) ^ 2 := by
  classical
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsplit : ∑ m ∈ S, winTerm Xd p m
      = ∑ m ∈ S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd), 2 / ((p * m : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun m _ => rfl)
  rw [hsplit]
  have hterm : ∀ m ∈ S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd),
      2 / ((p * m : ℕ) : ℝ) ≤ 2 / (Xd : ℝ) := by
    intro m hm
    rw [Finset.mem_filter] at hm
    have hlo : (Xd : ℝ) ≤ ((p * m : ℕ) : ℝ) := by exact_mod_cast hm.2.1
    exact div_le_div_of_nonneg_left (by norm_num) hXd0 hlo
  have hbound := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hbound
  refine hbound.trans ?_
  have hc : ((S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd)).card : ℝ)
      ≤ 2 * (Xd : ℝ) / (p : ℝ) ^ 2 := by
    refine card_dvd_window_leK hp _ (fun m hm => ?_)
    rw [Finset.mem_filter] at hm
    exact ⟨(hS m hm.1).1, (hS m hm.1).2, hm.2.2⟩
  have hmul : ((S.filter (fun m => Xd ≤ p * m ∧ p * m ≤ 2 * Xd)).card : ℝ) * (2 / (Xd : ℝ))
      ≤ (2 * (Xd : ℝ) / (p : ℝ) ^ 2) * (2 / (Xd : ℝ)) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  refine hmul.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The whole windowed `p²` domain sum** `Σ_{σ ∈ ramP2dom} winTerm ≤ 8/P`
(`TypicalPrice`'s private helper, re-derived verbatim). -/
private lemma winTerm_dom_sum_leK (N P Q Xd : ℕ) (hXd : 1 ≤ Xd) (hP : 1 ≤ P) :
    ∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2 ≤ 8 / (P : ℝ) := by
  classical
  rw [ramP2dom, Finset.sum_sigma]
  have hrow : ∀ p ∈ (Finset.Icc P Q).filter Nat.Prime,
      ∑ m ∈ ((((Finset.Icc 1 N).image (fun n => n / p)).filter
          (fun m => p * m ∈ Finset.Icc 1 N)).filter (fun m => p ∣ m)),
          winTerm Xd p m ≤ 4 / (p : ℝ) ^ 2 := by
    intro p hp
    rw [Finset.mem_filter] at hp
    refine winTerm_inner_row_leK hp.2.pos hXd _ (fun m hm => ?_)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hm
    refine ⟨hm.2, ?_⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; rw [h0, Nat.mul_zero] at hm; omega
    · exact h0
  refine (Finset.sum_le_sum hrow).trans ?_
  have hsub : ∑ p ∈ (Finset.Icc P Q).filter Nat.Prime, 4 / (p : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  refine hsub.trans ?_
  have heq : ∑ n ∈ Finset.Icc P Q, 4 / (n : ℝ) ^ 2
      = 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun n _ => by ring)
  rw [heq]
  have htail := sum_inv_sq_tail_le hP Q
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  calc 4 * ∑ n ∈ Finset.Icc P Q, 1 / (n : ℝ) ^ 2 ≤ 4 * (2 / (P : ℝ)) := by linarith
    _ = 8 / (P : ℝ) := by ring

/-- **`Σ_n ‖coeff_n‖/n ≤ 8/P`** — the FIRST factor of the direct route (`Σf² ≤ (max f)(Σf)`).
This is `TypicalPrice.ramP2mass_win_le`'s own `hsum`, stopped one step before the lossy
Cauchy–Schwarz `Σf² ≤ (Σf)²`. -/
private lemma ramP2coeff_sum_div_le (N P Q Xd : ℕ) (hXd : 1 ≤ Xd) (hP : 1 ≤ P)
    (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ / (n : ℝ) ≤ 8 / (P : ℝ) := by
  classical
  have hmaps : ∀ σ ∈ ramP2dom N P Q, σ.1 * σ.2 ∈ Finset.Icc 1 N := by
    intro σ hσ
    rw [ramP2dom] at hσ
    obtain ⟨-, h2⟩ := Finset.mem_sigma.mp hσ
    obtain ⟨h3, -⟩ := Finset.mem_filter.mp h2
    exact (Finset.mem_filter.mp h3).2
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeff N P Q a b c n‖ / (n : ℝ)
        ≤ ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
            winTerm Xd σ.1 σ.2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
    have heq : (∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n), winTerm Xd σ.1 σ.2)
        = (∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
            (if (Xd ≤ σ.1 * σ.2 ∧ σ.1 * σ.2 ≤ 2 * Xd) then (2 : ℝ) else 0)) / (n : ℝ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [Finset.mem_filter] at hσ
      rw [winTerm, hσ.2]
      split_ifs <;> simp
    rw [heq, div_le_div_iff_of_pos_right hn0, ramP2coeff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ hσ => ?_))
    obtain ⟨hσdom, -⟩ := Finset.mem_filter.mp hσ
    rw [ramP2dom] at hσdom
    obtain ⟨hσp, -⟩ := Finset.mem_sigma.mp hσdom
    obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hσp
    obtain ⟨hPle, hleQ⟩ := Finset.mem_Icc.mp hIcc
    exact ramP2_term_norm_le_win ha hb hc hasupp hwin hprime hPle hleQ σ.2
  have hfiber : (∑ n ∈ Finset.Icc 1 N,
        ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n), winTerm Xd σ.1 σ.2)
      = ∑ σ ∈ ramP2dom N P Q, winTerm Xd σ.1 σ.2 :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  refine le_trans ?_ (winTerm_dom_sum_leK N P Q Xd hXd hP)
  rw [← hfiber]
  exact Finset.sum_le_sum hpt

/-- **The fiber of `ramP2dom` over `n` injects into `n`'s prime divisors.**  A pair `(p,m)`
with `pm = n` is determined by `p`, and `p` is a prime divisor of `n`; hence the fiber
count is at most `ω(n)`. -/
private lemma fiber_card_le_omega {N P Q n : ℕ} (hn : n ≠ 0) :
    ((ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n)).card ≤ n.primeFactors.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun σ => σ.1) ?_ ?_
  · intro σ hσ
    obtain ⟨hdom, heq⟩ := Finset.mem_filter.mp hσ
    rw [ramP2dom] at hdom
    obtain ⟨hp, -⟩ := Finset.mem_sigma.mp hdom
    exact Nat.mem_primeFactors.mpr
      ⟨(Finset.mem_filter.mp hp).2, ⟨σ.2, heq.symm⟩, hn⟩
  · intro σ hσ τ hτ heq
    obtain ⟨hdom, hσn⟩ := Finset.mem_filter.mp hσ
    obtain ⟨-, hτn⟩ := Finset.mem_filter.mp hτ
    have hp : σ.1.Prime := by
      rw [ramP2dom] at hdom
      obtain ⟨hp1, -⟩ := Finset.mem_sigma.mp hdom
      exact (Finset.mem_filter.mp hp1).2
    have heq' : σ.1 = τ.1 := heq
    have hmul : σ.1 * σ.2 = σ.1 * τ.2 := by rw [hσn, heq', hτn]
    exact Sigma.ext heq' (heq_of_eq (Nat.eq_of_mul_eq_mul_left hp.pos hmul))

/-- **`ω(n) ≤ log₂ n`**, from `2^{ω(n)} ≤ ∏_{p ∣ n} p ≤ n`
(`Finset.pow_card_le_prod` + `Nat.prod_primeFactors_dvd`). -/
private lemma omega_mul_log_two_le {n : ℕ} (hn : 1 ≤ n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  have hpow : 2 ^ n.primeFactors.card ≤ n :=
    le_trans (Finset.pow_card_le_prod _ _ _
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le))
      (Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n))
  have hR : (2 : ℝ) ^ n.primeFactors.card ≤ (n : ℝ) := by exact_mod_cast hpow
  have h1 : Real.log ((2 : ℝ) ^ n.primeFactors.card) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hR
  rwa [Real.log_pow] at h1

/-- **The maximum of `‖coeff_n‖/n`** — the SECOND factor of the direct route.  Off the window
`[X_d, 2X_d]` the coefficient vanishes; on it the fiber sum is `≤ 2·ω(n)` and `n ≥ X_d`,
while `2^{ω(n)} ≤ n ≤ 2X_d` caps `ω(n)` by `log₂(2X_d)`. -/
private lemma ramP2coeff_norm_div_le {N P Q Xd : ℕ} (hXd : 1 ≤ Xd) {n : ℕ} (hn : 1 ≤ n)
    {a b c : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd) :
    ‖ramP2coeff N P Q a b c n‖ / (n : ℝ)
      ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ) := by
  classical
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ) := by positivity
  -- the fiber bound, in the indicator shape
  have hstep : ‖ramP2coeff N P Q a b c n‖
      ≤ ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
          (if (Xd ≤ σ.1 * σ.2 ∧ σ.1 * σ.2 ≤ 2 * Xd) then (2 : ℝ) else 0) := by
    rw [ramP2coeff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun σ hσ => ?_))
    obtain ⟨hσdom, -⟩ := Finset.mem_filter.mp hσ
    rw [ramP2dom] at hσdom
    obtain ⟨hσp, -⟩ := Finset.mem_sigma.mp hσdom
    obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hσp
    obtain ⟨hPle, hleQ⟩ := Finset.mem_Icc.mp hIcc
    exact ramP2_term_norm_le_win ha hb hc hasupp hwin hprime hPle hleQ σ.2
  by_cases hmem : Xd ≤ n ∧ n ≤ 2 * Xd
  · -- ⟦ON THE WINDOW⟧ `‖coeff n‖ ≤ 2ω(n) ≤ 2 log₂(2X_d)` and `n ≥ X_d`
    have hcap : ∑ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
          (if (Xd ≤ σ.1 * σ.2 ∧ σ.1 * σ.2 ≤ 2 * Xd) then (2 : ℝ) else 0)
        ≤ 2 * (((ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) := by
      have h := Finset.sum_le_sum (f := fun σ : Σ _ : ℕ, ℕ =>
          if (Xd ≤ σ.1 * σ.2 ∧ σ.1 * σ.2 ≤ 2 * Xd) then (2 : ℝ) else 0)
        (g := fun _ : Σ _ : ℕ, ℕ => (2 : ℝ))
        (s := (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n))
        (fun σ _ => by split_ifs <;> norm_num)
      rw [Finset.sum_const, nsmul_eq_mul] at h
      linarith
    have hcard : (((ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ)
        ≤ (n.primeFactors.card : ℝ) := by
      exact_mod_cast fiber_card_le_omega (P := P) (Q := Q) (N := N) (by omega)
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hnle : (n : ℝ) ≤ 2 * (Xd : ℝ) := by
      have : (n : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by exact_mod_cast hmem.2
      push_cast at this; linarith
    have homega : (n.primeFactors.card : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) := by
      rw [Real.logb, le_div_iff₀ hl2]
      refine le_trans (omega_mul_log_two_le hn) ?_
      exact Real.log_le_log hn0 hnle
    have hnXd : (Xd : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmem.1
    rw [div_le_iff₀ hn0]
    calc ‖ramP2coeff N P Q a b c n‖
        ≤ 2 * (((ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n)).card : ℝ) :=
          le_trans hstep hcap
      _ ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) := by linarith
      _ = 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ) * (Xd : ℝ) := by field_simp
      _ ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hnXd hB0
  · -- ⟦OFF THE WINDOW⟧ every fiber term is `0`
    have hzero : ∀ σ ∈ (ramP2dom N P Q).filter (fun σ => σ.1 * σ.2 = n),
        (if (Xd ≤ σ.1 * σ.2 ∧ σ.1 * σ.2 ≤ 2 * Xd) then (2 : ℝ) else 0) = 0 := by
      intro σ hσ
      rw [(Finset.mem_filter.mp hσ).2, if_neg hmem]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hstep
    have hz : ‖ramP2coeff N P Q a b c n‖ = 0 := le_antisymm hstep (norm_nonneg _)
    rw [hz, zero_div]
    exact hB0

/-- **K-2 — THE `p²` ROW AT MR's GRADE** (`ramP2mass_direct`), ⟦V9b⟧ finding (ii) repaired.

`TypicalPrice.ramP2mass_win_le` prices this row through `Σf² ≤ (Σf)²`, which returns
`64/P²`.  Against `lemma12Rows`' prefactor `2T + 20N ≍ X_d(T/X_d+1)` that is
`64X_d/P_j²·(T/X_d+1)`, and `CalFrame.Q_le_Xd` forces `X_d ≥ Q_{Jb} ≥ Q_j ≥ P_j²` at the
landed calibration — so EVERY level's `p²` row is `≥ 64`.  Not small; not MR's `(T/X+1)/P`.

The loss is exactly the Cauchy–Schwarz step.  The direct route keeps the sup:

  `Σ_n f_n² ≤ (max_n f_n)(Σ_n f_n)`,  `f_n := ‖coeff_n‖/n`,

with `max_n f_n ≤ 2ω(n)/X_d ≤ 2log₂(2X_d)/X_d` (`ramP2coeff_norm_div_le`, via
`2^{ω(n)} ≤ n ≤ 2X_d`) and `Σ_n f_n ≤ 8/P` (`ramP2coeff_sum_div_le`, the same `winTerm`
ledger `ramP2mass_win_le` uses).  The product is `16·log₂(2X_d)/(X_d·P)`, which against the
prefactor is `7680·log₂(2X_d)/P·(T/X_d+1)` — MR's own `1/P` grade, with only a logarithm
lost, in place of a row that was `≥ 64` at every level.

Every hypothesis is `ramP2mass_win_le`'s own; nothing new is assumed. -/
theorem ramP2mass_direct (N P Q Xd : ℕ) (hXd : 1 ≤ Xd) (hP : 1 ≤ P) (a b c : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖b n‖ ≤ 1) (hc : ∀ n, ‖c n‖ ≤ 1)
    (hasupp : ∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd)
    (hwin : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → c p * b m ≠ 0 →
      Xd ≤ p * m ∧ p * m ≤ 2 * Xd) :
    ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) := by
  classical
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hL0 : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hB0 : (0 : ℝ) ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ) := by positivity
  -- `Σ f² ≤ (max f)·(Σ f)`, pointwise
  have hsq : ∀ n ∈ Finset.Icc 1 N,
      ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ)
            * (‖ramP2coeff N P Q a b c n‖ / (n : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hmax := ramP2coeff_norm_div_le (N := N) (P := P) (Q := Q) hXd hn.1 ha hb hc
      hasupp hwin
    have hnn : (0 : ℝ) ≤ ‖ramP2coeff N P Q a b c n‖ / (n : ℝ) := by positivity
    calc ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
        = (‖ramP2coeff N P Q a b c n‖ / (n : ℝ))
            * (‖ramP2coeff N P Q a b c n‖ / (n : ℝ)) := by
          rw [← div_pow]; ring
      _ ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ)
            * (‖ramP2coeff N P Q a b c n‖ / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hmax hnn
  refine (Finset.sum_le_sum hsq).trans ?_
  rw [← Finset.mul_sum]
  have hrow := ramP2coeff_sum_div_le N P Q Xd hXd hP a b c ha hb hc hasupp hwin
  calc 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ)
        * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ / (n : ℝ)
      ≤ 2 * Real.logb 2 (2 * (Xd : ℝ)) / (Xd : ℝ) * (8 / (P : ℝ)) :=
        mul_le_mul_of_nonneg_left hrow hB0
    _ = 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((Xd : ℝ) * (P : ℝ)) := by
        field_simp
        ring

/-! ## §6 — K-4: THE SEAM ROW AT THE K-LADDER, AND ITS DENSITY COLLECTION AS A NUMBER -/

set_option maxHeartbeats 1000000 in
-- `SeamCalibration.seam_row_calibrated`'s 23 ladder-reads, re-run at `Q_j = P_j^{j²M}`; the
-- predicate-blind stones (`hUG34_unconditional`, `TLeg_feeds_capstone`) are cited verbatim
/-- **THE SEAM ROW, CLOSED AT THE K-LADDER** (`seam_row_calibratedK`).

`SeamCalibration.seam_row_calibrated` re-derived at the re-pinned family — same two halves
(`GradedCapstone.hUG34_unconditional` and `TLegExit.TLeg_bound`), same composition, same
absence of an integral on the right and of any ladder hypothesis, but now at a ladder whose
`Σ_j log P_j/log Q_j` MEETS MR eq (28) (`sum_ratioK_le`, `eq28_clears_of_M`).

**The ladder-reads that move** (all discharged from `CalFrameK` alone): `1 < Q_{Jb}`,
`P_{Jb} ≤ Q_{Jb}`, `Q_{Jb} ≤ Tann`, the `VJ`-family, `Q_1 ≤ X_d`, level 1's `P₁ ≤ Q₁`, and
`LevelGates` at every level (`levelGates_calibratedK`) — each now carrying the factor
`K_j = j²M ≥ 1`, which is exactly what `CalFrameK.one_le_M` supplies.  The reads that do NOT
move are the `P`-side and width ones (`3 ≤ P_{Jb}`, `2 ≤ H_{Jb}`, `0 ≤ α_{Jb}`,
`α_{Jb} ≤ 1/4 − η`, `2η ≤ 1`, `1 ≤ Jb`, `Jb ≤ Jset`), since `calP` and `calH` did not move.

**The surviving frame** is `SeamCalibration.seam_row_calibrated`'s verbatim with `CalFrame`
replaced by `CalFrameK` and every `calQ A G` replaced by `calQK A G M`.  Nothing else. -/
theorem seam_row_calibratedK :
    ∃ Cq cq T₀ Ccol X₀ Cs : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q A G M Jb : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S : ℝ),
        -- ⟦THE K-STATION FRAME⟧ the twelve scalar gates, in place of every ladder hypothesis
        CalFrameK η H1 A G M Jb Xd →
        2 ≤ H83 X theta293 →
        0 < X → Real.exp 1 ≤ X → Real.exp 1 ≤ Real.log X → 4 ≤ Real.log X →
        Real.exp 2 ≤ Real.log X →
        TannGate X Tann → 1 < Tann → Tann ≤ X →
        -- MR §2's cutoff, at the re-pinned ladder
        Real.log ((calQK A G M Jb : ℕ) : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) →
        T₀ ≤ Tann → 5 ≤ Real.log (Real.log Tann) → 1 ≤ Real.log Tann →
        Real.log Tann ≤ L → Real.exp 1 ≤ L →
        -- the `VJ`-family, collapsed to its worst corner
        Real.exp (mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          thinBundleG Tann VJ (calH H1 Jb) (calP A G Jb) (calQK A G M Jb)
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
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
          c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (2 * (calH H1 1 * Real.log ((calQK A G M 1 : ℕ) : ℝ) + 1)
                  * (Tann * ((calQK A G M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1)
                  * ((calP A G 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha η 1))
                  * (4 * (calH H1 1 / (1 - 2 * mrAlpha η 1))
                        * Real.exp ((1 - 2 * mrAlpha η 1) / calH H1 1)
                      + 60 * (calH H1 1 / mrAlpha η 1)
                          * Real.exp (4 * mrAlpha η 1 / calH H1 1))
                + 1536 * Cs * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240)
                    * (1 / ((calP A G 1 : ℕ) : ℝ))
                + ∑ j ∈ Finset.Icc 1 Jb,
                    lemma12Rows N Xd (calP A G j) (calQK A G M j) (calH H1 j) Tann a b c)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨Cq, cq, T₀, Ccol, X₀, hCq, hcq, hT₀, hX₀0, hcap⟩ := hUG34_unconditional
  obtain ⟨Cs, hCs, hfeed⟩ := TLeg_feeds_capstone
  refine ⟨Cq, cq, T₀, Ccol, X₀, Cs, hCq, hcq, hT₀, hX₀0, hCs, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q A G M Jb m₀ Ms Mt kk
    H1 X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hVJg hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup hNXd hcoef hwin
  -- ⟦THE LADDER, READ FROM THE K-FRAME⟧
  have hη := hF.eta_pos
  have hη6 := hF.eta_lt
  have hJb1 := hF.one_le_Jb
  have hG1 := hF.one_le_G
  have hM1 := hF.one_le_M
  have hEJbN : 24 ≤ calE A G Jb := by
    have h := calE_mono A hG1 hJb1
    rw [calE_one] at h
    exact le_trans hF.A_floor h
  have hJbR : (1 : ℝ) ≤ (Jb : ℝ) := by exact_mod_cast hJb1
  -- the K-exponent at the top of the ladder
  have hKpos : 1 ≤ (Jb ^ 2 * M) * calE A G Jb :=
    Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hJb1) hM1) (by omega)
  -- the top of the ladder
  have hQnat : 1 < calQK A G M Jb := by
    simp only [calQK]
    calc (1 : ℕ) < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ ((Jb ^ 2 * M) * calE A G Jb) := Nat.pow_le_pow_right (by norm_num) hKpos
  have hQ1 : (1 : ℝ) < ((calQK A G M Jb : ℕ) : ℝ) := by exact_mod_cast hQnat
  have hQpos : (0 : ℝ) < ((calQK A G M Jb : ℕ) : ℝ) := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (by omega) hF.Q_le_Xd
  have hHb2 : (2 : ℝ) ≤ calH H1 Jb := by
    simp only [calH]; nlinarith [hF.H1_two]
  have hHb0 : (0 : ℝ) < calH H1 Jb := by linarith
  have hα0 : (0 : ℝ) ≤ mrAlpha η Jb := (mrAlpha_pos η hη hη6 hJb1).le
  have hP3 : 3 ≤ calP A G Jb := by
    simp only [calP]
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ calE A G Jb := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hPQ : calP A G Jb ≤ calQK A G M Jb := calP_le_calQK hM1 hJb1
  -- `Q_{Jb} ≤ Tann`, DERIVED from `TannGate` and the cutoff
  have hlogX0 : (0 : ℝ) ≤ (Real.log X) ^ ((1 : ℝ) / 2) :=
    Real.rpow_nonneg (by linarith) _
  have hQT : ((calQK A G M Jb : ℕ) : ℝ) ≤ Tann := by
    calc ((calQK A G M Jb : ℕ) : ℝ) = Real.exp (Real.log ((calQK A G M Jb : ℕ) : ℝ)) :=
          (Real.exp_log hQpos).symm
      _ ≤ Real.exp ((Real.log X) ^ ((1 : ℝ) / 2)) := Real.exp_le_exp.mpr hJdef
      _ ≤ Real.exp (30 * (Real.log X) ^ ((1 : ℝ) / 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ ≤ Tann := hTgate
  -- the `VJ`-family, from the block top
  have hVJ : ∀ v ∈ ramI (calH H1 Jb) (calP A G Jb) (calQK A G M Jb),
      Real.exp (mrAlpha η Jb * (v : ℝ) / calH H1 Jb) ≤ VJ := by
    intro v hv
    have htop := ramI_top_le hHb0 hQ1.le hv
    have hstep : mrAlpha η Jb * (v : ℝ) / calH H1 Jb
        ≤ mrAlpha η Jb * Real.log ((calQK A G M Jb : ℕ) : ℝ) := by
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
  have hQ1Xd : calQK A G M 1 ≤ Xd := le_trans (calQK_mono A hG1 hJb1) hF.Q_le_Xd
  have hbot1 : ∀ v ∈ ramI (calH H1 1) (calP A G 1) (calQK A G M 1),
      1 ≤ ramRbot (calH H1 1) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI (by linarith)
      (one_le_calQK A G M 1) hQ1Xd hv
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have h : 1 ≤ calP A G 1 := by simp only [calP]; exact Nat.one_le_two_pow
    have : (1 : ℝ) ≤ ((calP A G 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  -- ⟦THE 𝒰-LEG AT THE K-LADDER⟧
  have hcapinst := hcap g c a cf hg hc1 hcf1 N Xd P Q Jb Jb (calP A G) (calQK A G M) m₀ Ms
    Mt kk (calH H1) (mrAlpha η) X Tann t₁ δ' V VJ L η Cb Rrad kmin Ymax ε EP2 E S
    hH2 hX0 hXe hLXe hL4 hlX2 hTgate hT1 hTX hQ1 hJdef hT₀T hLL5 hlogT1 hTLle hLe
    hJb1 le_rfl hHb2 hα0 hP3 hPQ hQT hVJ hα (by linarith) hMs hbudget hm₀2 hm₀ hMs4
    hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 ht₁ hrow hcoll hR0 hRrad hRlow
    hblk hbox hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate hKSgate hε0 habs hEP2 hErow herr hXN hN2 hsupp hSup
  -- ⟦THE 𝒯-LEG, AND THE COMPOSITION⟧
  exact hfeed c a b (calP A G) (calQK A G M) (calH H1) η Jb N Xd (calP A G 1) X Tann t₁ S ε
    hη hη6 hJb1 hXd1 hNXd (by linarith) hP1pos (levelGates_calibratedK hF) hH1two
    (by simp only [calP]; exact Nat.one_le_two_pow)
    (calP_le_calQK hM1 le_rfl) hbot1 hcoef hb1 (fun p => hc1 p) hwin
    hcapinst

/-- **THE SEAM ROW'S `Σ_j lemma12Rows`, AS A NUMBER** (`sum_lemma12Rows_priced_calibratedK`).

`TypicalPrice.sum_lemma12Rows_priced` — which was written with the ladder GENERIC precisely so
a re-pin would need no new wiring — instantiated at the K-family.  The density collection,
which `TypicalPrice.sum_lemma12Rows_priced_calibrated` had to leave at `C·Jb/2` (growing with
the cutoff, and refuted against eq (28)), is now

  `C·(2/M)`,

uniform in `Jb` and as small as the re-pin scale `M` is large.  With `M ≥ 8/δ` this is the
quantity `eq28_clears_of_M` certifies against MR §9's demand.  **The seam row is a number.** -/
theorem sum_lemma12Rows_priced_calibratedK :
    ∃ C : ℝ, 0 < C ∧ ∀ (A G M Jb N Xd : ℕ) (H1 T : ℝ) (a b c : ℕ → ℂ),
      1 ≤ A → 1 ≤ G → 1 ≤ M → 1 ≤ Xd → 0 ≤ T → 0 < H1 → (N : ℝ) ≤ 4 * (Xd : ℝ) →
      (∀ j ∈ Finset.Icc 1 Jb,
        Real.log ((calQK A G M j : ℕ) : ℝ) ≤ Real.sqrt (Real.log Xd)) →
      (100 : ℝ) ≤ Real.sqrt (Real.log Xd) →
      (∀ j ∈ Finset.Icc 1 Jb,
        ((Nat.sqrt Xd : ℝ) + 1)
            * ∏ p ∈ primeBand (calP A G j) (calQK A G M j), (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ)
            * (Real.log ((calP A G j : ℕ) : ℝ) / Real.log ((calQK A G M j : ℕ) : ℝ))) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → calP A G j ≤ p → p ≤ calQK A G M j →
        c p * b m ≠ 0 → (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      ∑ j ∈ Finset.Icc 1 Jb,
          lemma12Rows N Xd (calP A G j) (calQK A G M j) (calH H1 j) T a b c
        ≤ 480 * (T / (Xd : ℝ) + 1)
            * ((∑ j ∈ Finset.Icc 1 Jb,
                  ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH H1 j + 1)
                      * (Real.exp 1 / (Xd : ℝ) ^ 2))
                    + 64 * (Xd : ℝ) / ((calP A G j : ℕ) : ℝ) ^ 2
                    + 1 / (Xd : ℝ)))
              + C * (2 / (M : ℝ))) := by
  obtain ⟨C, hC, hsum⟩ := sum_lemma12Rows_priced
  refine ⟨C, hC, ?_⟩
  intro A G M Jb N Xd H1 T a b c hA hG hM hXd hT hH1 hN4 hreg hbig herr ha hb hc hasupp hwin
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hgates : ∀ j ∈ Finset.Icc 1 Jb,
      2 ≤ calP A G j ∧ calP A G j ≤ calQK A G M j ∧ 0 < calH H1 j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hE : 0 < calE A G j := by
      rw [calE]
      exact Nat.mul_pos (Nat.mul_pos hA (pow_pos hG (j - 1)))
        (pow_pos (Nat.factorial_pos j) 2)
    refine ⟨?_, calP_le_calQK hM hj.1, ?_⟩
    · rw [calP]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ calE A G j := Nat.pow_le_pow_right (by norm_num) hE
    · rw [calH]
      have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
      positivity
  have h := hsum (calP A G) (calQK A G M) (calH H1) Jb N Xd T a b c hXd hT hN4 hgates hreg
    hbig herr ha hb hc hasupp hwin
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ?_)
  · have hratio := sum_ratioK_le hA hG hM Jb
    have := mul_le_mul_of_nonneg_left hratio hC.le
    linarith
  · have hT0 : (0 : ℝ) ≤ T / (Xd : ℝ) := div_nonneg hT hXd0.le
    linarith

end Salt.MR
