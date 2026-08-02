/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorLadderLinear
import Salt.MR.A3Middle

/-!
# `ThmA2Linear` — the `thm_A2′` ladder at `AdoorL M = 2^36·M`

⟦LADDER-L, G1 §2⟧  The `_L` twin family of `ThmA2`, `ThmA2ChiSummed`, `ThmA2Pool`,
`ThmA2Rows`, `ThmA2Prime` and `A3Middle` at the LINEAR door.  Every twin is a RESTATEMENT of
the landed theorem with `Adoor M` replaced by `AdoorL M` in the ladder slot (`calP`, `calQK`,
`MemS`), the `G`-slot unchanged (`3072·M`, resp. `s13GK K M`), and the landed proof replayed:
the deep analytic content (`ThmA2Spine.thm_a2_spine`, `CapFreeArm*`, the seam-row stations) is
`(A,G)`-PARAMETRIC, so nothing is re-derived — the door's anchor is a symbol throughout.

The two objects that genuinely move are already landed elsewhere:
`ArithPageLinear.a2Level1_L` (the level-1 grade — the anchor is read in BOTH the numerator
`log 𝒬₁` and the denominator `𝒫₁^{1/12}`) and `ArithPageLinear.a2RowsSum_L`/`a2Mrow_L`.
This page consumes them; it does not re-derive them.

⚠ The `_gk` twins keep the LANDED narrow ceiling `K ≤ 1.7·10⁸` at their binders (they
quantify `M` internally, so the wide `K ≤ 1.7·10⁸·M` is not statable there); the wide frame
is reached through `kwide`, which is free at `1 ≤ M`.

Source pins: `docs/blueprints/flags.md` ⟦COMPOSE-FLAT-2⟧, ⟦LINEAR-PAGE⟧.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Complex
open scoped BigOperators

/-- The landed narrow `K`-ceiling implies the linear door's WIDE one, at `1 ≤ M`. -/
private lemma kwide {K M : ℕ} (hK : K ≤ 170000000) (hM : 1 ≤ M) : K ≤ 170000000 * M :=
  le_trans hK (Nat.le_mul_of_pos_right _ (by omega))

/-! ## §0 — the landed `private` stones, re-declared (all door-free) -/

/-- The `π`-arithmetic of the spine's prefactor `1/(2π²)`, isolated:
`236365/(2π) ≤ 37620`, `205/(2π) ≤ 33`, `39674880/(2π) ≤ 6315000`. -/
private lemma spine_scale {p Mr Bd w Eg eg : ℝ} (hp1 : 3.141592 < p)
    (hMr : 0 ≤ Mr) (hBd : 0 ≤ Bd) (hw : 0 ≤ w) (hEg : Eg ≤ 2 * p ^ 2 * eg) :
    1 / (2 * p ^ 2) * (236365 * p * Mr + 205 * p * Bd + 39674880 * p * w + Eg)
      ≤ 37620 * Mr + 33 * Bd + 6315000 * w + eg := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2pos : (0 : ℝ) < 2 * p ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hp2pos]
  have h1 : 236365 * p ≤ 75240 * p ^ 2 := by nlinarith
  have h2 : 205 * p ≤ 66 * p ^ 2 := by nlinarith
  have h3 : 39674880 * p ≤ 12630000 * p ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hMr, mul_le_mul_of_nonneg_right h2 hBd,
    mul_le_mul_of_nonneg_right h3 hw]

/-- The `π`-arithmetic of the spine's prefactor `1/(2π²)`, isolated (`ThmA2.spine_scale`'s
statement and proof, re-stated here because the original is module-private):
`236365/(2π) ≤ 37620`, `205/(2π) ≤ 33`, `39674880/(2π) ≤ 6315000`. -/
private lemma spine_scale_pool {p Mr Bd w Eg eg : ℝ} (hp1 : 3.141592 < p)
    (hMr : 0 ≤ Mr) (hBd : 0 ≤ Bd) (hw : 0 ≤ w) (hEg : Eg ≤ 2 * p ^ 2 * eg) :
    1 / (2 * p ^ 2) * (236365 * p * Mr + 205 * p * Bd + 39674880 * p * w + Eg)
      ≤ 37620 * Mr + 33 * Bd + 6315000 * w + eg := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2pos : (0 : ℝ) < 2 * p ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hp2pos]
  have h1 : 236365 * p ≤ 75240 * p ^ 2 := by nlinarith
  have h2 : 205 * p ≤ 66 * p ^ 2 := by nlinarith
  have h3 : 39674880 * p ≤ 12630000 * p ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hMr, mul_le_mul_of_nonneg_right h2 hBd,
    mul_le_mul_of_nonneg_right h3 hw]

/-- **THE FOUR NUMERALS** (`a2_weight_gates`).  With `w := (X/h)/T` the weight of the
dyadic family: `0 ≤ w ≤ 1`, and

  `w·(2T·Q₁/X_d + 1) ≤ 9`,  `w·(2·(2T)/X_d + 240) ≤ 244`,
  `w·(2T/X_d + 1) ≤ 3`,     `w·(2T/X + 1) ≤ 3/2`.

Everything reduces to `(X/h)/X_d ≤ 4/h` (from `X ≤ 4X_d`) and `w ≤ 1` (from `X/h ≤ T`). -/
private lemma a2_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
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
  have hr0 : (0 : ℝ) ≤ X / h / Xd := le_of_lt (div_pos hu0 hXd0)
  refine ⟨hw0, hw1, ?_, ?_, ?_, ?_⟩
  · have hid : X / h / T * (2 * T * Q1 / Xd + 1) = 2 * Q1 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * Q1 * (X / h / Xd) ≤ 8 := by
      have hstep : 2 * Q1 * (X / h / Xd) ≤ 2 * Q1 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
      have hval : 2 * Q1 * (4 / h) ≤ 8 := by
        rw [show 2 * Q1 * (4 / h) = 8 * Q1 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * (2 * T) / Xd + 240)
        = 4 * (X / h / Xd) + 240 * (X / h / T) := by
      field_simp; ring
    have h16 : 4 * (X / h / Xd) ≤ 4 := by
      have hstep : 4 * (X / h / Xd) ≤ 4 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 4 * (4 / h) ≤ 4 := by
        rw [show 4 * (4 / h) = 16 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / Xd + 1) = 2 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * (X / h / Xd) ≤ 2 := by
      have hstep : 2 * (X / h / Xd) ≤ 2 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 2 * (4 / h) ≤ 2 := by
        rw [show 2 * (4 / h) = 8 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / X + 1) = 2 / h + X / h / T := by
      field_simp
    have h2 : 2 / h ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hh0 (by norm_num)]
      linarith
    rw [hid]; linarith

/-- The weighting, summand by summand: four bounds compose into one. -/
private lemma a2_row_weigh {w A B C D a b c d : ℝ}
    (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (A + B + C + D) ≤ a + b + c + d := by
  have h : w * (A + B + C + D) = w * A + w * B + w * C + w * D := by ring
  rw [h]; linarith

/-- The §8.1 level-1 summand, weighted: the weight rides into the row's own free factor `R`
(`DoorFrameH1.level1_term_door_decays`' `R`-slot), where the `9`-gate meets it. -/
private lemma a2_level1_weigh {w Hq Lq R Pq Br Z : ℝ}
    (hkey : ∀ R' : ℝ, 0 ≤ R' → 2 * (Hq * Lq + 1) * R' * Pq * Br ≤ 5280 * R' * Z)
    (hR0 : 0 ≤ w * R) (hR9 : w * R ≤ 9) (hZ0 : 0 ≤ Z) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 47520 * Z := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = 2 * (Hq * Lq + 1) * (w * R) * Pq * Br := by ring
  rw [hid]
  refine le_trans (hkey (w * R) hR0) ?_
  nlinarith [mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤ 9 - w * R)]

/-- The `Cs`-summand, weighted at the `244`-gate: `1536·244 = 374784`. -/
private lemma a2_term2_weigh {w Cs R Y : ℝ} (hCs : 0 ≤ Cs) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Cs * Real.exp 3 * R * Y) ≤ 374784 * Cs * Real.exp 3 * Y := by
  have hid : w * (1536 * Cs * Real.exp 3 * R * Y)
      = 1536 * Cs * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Cs * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- The Lemma-12 summand, weighted at the `3`-gate: `480·3 = 1440`, and ⟦AMENDMENT G⟧'s
`×4` cover carries it to `a2Mrow`'s `5760`. -/
private lemma a2_term3_weigh {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (480 * R * S) ≤ 5760 * S := by
  have hid : w * (480 * R * S) = 480 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 480) hS)]

/-- **THE LEMMA-12 SUMMAND AT ⟦WALL 1⟧'s MR ROW** (`a2_term3_weigh_mr`).  The `hwin`-free
four-row exit prices the seam row at `960·(T_ann/X_d+1)·(…)` in place of `480·(…)`
(`M4RowMR`), so the `3`-gate gives `960·3 = 2880` — still inside `a2Mrow`'s `5760`, which is
⟦AMENDMENT G⟧'s `×4` cover of `1440`.  **The interface numeral does not move.** -/
private lemma a2_term3_weigh_mr {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (960 * R * S) ≤ 5760 * S := by
  have hid : w * (960 * R * S) = 960 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 960) hS)]

/-- The `𝒰`-leg summand, weighted at the `3/2`-gate: `2·(3/2) = 3`. -/
private lemma a2_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]

/-- The cap branch's weighting: five summands, the ball leg folded into the row slot. -/
private lemma a2_row_weigh_cap {w Sq A B C D a b c d : ℝ}
    (hA : w * A ≤ a) (hB : w * B ≤ b) (hSC : w * Sq + w * C ≤ c) (hD : w * D ≤ d) :
    w * (Sq + (A + B + C) + D) ≤ a + b + c + d := by
  have h : w * (Sq + (A + B + C) + D) = w * A + w * B + (w * Sq + w * C) + w * D := by ring
  rw [h]; linarith

/-- The cap branch's third slot: ball leg plus Lemma-12 rows, into `a2Mrow`'s `5760`.

**THE ONE-STEP RE-PROOF** (⟦THE WALL⟧'s wave, REFUTE-RESIDUE correction 4).  The rows are
weighed at `a2_term3_weigh`'s FULL `5760` — the same constant the cap-FREE branch spends —
and the `8S²` ball leg is paid ENTIRELY out of `Ccc`'s free slack, of which it is a
`720`-th: `hCcc` gives `Ccc·(2/M) ≥ Cst·(2/M) + S²`, hence `5760·S²` of room against a
demand of `8·S²`.  ⟦AMENDMENT G⟧'s `×4` cover (`1440 → 5760`) is therefore NOT spent here at
all — it stays available to the rows, exactly as on the cap-free branch, which is what makes
the two branches' `hR : w·R ≤ 3` gates readable as the same gate. -/
private lemma a2_term3_ball_weigh {w R Sb RS Cst Ccc Mr : ℝ}
    (hw1 : w ≤ 1) (hRS : 0 ≤ RS) (hC0 : 0 ≤ Cst) (hM1 : 1 ≤ Mr)
    (hCcc : Cst + Mr * Sb ^ 2 / 2 ≤ Ccc) (hR : w * R ≤ 3) :
    w * (8 * Sb ^ 2) + w * (480 * R * (RS + Cst * (2 / Mr)))
      ≤ 5760 * (RS + Ccc * (2 / Mr)) := by
  have hM0 : (0 : ℝ) < Mr := by linarith
  have hq0 : (0 : ℝ) < 2 / Mr := by positivity
  have hCq : (0 : ℝ) ≤ Cst * (2 / Mr) := mul_nonneg hC0 hq0.le
  have hball : w * (8 * Sb ^ 2) ≤ 8 * Sb ^ 2 := by nlinarith [sq_nonneg Sb]
  have hrows := a2_term3_weigh (w := w) (R := R) (S := RS + Cst * (2 / Mr))
    (by linarith) hR
  have hslack : (Cst + Mr * Sb ^ 2 / 2) * (2 / Mr) ≤ Ccc * (2 / Mr) :=
    mul_le_mul_of_nonneg_right hCcc hq0.le
  have hexp : (Cst + Mr * Sb ^ 2 / 2) * (2 / Mr) = Cst * (2 / Mr) + Sb ^ 2 := by field_simp
  rw [hexp] at hslack
  linarith [sq_nonneg Sb]

/-- The `π`-arithmetic of the spine's prefactor `1/(2π²)`, isolated (`ThmA2.spine_scale`'s
statement and proof; both the landed copy and `ThmA2Pool`'s are module-private):
`236365/(2π) ≤ 37620`, `205/(2π) ≤ 33`, `39674880/(2π) ≤ 6315000`. -/
private lemma spine_scale_prime {p Mr Bd w Eg eg : ℝ} (hp1 : 3.141592 < p)
    (hMr : 0 ≤ Mr) (hBd : 0 ≤ Bd) (hw : 0 ≤ w) (hEg : Eg ≤ 2 * p ^ 2 * eg) :
    1 / (2 * p ^ 2) * (236365 * p * Mr + 205 * p * Bd + 39674880 * p * w + Eg)
      ≤ 37620 * Mr + 33 * Bd + 6315000 * w + eg := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2pos : (0 : ℝ) < 2 * p ^ 2 := by positivity
  rw [one_div, inv_mul_eq_div, div_le_iff₀ hp2pos]
  have h1 : 236365 * p ≤ 75240 * p ^ 2 := by nlinarith
  have h2 : 205 * p ≤ 66 * p ^ 2 := by nlinarith
  have h3 : 39674880 * p ≤ 12630000 * p ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 hMr, mul_le_mul_of_nonneg_right h2 hBd,
    mul_le_mul_of_nonneg_right h3 hw]

/-- `ThmA2Rows.a2_weight_gates`, re-minted: with `w := (X/h)/T`, `0 ≤ w ≤ 1` and the four
`Tann`-linear factors weigh in at `9`, `244`, `3`, `3/2`. -/
private lemma a3_weight_gates {X h T Xd Q1 : ℝ} (hh4 : 4 ≤ h) (hX0 : 0 < X)
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
  have hr0 : (0 : ℝ) ≤ X / h / Xd := le_of_lt (div_pos hu0 hXd0)
  refine ⟨hw0, hw1, ?_, ?_, ?_, ?_⟩
  · have hid : X / h / T * (2 * T * Q1 / Xd + 1) = 2 * Q1 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * Q1 * (X / h / Xd) ≤ 8 := by
      have hstep : 2 * Q1 * (X / h / Xd) ≤ 2 * Q1 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by linarith)
      have hval : 2 * Q1 * (4 / h) ≤ 8 := by
        rw [show 2 * Q1 * (4 / h) = 8 * Q1 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * (2 * T) / Xd + 240)
        = 4 * (X / h / Xd) + 240 * (X / h / T) := by
      field_simp; ring
    have h16 : 4 * (X / h / Xd) ≤ 4 := by
      have hstep : 4 * (X / h / Xd) ≤ 4 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 4 * (4 / h) ≤ 4 := by
        rw [show 4 * (4 / h) = 16 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / Xd + 1) = 2 * (X / h / Xd) + X / h / T := by
      field_simp
    have h8 : 2 * (X / h / Xd) ≤ 2 := by
      have hstep : 2 * (X / h / Xd) ≤ 2 * (4 / h) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      have hval : 2 * (4 / h) ≤ 2 := by
        rw [show 2 * (4 / h) = 8 / h by ring, div_le_iff₀ hh0]
        linarith
      linarith
    rw [hid]; linarith
  · have hid : X / h / T * (2 * T / X + 1) = 2 / h + X / h / T := by
      field_simp
    have h2 : 2 / h ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hh0 (by norm_num)]
      linarith
    rw [hid]; linarith

/-- `ThmA2Rows.a2_row_weigh`, re-minted. -/
private lemma a3_row_weigh {w A B C D a b c d : ℝ}
    (hA : w * A ≤ a) (hB : w * B ≤ b) (hC : w * C ≤ c) (hD : w * D ≤ d) :
    w * (A + B + C + D) ≤ a + b + c + d := by
  have h : w * (A + B + C + D) = w * A + w * B + w * C + w * D := by ring
  rw [h]; linarith

/-- `ThmA2Rows.a2_level1_weigh`, re-minted. -/
private lemma a3_level1_weigh {w Hq Lq R Pq Br Z : ℝ}
    (hkey : ∀ R' : ℝ, 0 ≤ R' → 2 * (Hq * Lq + 1) * R' * Pq * Br ≤ 5280 * R' * Z)
    (hR0 : 0 ≤ w * R) (hR9 : w * R ≤ 9) (hZ0 : 0 ≤ Z) :
    w * (2 * (Hq * Lq + 1) * R * Pq * Br) ≤ 47520 * Z := by
  have hid : w * (2 * (Hq * Lq + 1) * R * Pq * Br)
      = 2 * (Hq * Lq + 1) * (w * R) * Pq * Br := by ring
  rw [hid]
  refine le_trans (hkey (w * R) hR0) ?_
  nlinarith [mul_nonneg hZ0 (by linarith : (0 : ℝ) ≤ 9 - w * R)]

/-- `ThmA2Rows.a2_term2_weigh`, re-minted: `1536·244 = 374784`. -/
private lemma a3_term2_weigh {w Cs R Y : ℝ} (hCs : 0 ≤ Cs) (hY : 0 ≤ Y) (hR : w * R ≤ 244) :
    w * (1536 * Cs * Real.exp 3 * R * Y) ≤ 374784 * Cs * Real.exp 3 * Y := by
  have hid : w * (1536 * Cs * Real.exp 3 * R * Y)
      = 1536 * Cs * Real.exp 3 * Y * (w * R) := by ring
  have h0 : (0 : ℝ) ≤ 1536 * Cs * Real.exp 3 * Y := by positivity
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR h0]

/-- `ThmA2Rows.a2_term3_weigh_mr`, re-minted: `960·3 = 2880 ≤ 5760`. -/
private lemma a3_term3_weigh_mr {w R S : ℝ} (hS : 0 ≤ S) (hR : w * R ≤ 3) :
    w * (960 * R * S) ≤ 5760 * S := by
  have hid : w * (960 * R * S) = 960 * S * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 960) hS)]

/-- `ThmA2Rows.a2_term4_weigh`, re-minted: `2·(3/2) = 3`. -/
private lemma a3_term4_weigh {w R Z : ℝ} (hZ : 0 ≤ Z) (hR : w * R ≤ 3 / 2) :
    w * (2 * (R * Z)) ≤ 3 * Z := by
  have hid : w * (2 * (R * Z)) = 2 * Z * (w * R) := by ring
  rw [hid]
  linarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ 2 * Z)]


/-! ### `ThmA2` :495 — `thm_a2'_of_rows` -/
/-- **thm_A2′, GIVEN THE ROW FAMILY** (`thm_a2'_of_rows_L`).  The frozen five-summand
interface, with the weighted seam-row family and the `T₀`-band supplied as binders (the
two branches of §5 are its two suppliers):

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500}`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

**The complete side-condition list**, all in-statement (law #253):  `1 ≤ M` (the door's
parameter); `e ≤ X` and `3 ≤ X`; `4 ≤ h` (the AS-2 MVT guard — NOT `3`);
`h ≤ X(log X)^{−1/5}` (Lemma 14's window frame); `X ≤ N ≤ 2X` and `a` supported above `X`
with `‖aₙ‖ ≤ 1`; `TannGate X (2X/h)` and `5 ≤ loglog(2X/h)` — equivalently the freeze's
`h`-CEILING `h ≤ 2X·e^{−e⁵}`, the honest deviation from MRT's bare `h ≥ 3`; the three
GRADING GATES (`hgP1`, `hgRows`, `hL4096`) and the `𝒰`-leg's exponent room
`0 ≤ ε ≤ θ₂₉₃ − 1/500` with `θ₂₉₃ = 1/(32(3e+1))` (so `1/500 < θ₂₉₃`, with room). -/
theorem thm_a2'_of_rows_L {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow_L Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hrp500 : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hL0 _
  have hrp13 : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hL0 _
  -- the level-1 grade is nonnegative
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hP64 := calP_door_one_ge_L hM
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  -- ⟦the row number, graded⟧
  have hMrowLe : a2Mrow_L Cs Ccc M Xd X ε
      ≤ 47520 * a2Level1_L M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500) := by
    unfold a2Mrow_L
    have hθ : theta293 < 1 / 32 := theta293_lt_one_div_32
    have hU : (Real.log X) ^ (-theta293 + ε) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hεwin.1, hεwin.2])
    linarith
  have hMrow'0 : (0 : ℝ) ≤ 47520 * a2Level1_L M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500) := by
    nlinarith
  -- ⟦the band, graded, with the `4096` summand absorbed⟧
  have h4096 : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500)
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hsp : (Real.log X) ^ (-(1 : ℝ) / 500)
        = (Real.log X) ^ (1 - (1 : ℝ) / 250) * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [hsp]
    exact mul_le_mul_of_nonneg_right hL4096
      (le_of_lt (Real.rpow_pos_of_pos hL0 _))
  have hBandLe : t0BandB X C₁' M₀
      ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + (Real.log X) ^ (-(1 : ℝ) / 500)
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have := t0BandB_grade (X := X) (C₁ := C₁') (M₀ := M₀) hX3
    linarith
  have hBand'0 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + (Real.log X) ^ (-(1 : ℝ) / 500)
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
    have h2 : (0 : ℝ) ≤ 9216 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
    linarith
  -- ⟦the Perron defect, to the limit⟧
  refine le_of_forall_pos_le_add (fun eg heg => ?_)
  have hpi := Real.pi_gt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨K, δ, hδ0, hδ1, hEg⟩ :=
    egap_small (X := X) (h := h) hX3 hh4 (show (0 : ℝ) < 2 * Real.pi ^ 2 * eg by positivity)
  have hspine := thm_a2_spine (N := N) (a := a) (X := X) (h := h)
    (Mrow := a2Mrow_L Cs Ccc M Xd X ε) (B₀ := t0BandB X C₁' M₀) (δ := δ) K
    hX hh4 hhX hδ0 hδ1 ha hsupp hN2 hTann hceil hrows hT0band
  refine hspine.trans ?_
  -- monotonicity in `Mrow` and `B₀`, then the `π`-arithmetic
  have hmono : 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * a2Mrow_L Cs Ccc M Xd X ε
            + 205 * Real.pi * t0BandB X C₁' M₀ + 39674880 * Real.pi / h
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))
      ≤ 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * (47520 * a2Level1_L M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500))
            + 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + (Real.log X) ^ (-(1 : ℝ) / 500)
                + 9216 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
            + 39674880 * Real.pi * (1 / h)
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2)) := by
    have hpre : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have e1 : 236365 * Real.pi * a2Mrow_L Cs Ccc M Xd X ε
        ≤ 236365 * Real.pi * (47520 * a2Level1_L M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500)) :=
      mul_le_mul_of_nonneg_left hMrowLe (by positivity)
    have e2 : 205 * Real.pi * t0BandB X C₁' M₀
        ≤ 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + (Real.log X) ^ (-(1 : ℝ) / 500)
            + 9216 * ballSupC ^ 2
              * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hBandLe (by positivity)
    have e3 : 39674880 * Real.pi / h = 39674880 * Real.pi * (1 / h) := by ring
    rw [e3]
    linarith
  refine hmono.trans ?_
  have hscale := spine_scale (p := Real.pi)
    (Mr := 47520 * a2Level1_L M + 5 * (Real.log X) ^ (-(1 : ℝ) / 500))
    (Bd := 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + (Real.log X) ^ (-(1 : ℝ) / 500)
        + 9216 * ballSupC ^ 2
          * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
    (w := 1 / h) (eg := eg) hpi hMrow'0 hBand'0 (by positivity) hEg
  refine hscale.trans ?_
  have hw : 6315000 * (1 / h) = 6315000 / h := by ring
  rw [hw]
  linarith

/-! ### `ThmA2` :660 — `calFrameK_doorH1_at` -/
/-- **THE DOOR FRAME AT THE ROW'S SCALE.**  `CalFrameK` at `η = 1/12`, `A = AdoorL M`,
`G = 3072M`, `Jb = 2`, `H₁ = H1doorL M` and ANY `X_d ≥ Q_{Jb}` — the landed inhabitant with
its single `X_d`-mentioning field (`Q_le_Xd`) relaxed from equality.  This is what lets the
seam row run at its own dyadic scale `X_d ≍ X` while the door keeps its `P`/`Q` ladder.
Every other field is `DoorFrameH1.calFrameK_satisfiable_doorH1_L`'s, verbatim. -/
theorem calFrameK_doorH1_at_L (M Xd : ℕ) (hM : 1 ≤ M)
    (hXd : calQK (AdoorL M) (3072 * M) M 2 ≤ Xd) :
    CalFrameK (1 / 12) (H1doorL M) (AdoorL M) (3072 * M) M 2 Xd := by
  have hF := calFrameK_satisfiable_doorH1_L M hM
  exact ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, hF.H1_two, hF.H1_pin, hXd⟩

/-! ### `ThmA2` :935 — `a2RowsSum_shift_gk` -/
/-- **⟦THE `Ccc`-SHIFT⟧, the row-sum slot** (`a2RowsSum_shift_L_gk`).  The twin's row-sum gate
is the LANDED gate at the shifted free constant

  `Ccc_gk := Ccc + (M/2)·(a2RowsSum_L_gk K M X_d − a2RowsSum_L M X_d)`   (`≤ Ccc`).

`a2Mrow_L`/`a2RowsSum_L` have exactly one free-constant slot, entering as `C·(2/M)`, so the whole
lever motion in the row page is absorbed by a shift of that constant — no estimate is
re-run anywhere downstream. -/
lemma a2RowsSum_shift_L_gk (K : ℕ) (C : ℝ) {M : ℕ} (Xd : ℕ) (hM : 1 ≤ M) :
    a2RowsSum_L M Xd + (C + (M : ℝ) / 2 * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd))
        * (2 / (M : ℝ))
      = a2RowsSum_L_gk K M Xd + C * (2 / (M : ℝ)) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcancel : (M : ℝ) / 2 * (2 / (M : ℝ)) = 1 := by field_simp
  have hexp : (C + (M : ℝ) / 2 * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd)) * (2 / (M : ℝ))
      = C * (2 / (M : ℝ))
        + ((M : ℝ) / 2 * (2 / (M : ℝ))) * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd) := by
    ring
  rw [hexp, hcancel]
  ring

/-! ### `ThmA2` :956 — `a2Mrow_shift_gk` -/
/-- **⟦THE `Ccc`-SHIFT⟧, the row-number slot** (`a2Mrow_shift_L_gk`). -/
lemma a2Mrow_shift_L_gk (K : ℕ) (Cs C : ℝ) {M : ℕ} (Xd : ℕ) (X ε : ℝ) (hM : 1 ≤ M) :
    a2Mrow_L Cs (C + (M : ℝ) / 2 * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd)) M Xd X ε
      = a2Mrow_L_gk K Cs C M Xd X ε := by
  rw [a2Mrow_L, a2Mrow_L_gk, calP_doorL_one_gk, a2RowsSum_shift_L_gk K C Xd hM]

/-! ### `ThmA2` :962 — `calFrameK_doorH1_at_gk` -/
/-- **THE DOOR FRAME AT THE ROW'S SCALE, AT THE G-LEVER** (`calFrameK_doorH1_at_L_gk`).
`calFrameK_doorH1_at_L` with `G := s13GK K M`; the single `X_d`-mentioning field is relaxed
from equality exactly as in the landed statement. -/
theorem calFrameK_doorH1_at_L_gk (K M Xd : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000)
    (hXd : calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) :
    CalFrameK (1 / 12) (H1doorL M) (AdoorL M) (s13GK K M) M 2 Xd := by
  have hF := calFrameK_satisfiable_doorH1_L_gk K M hM (kwide hK hM)
  exact ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, hF.H1_two, hF.H1_pin, hXd⟩

/-- **⟦THE WIDE DOOR FRAME⟧** (`calFrameK_doorH1_at_L_gk_kwide`) — `calFrameK_doorH1_at_L_gk`
with the `kwide` hop deleted.

`ThmA2Linear.kwide` is the private step `K ≤ 1.7·10⁸ → 1 ≤ M → K ≤ 1.7·10⁸·M`; it is the ONE
place the L chain throws the `M` factor away.  The landed frame
`DoorLadderLinear.calFrameK_satisfiable_doorH1_L_gk` already takes the WIDE ceiling, so deleting
the hop is free — this twin takes `K ≤ 1.7·10⁸·M` directly, and at `K = KlevF A`,
`M = flatDoorM A` that hypothesis is `KlevF_le_wideCeiling`.

⟦THE ROOT OF P2(b)⟧  Every `hK : K ≤ 170000000` on the L chain is spent, ultimately, here (via
`M4RowSpineLinear:1493` and `A3Middle:1031/:1148`); this twin is where the propagation of the
weakened ceiling starts. -/
theorem calFrameK_doorH1_at_L_gk_kwide (K M Xd : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000 * M)
    (hXd : calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd) :
    CalFrameK (1 / 12) (H1doorL M) (AdoorL M) (s13GK K M) M 2 Xd := by
  have hF := calFrameK_satisfiable_doorH1_L_gk K M hM hK
  exact ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, hF.H1_two, hF.H1_pin, hXd⟩

/-! ### `ThmA2` :972 — `thm_a2'_of_rows_gk` -/
/-- **thm_A2′ AT THE G-LEVER** (`thm_a2'_of_rows_L_gk`).  `thm_a2'_of_rows_L` verbatim with
`G := s13GK K M`: the row family is taken at `a2Mrow_L_gk`, the `𝒫₁` gate at the lever's `𝒫₁`
(same symbol — level 1), and the row-sum gate at `a2RowsSum_L_gk`.  The conclusion is
BYTE-IDENTICAL to the landed one, `a2Level1_L M` included, because every summand of the
five-summand interface is either `G`-free or level-1.

The proof spends no new estimate.  The twin's row number is the LANDED `a2Mrow_L` at the
shifted constant

  `Ccc_gk := Ccc + (M/2)·(a2RowsSum_L_gk K M X_d − a2RowsSum_L M X_d)   (≤ Ccc)`,

so `thm_a2'_of_rows_L` is instantiated once, at that constant, and the three moved hypotheses
match on the nose. -/
theorem thm_a2'_of_rows_L_gk (K : ℕ) {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
        ≤ a2Mrow_L_gk K Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  -- ⟦THE `Ccc`-SHIFT⟧ the twin's row number IS the landed one at this constant
  have hrowsum := a2RowsSum_shift_L_gk K Ccc (M := M) Xd hM
  have hMrow := a2Mrow_shift_L_gk K Cs Ccc (M := M) Xd X ε hM
  exact thm_a2'_of_rows_L hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil
    (fun T h1 h2 h3 h4 => (hrows T h1 h2 h3 h4).trans (le_of_eq hMrow.symm)) hT0band
    (by rw [← calP_doorL_one_gk (K := K)]; exact hgP1)
    (by rw [hrowsum]; exact hgRows) hεwin hL4096

/-! ### `ThmA2ChiSummed` :196 — `thm_a2'_of_rows_chiSummed` -/
/-- **⟦A4-D1b⟧ THE `Σ_χ` FROZEN INTERFACE** (`thm_a2'_of_rows_chiSummed_L`).  The character sum
of `ThmA2.thm_a2'_of_rows_L`' five-summand bound, at a GENERIC `χ`-indexed coefficient family
and INDEXED constant families `Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ`:

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ ∑_χ 8448·C₁'(χ)²·exp(−M₀(χ)/e)`
`   + φ(q)·[ 1787702400·a2Level1_L M`
`          + 188133·(log X)^{−1/500}`
`          + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
`          + 6315000/h ]`.

⟦THE LEDGER, ITEMISED⟧ ONE summand — the `T₀`-band's, the only one carrying a character
datum — is a genuine character sum; the other FOUR are `χ`-free and each pays exactly one
`φ(q)`.  The v2 addendum's ⟦A2⟧ six-debit classification (which of these are g-arm-absorbable
`X`-side and which tighten ⟦gate 8⟧ on the `P₁/M`-side) is COUNCIL arithmetic and is
deliberately absent here: this statement exhibits the debits, it does not price them.

Every per-character hypothesis is quantified `∀ χ`: the coefficient bound, the support
condition, the weighted row family at `a2Mrow_L (Cs χ) (Ccc χ) M Xd X (ε χ)`, the `T₀`-band at
`t0BandB X (C₁' χ) (M₀ χ)`, the two grading gates, and the exponent room.  The frame
(`hM`, `hX`, `hX3`, `hh4`, `hhX`, `hN2`, `hTann`, `hceil`, `hL4096`) is character-blind and
stays global. -/
theorem thm_a2'_of_rows_chiSummed_L {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow_L (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum_L M Xd + Ccc χ * (2 / (M : ℝ)))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ε χ ∧ ε χ ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1_L M
              + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  -- ⟦move 1⟧ the `q = 1` interface at each character's OWN datum and OWN constants
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
        ≤ 8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ)
          + (1787702400 * a2Level1_L M
            + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h) := by
    intro χ _
    have hrow := thm_a2'_of_rows_L (N := N) (M := M) (Xd := Xd) (a := a χ) (X := X) (h := h)
      (Cs := Cs χ) (Ccc := Ccc χ) (C₁' := C₁' χ) (M₀ := M₀ χ) (ε := ε χ)
      hM hX hX3 hh4 hhX (ha χ) (hsupp χ) hN2 hTann hceil (hrowsSum χ) (hT0bandSum χ)
      (hgP1 χ) (hgRows χ) (hεwin χ) hL4096
    refine le_trans hrow (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum, then ⟦move 3⟧ the split: `φ(q)` on the four `χ`-free summands
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [a2_sum_head_split]

/-! ### `ThmA2ChiSummed` :284 — `thm_a2'_of_rows_chiSummed_gk` -/
/-- **thm_A2′ χ-SUMMED, AT THE G-LEVER** (`thm_a2'_of_rows_chiSummed_L_gk`). -/
theorem thm_a2'_of_rows_chiSummed_L_gk (K : ℕ) {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow_L_gk K (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum_L_gk K M Xd + Ccc χ * (2 / (M : ℝ)))
        ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : ∀ χ : DirichletCharacter ℂ q, 0 ≤ ε χ ∧ ε χ ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1_L M
              + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  refine thm_a2'_of_rows_chiSummed_L (Xd := Xd) (Cs := Cs) (Ccc := fun χ =>
      Ccc χ + (M : ℝ) / 2 * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0bandSum ?_ ?_ hεwin hL4096
  · intro χ T h1 h2 h3 h4
    exact (hrowsSum χ T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow_shift_L_gk K (Cs χ) (Ccc χ) (M := M) Xd X (ε χ) hM).symm)
  · intro χ
    rw [← calP_doorL_one_gk (K := K)]
    exact hgP1 χ
  · intro χ
    rw [a2RowsSum_shift_L_gk K (Ccc χ) (M := M) Xd hM]
    exact hgRows χ

/-! ### `ThmA2Pool` :70 — `thm_a2'_of_rows_pool` -/
/-- **thm_A2′ AT A FREE CONSTANT POOL** (`thm_a2'_of_rows_pool_L`) — ⟦R2⟧'s crossing twin of
`ThmA2.thm_a2'_of_rows_L`.  The frozen five-summand interface with the three `X`-side sources
pooled into ONE free real `π₀ ≥ 0`:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·π₀`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

⟦THE GATE LIST, AGAINST THE LANDED ONE⟧ the frame (`hM`, `hX`, `hX3`, `hh4`, `hhX`, `ha`,
`hsupp`, `hN2`, `hTann`, `hceil`) and the two suppliers (`hrows`, `hT0band`) are VERBATIM.
In place of the landed `hgP1`/`hgRows`/`hεwin`/`hL4096` stand FOUR pool gates:
`hpool : 0 ≤ π₀`, `hgP1`/`hgRows` at `≤ π₀`, and the two gates that were derivations —
`hgU : (log X)^{−θ₂₉₃+ε} ≤ π₀` (so `ε` is FREE: no exponent-room hypothesis survives) and
`hgBand : 4096·(log X)^{−1+1/500} ≤ π₀`.

⟦WHY THE COEFFICIENT IS `188133` AGAIN⟧ the pool enters the row number FIVE times
(`1 + 1 + 3`: `hgP1`, `hgRows`, and the `𝒰`-leg's `3·(log X)^{−θ₂₉₃+ε}`) and the band ONCE,
and the `π`-scaling pays `37620` and `33` for those two channels: `37620·5 + 33 = 188133`.
Setting `π₀ := (log X)^{−1/500}` recovers the landed statement exactly. -/
theorem thm_a2'_of_rows_pool_L {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow_L Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log X) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hrp13 : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hL0 _
  -- the level-1 grade is nonnegative
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hP64 := calP_door_one_ge_L hM
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  -- ⟦the row number, graded AT THE POOL⟧ — three sources, `1 + 1 + 3` copies
  have hMrowLe : a2Mrow_L Cs Ccc M Xd X ε ≤ 47520 * a2Level1_L M + 5 * π₀ := by
    unfold a2Mrow_L
    linarith
  have hMrow'0 : (0 : ℝ) ≤ 47520 * a2Level1_L M + 5 * π₀ := by linarith
  -- ⟦the band, graded, with the `4096` summand absorbed INTO THE POOL⟧
  have hBandLe : t0BandB X C₁' M₀
      ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have := t0BandB_grade (X := X) (C₁ := C₁') (M₀ := M₀) hX3
    linarith
  have hBand'0 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
    have h2 : (0 : ℝ) ≤ 9216 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
    linarith
  -- ⟦the Perron defect, to the limit⟧
  refine le_of_forall_pos_le_add (fun eg heg => ?_)
  have hpi := Real.pi_gt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨K, δ, hδ0, hδ1, hEg⟩ :=
    egap_small (X := X) (h := h) hX3 hh4 (show (0 : ℝ) < 2 * Real.pi ^ 2 * eg by positivity)
  have hspine := thm_a2_spine (N := N) (a := a) (X := X) (h := h)
    (Mrow := a2Mrow_L Cs Ccc M Xd X ε) (B₀ := t0BandB X C₁' M₀) (δ := δ) K
    hX hh4 hhX hδ0 hδ1 ha hsupp hN2 hTann hceil hrows hT0band
  refine hspine.trans ?_
  -- monotonicity in `Mrow` and `B₀`, then the `π`-arithmetic
  have hmono : 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * a2Mrow_L Cs Ccc M Xd X ε
            + 205 * Real.pi * t0BandB X C₁' M₀ + 39674880 * Real.pi / h
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))
      ≤ 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * (47520 * a2Level1_L M + 5 * π₀)
            + 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + π₀
                + 9216 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
            + 39674880 * Real.pi * (1 / h)
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2)) := by
    have hpre : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have e1 : 236365 * Real.pi * a2Mrow_L Cs Ccc M Xd X ε
        ≤ 236365 * Real.pi * (47520 * a2Level1_L M + 5 * π₀) :=
      mul_le_mul_of_nonneg_left hMrowLe (by positivity)
    have e2 : 205 * Real.pi * t0BandB X C₁' M₀
        ≤ 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + π₀
            + 9216 * ballSupC ^ 2
              * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hBandLe (by positivity)
    have e3 : 39674880 * Real.pi / h = 39674880 * Real.pi * (1 / h) := by ring
    rw [e3]
    linarith
  refine hmono.trans ?_
  have hscale := spine_scale_pool (p := Real.pi)
    (Mr := 47520 * a2Level1_L M + 5 * π₀)
    (Bd := 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
          * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
    (w := 1 / h) (eg := eg) hpi hMrow'0 hBand'0 (by positivity) hEg
  refine hscale.trans ?_
  have hw : 6315000 * (1 / h) = 6315000 / h := by ring
  rw [hw]
  linarith

/-! ### `ThmA2Pool` :214 — `thm_a2'_of_rows_chiSummed_pool` -/
/-- **⟦R2 — THE `Σ_χ` FROZEN INTERFACE AT A FREE POOL⟧** (`thm_a2'_of_rows_chiSummed_pool_L`).
The character sum of §1's five-summand bound, at a GENERIC `χ`-indexed coefficient family,
INDEXED constant families `Cs Ccc C₁' M₀ ε`, and a **`χ`-FREE pool `π₀`**:

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ ∑_χ 8448·C₁'(χ)²·exp(−M₀(χ)/e)`
`   + φ(q)·[ 1787702400·a2Level1_L M + 188133·π₀`
`          + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)² + 6315000/h ]`.

⟦THE φ(q) LEDGER — WHY THE POOL MUST NOT BE INDEXED⟧ the ledger's mechanism is
`a2_sum_const_chars`: a summand pays one `φ(q)` exactly when it is `χ`-free.  A per-`χ` pool
`π₀ χ` would land the third summand on the `∑_χ` side with the band head, and the single
`φ(q)` payment of KNOT2-SCOPE's accounting would break.  Hence `π₀ : ℝ`, global.

The per-character gates are `hgP1`/`hgRows` (`∀ χ`, at `≤ π₀`) and the two suppliers; the
frame, `hpool`, `hgU` and `hgBand` are character-blind and stay global — `hgU` reads the
`𝒰`-leg exponent at a `χ`-indexed `ε`, so it too is quantified `∀ χ`. -/
theorem thm_a2'_of_rows_chiSummed_pool_L {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h π₀ : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow_L (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum_L M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
    (hgU : ∀ χ : DirichletCharacter ℂ q, (Real.log X) ^ (-theta293 + ε χ) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1_L M
              + 188133 * π₀
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  -- ⟦move 1⟧ §1 at each character's OWN datum and OWN constants, at the SHARED pool
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
        ≤ 8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ)
          + (1787702400 * a2Level1_L M
            + 188133 * π₀
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h) := by
    intro χ _
    have hrow := thm_a2'_of_rows_pool_L (N := N) (M := M) (Xd := Xd) (a := a χ) (X := X) (h := h)
      (Cs := Cs χ) (Ccc := Ccc χ) (C₁' := C₁' χ) (M₀ := M₀ χ) (ε := ε χ) (π₀ := π₀)
      hM hX hX3 hh4 hhX (ha χ) (hsupp χ) hN2 hTann hceil (hrowsSum χ) (hT0bandSum χ)
      hpool (hgP1 χ) (hgRows χ) (hgU χ) hgBand
    refine le_trans hrow (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum, then ⟦move 3⟧ the split: `φ(q)` on the four `χ`-free summands
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [a2_sum_head_split]

/-! ### `ThmA2Pool` :295 — `thm_a2'_of_rows_pool_gk` -/
/-- **thm_A2′ AT THE FREE POOL, AT THE G-LEVER** (`thm_a2'_of_rows_pool_L_gk`). -/
theorem thm_a2'_of_rows_pool_L_gk (K : ℕ) {N M Xd : ℕ} {a : ℕ → ℂ}
    {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
        ≤ a2Mrow_L_gk K Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log X) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  refine thm_a2'_of_rows_pool_L (Xd := Xd) (Cs := Cs)
    (Ccc := Ccc + (M : ℝ) / 2 * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0band hpool ?_ ?_ hgU hgBand
  · intro T h1 h2 h3 h4
    exact (hrows T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow_shift_L_gk K Cs Ccc (M := M) Xd X ε hM).symm)
  · rw [← calP_doorL_one_gk (K := K)]
    exact hgP1
  · rw [a2RowsSum_shift_L_gk K Ccc (M := M) Xd hM]
    exact hgRows

/-! ### `ThmA2Pool` :334 — `thm_a2'_of_rows_chiSummed_pool_gk` -/
/-- **thm_A2′ χ-SUMMED AT THE FREE POOL, AT THE G-LEVER**
(`thm_a2'_of_rows_chiSummed_pool_L_gk`). -/
theorem thm_a2'_of_rows_chiSummed_pool_L_gk (K : ℕ) {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h π₀ : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow_L_gk K (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum_L_gk K M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
    (hgU : ∀ χ : DirichletCharacter ℂ q, (Real.log X) ^ (-theta293 + ε χ) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1_L M
              + 188133 * π₀
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  refine thm_a2'_of_rows_chiSummed_pool_L (Xd := Xd) (Cs := Cs) (Ccc := fun χ =>
      Ccc χ + (M : ℝ) / 2 * (a2RowsSum_L_gk K M Xd - a2RowsSum_L M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0bandSum hpool ?_ ?_ hgU hgBand
  · intro χ T h1 h2 h3 h4
    exact (hrowsSum χ T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow_shift_L_gk K (Cs χ) (Ccc χ) (M := M) Xd X (ε χ) hM).symm)
  · intro χ
    rw [← calP_doorL_one_gk (K := K)]
    exact hgP1 χ
  · intro χ
    rw [a2RowsSum_shift_L_gk K (Ccc χ) (M := M) Xd hM]
    exact hgRows χ

/-! ### `ThmA2Rows` :196 — `a2RowsSum_nonneg` -/
/-- `a2RowsSum_L` is a sum of nonnegative terms (`1 ≤ X_d`, `H₁ ≥ 2`, `P_j ≥ 1`). -/
private lemma a2RowsSum_nonneg_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum_L M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  unfold a2RowsSum_L
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1doorL M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (AdoorL M) (3072 * M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1doorL M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ))
      / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-! ### `ThmA2Rows` :292 — `a2Rows_of_capfree` -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the landed cap-free row at `Tann = 2T`, with ~60
-- binders threaded; the elaboration of that single application is the whole cost
/-- **THE CAP-FREE ROW FAMILY** (`a2Rows_of_capfree_L`).  On the `CapFreeFloor` branch, the
`hrows` binder of `ThmA2.thm_a2'_of_rows_L` — the WEIGHTED seam-row family at the corrected
door pin (`A = AdoorL M`, `G = 3072M`, `Jb = 2`, `H₁ = H1doorL M`, `η = 1/12`) — with the
row's own constants `Cs`, `C` exposed for the interface's two grading gates.

The four weighting numerals are `ThmA2`'s own (`a2Mrow_L`'s docstring), proved in §1 from
`X/h ≤ T`, `2T ≤ X`, `X ≤ 4X_d` (the row's `X ≤ N ≤ 4X_d`), `Q₁ ≤ h` (the `[P₁,Q₁] ⊆ [1,h]`
gate) and `h ≥ 4`.  Nothing is conditional: on this branch the ball leg is VACUOUS
(`t₁ := 0`, `S := 0`) inside the landed capstone, so no station, no produced centre, no
`8S²`. -/
theorem a2Rows_of_capfree_L :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        CapFreeFloor g X →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0 hPlow
    hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW
    hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4
    hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (AdoorL M) (3072 * M) M 2 m₀ Ms Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_L hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one_L hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :440 — `a2Rows_of_cap` -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the landed socketed row at `Tann = 2T`, `t₁ = v₀`
/-- **THE SOCKETED ROW FAMILY** (`a2Rows_of_cap_L`).  On the `¬ CapFreeFloor` branch, the
`hrows` binder of `ThmA2.thm_a2'_of_rows_L`: `CapFreeArm.seam_row_number_nocap` at the ROUTING
WITNESS `t₁ := v₀` (`ThmA2.a2_row_cap_of_not_capFreeFloor` — hence the `800 < loglog X`
threshold, ⟦AMENDMENT E⟧'s T-NEW-1 break-even), with the collision socket supplied by
`CapFreeArm.pocketSocket_of_row` (whose constant `Ccol` is exposed, and whose gate
`collisionGate X 25 Ccol` is carried in-statement).

**CONDITIONAL, in statement, on exactly two named things** (law #253, nothing absorbed):

* `hStation` — the ball-leg supply at grade `Sb`, UNIFORMLY over centres in the box
  `|t₁| ≤ X`.  `SPartStation.seam_ball_leg_station_M_gen` is what supplies it at each fixed
  centre; `a2_station_supply_pointwise` below prints that price with the T3-gap cap
  (`hMcap`), the `M₀` floor and the datum equation as visible binders.  It is carried, not
  derived, because the centre `v₀` is produced inside this proof while the station's
  threshold `X₀` sits under `∀ t₁` in its statement (module docstring, item 2).
* `hCcc` — `C + M·Sb²/2 ≤ Ccc`: the row's `8S²` ball summand paid out of `a2Mrow_L`'s FREE
  constant slot, since `a2Mrow_L` has no `M`-shaped summand of its own.  The analytic
  obligation then surfaces at `thm_a2'_of_rows_L`' `hgRows` gate, read at this `Ccc`.

Everything else is the cap-free branch's list verbatim: §2's single `CapFreeFloor g X`
becomes the five binders `800 < loglog X`, `¬ CapFreeFloor g X`, `collisionGate X 25 Ccol`,
`hStation`, `hCcc` (and the two extra reals `Sb`, `Ccc`); nothing else moves. -/
theorem a2Rows_of_cap_L :
    ∃ Cq cq T₀ X₀ Cs C Ccol : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) → ¬ CapFreeFloor g X →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L Cs Ccc M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_nocap
  obtain ⟨Ccol, hpock⟩ := pocketSocket_of_row
  refine ⟨Cq, cq, T₀, X₀, Cs, C, Ccol, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0
    hPlow hQ0 hQhigh hPQ83 hLL hnfl hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k hMfl0
    hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROUTING WITNESS⟧ the bare-datum cap at `v₀`, and the socket it closes
  obtain ⟨v₀, hv₀box, hv₀cap⟩ := a2_row_cap_of_not_capFreeFloor hLL hnfl
  have hsock : PocketSocket g P Q X theta293 v₀ :=
    hpock g hg P Q X theta293 v₀ hXe hLXe theta293_pos
      (le_of_lt theta293_lt_one_div_32) hPlow hQhigh hPQ83 hv₀box hv₀cap hgate
  -- ⟦THE BALL LEG⟧ the carried supply, read at the produced centre
  have hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ 2 * T → |t - v₀| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - v₀|) :=
    fun t h1 h2 h3 m hm => hStation v₀ hv₀box t h1 (le_trans h2 h2b) h3 m hm
  -- ⟦THE ROW, at `Tann = 2T`, `t₁ = v₀`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (AdoorL M) (3072 * M) M 2 m₀ Ms Mt kk
    (H1doorL M) X (2 * T) v₀ δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2)) Sb
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hSup hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L M Xd := a2RowsSum_nonneg_L hM hXd1
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one_L hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L
  refine a2_row_weigh_cap ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_ball_weigh hw1 hRS0 hC.le hM1' hCcc hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :614 — `thm_a2'` -/
set_option maxHeartbeats 1000000 in
-- the composition: two branch suppliers into `ThmA2.thm_a2'_of_rows_L`, one `by_cases`
/-- **`thm_A2′`** (`thm_a2'_L`).  The frozen five-summand interface of
`ThmA2.thm_a2'_of_rows_L`, with its `hrows` binder DISCHARGED on both branches of the
`CapFreeFloor` dichotomy:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e) + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·(log X)^{−1/500} + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

The side conditions are the union of the two branches' lists (§2's = §3's minus three
binders) with `thm_a2'_of_rows_L`' own, all in-statement.  The two branch constant sets ride
side by side: `(Cq₁,cq₁,T₀₁,X₀₁,Cs₁,C₁)` from `a2Rows_of_capfree_L`,
`(Cq₂,cq₂,T₀₂,X₀₂,Cs₂,C₂)` and the collision constant `Ccol` from `a2Rows_of_cap_L`; FIVE
binders are stated at both (`A2Frame`, `X₀ ≤ kmin`, the `Cq`-gate, and the two grading
gates `hgP1`/`hgRows`) — the two capstones are separate existentials, so their constants
cannot be identified by any consumer.

⚠ CONDITIONAL exactly where §3 is: `hStation` (the ball-leg supply over the box, whose
per-centre price `a2_station_supply_pointwise` prints, T3 cap included) and `hCcc` (the
`8S²` slot).  On the `CapFreeFloor` branch neither is used — that branch is unconditional. -/
theorem thm_a2'_L :
    ∃ Cq₁ cq₁ T₀₁ X₀₁ Cs₁ C₁ Cq₂ cq₂ T₀₂ X₀₂ Cs₂ C₂ Ccol : ℝ,
      0 < Cq₁ ∧ 0 < cq₁ ∧ 3 ≤ T₀₁ ∧ 0 < X₀₁ ∧ 0 < Cs₁ ∧ 0 < C₁ ∧
      0 < Cq₂ ∧ 0 < cq₂ ∧ 3 ≤ T₀₂ ∧ 0 < X₀₂ ∧ 0 < Cs₂ ∧ 0 < C₂ ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc C₁' M₀ : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₁ T₀₁ →
        A2Frame g cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₂ T₀₂ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C₂ + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀₁ ≤ kmin → X₀₂ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq₁ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        1728 * Cq₂ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        3 ≤ X → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
        TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
        (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X C₁' M₀ →
        374784 * Cs₁ * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        374784 * Cs₂ * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum_L M Xd + C₁ * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum_L M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        (0 ≤ ε ∧ ε ≤ theta293 - 1 / 500) →
        4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
        1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
          ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + 1787702400 * a2Level1_L M
            + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h := by
  obtain ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hcapfree⟩ :=
    a2Rows_of_capfree_L
  obtain ⟨Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, hcap⟩ :=
    a2Rows_of_cap_L
  refine ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol,
    hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc C₁' M₀ hM hXdQ F₁ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ
    hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k₁
    hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hCqgate₂ hε0 habs
    hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp hX3 hhX hTann hceil
    hT0band hgP1₁ hgP1₂ hgRows₁ hgRows₂ hεwin hL4096
  -- ⟦R3c⟧ the row's `EP₂` budget is now the ε-GRADED one; the frozen interface still
  -- carries the sharp `(log X)^{−θ₂₉₃}` gate, which is stronger (`ε ≥ 0`, `log X ≥ 1`)
  have hL1 : (1 : ℝ) ≤ Real.log X := le_trans (Real.one_le_exp (by norm_num)) hlX2
  have hEP2ε : 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) :=
    le_trans hEP2 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  by_cases hfl : CapFreeFloor g X
  · exact thm_a2'_of_rows_L hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcapfree g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 hM hXdQ F₁ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV
        hCb0 hPlow hQ0 hQhigh hPQ83 hfl hR0 hRrad hRlow hCbound hX₀k₁ hMfl0 hk2 hkX hkk
        hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hε0 habs hEP2ε hXN hN2 hsupp hNXd hcoef
        hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₁ hgRows₁ hεwin hL4096
  · exact thm_a2'_of_rows_L hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcap g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 Sb Ccc hM hXdQ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1
        hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hfl hgate hStation hCcc hR0 hRrad hRlow
        hCbound hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₂ hε0
        habs hEP2ε hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₂ hgRows₂ hεwin hL4096

/-! ### `ThmA2Rows` :877 — `a2Rows_of_capfree3` -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the `3X`-minted cap-free row at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY, AT THE `3X` MINT** (`a2Rows_of_capfree3_L`).
`a2Rows_of_capfree_L` with its `X`-box inputs replaced by the mint's: the frame is
`CapFreeArm3.A2Frame3` (whose `box` field is the SATISFIABLE `≤ 3X` one) and the row is
`CapFreeArm3.seam_row_number_capfree3`.

⟦THE SOCKET CUT⟧ the third `X`-box input — the datum `CapFreeArm3.CapFreeFloor3` — is GONE,
and with it `g`, `hg`, `ShortIntervalDatum` and the whole `kmin`/`Ymax` ladder.  In their
place the row carries `CofactorSocket … X Rrad 0 R̄ b` at the window's TOP (antitone in the
height, `CofactorSocket.mono`, exactly as `A2Frame3.box_at` is) plus the single grade
`R̄ ≤ gradeCR2 C_b·(log X)^{−ρ₂₉₃}`.  The co-factor datum is the SAME free `b` the
factorization binder already carried.

The weighting arithmetic, the four numerals and the CONCLUSION are §2's verbatim. -/
theorem a2Rows_of_capfree3_L :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_L hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one_L hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :1011 — `a2Rows_of_capfree3_end` -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of the strict/fused `3X`-minted row at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY AT THE `3X` MINT — STRICT/FUSED** (`a2Rows_of_capfree3_end_L`).
`a2Rows_of_capfree3_L` at ⟦THE ENDPOINT WALL⟧'s repair (flags ⟦ENDPOINT-ROW-SCOPE⟧,
⟦ENDPOINT-REF⟧): the inlined pair-law binder carries the STRICT antecedent `X_d < p·m`, and
the row is `CapFreeArm3.seam_row_number_capfree3_end`.

⟦AMENDMENT 1⟧ is what makes this ADDITIVE.  The endpoint mass is absorbed upstream, inside
`M4RowMR.four_rows_le_end`'s unspent `1.5×` on the `B2` slot, so
`seam_row_number_capfree3_end`'s right-hand side is the landed one BYTE FOR BYTE.  Hence
`a2Mrow_L`, `a2RowsSum_L`, `a2_term3_weigh_mr`, `thm_a2'_of_rows_L` and the whole frozen five-
summand interface do not move: this is a new theorem beside `a2Rows_of_capfree3_L`, not a
restatement of it.  The weighting arithmetic, the four numerals and the CONCLUSION are
`a2Rows_of_capfree3_L`'s verbatim. -/
theorem a2Rows_of_capfree3_end_L :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3_end
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_L hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one_L hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :1222 — `a2RowsSum_nonneg_gk` -/
lemma a2RowsSum_nonneg_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum_L_gk K M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  unfold a2RowsSum_L_gk
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1doorL M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (AdoorL M) (s13GK K M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have hlogb : (0 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1doorL M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ))
      / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ) :=
    div_nonneg (by linarith) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-! ### `ThmA2Rows` :1252 — `a2Rows_of_capfree_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem a2Rows_of_capfree_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        CapFreeFloor g X →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0 hPlow
    hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW
    hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4
    hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (AdoorL M) (s13GK K M) M 2 m₀ Ms Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hfloor hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_L_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L_gk K hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := a2Level1_L_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L_gk
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :1377 — `a2Rows_of_cap_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem a2Rows_of_cap_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C Ccol : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) → ¬ CapFreeFloor g X →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L_gk K Cs Ccc M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_nocap
  obtain ⟨Ccol, hpock⟩ := pocketSocket_of_row
  refine ⟨Cq, cq, T₀, X₀, Cs, C, Ccol, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hCb0
    hPlow hQ0 hQhigh hPQ83 hLL hnfl hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k hMfl0
    hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate hε0 habs hEP2 hXN hN2 hsupp
    hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROUTING WITNESS⟧ the bare-datum cap at `v₀`, and the socket it closes
  obtain ⟨v₀, hv₀box, hv₀cap⟩ := a2_row_cap_of_not_capFreeFloor hLL hnfl
  have hsock : PocketSocket g P Q X theta293 v₀ :=
    hpock g hg P Q X theta293 v₀ hXe hLXe theta293_pos
      (le_of_lt theta293_lt_one_div_32) hPlow hQhigh hPQ83 hv₀box hv₀cap hgate
  -- ⟦THE BALL LEG⟧ the carried supply, read at the produced centre
  have hSup : ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ 2 * T → |t - v₀| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - v₀|) :=
    fun t h1 h2 h3 m hm => hStation v₀ hv₀box t h1 (le_trans h2 h2b) h3 m hm
  -- ⟦THE ROW, at `Tann = 2T`, `t₁ = v₀`⟧
  have hinst := hrow g c a b cf hg hc1 hb1 hcf1 N Xd P Q (AdoorL M) (s13GK K M) M 2 m₀ Ms Mt kk
    (H1doorL M) X (2 * T) v₀ δ' V VJ L (1 / 12) Cb Rrad kmin Ymax ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2)) Sb
    hF hH2 hX0 hXe hLXe hL4 hlX2 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hsock hR0 hRrad hRlow (F.blocks _ h2a h2b)
    (F.box_at h2b) hCbound hX₀k hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr
    hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl (F.err _ h2a h2b) hXN hN2 hsupp
    hSup hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, hw1, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hM1' : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L_gk K M Xd := a2RowsSum_nonneg_L_gk K hM hXd1
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L_gk K hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := a2Level1_L_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L_gk
  refine a2_row_weigh_cap ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_ball_weigh hw1 hRS0 hC.le hM1' hCcc hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :1514 — `thm_a2'_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem thm_a2'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq₁ cq₁ T₀₁ X₀₁ Cs₁ C₁ Cq₂ cq₂ T₀₂ X₀₂ Cs₂ C₂ Ccol : ℝ,
      0 < Cq₁ ∧ 0 < cq₁ ∧ 3 ≤ T₀₁ ∧ 0 < X₀₁ ∧ 0 < Cs₁ ∧ 0 < C₁ ∧
      0 < Cq₂ ∧ 0 < cq₂ ∧ 3 ≤ T₀₂ ∧ 0 < X₀₂ ∧ 0 < Cs₂ ∧ 0 < C₂ ∧
      ∀ (g c a b cf : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad kmin Ymax ε EP2 Sb Ccc C₁' M₀ : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame g cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₁ T₀₁ →
        A2Frame g cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq₂ T₀₂ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        0 ≤ Cb → P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X → P ≤ Q →
        800 < Real.log (Real.log X) →
        collisionGate X 25 Ccol →
        (∀ t₁ : ℝ, |t₁| ≤ X → ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ X → |t - t₁| ≤ seamRad X →
          ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ Sb * (m : ℝ) / (1 + |t - t₁|)) →
        C₂ + (M : ℝ) * Sb ^ 2 / 2 ≤ Ccc →
        0 < Rrad → Rrad ≤ seamRad X → seamRad X ≤ Rrad →
        ShortIntervalDatum Cb →
        X₀₁ ≤ kmin → X₀₂ ≤ kmin → 0 ≤ cofactorMfl X theta293 kmin → 2 ≤ kmin → kmin ≤ X →
        (∀ j ∈ ramI (H83 X theta293) P Q, kmin ≤ ((kk j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, pin2Gate ≤ ((Mt j : ℕ) : ℝ)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, ((Mt j : ℕ) : ℝ) ≤ Ymax) →
        (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin →
        pin2Gate ≤ Ymax → Real.log Ymax ≤ 2 * Real.log kmin →
        Real.log X ≤ Real.log Ymax →
        32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293) →
        1728 * Cq₁ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        1728 * Cq₂ * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m → a (p * m) = b m * c p) →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m : ℕ, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → c p * b m ≠ 0 →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        3 ≤ X → h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)) →
        TannGate X (2 * (X / h)) → 5 ≤ Real.log (Real.log (2 * (X / h))) →
        (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X C₁' M₀ →
        374784 * Cs₁ * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        374784 * Cs₂ * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
          ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum_L_gk K M Xd + C₁ * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        5760 * (a2RowsSum_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) →
        (0 ≤ ε ∧ ε ≤ theta293 - 1 / 500) →
        4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250) →
        1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
          ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + 1787702400 * a2Level1_L M
            + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h := by
  obtain ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hcapfree⟩ :=
    a2Rows_of_capfree_L_gk K hK
  obtain ⟨Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, hcap⟩ :=
    a2Rows_of_cap_L_gk K hK
  refine ⟨Cq₁, cq₁, T₀₁, X₀₁, Cs₁, C₁, Cq₂, cq₂, T₀₂, X₀₂, Cs₂, C₂, Ccol,
    hCq₁, hcq₁, hT₀₁, hX₀₁, hCs₁, hC₁, hCq₂, hcq₂, hT₀₂, hX₀₂, hCs₂, hC₂, ?_⟩
  intro g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin Ymax ε
    EP2 Sb Ccc C₁' M₀ hM hXdQ F₁ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ
    hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hgate hStation hCcc hR0 hRrad hRlow hCbound hX₀k₁
    hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hCqgate₂ hε0 habs
    hEP2 hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp hX3 hhX hTann hceil
    hT0band hgP1₁ hgP1₂ hgRows₁ hgRows₂ hεwin hL4096
  -- ⟦R3c⟧ the row's `EP₂` budget is now the ε-GRADED one; the frozen interface still
  -- carries the sharp `(log X)^{−θ₂₉₃}` gate, which is stronger (`ε ≥ 0`, `log X ≥ 1`)
  have hL1 : (1 : ℝ) ≤ Real.log X := le_trans (Real.one_le_exp (by norm_num)) hlX2
  have hEP2ε : 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) :=
    le_trans hEP2 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  by_cases hfl : CapFreeFloor g X
  · exact thm_a2'_of_rows_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcapfree g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 hM hXdQ F₁ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV
        hCb0 hPlow hQ0 hQhigh hPQ83 hfl hR0 hRrad hRlow hCbound hX₀k₁ hMfl0 hk2 hkX hkk
        hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₁ hε0 habs hEP2ε hXN hN2 hsupp hNXd hcoef
        hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₁ hgRows₁ hεwin hL4096
  · exact thm_a2'_of_rows_L_gk K hM hXe hX3 hh4 hhX ha1 hsupp hN2 hTann hceil
      (hcap g c a b cf hg hc1 hb1 hcf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad kmin
        Ymax ε EP2 Sb Ccc hM hXdQ F₂ hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1
        hVδ hlogV hCb0 hPlow hQ0 hQhigh hPQ83 hLL hfl hgate hStation hCcc hR0 hRrad hRlow
        hCbound hX₀k₂ hMfl0 hk2 hkX hkk hMtpin hMt hgateW hYpin hWY hXY hthr hCqgate₂ hε0
        habs hEP2ε hXN hN2 hsupp hNXd hcoef hwin hQXd hXdbig hN4 hdom ha1 hasupp)
      hT0band hgP1₂ hgRows₂ hεwin hL4096

/-! ### `ThmA2Rows` :1631 — `a2Rows_of_capfree3_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem a2Rows_of_capfree3_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (s13GK K M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_L_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L_gk K hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := a2Level1_L_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L_gk
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Rows` :1747 — `a2Rows_of_capfree3_end_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem a2Rows_of_capfree3_end_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow_L_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ := seam_row_number_capfree3_end
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (s13GK K M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a2_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum_L_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum_nonneg_L_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L_gk K hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := a2Level1_L_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow_L_gk
  refine a2_row_weigh ?_ ?_ ?_ ?_
  · exact a2_level1_weigh (fun R' hR' => level1_term_door_decays_L_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a2_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a2_term3_weigh_mr hRS0 hg3
  · exact a2_term4_weigh hZ0 hg32

/-! ### `ThmA2Prime` :54 — `a2Mrow'` -/
/-- **THE FLAT ROW NUMBER — R1** (`a2Mrow'_L`).  `ThmA2.a2Mrow_L` with its Lemma-12 slot read at
the re-priced `ThmA2.a2RowsSum'_L`: the `p²` rows are the `X_d`-FREE constant `24/𝒫ⱼ`.  The
other three summands — the §8.1 level-1 term, the `Cs`-row and the `𝒰`-leg — are
`a2Mrow_L`'s, byte for byte, and the ⟦AMENDMENT G⟧ `×4` cover `5760` never moves. -/
def a2Mrow'_L (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) : ℝ :=
  47520 * a2Level1_L M
    + 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    + 5760 * (a2RowsSum'_L M Xd + C * (2 / (M : ℝ)))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-! ### `ThmA2Prime` :94 — `thm_a2'_of_rows_pool'` -/
/-- **⟦THE R1×R2 JOIN⟧** (`thm_a2'_of_rows_pool'_L`) — `ThmA2Pool.thm_a2'_of_rows_pool_L` with
its row family at `a2Mrow'_L` and its second grading gate at `a2RowsSum'_L`:

  `(1/X)∫_X^{2X} ‖(1/h)·S(x)‖² dx`
  `  ≤ 8448·C₁'²·exp(−M₀/e)`
  `   + 1787702400·(log Q₁)^{1/3}/P₁^{1/12}`
  `   + 188133·π₀`
  `   + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)²`
  `   + 6315000/h`.

⟦THE GATE LIST⟧ against `thm_a2'_of_rows_pool_L`: the frame (`hM`, `hX`, `hX3`, `hh4`, `hhX`,
`ha`, `hsupp`, `hN2`, `hTann`, `hceil`), the band supplier `hT0band` and the four pool gates
`hpool`/`hgP1`/`hgU`/`hgBand` are VERBATIM.  Exactly TWO slots move, in the same direction:
`hrows` reads `a2Mrow'_L` and `hgRows` reads `a2RowsSum'_L`.  Both are the primed — i.e.
SMALLER — objects, so both hypotheses are WEAKER and the conclusion is unchanged: this
theorem is strictly stronger than its R2 sibling, which is strictly stronger than the S8
summit's own `thm_a2'_of_rows_L`.

⟦WHY THE PROOF IS THE POOL TWIN'S, UNCHANGED⟧ `hgRows` enters through exactly one step —
the `linarith` behind `hMrowLe : a2Mrow'_L ≤ 47520·a2Level1_L M + 5·π₀` — and it enters as a
bound on the row number's third summand, whichever sum sits inside it.  Nothing downstream
of `hMrowLe` mentions the rows at all. -/
theorem thm_a2'_of_rows_pool'_L {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow'_L Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log X) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hh0 : (0 : ℝ) < h := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hLL0 : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hrp13 : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hL0 _
  -- the level-1 grade is nonnegative
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hP64 := calP_door_one_ge_L hM
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    have h1 : (0 : ℝ) ≤ (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      Real.rpow_nonneg (by linarith) _
    have h2 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_pos_of_pos (by linarith) _
    exact div_nonneg h1 h2.le
  -- ⟦the PRIMED row number, graded AT THE POOL⟧ — three sources, `1 + 1 + 3` copies
  have hMrowLe : a2Mrow'_L Cs Ccc M Xd X ε ≤ 47520 * a2Level1_L M + 5 * π₀ := by
    unfold a2Mrow'_L
    linarith
  have hMrow'0 : (0 : ℝ) ≤ 47520 * a2Level1_L M + 5 * π₀ := by linarith
  -- ⟦the band, graded, with the `4096` summand absorbed INTO THE POOL⟧
  have hBandLe : t0BandB X C₁' M₀
      ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have := t0BandB_grade (X := X) (C₁ := C₁') (M₀ := M₀) hX3
    linarith
  have hBand'0 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
    have h2 : (0 : ℝ) ≤ 9216 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
    linarith
  -- ⟦the Perron defect, to the limit⟧
  refine le_of_forall_pos_le_add (fun eg heg => ?_)
  have hpi := Real.pi_gt_d6
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨K, δ, hδ0, hδ1, hEg⟩ :=
    egap_small (X := X) (h := h) hX3 hh4 (show (0 : ℝ) < 2 * Real.pi ^ 2 * eg by positivity)
  have hspine := thm_a2_spine (N := N) (a := a) (X := X) (h := h)
    (Mrow := a2Mrow'_L Cs Ccc M Xd X ε) (B₀ := t0BandB X C₁' M₀) (δ := δ) K
    hX hh4 hhX hδ0 hδ1 ha hsupp hN2 hTann hceil hrows hT0band
  refine hspine.trans ?_
  -- monotonicity in `Mrow` and `B₀`, then the `π`-arithmetic
  have hmono : 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * a2Mrow'_L Cs Ccc M Xd X ε
            + 205 * Real.pi * t0BandB X C₁' M₀ + 39674880 * Real.pi / h
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2))
      ≤ 1 / (2 * Real.pi ^ 2)
        * (236365 * Real.pi * (47520 * a2Level1_L M + 5 * π₀)
            + 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
                + π₀
                + 9216 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
            + 39674880 * Real.pi * (1 / h)
            + (34560 * δ * (Real.pi + 2 * Real.log (1 + 2 ^ K * (X / h))) ^ 2
              + 1152 * (12 * h / (2 ^ K * δ)
                  + (8 * h / 2 ^ K) * (1 + Real.log (3 * X))) ^ 2)) := by
    have hpre : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hpre
    have e1 : 236365 * Real.pi * a2Mrow'_L Cs Ccc M Xd X ε
        ≤ 236365 * Real.pi * (47520 * a2Level1_L M + 5 * π₀) :=
      mul_le_mul_of_nonneg_left hMrowLe (by positivity)
    have e2 : 205 * Real.pi * t0BandB X C₁' M₀
        ≤ 205 * Real.pi * (256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
            + π₀
            + 9216 * ballSupC ^ 2
              * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hBandLe (by positivity)
    have e3 : 39674880 * Real.pi / h = 39674880 * Real.pi * (1 / h) := by ring
    rw [e3]
    linarith
  refine hmono.trans ?_
  have hscale := spine_scale_prime (p := Real.pi)
    (Mr := 47520 * a2Level1_L M + 5 * π₀)
    (Bd := 256 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + π₀
        + 9216 * ballSupC ^ 2
          * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2))
    (w := 1 / h) (eg := eg) hpi hMrow'0 hBand'0 (by positivity) hEg
  refine hscale.trans ?_
  have hw : 6315000 * (1 / h) = 6315000 / h := by ring
  rw [hw]
  linarith

/-! ### `ThmA2Prime` :239 — `thm_a2'_of_rows_chiSummed_pool'` -/
/-- **⟦THE R1×R2 JOIN, `Σ_χ`⟧** (`thm_a2'_of_rows_chiSummed_pool'_L`).  §2's character sum, at
a generic `χ`-indexed coefficient family, INDEXED constant families `Cs Ccc C₁' M₀ ε`, and a
`χ`-FREE pool `π₀`:

`∑_χ (1/X)∫_X^{2X} ‖(1/h)·S_χ(x)‖² dx`
`  ≤ ∑_χ 8448·C₁'(χ)²·exp(−M₀(χ)/e)`
`   + φ(q)·[ 1787702400·a2Level1_L M + 188133·π₀`
`          + 304128·ballSupC²·(log X)^{−43/45}·(1+loglog X)² + 6315000/h ]`.

⟦THE φ(q) LEDGER IS UNTOUCHED BY R1⟧ `a2RowsSum'_L` sits inside the per-character `hgRows`,
which was already on the `∀ χ` side; the pool stays global for exactly the reason
`ThmA2Pool` records (a per-`χ` pool would move the third summand onto the `∑_χ` side and
break the single `φ(q)` payment). -/
theorem thm_a2'_of_rows_chiSummed_pool'_L {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h π₀ : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow'_L (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum'_L M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
    (hgU : ∀ χ : DirichletCharacter ℂ q, (Real.log X) ^ (-theta293 + ε χ) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1_L M
              + 188133 * π₀
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  -- ⟦move 1⟧ §2 at each character's OWN datum and OWN constants, at the SHARED pool
  have hper : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
      1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
        ≤ 8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ)
          + (1787702400 * a2Level1_L M
            + 188133 * π₀
            + 304128 * ballSupC ^ 2
                * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
            + 6315000 / h) := by
    intro χ _
    have hrow := thm_a2'_of_rows_pool'_L (N := N) (M := M) (Xd := Xd) (a := a χ) (X := X) (h := h)
      (Cs := Cs χ) (Ccc := Ccc χ) (C₁' := C₁' χ) (M₀ := M₀ χ) (ε := ε χ) (π₀ := π₀)
      hM hX hX3 hh4 hhX (ha χ) (hsupp χ) hN2 hTann hceil (hrowsSum χ) (hT0bandSum χ)
      hpool (hgP1 χ) (hgRows χ) (hgU χ) hgBand
    refine le_trans hrow (le_of_eq ?_)
    ring
  -- ⟦move 2⟧ the character sum, then ⟦move 3⟧ the split: `φ(q)` on the four `χ`-free summands
  refine le_trans (Finset.sum_le_sum hper) ?_
  rw [a2_sum_head_split]

/-! ### `ThmA2Prime` :317 — `thm_a2'_of_rows'` -/
/-- **thm_A2′ AT THE PRIMED ROW SUM** (`thm_a2'_of_rows'_L`) — `ThmA2.thm_a2'_of_rows_L` with
`a2Mrow_L ↦ a2Mrow'_L` and `a2RowsSum_L ↦ a2RowsSum'_L`, the frozen conclusion BYTE-IDENTICAL.

⟦THE S8 SUMMIT BECOMES STRICTLY STRONGER⟧ — this is that sentence as a kernel object: the
hypothesis list differs from the landed one in exactly two slots, both of which name the
SMALLER (`a2RowsSum'_L ≤ a2RowsSum_L`, `a2Mrow'_L ≤ a2Mrow_L`) object, and the conclusion is the
frozen one unchanged. -/
theorem thm_a2'_of_rows'_L {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2) ≤ a2Mrow'_L Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum'_L M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hrp500 : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hL0 _
  -- ⟦the `𝒰`-leg gate⟧ the landed derivation from `hεwin`
  have hgU : (Real.log X) ^ (-theta293 + ε) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hθ : theta293 < 1 / 32 := theta293_lt_one_div_32
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hεwin.1, hεwin.2])
  -- ⟦the band absorption⟧ the landed derivation from `hL4096`
  have hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500)
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hsp : (Real.log X) ^ (-(1 : ℝ) / 500)
        = (Real.log X) ^ (1 - (1 : ℝ) / 250) * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [hsp]
    exact mul_le_mul_of_nonneg_right hL4096
      (le_of_lt (Real.rpow_pos_of_pos hL0 _))
  exact thm_a2'_of_rows_pool'_L hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil hrows hT0band
    hrp500.le hgP1 hgRows hgU hgBand

/-! ### `ThmA2Prime` :377 — `a2Mrow'_gk` -/
/-- **THE FLAT ROW NUMBER — R1, AT THE G-LEVER** (`a2Mrow'_L_gk`). -/
noncomputable def a2Mrow'_L_gk (K : ℕ) (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) : ℝ :=
  47520 * a2Level1_L M
    + 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    + 5760 * (a2RowsSum'_L_gk K M Xd + C * (2 / (M : ℝ)))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-! ### `ThmA2Prime` :391 — `a2RowsSum'_shift_gk` -/
/-- ⟦THE `Ccc`-SHIFT⟧ at the primed row sum. -/
lemma a2RowsSum'_shift_L_gk (K : ℕ) (C : ℝ) {M : ℕ} (Xd : ℕ) (hM : 1 ≤ M) :
    a2RowsSum'_L M Xd + (C + (M : ℝ) / 2 * (a2RowsSum'_L_gk K M Xd - a2RowsSum'_L M Xd))
        * (2 / (M : ℝ))
      = a2RowsSum'_L_gk K M Xd + C * (2 / (M : ℝ)) := by
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hcancel : (M : ℝ) / 2 * (2 / (M : ℝ)) = 1 := by field_simp
  have hexp : (C + (M : ℝ) / 2 * (a2RowsSum'_L_gk K M Xd - a2RowsSum'_L M Xd)) * (2 / (M : ℝ))
      = C * (2 / (M : ℝ))
        + ((M : ℝ) / 2 * (2 / (M : ℝ))) * (a2RowsSum'_L_gk K M Xd - a2RowsSum'_L M Xd) := by
    ring
  rw [hexp, hcancel]
  ring

/-! ### `ThmA2Prime` :405 — `a2Mrow'_shift_gk` -/
/-- ⟦THE `Ccc`-SHIFT⟧ at the primed row number. -/
lemma a2Mrow'_shift_L_gk (K : ℕ) (Cs C : ℝ) {M : ℕ} (Xd : ℕ) (X ε : ℝ) (hM : 1 ≤ M) :
    a2Mrow'_L Cs (C + (M : ℝ) / 2 * (a2RowsSum'_L_gk K M Xd - a2RowsSum'_L M Xd)) M Xd X ε
      = a2Mrow'_L_gk K Cs C M Xd X ε := by
  rw [a2Mrow'_L, a2Mrow'_L_gk, calP_doorL_one_gk, a2RowsSum'_shift_L_gk K C Xd hM]

/-! ### `ThmA2Prime` :411 — `thm_a2'_of_rows_pool'_gk` -/
/-- **⟦THE R1×R2 JOIN⟧ AT THE G-LEVER** (`thm_a2'_of_rows_pool'_L_gk`). -/
theorem thm_a2'_of_rows_pool'_L_gk (K : ℕ) {N M Xd : ℕ} {a : ℕ → ℂ}
    {X h Cs Ccc C₁' M₀ ε π₀ : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
        ≤ a2Mrow'_L_gk K Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hpool : 0 ≤ π₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : 5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ))) ≤ π₀)
    (hgU : (Real.log X) ^ (-theta293 + ε) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * π₀
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  refine thm_a2'_of_rows_pool'_L (Xd := Xd) (Cs := Cs)
    (Ccc := Ccc + (M : ℝ) / 2 * (a2RowsSum'_L_gk K M Xd - a2RowsSum'_L M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0band hpool ?_ ?_ hgU hgBand
  · intro T h1 h2 h3 h4
    exact (hrows T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow'_shift_L_gk K Cs Ccc (M := M) Xd X ε hM).symm)
  · rw [← calP_doorL_one_gk (K := K)]
    exact hgP1
  · rw [a2RowsSum'_shift_L_gk K Ccc (M := M) Xd hM]
    exact hgRows

/-! ### `ThmA2Prime` :450 — `thm_a2'_of_rows_chiSummed_pool'_gk` -/
/-- **⟦THE R1×R2 JOIN, χ-SUMMED⟧ AT THE G-LEVER**
(`thm_a2'_of_rows_chiSummed_pool'_L_gk`). -/
theorem thm_a2'_of_rows_chiSummed_pool'_L_gk (K : ℕ) {q : ℕ} [NeZero q] {N M Xd : ℕ}
    {a : DirichletCharacter ℂ q → ℕ → ℂ} {X h π₀ : ℝ}
    {Cs Ccc C₁' M₀ ε : DirichletCharacter ℂ q → ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, ‖a χ n‖ ≤ 1)
    (hsupp : ∀ χ : DirichletCharacter ℂ q, ∀ n : ℕ, (n : ℝ) ≤ X → a χ n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrowsSum : ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X →
      TannGate X (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N (a χ) t‖ ^ 2)
        ≤ a2Mrow'_L_gk K (Cs χ) (Ccc χ) M Xd X (ε χ))
    (hT0bandSum : ∀ χ : DirichletCharacter ℂ q,
      (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA (a χ) (seamS0 N X) t‖ ^ 2)
        ≤ t0BandB X (C₁' χ) (M₀ χ))
    (hpool : 0 ≤ π₀)
    (hgP1 : ∀ χ : DirichletCharacter ℂ q,
      374784 * Cs χ * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hgRows : ∀ χ : DirichletCharacter ℂ q,
      5760 * (a2RowsSum'_L_gk K M Xd + Ccc χ * (2 / (M : ℝ))) ≤ π₀)
    (hgU : ∀ χ : DirichletCharacter ℂ q, (Real.log X) ^ (-theta293 + ε χ) ≤ π₀)
    (hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) ≤ π₀) :
    ∑ χ : DirichletCharacter ℂ q,
        1 / X * (∫ x in X..(2 * X),
          ‖((1 / h : ℝ) : ℂ) * shortSum (a χ) (seamS0 N X) x h‖ ^ 2)
      ≤ (∑ χ : DirichletCharacter ℂ q,
            8448 * C₁' χ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀ χ))
        + (q.totient : ℝ)
            * (1787702400 * a2Level1_L M
              + 188133 * π₀
              + 304128 * ballSupC ^ 2
                  * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
              + 6315000 / h) := by
  refine thm_a2'_of_rows_chiSummed_pool'_L (Xd := Xd) (Cs := Cs) (Ccc := fun χ =>
      Ccc χ + (M : ℝ) / 2 * (a2RowsSum'_L_gk K M Xd - a2RowsSum'_L M Xd))
    hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil ?_ hT0bandSum hpool ?_ ?_ hgU hgBand
  · intro χ T h1 h2 h3 h4
    exact (hrowsSum χ T h1 h2 h3 h4).trans
      (le_of_eq (a2Mrow'_shift_L_gk K (Cs χ) (Ccc χ) (M := M) Xd X (ε χ) hM).symm)
  · intro χ
    rw [← calP_doorL_one_gk (K := K)]
    exact hgP1 χ
  · intro χ
    rw [a2RowsSum'_shift_L_gk K (Ccc χ) (M := M) Xd hM]
    exact hgRows χ

/-! ### `ThmA2Prime` :501 — `thm_a2'_of_rows'_gk` -/
/-- **thm_A2′ AT THE PRIMED ROW SUM, AT THE G-LEVER** (`thm_a2'_of_rows'_L_gk`) — the frozen
five-summand conclusion, BYTE-IDENTICAL, carrying the two WEAKEST gates of the whole family:
the primed row sum AND the lever's larger `𝒫₂`. -/
theorem thm_a2'_of_rows'_L_gk (K : ℕ) {N M Xd : ℕ} {a : ℕ → ℂ} {X h Cs Ccc C₁' M₀ ε : ℝ}
    (hM : 1 ≤ M)
    (hX : Real.exp 1 ≤ X) (hX3 : 3 ≤ X) (hh4 : 4 ≤ h)
    (hhX : h ≤ X * (Real.log X) ^ (-(1 / 5 : ℝ)))
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hN2 : (N : ℝ) ≤ 2 * X)
    (hTann : TannGate X (2 * (X / h)))
    (hceil : 5 ≤ Real.log (Real.log (2 * (X / h))))
    (hrows : ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
      5 ≤ Real.log (Real.log (2 * T)) →
      X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
        ≤ a2Mrow'_L_gk K Cs Ccc M Xd X ε)
    (hT0band : (∫ t in (-(seamT0 X))..(seamT0 X),
      ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ t0BandB X C₁' M₀)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hgRows : 5760 * (a2RowsSum'_L_gk K M Xd + Ccc * (2 / (M : ℝ)))
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500))
    (hεwin : 0 ≤ ε ∧ ε ≤ theta293 - 1 / 500)
    (hL4096 : 4096 ≤ (Real.log X) ^ (1 - (1 : ℝ) / 250)) :
    1 / X * (∫ x in X..(2 * X), ‖((1 / h : ℝ) : ℂ) * shortSum a (seamS0 N X) x h‖ ^ 2)
      ≤ 8448 * C₁' ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        + 1787702400 * a2Level1_L M
        + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        + 304128 * ballSupC ^ 2
            * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        + 6315000 / h := by
  have hL1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hrp500 : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hL0 _
  have hgU : (Real.log X) ^ (-theta293 + ε) ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hθ : theta293 < 1 / 32 := theta293_lt_one_div_32
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [hεwin.1, hεwin.2])
  have hgBand : 4096 * (Real.log X) ^ (-(1 : ℝ) + 1 / 500)
      ≤ (Real.log X) ^ (-(1 : ℝ) / 500) := by
    have hsp : (Real.log X) ^ (-(1 : ℝ) / 500)
        = (Real.log X) ^ (1 - (1 : ℝ) / 250) * (Real.log X) ^ (-(1 : ℝ) + 1 / 500) := by
      rw [← Real.rpow_add hL0]; norm_num
    rw [hsp]
    exact mul_le_mul_of_nonneg_right hL4096
      (le_of_lt (Real.rpow_pos_of_pos hL0 _))
  exact thm_a2'_of_rows_pool'_L_gk K hM hX hX3 hh4 hhX ha hsupp hN2 hTann hceil hrows hT0band
    hrp500.le hgP1 hgRows hgU hgBand

/-! ### `A3Middle` :162 — `a2RowsSum'_nonneg` -/
/-- `ThmA2.a2RowsSum'_L` is a sum of nonnegative terms — `ThmA2Rows.a2RowsSum_nonneg_L`'s twin,
and STRICTLY easier: the `p²` slot is the constant `24/𝒫ⱼ`, so the `log₂(2X_d) ≥ 0` step of
the landed proof disappears. -/
private lemma a2RowsSum'_nonneg_L {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum'_L M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  unfold a2RowsSum'_L
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1doorL M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (AdoorL M) (3072 * M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1doorL M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 24 / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) :=
    div_nonneg (by norm_num) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-! ### `A3Middle` :424 — `a2Rows_of_capfree3_end'` -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of §3 at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY AT THE `3X` MINT — STRICT/FUSED, R1**
(`a2Rows_of_capfree3_end'_L`) — **THE A3 MIDDLE'S EXIT**.
`ThmA2Rows.a2Rows_of_capfree3_end_L`'s twin over §3, landing at `ThmA2Prime.a2Mrow'_L`.

The hypothesis list, the weighting arithmetic and the four numerals `9`/`244`/`3`/`3/2` are
the landed theorem's verbatim; the ONLY change is the object the third weighing step lands
in — `a2RowsSum'_L` in place of `a2RowsSum_L`, which `a3_term3_weigh_mr` is blind to (it prices
`960·R·S ≤ 5760·S` for ANY nonnegative `S`).

This is the supplier `ThmA2Prime.thm_a2'_of_rows_pool'_L`'s `hrows` binder asks for, and it is
the only one: the primed slot admits no landed-form row. -/
theorem a2Rows_of_capfree3_end'_L :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow'_L Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ :=
    seam_row_number_capfree3_end'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint, at the PRIMED bracket⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a3_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum'_L M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum'_nonneg_L hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one_L hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow'_L
  refine a3_row_weigh ?_ ?_ ?_ ?_
  · exact a3_level1_weigh (fun R' hR' => level1_term_door_decays_L hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a3_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a3_term3_weigh_mr hRS0 hg3
  · exact a3_term4_weigh hZ0 hg32

/-! ### `A3Middle` :791 — `a2Rows_of_capfree3'` -/
set_option maxHeartbeats 1000000 in
-- one predicate-blind application of ⟦R1⟧'s `3X`-minted cap-free row at `Tann = 2T`
/-- **THE CAP-FREE ROW FAMILY AT THE `3X` MINT — R1** (`a2Rows_of_capfree3'_L`) —
**THE A3 MIDDLE'S CLOSED-WINDOW EXIT**.  `ThmA2Rows.a2Rows_of_capfree3_L`'s twin over §6,
landing at `ThmA2Prime.a2Mrow'_L`.

This is the arm `M4MeanSq.m4_meansq_per_chi_gen_L` consumes (its coefficient binder carries the
CLOSED window `X_d ≤ p·m`), so it is the supplier the joined capstone
`M4MeanSqPrime.m4_meansq_per_chi_gen_join_L` needs.  §4's `a2Rows_of_capfree3_end'_L` is the
strict/fused sibling, for the door's own half-open cut.

The hypothesis list, the weighting arithmetic and the four numerals are the landed theorem's
verbatim; the only change is the object the third weighing step lands in. -/
theorem a2Rows_of_capfree3'_L :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (3072 * M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (3072 * M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (3072 * M) j ≤ p →
          p ≤ calQK (AdoorL M) (3072 * M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (3072 * M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (3072 * M) j)
                    (calQK (AdoorL M) (3072 * M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (3072 * M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow'_L Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ :=
    seam_row_number_capfree3'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (3072 * M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L M Xd hM hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (3072 * M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a3_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum'_L M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum'_nonneg_L hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := by
    unfold a2Level1_L
    exact div_nonneg
      (Real.rpow_nonneg (le_trans (by norm_num) (one_le_log_calQK_door_one_L hM)) _)
      (Real.rpow_pos_of_pos hP0 _).le
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow'_L
  refine a3_row_weigh ?_ ?_ ?_ ?_
  · exact a3_level1_weigh (fun R' hR' => level1_term_door_decays_L hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a3_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a3_term3_weigh_mr hRS0 hg3
  · exact a3_term4_weigh hZ0 hg32

/-! ### `A3Middle` :932 — `a2RowsSum'_nonneg_gk` -/
lemma a2RowsSum'_nonneg_L_gk (K : ℕ) {M Xd : ℕ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd) :
    0 ≤ a2RowsSum'_L_gk K M Xd := by
  have hXd1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hH1 : (2 : ℝ) ≤ H1doorL M := H1door_two_L hM
  unfold a2RowsSum'_L_gk
  refine Finset.sum_nonneg (fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hcalH : (0 : ℝ) < calH (H1doorL M) j := by
    rw [calH]; nlinarith
  have hP1 : (1 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ) := by
    have h : 1 ≤ calP (AdoorL M) (s13GK K M) j := by
      simp only [calP]; exact Nat.one_le_two_pow
    exact_mod_cast h
  have h1 : (0 : ℝ) ≤ (Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
      * (Real.exp 1 / (Xd : ℝ) ^ 2)) := by
    have hq : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j :=
      div_nonneg (by positivity) hcalH.le
    have hr : (0 : ℝ) ≤ Real.exp 1 / (Xd : ℝ) ^ 2 := by positivity
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.exp 1 * (Xd : ℝ)
      / calH (H1doorL M) j + 1) hr
    nlinarith
  have h2 : (0 : ℝ) ≤ 24 / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ) :=
    div_nonneg (by norm_num) (by linarith)
  have h3 : (0 : ℝ) ≤ 1 / (Xd : ℝ) := by positivity
  linarith

/-! ### `A3Middle` :959 — `a2Rows_of_capfree3_end'_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem a2Rows_of_capfree3_end'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
          (Xd : ℝ) < (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ :=
    seam_row_number_capfree3_end'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint, at the PRIMED bracket⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (s13GK K M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a3_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum'_L_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum'_nonneg_L_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L_gk K hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := a2Level1_L_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow'_L_gk
  refine a3_row_weigh ?_ ?_ ?_ ?_
  · exact a3_level1_weigh (fun R' hR' => level1_term_door_decays_L_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a3_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a3_term3_weigh_mr hRS0 hg3
  · exact a3_term4_weigh hZ0 hg32

/-! ### `A3Middle` :1075 — `a2Rows_of_capfree3'_gk` -/
set_option maxHeartbeats 1000000 in
-- the landed budget, replayed: this twin re-elaborates the same ~60-binder
-- application once more at the linear anchor; the cost is the binder list, not the proof
theorem a2Rows_of_capfree3'_L_gk (K : ℕ) (hK : K ≤ 170000000) :
    ∃ Cq cq T₀ X₀ Cs C : ℝ, 0 < Cq ∧ 0 < cq ∧ 3 ≤ T₀ ∧ 0 < X₀ ∧ 0 < Cs ∧ 0 < C ∧
      ∀ (c a b cf : ℕ → ℂ) (bfam : ℕ → ℕ → ℂ), (∀ n : ℕ, ‖c n‖ ≤ 1) →
        (∀ n : ℕ, ‖b n‖ ≤ 1) → (∀ n : ℕ, ‖cf n‖ ≤ 1) → (∀ j n : ℕ, ‖bfam j n‖ ≤ 1) →
      ∀ (N Xd P Q M : ℕ) (m₀ Ms Mt kk : ℕ → ℕ),
      ∀ (X h δ' V VJ L Cb Rrad Rbar ε EP2 : ℝ),
        1 ≤ M → calQK (AdoorL M) (s13GK K M) M 2 ≤ Xd →
        A2Frame3 b cf a N Xd P Q (AdoorL M) (s13GK K M) M 2 Ms Mt kk (H1doorL M) X h δ' VJ L
          (1 / 12) Cb Rrad EP2 cq T₀ →
        2 ≤ H83 X theta293 →
        Real.exp 1 ≤ X → Real.exp 2 ≤ Real.log X →
        4 ≤ h → ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) ≤ h →
        Real.exp 1 ≤ L →
        Real.exp (mrAlpha (1 / 12) 2
            * Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ)) ≤ VJ →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ramRrange (H83 X theta293) N Xd j ⊆ Finset.Icc 1 (Ms j)) →
        (∀ j ∈ ramI (H83 X theta293) P Q, 2 ≤ m₀ j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 X theta293) Xd j) →
        (∀ j ∈ ramI (H83 X theta293) P Q,
          ((Ms j : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) →
        1 ≤ V → V⁻¹ ≤ δ' → Real.log V ≤ 100 * Real.log L →
        P83 X theta293 ≤ (P : ℝ) → 0 < Q → (Q : ℝ) ≤ Q83 X →
        Rrad ≤ seamRad X →
        -- ⟦THE ONE NEW DATUM⟧ the co-factor socket at the window's TOP, and its grade
        0 ≤ Rbar → Rbar ≤ gradeCR2 Cb * (Real.log X) ^ (-rho293) →
        CofactorSocket (H83 X theta293) N Xd P Q X Rrad 0 Rbar b →
        1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log X) ^ (2 * theta293) →
        0 ≤ ε → 8640 ≤ (Real.log X) ^ ε → 12 * EP2 ≤ (Real.log X) ^ (-theta293 + ε) →
        X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        2 * Xd ≤ N →
        (∀ j ∈ Finset.Icc 1 2, ∀ p m, p.Prime → calP (AdoorL M) (s13GK K M) j ≤ p →
          p ≤ calQK (AdoorL M) (s13GK K M) M j → ¬ p ∣ m →
          (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) → (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ) →
          a (p * m) = bfam j m * c p) →
        Real.log ((calQK (AdoorL M) (s13GK K M) M 2 : ℕ) : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (100 : ℝ) ≤ Real.sqrt (Real.log (Xd : ℝ)) →
        (N : ℝ) ≤ 4 * (Xd : ℝ) →
        (∀ j ∈ Finset.Icc 1 2,
          ((Nat.sqrt Xd : ℝ) + 1)
              * ∏ p ∈ primeBand (calP (AdoorL M) (s13GK K M) j)
                    (calQK (AdoorL M) (s13GK K M) M j), (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
                / Real.log ((calQK (AdoorL M) (s13GK K M) M j : ℕ) : ℝ))) →
        (∀ n : ℕ, ‖a n‖ ≤ 1) →
        (∀ n : ℕ, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        ∀ T : ℝ, X / h ≤ T → 2 * T ≤ X → TannGate X (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          X / h / T * (∫ t in seamAnn X (2 * T), ‖spoly N a t‖ ^ 2)
            ≤ a2Mrow'_L_gk K Cs C M Xd X ε := by
  obtain ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, hrow⟩ :=
    seam_row_number_capfree3'
  refine ⟨Cq, cq, T₀, X₀, Cs, C, hCq, hcq, hT₀, hX₀0, hCs, hC, ?_⟩
  intro c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q M m₀ Ms Mt kk X h δ' V VJ L Cb Rrad Rbar ε
    EP2 hM hXdQ F hH2 hXe hlX2 hh4 hQ1h hLe hVJg hMs hm₀2 hm₀ hMs4 hV1 hVδ hlogV hPlow
    hQ0 hQhigh hRrad hRbar0 hRgrade hsockR hCqgate hε0 habs hEP2 hXN hN2 hsupp hNXd hcoef
    hQXd hXdbig hN4 hdom ha1 hasupp T hT hTX2 hTgate hTll
  -- ⟦the scale page⟧
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hsplit : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_gt_d9]
  have hLXe : Real.exp 1 ≤ Real.log X :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hlX2
  have hL4 : (4 : ℝ) ≤ Real.log X := le_trans he2 hlX2
  have hL0 : (0 : ℝ) ≤ Real.log X := by linarith
  have hXd1 : 1 ≤ Xd := le_trans (one_le_calQK (AdoorL M) (s13GK K M) M 2) hXdQ
  have hXd1' : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd1
  have hX4Xd : X ≤ 4 * (Xd : ℝ) := le_trans hXN hN4
  have hQ10 : (0 : ℝ) ≤ ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  -- ⟦the frame at the row's own scale⟧
  have hF := calFrameK_doorH1_at_L_gk K M Xd hM hK hXdQ
  -- ⟦the window's two endpoints, at `Tann = 2T`⟧
  have h2a : 2 * (X / h) ≤ 2 * T := by linarith
  have h2b : (2 : ℝ) * T ≤ X := hTX2
  have h2T0 : (0 : ℝ) < 2 * T := by
    have : (0 : ℝ) < X / h := div_pos hX0 (by linarith)
    linarith
  -- ⟦THE ROW, at `Tann = 2T`, at the `3X` mint⟧
  have hinst := hrow c a b cf bfam hc1 hb1 hcf1 hbf1 N Xd P Q (AdoorL M) (s13GK K M) M 2 m₀ Ms
    Mt kk
    (H1doorL M) X (2 * T) δ' V VJ L (1 / 12) Cb Rrad Rbar ε EP2
    (3 * (720 * (2 * T / X + 1) / H83 X theta293 + EP2))
    hF hH2 hX0 hXe hLXe hL4 hTgate (F.one_lt _ h2a h2b) h2b (F.T0_le _ h2a h2b) hTll
    (F.one_le_log _ h2a h2b) (F.log_le_L _ h2a h2b) hLe hVJg hMs (F.thin _ h2a h2b) hm₀2 hm₀
    hMs4 hV1 hVδ hlogV hPlow hQ0 hQhigh hRrad hRbar0 hRgrade (hsockR.mono h2b)
    (F.blocks _ h2a h2b) hCqgate (F.ksGate_at h2T0 h2b hL0) hε0 habs hEP2 le_rfl
    (F.err _ h2a h2b) hXN hN2 hsupp hNXd hcoef hQXd hXdbig hN4 hdom ha1 hasupp
  -- ⟦THE WEIGHTING⟧
  obtain ⟨hw0, -, hg9, hg244, hg3, hg32⟩ :=
    a3_weight_gates (X := X) (h := h) (T := T) (Xd := (Xd : ℝ))
      (Q1 := ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) hh4 hX0 hT hX4Xd hQ1h hQ10
  refine (mul_le_mul_of_nonneg_left hinst hw0).trans ?_
  have hRS0 : (0 : ℝ) ≤ a2RowsSum'_L_gk K M Xd + C * (2 / (M : ℝ)) := by
    have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ C * (2 / (M : ℝ)) := by positivity
    linarith [a2RowsSum'_nonneg_L_gk K hM hXd1]
  have hZ0 : (0 : ℝ) ≤ (Real.log X) ^ (-theta293 + ε) :=
    Real.rpow_nonneg hL0 _
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
    linarith [calP_door_one_ge_L_gk K hM]
  have hlvl0 : (0 : ℝ) ≤ a2Level1_L M := a2Level1_L_nonneg hM
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (div_pos hX0 (by linarith)) hT
  have hRnn : (0 : ℝ) ≤ 2 * T * ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) / (Xd : ℝ) + 1 := by
    have := div_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * T) hQ10)
      (by linarith : (0 : ℝ) ≤ (Xd : ℝ))
    linarith
  unfold a2Mrow'_L_gk
  refine a3_row_weigh ?_ ?_ ?_ ?_
  · exact a3_level1_weigh (fun R' hR' => level1_term_door_decays_L_gk K hM hR')
      (mul_nonneg hw0 hRnn) hg9 hlvl0
  · exact a3_term2_weigh hCs.le (div_pos one_pos hP0).le hg244
  · exact a3_term3_weigh_mr hRS0 hg3
  · exact a3_term4_weigh hZ0 hg32

end Salt.MR

end
