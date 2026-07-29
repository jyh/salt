/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TLegKill
import Salt.MR.TLegE1
import Salt.MR.USetBalance
import Salt.MR.USetPrice

/-!
# TLegExit — the level-`j` page, the `j`-collection and the graded `𝒯`-leg (ROUTE G, `G5`)

`docs/exploration/hsup-design.md` ⟦V6⟧'s Route-G ladder, node `G5`: MR §8.2's level-`j` page
assembled (`Ej_bound`), MR's `α`-sequence gates read off eq (20) (`alpha_gates_from_eta`), the
`j`-collection (`sum_Ej_collected`) and the whole graded `𝒯`-leg (`TLeg_bound`) on top of
`G2`–`G4f`.  Everything here is **parallel and additive**: no landed statement is touched.

## The four `G4DEF` handoffs, and what they cost

`Salt.MR.TLegKill`'s module docstring enumerates exactly what `G4d`/`G4e`/`G4f` left open.
Each is discharged here, and the price is VISIBLE in the statements (law #253):

1. **The `(v,r)`-sum.**  `Ej_bound` is the assembly: `lemma12_on_TsetG` at level `j` → the
   graded gain (`norm_ramMain_sq_le_of_mem_TsetG`) → `G4a`'s covering
   (`integral_TsetG_le_card_mul`, cost `#I_{j−1}`) → `cell_bound_pinned` per cell → the
   uniform cell price (`cell_price_uniform`) → the geometry collapse
   (`level_geometry_collapse`) → the kill (`level_kill_budget`, `level_kill_collected`).
   The `v`-sum is FREE at level `j ≥ 2`: after the kill the summand is `v`-free, so it is
   `#I_j` times its top — no geometric series is needed (that was §8.1's business).
2. **The `2^{ℓ}` absorption.**  `mix_moment`'s second term carries `(2Y₁)^{ℓ}M_r/(Y₁^{ℓ}X₀)`.
   Here `2Y₁ ≤ 4e^{r/H_{j−1}}` and the pin's own ceiling turn it into
   `4^{ℓ}·e^{r/H_{j−1}}`, and `4^{ℓ} ≤ 4·exp(2 log 2·(v/H_j)/lPp)` — an exponent that must be
   PAID out of the `α`-decay.  **The budget is `CellGates … (η/2) j`**: MR's conditions
   `(2)`/`(3)` at the halved `η`, with the `α`-sequence still at `η`.  Only gate `(2)` is
   genuinely halved — gate `(3)` at `η/2` IMPLIES MR's own `(3)` at `η`, which is what
   `level_kill_collected_P1` consumes, so the exit exponent is MR's own `η/(2j²)` and no
   numeral downstream moves.
3. **`(ℓ+1)!²` vs `ℓ!²`.**  The corpus' `ℓ!²` is used as landed (`factorial_sq_le_pin`); MR's
   literal `(ℓ+1)!²` is not re-paid, and no consumer here asks for it.
4. **The `v`-floor deficit.**  `v ∈ I_j` gives `v/H_j ≥ log P_j − 1/H_j`, never `≥ log P_j`.
   Instead of carrying `hv` as a gate (which `level_kill_exp` does), the deficit is PAID:
   `level_kill_budget` swallows it into ONE visible factor `e^1` (the exponent's slack is
   `(η/(2j²))/H_j ≤ 1`), so the assembled page carries `Real.exp 3`, not a hypothesis.

## The arithmetic of the budget (the whole of `G5`, in five lines)

With `u := v/H_j`, `s := r/H_{j−1}`, `lPp := log P_{j−1} − 1`, `A := (η/2)/(4j²) = η/(8j²)`
(gate `(2)` at the halved `η`) and `16 ≤ log Q_j` (so `log 2 ≤ (1/4)·loglog Q_j`):

* the pin's `ℓ!²` costs `2u·llQ/lPp ≤ 2u·(5/4)A` at `llQ = log 2 + loglog Q_j`;
* the `2^{ℓ}` costs `2u·log 2/lPp ≤ 2u·(1/4)A`;
* the `α`-decay pays `2u(α_{j−1} − α_j) ≤ −2u·η/(2j²) = −2u·(4A)`  (`mrAlpha_decay_le`);
* net exponent `≤ 2u·(3/2 − 4)A = −5uA ≤ −u·η/(2j²)`, i.e. `P_j^{−η/(2j²)}` at the floor;
* `level_kill_collected_P1 η` consumes EXACTLY `P_j^{−η/(2j²)}` — MR's own exponent.

The two ends meet with no numeral tuned: halving gate `(2)` buys the two absorptions out of
the decay's own slack (`5A` spent against `4A` needed), and the collection is untouched.

## The stones

* **H-2** — `mrAlpha_mono`, `mrAlpha_pos`, `mrAlpha_le_quarter`, `alpha_gates_from_eta`
  (eq (20)'s numerals: `0 < α₁`, `2α_j < 1`, the monotone chain).
* the block-range arithmetic — `ramI_bottom_deficit`, `ramI_top_le`, `ramI_pos_of_mem`,
  `ramI_card_two_mul`.
* **the kill with the budget** — `level_kill_budget`.
* **the uniform cell price** — `cell_price_uniform` (the `(v,r)`-free envelope).
* **the geometry collapse** — `level_geometry_collapse` (MR p.27's collapse at the ASSEMBLED
  counts: `2·#I_j²·#I_{j−1}·4(log Q_j)²·Q_{j−1}² ≤ 1536·j⁶Q_{j−1}³`, exponent `65/24 ≤ 3`,
  the same margin MR spends).
* **H-1** — `LevelGates` (the per-level gate bundle) and `Ej_bound` (THE LEVEL-`j` PAGE).
* **H-3** — `sum_Ej_collected` and `TLeg_bound` (THE GRADED `𝒯`-LEG).
* **H-4** — `TLeg_feeds_capstone` (the graded row with the `𝒯`-leg bounded).

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 (`(2)`, `(3)`, p.6), §8.1–§8.2
pp. 25–27, p.24 (eq (20), the `H_j` table); `docs/sources/mr_extract.md` §2.7, §6.6;
`docs/exploration/hsup-design.md` ⟦V6⟧.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — Lemma 12's three error rows, named -/

/-- **Lemma 12's three error rows at one level**, exactly as `lemma12_on_TsetG` emits them.
Naming them is what lets the `j`-collection state its own error term without a page of
transcription; the def unfolds by `rfl`, so a consumer that wants the rows spelled out
writes `rw [lemma12Rows]`. -/
noncomputable def lemma12Rows (N Xd P Q : ℕ) (H T : ℝ) (a b c : ℕ → ℂ) : ℝ :=
  2 * (3 * ((2 * T + 20 * (N : ℝ))
          * ((2 * Real.exp 1 * (Xd : ℝ) / H + 1) * (Real.exp 1 / (Xd : ℝ) ^ 2))
      + (2 * T + 20 * (N : ℝ))
          * ∑ n ∈ Finset.Icc 1 N, ‖ramP2coeff N P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2
      + (2 * T + 20 * (N : ℝ))
          * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2))

/-! ## §2 — H-2: MR eq (20)'s numerals -/

/-- **The `α`-sequence is monotone** (eq (20), p.24): `α_i ≤ α_j` for `1 ≤ i ≤ j` and
`0 ≤ η`.  `TLegKill.mrAlpha_pred_lt` is the strict one-step form; this is the chain the
level-1 gates are transported along. -/
theorem mrAlpha_mono (η : ℝ) (hη : 0 ≤ η) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    mrAlpha η i ≤ mrAlpha η j := by
  have hiR : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hijR : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hi0 : (0 : ℝ) < (i : ℝ) := by linarith
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hinv : 1 / (2 * (j : ℝ)) ≤ 1 / (2 * (i : ℝ)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hinv hη
  rw [mrAlpha, mrAlpha]
  linarith

/-- `0 < α_j` for `j ≥ 1` and MR's `η ∈ (0,1/6)`: `α_j ≥ α₁ = 1/4 − (3/2)η > 0`. -/
theorem mrAlpha_pos (η : ℝ) (hη : 0 < η) (h6 : η < 1 / 6) {j : ℕ} (hj : 1 ≤ j) :
    0 < mrAlpha η j := by
  have h1 : mrAlpha η 1 = 1 / 4 - η * (1 + 1 / 2) := by
    rw [mrAlpha]; norm_num
  have hchain := mrAlpha_mono η hη.le (le_refl 1) hj
  rw [h1] at hchain
  linarith

/-- `α_j ≤ 1/4` for `0 ≤ η` and `j ≥ 1`: the `α`-sequence's ceiling (eq (20)). -/
theorem mrAlpha_le_quarter (η : ℝ) (hη : 0 ≤ η) {j : ℕ} (hj : 1 ≤ j) :
    mrAlpha η j ≤ 1 / 4 := by
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpos : (0 : ℝ) ≤ η * (1 + 1 / (2 * (j : ℝ))) := by
    have : (0 : ℝ) ≤ 1 / (2 * (j : ℝ)) := by positivity
    nlinarith
  rw [mrAlpha]
  linarith

/-- **H-2 — the `α`-gates of `G1a`/`G3`/`G4`, from `η ∈ (0,1/6)` alone** (MR eq (20)).
`αseq := mrAlpha η` satisfies every numeral the graded `𝒯`-leg asks of it: the level-1 pair
`0 < α₁`, `2α₁ < 1` that `E1_pin` carries, the uniform `2α_j < 1` and `0 ≤ α_j` the covering
and the cell page carry, and the monotone chain `α₁ ≤ α_j` of eq (20). -/
theorem alpha_gates_from_eta (η : ℝ) (hη : 0 < η) (h6 : η < 1 / 6) :
    0 < mrAlpha η 1 ∧ 2 * mrAlpha η 1 < 1 ∧
      (∀ j : ℕ, 1 ≤ j → 0 < mrAlpha η j ∧ 2 * mrAlpha η j < 1 ∧ mrAlpha η 1 ≤ mrAlpha η j) := by
  refine ⟨mrAlpha_pos η hη h6 (le_refl 1), ?_, ?_⟩
  · have := mrAlpha_le_quarter η hη.le (le_refl 1); linarith
  · intro j hj
    refine ⟨mrAlpha_pos η hη h6 hj, ?_, mrAlpha_mono η hη.le (le_refl 1) hj⟩
    have := mrAlpha_le_quarter η hη.le hj; linarith

/-! ## §3 — the block-range arithmetic (the floor's two faces) -/

/-- **The block bottom with the floor's deficit VISIBLE** (handoff 4): `v ∈ I` gives
`log P − 1/H ≤ v/H`, never `≥ log P`. -/
lemma ramI_bottom_deficit {H : ℝ} (hH : 0 < H) {P Q v : ℕ} (hv : v ∈ ramI H P Q) :
    Real.log (P : ℝ) - 1 / H ≤ (v : ℝ) / H := by
  rw [ramI, Finset.mem_Icc] at hv
  have h : ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv.1
  have hfl : H * Real.log (P : ℝ) < ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hsum : (v : ℝ) / H + 1 / H = ((v : ℝ) + 1) / H := by ring
  rw [sub_le_iff_le_add, hsum, le_div_iff₀ hH]
  nlinarith [h, hfl]

/-- **The block top**: `v ∈ I` gives `v/H ≤ log Q`. -/
lemma ramI_top_le {H : ℝ} (hH : 0 < H) {P Q v : ℕ} (hQ : (1 : ℝ) ≤ (Q : ℝ))
    (hv : v ∈ ramI H P Q) : (v : ℝ) / H ≤ Real.log (Q : ℝ) := by
  have hlogQ : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ
  rw [ramI, Finset.mem_Icc] at hv
  have h : (v : ℝ) ≤ ((⌊H * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hv.2
  have hfl : ((⌊H * Real.log (Q : ℝ)⌋₊ : ℕ) : ℝ) ≤ H * Real.log (Q : ℝ) :=
    Nat.floor_le (by positivity)
  rw [div_le_iff₀ hH]
  nlinarith [h, hfl]

/-- **The block range is positive** when the bottom is: `2 ≤ H` and `2 ≤ log P` put
`⌊H log P⌋ ≥ 4`, so every `v ∈ I` has `0 < v`.  (`ellPin`'s arithmetic and
`factorial_sq_le_pin` both need it.) -/
lemma ramI_pos_of_mem {H : ℝ} (hH : 2 ≤ H) {P Q v : ℕ} (hP : 2 ≤ Real.log (P : ℝ))
    (hv : v ∈ ramI H P Q) : 0 < v := by
  rw [ramI, Finset.mem_Icc] at hv
  have h4 : (4 : ℕ) ≤ ⌊H * Real.log (P : ℝ)⌋₊ := by
    refine Nat.le_floor ?_
    push_cast
    nlinarith
  omega

/-- **The card page, doubled**: `#I ≤ 2·H log Q` whenever `1 ≤ H log Q`
(`USetPrice.ramI_card_le`'s `+1` absorbed).  This is the form the geometry collapse eats. -/
lemma ramI_card_two_mul {H : ℝ} (P Q : ℕ) (h1 : 1 ≤ H * Real.log (Q : ℝ)) :
    ((ramI H P Q).card : ℝ) ≤ 2 * (H * Real.log (Q : ℝ)) := by
  have := ramI_card_le H P Q (by linarith)
  linarith

/-! ## §4 — the kill, with the two absorptions and the floor deficit paid -/

/-- **THE KILL AT THE BUDGET** (MR p.27, with `G5`'s two absorptions and the floor deficit
priced).  For any slack `w ≤ 3η/(16j²)` — which is what gate `(2)` at the halved `η` leaves
after `ℓ!²`'s `(5/4)A` and `2^{ℓ}`'s `(1/4)A` — and any `u ≥ log P_j − 1/H_j`,

  `exp(2u(α_{j−1} − α_j + w)) ≤ e·P_j^{−η/(2j²)}`.

The exit exponent is MR's own `η/(2j²)` (the budget leaves `5η/(8j²)`, so the halved-`η`
gate `(2)` is paid for out of slack, not out of the exit).  The `e` is handoff 4 PAID: the
exponent's slack from the floor deficit is `(η/(2j²))/H_j ≤ 1` (`0 < η < 1/6`, `2 ≤ j`,
`2 ≤ H_j`), so no `hv` gate is carried. -/
theorem level_kill_budget (η u Hj : ℝ) (hη : 0 < η) (h6 : η < 1 / 6) {j : ℕ} (hj : 2 ≤ j)
    (hHj : 2 ≤ Hj) (Pj : ℕ) (hPj : (0 : ℝ) < (Pj : ℝ))
    (hu : Real.log (Pj : ℝ) - 1 / Hj ≤ u) (hu0 : 0 ≤ u)
    (w : ℝ) (hw : w ≤ 3 * η / (16 * (j : ℝ) ^ 2)) :
    Real.exp (2 * u * (mrAlpha η (j - 1) - mrAlpha η j + w))
      ≤ Real.exp 1 * (Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hjne : ((j : ℝ)) ≠ 0 := ne_of_gt hj0
  have hdec := mrAlpha_decay_le η hη hj
  have hjsq : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith
  -- the net exponent per unit of `u`
  have hX : (0 : ℝ) ≤ η / (16 * (j : ℝ) ^ 2) := by positivity
  have hnet : mrAlpha η (j - 1) - mrAlpha η j + w ≤ -(η / (4 * (j : ℝ) ^ 2)) := by
    have h1 : η / (2 * (j : ℝ) ^ 2) = 8 * (η / (16 * (j : ℝ) ^ 2)) := by field_simp; ring
    have h2 : η / (4 * (j : ℝ) ^ 2) = 4 * (η / (16 * (j : ℝ) ^ 2)) := by field_simp; ring
    have h3 : 3 * η / (16 * (j : ℝ) ^ 2) = 3 * (η / (16 * (j : ℝ) ^ 2)) := by ring
    linarith [hdec, hw, hX, h1.le, h1.ge, h2.le, h2.ge, h3.le, h3.ge]
  have hcoef : (0 : ℝ) < η / (4 * (j : ℝ) ^ 2) := by positivity
  -- the exponent, bounded by the floor with the deficit's slack made visible
  have hstep : 2 * u * (mrAlpha η (j - 1) - mrAlpha η j + w)
      ≤ -(2 * (η / (4 * (j : ℝ) ^ 2))) * (Real.log (Pj : ℝ) - 1 / Hj) := by
    have h1 : 2 * u * (mrAlpha η (j - 1) - mrAlpha η j + w)
        ≤ 2 * u * -(η / (4 * (j : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hnet (by linarith)
    nlinarith [hu, hcoef, h1]
  -- the deficit's own slack is at most `1`
  have hH0 : (0 : ℝ) < Hj := by linarith
  have hslack : 2 * (η / (4 * (j : ℝ) ^ 2)) * (1 / Hj) ≤ 1 := by
    have hinv : 1 / Hj ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hH0 (by norm_num : (0:ℝ) < 2)]; linarith
    have hsmall : η / (4 * (j : ℝ) ^ 2) ≤ 1 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 16)]
      nlinarith
    nlinarith [hinv, hsmall, hcoef, one_div_pos.mpr hH0]
  have hexp : Real.exp (2 * u * (mrAlpha η (j - 1) - mrAlpha η j + w))
      ≤ Real.exp (1 + -(2 * (η / (4 * (j : ℝ) ^ 2))) * Real.log (Pj : ℝ)) := by
    refine Real.exp_le_exp.mpr ?_
    have hid : -(2 * (η / (4 * (j : ℝ) ^ 2))) * (Real.log (Pj : ℝ) - 1 / Hj)
        = -(2 * (η / (4 * (j : ℝ) ^ 2))) * Real.log (Pj : ℝ)
          + 2 * (η / (4 * (j : ℝ) ^ 2)) * (1 / Hj) := by ring
    linarith [hstep, hid.le, hid.ge, hslack]
  refine le_trans hexp (le_of_eq ?_)
  rw [Real.exp_add, Real.rpow_def_of_pos hPj]
  congr 2
  field_simp
  ring

/-! ## §5 — the uniform cell price: the `(v,r)`-free envelope -/

set_option maxHeartbeats 800000 in
-- eleven visible factors are multiplied and re-associated by `ring` in one `calc`; the
-- default budget is exhausted by the `isDefEq` on the assembled cell expression
/-- **THE UNIFORM CELL PRICE** — `cell_bound_pinned`'s exit, multiplied by the graded gain
`e^{−2α_j v/H_j}` and made FREE of both `v` and `r`:

  `e^{−2α_j v/H_j}·[the pinned cell bound at (v,r)]
     ≤ (2T/X_d + 240)·C·e³·4(log Q_j)²·Q_{j−1}²·P_j^{−η/(2j²)}`.

Every one of MR's `≪`-absorptions is a visible factor here (law #253):

* `2Y₁ ≤ 4e^{r/H_{j−1}}` and `M_r ≤ 3X_de^{−v/H_j}` — the two ceilings, at `1 ≤ X_v`;
* `4^{ℓ} ≤ 4·exp(2 log 2·(v/H_j)/lPp)` — **handoff 2**, the `2^{ℓ}`, paid into the exponent;
* `ℓ!² ≤ exp(2(v/H_j)llQ/lPp)·(2 log Q_j)²·e²` at `llQ = log 2 + loglog Q_j` — **handoff 3**
  at the corpus' `ℓ!²`;
* `e^{2α_{j−1}r/H_{j−1}}·e^{r/H_{j−1}} ≤ Q_{j−1}²` — the block-range top;
* the floor deficit — **handoff 4** — inside `level_kill_budget`'s single `e¹`.

The `η`-budget is `hgate2` (MR's `(2)` at the HALVED `η`) together with `hlog2`
(`log 2 ≤ (1/4)loglog Q_j`, i.e. `16 ≤ log Q_j`): the two put the total exponent slack at
`3η/(16j²)`, exactly `level_kill_budget`'s ceiling. -/
theorem cell_price_uniform (η T C lPp Hj Hp : ℝ) (j v r Xd Pj Qj Qp : ℕ)
    (hη : 0 < η) (h6 : η < 1 / 6) (hj : 2 ≤ j) (hHj : 2 ≤ Hj) (hHp : 2 ≤ Hp)
    (hC : 0 < C) (hT : 0 ≤ T) (hXd : 1 ≤ Xd)
    (hvpos : 0 < v) (hrpos : 0 < r)
    (hlPp : 1 ≤ lPp) (hlow : lPp ≤ (r : ℝ) / Hp)
    (hutop : (v : ℝ) / Hj + 1 ≤ 2 * Real.log (Qj : ℝ)) (hlogQj : 1 ≤ Real.log (Qj : ℝ))
    (hstop : (r : ℝ) / Hp ≤ Real.log (Qp : ℝ)) (hQp : (1 : ℝ) ≤ (Qp : ℝ))
    (hufloor : Real.log (Pj : ℝ) - 1 / Hj ≤ (v : ℝ) / Hj) (hPj : (0 : ℝ) < (Pj : ℝ))
    (hbot : 1 ≤ ramRbot Hj Xd v)
    (hgate2 : Real.log (Real.log (Qj : ℝ)) / lPp ≤ η / 2 / (4 * (j : ℝ) ^ 2))
    (hlog2 : Real.log 2 ≤ (1 / 4) * Real.log (Real.log (Qj : ℝ))) :
    Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hj)
        * (Real.exp (2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * mrAlpha η (j - 1) * (r : ℝ) / Hp)
            * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
                    ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ))
                * ((((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2 * (C / (Xd : ℝ)))))
      ≤ (2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 * (4 * Real.log (Qj : ℝ) ^ 2)
          * (Qp : ℝ) ^ 2 * ((Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))) := by
  have hHj0 : (0 : ℝ) < Hj := by linarith
  have hHp0 : (0 : ℝ) < Hp := by linarith
  have hHjne : Hj ≠ 0 := ne_of_gt hHj0
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hXdne : (Xd : ℝ) ≠ 0 := ne_of_gt hXdR
  have hlPp0 : (0 : ℝ) < lPp := by linarith
  have hlPpne : lPp ≠ 0 := ne_of_gt hlPp0
  have hs0 : (0 : ℝ) ≤ (r : ℝ) / Hp := by positivity
  have hspos : (0 : ℝ) < (r : ℝ) / Hp := lt_of_lt_of_le hlPp0 hlow
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hvpos
  have hupos : (0 : ℝ) < (v : ℝ) / Hj := div_pos hvR hHj0
  have hu0 : (0 : ℝ) ≤ (v : ℝ) / Hj := hupos.le
  have hlogQj0 : (0 : ℝ) < Real.log (Qj : ℝ) := by linarith
  have hllQ0 : (0 : ℝ) ≤ Real.log (Real.log (Qj : ℝ)) := Real.log_nonneg hlogQj
  have hlog20 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hαp0 : (0 : ℝ) ≤ mrAlpha η (j - 1) := (mrAlpha_pos η hη h6 (by omega)).le
  have hαp4 : mrAlpha η (j - 1) ≤ 1 / 4 := mrAlpha_le_quarter η hη.le (by omega)
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjne : ((j : ℝ)) ≠ 0 := by intro h; rw [h] at hjR; linarith
  -- ⟦THE FACTORIAL PAGE⟧ `ℓ!² ≤ exp(2u·llQ/lPp)·4(log Q_j)²·e²`
  have hexpllQ : Real.exp (Real.log 2 + Real.log (Real.log (Qj : ℝ))) = 2 * Real.log (Qj : ℝ) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_log hlogQj0]
  have hllQle : Real.log ((v : ℝ) / Hj + 1)
      ≤ Real.log 2 + Real.log (Real.log (Qj : ℝ)) := by
    have h1 : Real.log ((v : ℝ) / Hj + 1) ≤ Real.log (2 * Real.log (Qj : ℝ)) :=
      Real.log_le_log (by linarith) hutop
    rwa [Real.log_mul (by norm_num) (ne_of_gt hlogQj0)] at h1
  have hb2 : (((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2
      ≤ Real.exp (2 * ((v : ℝ) / Hj)
            * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp)
          * (4 * Real.log (Qj : ℝ) ^ 2) * Real.exp 2 := by
    have hfac := factorial_sq_le_pin Hj Hp (Real.log 2 + Real.log (Real.log (Qj : ℝ))) lPp
      v r hHj0 hHp0 hrpos hvpos hlPp hlow hllQle
    rw [hexpllQ] at hfac
    have hid : (2 * Real.log (Qj : ℝ)) ^ 2 = 4 * Real.log (Qj : ℝ) ^ 2 := by ring
    rwa [hid] at hfac
  -- ⟦THE TWO CEILINGS⟧
  have hexps1 : (1 : ℝ) ≤ Real.exp ((r : ℝ) / Hp) := by
    have h := Real.exp_le_exp.mpr hs0
    rwa [Real.exp_zero] at h
  have hY : ((⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ≤ 2 * Real.exp ((r : ℝ) / Hp) := by
    have h := Nat.ceil_lt_add_one (Real.exp_pos ((r : ℝ) / Hp)).le
    linarith
  have hMr : ((⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) ≤ 3 * ramRbot Hj Xd v := by
    have h := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ 2 * ramRbot Hj Xd v)
    linarith
  have hramR : ramRbot Hj Xd v = (Xd : ℝ) * Real.exp (-((v : ℝ) / Hj)) := by
    rw [ramRbot, neg_div]
  -- ⟦HANDOFF 2⟧ the `4^{ℓ}`
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hellle : ((ellPin Hj Hp v r : ℕ) : ℝ) ≤ (v : ℝ) / Hj / lPp + 1 := by
    have hx : (0 : ℝ) ≤ ((v : ℝ) / Hj) / ((r : ℝ) / Hp) := by positivity
    have h1 := ellPin_le_add_one Hj Hp v r hx
    have h2 : ((v : ℝ) / Hj) / ((r : ℝ) / Hp) ≤ ((v : ℝ) / Hj) / lPp :=
      (div_le_div_iff_of_pos_left hupos hspos hlPp0).mpr hlow
    linarith
  have hpow4 : (4 : ℝ) ^ (ellPin Hj Hp v r)
      ≤ 4 * Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) := by
    have he : (4 : ℝ) ^ (ellPin Hj Hp v r)
        = Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * Real.log 4) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 4)]
    have hexp4 : Real.exp (2 * Real.log 2) = 4 := by
      rw [← hlog4, Real.exp_log (by norm_num : (0:ℝ) < 4)]
    have hl40 : (0 : ℝ) ≤ Real.log 4 := by rw [hlog4]; linarith
    have hstep : ((ellPin Hj Hp v r : ℕ) : ℝ) * Real.log 4
        ≤ ((v : ℝ) / Hj / lPp + 1) * Real.log 4 :=
      mul_le_mul_of_nonneg_right hellle hl40
    have hid : ((v : ℝ) / Hj / lPp + 1) * Real.log 4
        = 2 * Real.log 2 * ((v : ℝ) / Hj) / lPp + 2 * Real.log 2 := by
      rw [hlog4]; ring
    rw [he]
    calc Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * Real.log 4)
        ≤ Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp + 2 * Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith [hstep, hid.le, hid.ge])
      _ = Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) * 4 := by
          rw [Real.exp_add, hexp4]
      _ = 4 * Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) := by ring
  -- ⟦THE ASSEMBLED `M`-TERM⟧
  have hcast : (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊) ^ (ellPin Hj Hp v r)
        * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)
      = ((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
        * ((⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) := by
    push_cast
    ring
  have hpowY : ((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
      ≤ 4 ^ (ellPin Hj Hp v r)
          * Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)) := by
    have hbase : ((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ≤ 4 * Real.exp ((r : ℝ) / Hp) := by
      push_cast
      linarith
    calc ((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
        ≤ (4 * Real.exp ((r : ℝ) / Hp)) ^ (ellPin Hj Hp v r) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
      _ = 4 ^ (ellPin Hj Hp v r)
            * Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)) := by
          rw [mul_pow, ← Real.exp_nat_mul]
  have hMbound : 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊) ^ (ellPin Hj Hp v r)
        * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)
      ≤ 240 * (Xd : ℝ) * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
          * Real.exp ((r : ℝ) / Hp)) := by
    have hprod : ((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
          * ((⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)
        ≤ (4 ^ (ellPin Hj Hp v r)
            * Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)))
          * (3 * ramRbot Hj Xd v) :=
      mul_le_mul hpowY hMr (Nat.cast_nonneg _) (by positivity)
    have hkey := ellPin_mul_block_le Hj Hp v r hHj0 hHp0 hrpos
    have hexpk : Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp))
        ≤ Real.exp ((v : ℝ) / Hj + (r : ℝ) / Hp) := Real.exp_le_exp.mpr hkey
    have hstep2 : (4 ^ (ellPin Hj Hp v r)
          * Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)))
        ≤ (4 * Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp))
            * Real.exp ((v : ℝ) / Hj + (r : ℝ) / Hp) :=
      mul_le_mul hpow4 hexpk (Real.exp_pos _).le (by positivity)
    have hcan : Real.exp ((v : ℝ) / Hj + (r : ℝ) / Hp) * Real.exp (-((v : ℝ) / Hj))
        = Real.exp ((r : ℝ) / Hp) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊) ^ (ellPin Hj Hp v r)
            * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)
        = 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
              * ((⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)) := by rw [hcast]
      _ ≤ 20 * ((4 ^ (ellPin Hj Hp v r)
              * Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)))
            * (3 * ramRbot Hj Xd v)) := by
          exact mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ ≤ 20 * ((4 * Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
              * Real.exp ((v : ℝ) / Hj + (r : ℝ) / Hp))
            * (3 * ((Xd : ℝ) * Real.exp (-((v : ℝ) / Hj))))) := by
          rw [hramR] at hprod ⊢
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep2 ?_) (by norm_num)
          positivity
      _ = 240 * (Xd : ℝ) * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
            * (Real.exp ((v : ℝ) / Hj + (r : ℝ) / Hp) * Real.exp (-((v : ℝ) / Hj)))) := by
          ring
      _ = 240 * (Xd : ℝ) * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
            * Real.exp ((r : ℝ) / Hp)) := by rw [hcan]
  -- ⟦THE COEFFICIENT ROW⟧
  have hMre0 : (0 : ℝ) ≤ (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊) ^ (ellPin Hj Hp v r)
      * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hK1 : (1 : ℝ) ≤ Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
      * Real.exp ((r : ℝ) / Hp) := by
    have h1 : (1 : ℝ) ≤ Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) := by
      have h := Real.exp_le_exp.mpr (by positivity :
        (0:ℝ) ≤ 2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
      rwa [Real.exp_zero] at h
    nlinarith [hexps1, h1]
  have hb3 : (2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊) ^ (ellPin Hj Hp v r)
          * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)) * (C / (Xd : ℝ))
      ≤ ((2 * T / (Xd : ℝ) + 240) * C)
          * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) * Real.exp ((r : ℝ) / Hp)) := by
    have hCX : (0 : ℝ) ≤ C / (Xd : ℝ) := by positivity
    have hstep := mul_le_mul_of_nonneg_right
      (by linarith [hMbound] : 2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
          ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)
        ≤ 2 * T + 240 * (Xd : ℝ) * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
            * Real.exp ((r : ℝ) / Hp))) hCX
    have hid : (2 * T + 240 * (Xd : ℝ) * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
          * Real.exp ((r : ℝ) / Hp))) * (C / (Xd : ℝ))
        = 2 * T * C / (Xd : ℝ) + 240 * C * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
            * Real.exp ((r : ℝ) / Hp)) := by
      field_simp
    have hid2 : ((2 * T / (Xd : ℝ) + 240) * C)
          * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) * Real.exp ((r : ℝ) / Hp))
        = (2 * T * C / (Xd : ℝ))
            * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) * Real.exp ((r : ℝ) / Hp))
          + 240 * C * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
              * Real.exp ((r : ℝ) / Hp)) := by ring
    have hTC : (0 : ℝ) ≤ 2 * T * C / (Xd : ℝ) := by positivity
    have hmono : 2 * T * C / (Xd : ℝ)
        ≤ (2 * T * C / (Xd : ℝ))
            * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp) * Real.exp ((r : ℝ) / Hp)) := by
      nlinarith [hK1, hTC]
    linarith [hstep, hid.le, hid.ge, hid2.le, hid2.ge, hmono]
  -- ⟦THE ENTRY TICKET AT THE PIN⟧
  have hb1 := exp_ellPin_cancel Hj Hp (mrAlpha η j) (mrAlpha η (j - 1)) v r hHj0 hHp0 hrpos hαp0
  -- ⟦THE THREE BOUNDS, MULTIPLIED⟧
  have hre : Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hj)
        * (Real.exp (2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * mrAlpha η (j - 1) * (r : ℝ) / Hp)
            * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
                    ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ))
                * ((((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2 * (C / (Xd : ℝ)))))
      = (Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hj)
            * Real.exp (2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * mrAlpha η (j - 1) * (r : ℝ) / Hp))
        * ((((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2
            * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
                  ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ))
                * (C / (Xd : ℝ)))) := by ring
  rw [hre]
  have hcpos : (0 : ℝ) ≤ (((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2
      * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
            ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)) * (C / (Xd : ℝ))) := by
    have h1 : (0 : ℝ) ≤ 2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
        ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ C / (Xd : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2 := by positivity
    exact mul_nonneg h3 (mul_nonneg h1 h2)
  have hinner : (((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2
        * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
              ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ)) * (C / (Xd : ℝ)))
      ≤ (Real.exp (2 * ((v : ℝ) / Hj) * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp)
            * (4 * Real.log (Qj : ℝ) ^ 2) * Real.exp 2)
        * (((2 * T / (Xd : ℝ) + 240) * C)
            * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
                * Real.exp ((r : ℝ) / Hp))) := by
    refine mul_le_mul hb2 hb3 ?_ (by positivity)
    have h1 : (0 : ℝ) ≤ 2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hp)⌉₊)
        ^ (ellPin Hj Hp v r) * ⌈2 * ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) := by linarith
    have h2 : (0 : ℝ) ≤ C / (Xd : ℝ) := by positivity
    exact mul_nonneg h1 h2
  refine le_trans (mul_le_mul hb1 hinner hcpos (Real.exp_pos _).le) ?_
  -- ⟦THE MERGE, THE KILL, THE BLOCK TOP⟧
  have hexpprod : Real.exp (2 * (v : ℝ) * (mrAlpha η (j - 1) - mrAlpha η j) / Hj
          + 2 * mrAlpha η (j - 1) * ((r : ℝ) / Hp))
        * ((Real.exp (2 * ((v : ℝ) / Hj)
              * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp)
            * (4 * Real.log (Qj : ℝ) ^ 2) * Real.exp 2)
          * (((2 * T / (Xd : ℝ) + 240) * C)
              * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
                  * Real.exp ((r : ℝ) / Hp))))
      = ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 2 * (4 * Real.log (Qj : ℝ) ^ 2))
        * (Real.exp (2 * ((v : ℝ) / Hj)
              * (mrAlpha η (j - 1) - mrAlpha η j
                  + ((Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp + Real.log 2 / lPp)))
            * Real.exp ((2 * mrAlpha η (j - 1) + 1) * ((r : ℝ) / Hp))) := by
    have hexps : 2 * (v : ℝ) * (mrAlpha η (j - 1) - mrAlpha η j) / Hj
            + 2 * mrAlpha η (j - 1) * ((r : ℝ) / Hp)
          + 2 * ((v : ℝ) / Hj) * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp
          + 2 * Real.log 2 * ((v : ℝ) / Hj) / lPp + (r : ℝ) / Hp
        = 2 * ((v : ℝ) / Hj)
              * (mrAlpha η (j - 1) - mrAlpha η j
                  + ((Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp + Real.log 2 / lPp))
            + (2 * mrAlpha η (j - 1) + 1) * ((r : ℝ) / Hp) := by
      ring
    calc Real.exp (2 * (v : ℝ) * (mrAlpha η (j - 1) - mrAlpha η j) / Hj
              + 2 * mrAlpha η (j - 1) * ((r : ℝ) / Hp))
            * ((Real.exp (2 * ((v : ℝ) / Hj)
                  * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp)
                * (4 * Real.log (Qj : ℝ) ^ 2) * Real.exp 2)
              * (((2 * T / (Xd : ℝ) + 240) * C)
                  * (Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
                      * Real.exp ((r : ℝ) / Hp))))
        = ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 2 * (4 * Real.log (Qj : ℝ) ^ 2))
            * (Real.exp (2 * (v : ℝ) * (mrAlpha η (j - 1) - mrAlpha η j) / Hj
                  + 2 * mrAlpha η (j - 1) * ((r : ℝ) / Hp))
                * Real.exp (2 * ((v : ℝ) / Hj)
                    * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp)
                * Real.exp (2 * Real.log 2 * ((v : ℝ) / Hj) / lPp)
                * Real.exp ((r : ℝ) / Hp)) := by ring
      _ = ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 2 * (4 * Real.log (Qj : ℝ) ^ 2))
            * Real.exp (2 * (v : ℝ) * (mrAlpha η (j - 1) - mrAlpha η j) / Hj
                  + 2 * mrAlpha η (j - 1) * ((r : ℝ) / Hp)
                + 2 * ((v : ℝ) / Hj)
                    * (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp
                + 2 * Real.log 2 * ((v : ℝ) / Hj) / lPp + (r : ℝ) / Hp) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ = ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 2 * (4 * Real.log (Qj : ℝ) ^ 2))
            * (Real.exp (2 * ((v : ℝ) / Hj)
                  * (mrAlpha η (j - 1) - mrAlpha η j
                      + ((Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp
                          + Real.log 2 / lPp)))
                * Real.exp ((2 * mrAlpha η (j - 1) + 1) * ((r : ℝ) / Hp))) := by
          rw [← Real.exp_add, hexps]
  rw [hexpprod]
  have hwbound : (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp + Real.log 2 / lPp
      ≤ 3 * η / (16 * (j : ℝ) ^ 2) := by
    have hid : (Real.log 2 + Real.log (Real.log (Qj : ℝ))) / lPp + Real.log 2 / lPp
        = (Real.log 2 + Real.log (Real.log (Qj : ℝ)) + Real.log 2) / lPp := by
      ring
    have hnum : Real.log 2 + Real.log (Real.log (Qj : ℝ)) + Real.log 2
        ≤ 3 / 2 * Real.log (Real.log (Qj : ℝ)) := by linarith
    have hdiv : (Real.log 2 + Real.log (Real.log (Qj : ℝ)) + Real.log 2) / lPp
        ≤ (3 / 2 * Real.log (Real.log (Qj : ℝ))) / lPp :=
      (div_le_div_iff_of_pos_right hlPp0).mpr hnum
    have hid2 : (3 / 2 * Real.log (Real.log (Qj : ℝ))) / lPp
        = 3 / 2 * (Real.log (Real.log (Qj : ℝ)) / lPp) := by ring
    have hgg : 3 / 2 * (Real.log (Real.log (Qj : ℝ)) / lPp)
        ≤ 3 / 2 * (η / 2 / (4 * (j : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hgate2 (by norm_num)
    have hid3 : 3 / 2 * (η / 2 / (4 * (j : ℝ) ^ 2)) = 3 * η / (16 * (j : ℝ) ^ 2) := by
      field_simp
      ring
    linarith [hid.le, hid.ge, hdiv, hid2.le, hid2.ge, hgg, hid3.le, hid3.ge]
  have hkill := level_kill_budget η ((v : ℝ) / Hj) Hj hη h6 hj hHj Pj hPj hufloor hu0 _ hwbound
  have hQsq : Real.exp ((2 * mrAlpha η (j - 1) + 1) * ((r : ℝ) / Hp)) ≤ (Qp : ℝ) ^ 2 := by
    have hlogQp : (0 : ℝ) ≤ Real.log (Qp : ℝ) := Real.log_nonneg hQp
    have h1 : (2 * mrAlpha η (j - 1) + 1) * ((r : ℝ) / Hp) ≤ 2 * Real.log (Qp : ℝ) := by
      nlinarith [hαp4, hstop, hs0, hαp0]
    have h2 : (2 : ℝ) * Real.log (Qp : ℝ) = Real.log ((Qp : ℝ) ^ (2:ℕ)) := by
      rw [Real.log_pow]
      push_cast
      ring
    calc Real.exp ((2 * mrAlpha η (j - 1) + 1) * ((r : ℝ) / Hp))
        ≤ Real.exp (2 * Real.log (Qp : ℝ)) := Real.exp_le_exp.mpr h1
      _ = (Qp : ℝ) ^ 2 := by
          rw [h2, Real.exp_log (pow_pos (by linarith : (0:ℝ) < (Qp : ℝ)) 2)]
  have hK0 : (0 : ℝ) ≤ (2 * T / (Xd : ℝ) + 240) * C * Real.exp 2 * (4 * Real.log (Qj : ℝ) ^ 2) := by
    have h1 : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) + 240 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hC.le) (Real.exp_pos 2).le) (by positivity)
  refine le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hkill hQsq (Real.exp_pos _).le (by positivity)) hK0) (le_of_eq ?_)
  rw [show Real.exp 3 = Real.exp 2 * Real.exp 1 by rw [← Real.exp_add]; norm_num]
  ring

/-! ## §6 — the geometry collapse at the ASSEMBLED counts -/

/-- **MR p.27's collapse, at the counts the level page actually produces.**  With the block
counts doubled (`ramI_card_two_mul`), the level-`j` page's geometric prefactor is

  `2·(2H_j log Q_j)²·(2H_{j−1} log Q_{j−1})·4(log Q_j)²·Q_{j−1}² ≤ 1536·j⁶·Q_{j−1}³`.

The exponent bookkeeping is MR's own and lands on the SAME margin: `H_j²H_{j−1} ≤ H_j³ ≤
j⁶P₁^{1/2} ≤ j⁶Q_{j−1}^{1/2}`, `(log Q_j)^4 ≤ Q_{j−1}^{1/6}` (gate `(2)`'s
`log Q_j ≤ Q_{j−1}^{1/24}`), `log Q_{j−1} ≤ 24Q_{j−1}^{1/24}`
(`Real.log_le_rpow_div`), and `1/2 + 1/6 + 1/24 + 2 = 65/24 ≤ 3`.  The `H_j` pin of p.24
rides as the hypothesis `hH3`, exactly as in `TLegKill.cell_geometry_collapse`. -/
theorem level_geometry_collapse (Hj Hp : ℝ) (j P1 Qj Qp : ℕ)
    (hHpj : Hp ≤ Hj) (hQp1 : (1 : ℝ) ≤ (Qp : ℝ))
    (hlogQj0 : 0 ≤ Real.log (Qj : ℝ))
    (hlogQjr : Real.log (Qj : ℝ) ≤ (Qp : ℝ) ^ ((1 : ℝ) / 24))
    (hlogQp0 : 0 ≤ Real.log (Qp : ℝ))
    (hH3 : Hj ^ 3 ≤ (j : ℝ) ^ 6 * (P1 : ℝ) ^ ((1 : ℝ) / 2))
    (hP1Qp : (P1 : ℝ) ≤ (Qp : ℝ)) :
    2 * (2 * (Hj * Real.log (Qj : ℝ))) ^ 2 * (2 * (Hp * Real.log (Qp : ℝ)))
        * (4 * Real.log (Qj : ℝ) ^ 2) * (Qp : ℝ) ^ 2
      ≤ 1536 * (j : ℝ) ^ 6 * (Qp : ℝ) ^ 3 := by
  have hQp0 : (0 : ℝ) < (Qp : ℝ) := by linarith
  have hr2 : (0 : ℝ) ≤ (Qp : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hQp0.le _
  have hr6 : (0 : ℝ) ≤ (Qp : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hQp0.le _
  have hr24 : (0 : ℝ) ≤ (Qp : ℝ) ^ ((1 : ℝ) / 24) := Real.rpow_nonneg hQp0.le _
  have hstep1 : Hj ^ 2 * Hp ≤ Hj ^ 3 := by nlinarith [sq_nonneg Hj, hHpj]
  have hstep4 : Hj ^ 3 ≤ (j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2) := by
    refine le_trans hH3 (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hP1Qp (by norm_num)
  have hstep2 : Real.log (Qj : ℝ) ^ 4 ≤ (Qp : ℝ) ^ ((1 : ℝ) / 6) := by
    calc Real.log (Qj : ℝ) ^ 4 ≤ ((Qp : ℝ) ^ ((1 : ℝ) / 24)) ^ 4 :=
          pow_le_pow_left₀ hlogQj0 hlogQjr 4
      _ = (Qp : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_natCast ((Qp : ℝ) ^ ((1 : ℝ) / 24)) 4, ← Real.rpow_mul hQp0.le]
          norm_num
  have hstep3 : Real.log (Qp : ℝ) ≤ 24 * (Qp : ℝ) ^ ((1 : ℝ) / 24) := by
    have h := Real.log_le_rpow_div hQp0.le (by norm_num : (0:ℝ) < (1:ℝ)/24)
    have hid : (Qp : ℝ) ^ ((1 : ℝ) / 24) / ((1 : ℝ) / 24) = 24 * (Qp : ℝ) ^ ((1 : ℝ) / 24) := by
      ring
    linarith [h, hid.le, hid.ge]
  have hAA : Hj ^ 2 * Hp ≤ (j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2) := le_trans hstep1 hstep4
  have hpow : (Qp : ℝ) ^ ((1 : ℝ) / 2) * (Qp : ℝ) ^ ((1 : ℝ) / 6)
      * (Qp : ℝ) ^ ((1 : ℝ) / 24) * (Qp : ℝ) ^ 2 ≤ (Qp : ℝ) ^ 3 := by
    have hc2 : ((Qp : ℝ)) ^ (2 : ℕ) = (Qp : ℝ) ^ ((2 : ℝ)) := by
      rw [← Real.rpow_natCast (Qp : ℝ) 2]; norm_num
    have hc3 : ((Qp : ℝ)) ^ (3 : ℕ) = (Qp : ℝ) ^ ((3 : ℝ)) := by
      rw [← Real.rpow_natCast (Qp : ℝ) 3]; norm_num
    rw [hc2, hc3, ← Real.rpow_add hQp0, ← Real.rpow_add hQp0, ← Real.rpow_add hQp0]
    refine Real.rpow_le_rpow_of_exponent_le hQp1 ?_
    norm_num
  calc 2 * (2 * (Hj * Real.log (Qj : ℝ))) ^ 2 * (2 * (Hp * Real.log (Qp : ℝ)))
          * (4 * Real.log (Qj : ℝ) ^ 2) * (Qp : ℝ) ^ 2
      = 64 * (Hj ^ 2 * Hp) * Real.log (Qj : ℝ) ^ 4 * Real.log (Qp : ℝ) * (Qp : ℝ) ^ 2 := by
        ring
    _ ≤ 64 * ((j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2)) * ((Qp : ℝ) ^ ((1 : ℝ) / 6))
          * (24 * (Qp : ℝ) ^ ((1 : ℝ) / 24)) * (Qp : ℝ) ^ 2 := by
        have hm1 : 64 * (Hj ^ 2 * Hp) ≤ 64 * ((j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hAA (by norm_num)
        have hm2 := mul_le_mul hm1 hstep2 (by positivity)
          (by positivity : (0:ℝ) ≤ 64 * ((j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2)))
        have hm3 := mul_le_mul hm2 hstep3 hlogQp0
          (by positivity : (0:ℝ) ≤ 64 * ((j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2))
            * ((Qp : ℝ) ^ ((1 : ℝ) / 6)))
        exact mul_le_mul_of_nonneg_right hm3 (by positivity)
    _ = 1536 * (j : ℝ) ^ 6 * ((Qp : ℝ) ^ ((1 : ℝ) / 2) * (Qp : ℝ) ^ ((1 : ℝ) / 6)
          * (Qp : ℝ) ^ ((1 : ℝ) / 24) * (Qp : ℝ) ^ 2) := by ring
    _ ≤ 1536 * (j : ℝ) ^ 6 * (Qp : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

/-! ## §7 — the graded gain, alone -/

/-- **The graded gain as an integral step** (`G3a-ii` without the mean-value theorem).  On
any measurable `A ⊆ [−T,T]` inside `𝒯ⱼ`, MR (21) pulls the level-`j` threshold out:

  `∫_A ‖(Q·R)_{v,H_j}(1+it)‖² dt ≤ e^{−2α_j v/H_j}·∫_A ‖R_{v,H_j}(1+it)‖² dt`.

§8.1 (`TLegE1`) continues with the MVT; §8.2 continues with the covering and the moment, so
the two pages branch exactly here. -/
theorem integral_ramMain_le_exp_mul_ramR (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ)
    (Hseq αseq : ℕ → ℝ) (Jb j N Xd : ℕ) (T : ℝ) (A : Set ℝ)
    (hAm : MeasurableSet A) (hAsub : A ⊆ Set.Icc (-T) T)
    (hAT : A ⊆ TsetG c Pseq Qseq Hseq αseq Jb j)
    (v : ℕ) (hv : v ∈ ramI (Hseq j) (Pseq j) (Qseq j)) :
    (∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * ∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
  have hcontM : Continuous
      (fun t : ℝ => ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2) :=
    (continuous_ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v).norm.pow 2
  have hcontR : Continuous
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) :=
    (continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2
  have hIntM : IntegrableOn
      (fun t : ℝ => ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2) A :=
    (hcontM.integrableOn_Icc (a := -T) (b := T)).mono_set hAsub
  have hIntR : IntegrableOn
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) A :=
    (hcontR.integrableOn_Icc (a := -T) (b := T)).mono_set hAsub
  have hpt : (∫ t in A, ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ ∫ t in A, Real.exp (-(2 * αseq j) * (v : ℝ) / Hseq j)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    setIntegral_mono_on hIntM (hIntR.const_mul _) hAm
      (fun t ht => norm_ramMain_sq_le_of_mem_TsetG (hAT ht) hv N Xd b)
  rwa [MeasureTheory.integral_const_mul] at hpt

/-! ## §8 — H-1: `LevelGates` and THE LEVEL-`j` PAGE -/

/-- **The per-level gate bundle** (law #253: every gate `Ej_bound` spends, named).

The head field is the whole budget: `CellGates Pseq Qseq (η/2) j` is MR's `(2)`/`(3)` at the
HALVED `η`, while the `α`-sequence stays at `η` (`mrAlpha η`).  Gate `(2)` at `η/2` is what
pays the `2^{ℓ}` and the ceiling slop (`cell_price_uniform`); gate `(3)` at `η/2` implies
MR's own `(3)` at `η`, which is what `level_kill_collected_P1` consumes.  The remaining
fields are §8.2's own frame: the two widths and their order, the `H_j` pin of p.24, the
block bottoms `16 ≤ log Q_j`, `2 ≤ log P_{j−1}`, `2 ≤ log P_j` (the first is exactly
`log 2 ≤ (1/4)loglog Q_j`, the other two make the pin's arithmetic non-degenerate), the
`P₁`-anchor and the sharp-length gate `Q_j ≤ X_d`. -/
structure LevelGates (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (η : ℝ) (P1 Xd j : ℕ) : Prop where
  /-- MR's `(2)`/`(3)` at the HALVED `η` — the `G5` budget. -/
  cell : CellGates Pseq Qseq (η / 2) j
  /-- MR's own range for the `α`-sequence's `η`. -/
  eta_lt6 : η < 1 / 6
  /-- Lemma 12's width gate at level `j`. -/
  two_le_Hj : 2 ≤ Hseq j
  /-- The moment's width gate at level `j−1`. -/
  two_le_Hp : 2 ≤ Hseq (j - 1)
  /-- The `H`-sequence's order (p.24: `H_j = j²P₁^{1/6−η}/(log Q₁)^{1/3}` increases). -/
  Hp_le_Hj : Hseq (j - 1) ≤ Hseq j
  /-- The `H_j` pin of p.24, in the form the collapse eats. -/
  Hj_pin : Hseq j ^ 3 ≤ (j : ℝ) ^ 6 * (P1 : ℝ) ^ ((1 : ℝ) / 2)
  /-- `16 ≤ log Q_j`, i.e. `log 2 ≤ (1/4)loglog Q_j` — the slop's own gate. -/
  logQj_ge : 16 ≤ Real.log (Qseq j : ℝ)
  /-- `2 ≤ log P_{j−1}`: the block bottom `lPp = log P_{j−1} − 1` is `≥ 1`. -/
  logPp_ge : 2 ≤ Real.log (Pseq (j - 1) : ℝ)
  /-- `2 ≤ log P_j`: the level-`j` block range is nonempty and `0 < v` on it. -/
  logPj_ge : 2 ≤ Real.log (Pseq j : ℝ)
  /-- MR p.27's last step: `P₁ ≤ Q_{j−1}`. -/
  P1_le_Qp : (P1 : ℝ) ≤ (Qseq (j - 1) : ℝ)
  /-- The `P₁`-anchor is a genuine modulus. -/
  one_le_P1 : 1 ≤ P1
  /-- The SHARP-`M` law's gate: `Q_j ≤ X_d` makes `X_v = X_de^{−v/H_j} ≥ 1` on all of `I_j`. -/
  Qj_le_Xd : Qseq j ≤ Xd

set_option maxHeartbeats 800000 in
-- the level page composes seven landed stones under one `∀ v ∈ I_j, ∀ r ∈ I_{j−1}`; the
-- default budget is exhausted by the assembled cell expression's `isDefEq`
/-- **H-1 — THE LEVEL-`j` PAGE (MR §8.2, `j ≥ 2`).**

  `∫_{A_j}‖F(1+it)‖² dt ≤ 1536·C·e³·(2T/X_d + 240)·1/(j²P₁) + E_j`,

`A_j := (Ann ∖ ball) ∩ 𝒯ⱼ`, `E_j` Lemma 12's three rows at level `j` (`lemma12Rows`), `C`
the absolute Shiu constant of `cell_bound_pinned`.  This is MR p.27's exit: the level page is
`≪ 1/(j²P₁)` times the mean-value factor, so the `j`-sum converges against `Σ1/j²`.

The assembly, in the order the stones fire: `lemma12_on_TsetG` at `(H_j,P_j,Q_j)` → the
graded gain `integral_ramMain_le_exp_mul_ramR` → `G4a`'s covering
`integral_TsetG_le_card_mul` at `#I_{j−1}` → `cell_bound_pinned` on each cell →
`cell_price_uniform` (which makes the bound free of BOTH `v` and `r`, paying handoffs 2–4)
→ `ramI_card_two_mul` + `level_geometry_collapse` → `level_kill_collected_P1`.

The `v`-sum is FREE here: after the kill the summand no longer depends on `v`, so it is
`#I_j` times its top — §8.1's geometric series has no counterpart at `j ≥ 2`. -/
theorem Ej_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (c a b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ) (η : ℝ)
      (Jb j N Xd P1 : ℕ) (X T t₁ : ℝ),
      LevelGates Pseq Qseq Hseq η P1 Xd j →
      1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T →
      (∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m → a (p * m) = b m * c p) →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j → c p * b m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖spoly N a t‖ ^ 2)
        ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
              * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
          + lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a b c := by
  obtain ⟨C, hC, hcell⟩ := cell_bound_pinned
  refine ⟨C, hC, ?_⟩
  intro c a b Pseq Qseq Hseq η Jb j N Xd P1 X T t₁ hG hXd hN hT hcoef hb hc hwin
  -- ⟦THE GATES, UNPACKED⟧
  have hη2 : (0 : ℝ) < η / 2 := hG.cell.eta_pos
  have hη : (0 : ℝ) < η := by linarith
  have hj : 2 ≤ j := hG.cell.two_le_j
  have hjR : (2 : ℝ) ≤ (j : ℝ) := hG.cell.jR_two
  have hHj : 2 ≤ Hseq j := hG.two_le_Hj
  have hHp : 2 ≤ Hseq (j - 1) := hG.two_le_Hp
  have hHj0 : (0 : ℝ) < Hseq j := by linarith
  have hHp0 : (0 : ℝ) < Hseq (j - 1) := by linarith
  have hlogQj : (16 : ℝ) ≤ Real.log (Qseq j : ℝ) := hG.logQj_ge
  have hlogPj : (2 : ℝ) ≤ Real.log (Pseq j : ℝ) := hG.logPj_ge
  have hlogPp : (2 : ℝ) ≤ Real.log (Pseq (j - 1) : ℝ) := hG.logPp_ge
  have hlogQp : (2 : ℝ) ≤ Real.log (Qseq (j - 1) : ℝ) := le_trans hlogPp hG.cell.logP_le_logQ
  have hQj1 : 1 ≤ Qseq j := by
    rcases Nat.eq_zero_or_pos (Qseq j) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogQj; linarith
    · exact h
  have hPj1 : 1 ≤ Pseq j := by
    rcases Nat.eq_zero_or_pos (Pseq j) with h | h
    · rw [h, Nat.cast_zero, Real.log_zero] at hlogPj; linarith
    · exact h
  have hQjR : (1 : ℝ) ≤ (Qseq j : ℝ) := by exact_mod_cast hQj1
  have hPjR : (0 : ℝ) < (Pseq j : ℝ) := by exact_mod_cast hPj1
  have hQp1 : (1 : ℝ) < (Qseq (j - 1) : ℝ) := hG.cell.one_lt_Qpred
  have hP1R : (0 : ℝ) < (P1 : ℝ) := by exact_mod_cast hG.one_le_P1
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  -- `log 2 ≤ (1/4)loglog Q_j`, from `16 ≤ log Q_j`
  have hlog2 : Real.log 2 ≤ (1 / 4) * Real.log (Real.log (Qseq j : ℝ)) := by
    have h16 : Real.log (16 : ℝ) ≤ Real.log (Real.log (Qseq j : ℝ)) :=
      Real.log_le_log (by norm_num) hlogQj
    have hid : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ (4:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [h16, hid.le, hid.ge]
  -- the SHARP-`M` gate on all of `I_j`
  have hbot : ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j), 1 ≤ ramRbot (Hseq j) Xd v :=
    fun v hv => ramRbot_one_le_of_mem_ramI hHj0 hQj1 hG.Qj_le_Xd hv
  -- gate `(3)` at the FULL `η`, from the halved-`η` bundle
  have hg3 : 8 * Real.log (Qseq (j - 1) : ℝ) + 16 * Real.log (j : ℝ)
      ≤ (η / (j : ℝ) ^ 2) * Real.log (Pseq j : ℝ) := by
    have h := hG.cell.gate3
    have hjsq : (0 : ℝ) < (j : ℝ) ^ 2 := by nlinarith
    have hmono : η / 2 / (j : ℝ) ^ 2 ≤ η / (j : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right hjsq).mpr (by linarith)
    have hstep := mul_le_mul_of_nonneg_right hmono (by linarith : (0:ℝ) ≤ Real.log (Pseq j : ℝ))
    linarith
  have hkill := level_kill_collected_P1 η j (Pseq j) (Qseq (j - 1)) P1 hj hQp1 hPjR hP1R
    hG.P1_le_Qp hg3
  -- ⟦THE WINDOW⟧
  have hAm : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hAsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  set cp : ℝ := (2 * T / (Xd : ℝ) + 240) * C * Real.exp 3
      * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2
      * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))) with hcpdef
  -- ⟦THE PER-BLOCK BOUND: gain → covering → cell → the uniform price⟧
  have hstep : ∀ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        ≤ ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp := by
    intro v hv
    have hvpos : 0 < v := ramI_pos_of_mem hHj hlogPj hv
    have hufloor : Real.log (Pseq j : ℝ) - 1 / Hseq j ≤ (v : ℝ) / Hseq j :=
      ramI_bottom_deficit hHj0 hv
    have hutop0 : (v : ℝ) / Hseq j ≤ Real.log (Qseq j : ℝ) := ramI_top_le hHj0 hQjR hv
    have hcellB : ∀ r ∈ ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)),
        (∫ t in (seamAnn X T \ seamBall X t₁)
              ∩ TsetGr c Pseq Qseq Hseq (mrAlpha η) Jb j r,
            ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
          ≤ Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j) * cp := by
      intro r hr
      have hrpos : 0 < r := ramI_pos_of_mem hHp hlogPp hr
      have hlow : Real.log (Pseq (j - 1) : ℝ) - 1 ≤ (r : ℝ) / Hseq (j - 1) := by
        have h := ramI_bottom_deficit hHp0 hr
        have h2 : 1 / Hseq (j - 1) ≤ 1 := by
          rw [div_le_one hHp0]; linarith
        linarith
      have hstop : (r : ℝ) / Hseq (j - 1) ≤ Real.log (Qseq (j - 1) : ℝ) :=
        ramI_top_le hHp0 (by linarith) hr
      have hcb := hcell c b Pseq Qseq Hseq (mrAlpha η) Jb j r N Xd v T _
        hHp hrpos hXd hT
        (measurableSet_annulus_TsetGr c Pseq Qseq Hseq (mrAlpha η) Jb j r X T t₁)
        (annulus_TsetGr_subset_Icc c Pseq Qseq Hseq (mrAlpha η) Jb j r X T t₁)
        Set.inter_subset_right hb hc
      have hcp := cell_price_uniform η T C (Real.log (Pseq (j - 1) : ℝ) - 1)
        (Hseq j) (Hseq (j - 1)) j v r Xd (Pseq j) (Qseq j) (Qseq (j - 1))
        hη hG.eta_lt6 hj hHj hHp hC hT hXd hvpos hrpos (by linarith) hlow
        (by linarith) (by linarith) hstop (by linarith) hufloor hPjR (hbot v hv)
        hG.cell.gate2 hlog2
      rw [← hcpdef] at hcp
      refine le_trans hcb ?_
      have hE : Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j)
          * Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j) = 1 := by
        rw [← Real.exp_add,
          show 2 * mrAlpha η j * (v : ℝ) / Hseq j
              + -(2 * mrAlpha η j) * (v : ℝ) / Hseq j = 0 by ring, Real.exp_zero]
      have h2 := mul_le_mul_of_nonneg_left hcp
        (Real.exp_pos (2 * mrAlpha η j * (v : ℝ) / Hseq j)).le
      rw [← mul_assoc, hE, one_mul] at h2
      exact h2
    have hcov := integral_TsetG_le_card_mul c Pseq Qseq Hseq (mrAlpha η) Jb j hj
      ((continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2)
      (fun t => sq_nonneg _) hT (seamAnn X T \ seamBall X t₁) hAm hAsub _ hcellB
    have hgain := integral_ramMain_le_exp_mul_ramR c b Pseq Qseq Hseq (mrAlpha η) Jb j N Xd T
      ((seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j)
      (hAm.inter (measurableSet_TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j))
      (fun _ ht => hAsub ht.1) Set.inter_subset_right v hv
    have hE' : Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
        * Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j) = 1 := by
      rw [← Real.exp_add,
        show -(2 * mrAlpha η j) * (v : ℝ) / Hseq j
            + 2 * mrAlpha η j * (v : ℝ) / Hseq j = 0 by ring, Real.exp_zero]
    calc (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
            ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
        ≤ Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
            * ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
                ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := hgain
      _ ≤ Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
            * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
                * (Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j) * cp)) :=
          mul_le_mul_of_nonneg_left hcov (Real.exp_pos _).le
      _ = (Real.exp (-(2 * mrAlpha η j) * (v : ℝ) / Hseq j)
              * Real.exp (2 * mrAlpha η j * (v : ℝ) / Hseq j))
            * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp) := by
          ring
      _ = ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp := by
          rw [hE', one_mul]
  -- ⟦THE `v`-SUM: free, the summand is `v`-independent⟧
  have hsum : (∑ v ∈ ramI (Hseq j) (Pseq j) (Qseq j),
        ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖ramMain (Hseq j) N Xd (Pseq j) (Qseq j) b c v t‖ ^ 2)
      ≤ ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
          * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp) := by
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  -- ⟦THE GEOMETRY AND THE KILL⟧
  have hTX0 : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) + 240 := by
    have h : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) := div_nonneg (by linarith) hXdR.le
    linarith
  have hGpos : (0 : ℝ) ≤ (2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 :=
    mul_nonneg (mul_nonneg hTX0 hC.le) (Real.exp_pos 3).le
  have hPjrpow : (0 : ℝ) ≤ (Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))) :=
    Real.rpow_nonneg hPjR.le _
  have hc1 : ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
      ≤ 2 * (Hseq j * Real.log (Qseq j : ℝ)) := ramI_card_two_mul _ _ (by nlinarith)
  have hc2 : ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
      ≤ 2 * (Hseq (j - 1) * Real.log (Qseq (j - 1) : ℝ)) := ramI_card_two_mul _ _ (by nlinarith)
  have hgeom := level_geometry_collapse (Hseq j) (Hseq (j - 1)) j P1 (Qseq j) (Qseq (j - 1))
    hG.Hp_le_Hj (by linarith) (by linarith) hG.cell.logQ_le_rpow_of_gate2 (by linarith)
    hG.Hj_pin hG.P1_le_Qp
  have hcardgeom : 2 * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
        * ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
        * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2
      ≤ 1536 * (j : ℝ) ^ 6 * (Qseq (j - 1) : ℝ) ^ 3 := by
    refine le_trans ?_ hgeom
    have h1 : (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
        ≤ (2 * (Hseq j * Real.log (Qseq j : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hc1 2
    have hA : 2 * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
        ≤ 2 * (2 * (Hseq j * Real.log (Qseq j : ℝ))) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have hB := mul_le_mul hA hc2 (Nat.cast_nonneg _) (by positivity)
    have hD := mul_le_mul_of_nonneg_right hB
      (by positivity : (0:ℝ) ≤ 4 * Real.log (Qseq j : ℝ) ^ 2)
    exact mul_le_mul_of_nonneg_right hD (by positivity)
  have hmain : 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
        * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
            * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ) * cp))
      ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
          * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) := by
    rw [hcpdef]
    calc 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
            * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)
                * (((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
                    * ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3
                        * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2
                        * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))))))
        = (2 * (((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ)) ^ 2
              * ((ramI (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1))).card : ℝ)
              * (4 * Real.log (Qseq j : ℝ) ^ 2) * (Qseq (j - 1) : ℝ) ^ 2)
            * (((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3)
                * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))))) := by ring
      _ ≤ (1536 * (j : ℝ) ^ 6 * (Qseq (j - 1) : ℝ) ^ 3)
            * (((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3)
                * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))))) :=
          mul_le_mul_of_nonneg_right hcardgeom (mul_nonneg hGpos hPjrpow)
      _ = ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 * 1536)
            * ((j : ℝ) ^ 6 * (Qseq (j - 1) : ℝ) ^ 3
                * ((Pseq j : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))))) := by ring
      _ ≤ ((2 * T / (Xd : ℝ) + 240) * C * Real.exp 3 * 1536)
            * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hkill (mul_nonneg hGpos (by norm_num))
      _ = 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
            * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) := by ring
  -- ⟦LEMMA 12, AND THE ROWS⟧
  have hL12 := lemma12_on_TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j hHj N Xd hXd hN hPj1
    a b c hcoef hb hc hwin X T t₁ hT
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (by positivity : (0:ℝ) ≤ 2 * ((ramI (Hseq j) (Pseq j) (Qseq j)).card : ℝ))
  rw [lemma12Rows]
  linarith [hL12, hscaled, hmain]

/-! ## §9 — H-3: the `j`-collection and THE GRADED `𝒯`-LEG -/

/-- **H-3a — the `j`-collection** (MR p.27's last line).  A family priced at
`K/(j²P₁) + R_j` on `2 ≤ j ≤ J` sums against `Σ_{j≥2}1/j² ≤ 1` (`USetBalance.sum_inv_sq_Icc_le`
at `j₀ = 2`):

  `Σ_{j=2}^{J} E_j ≤ K/P₁ + Σ_{j=2}^{J} R_j`.

`J` never appears on the right: this is exactly why MR's `η/(2j²)` in condition `(3)` carries
a `j²` and not a `j` — the collection has to converge uniformly in `J`, which grows with
`X` (catch #253). -/
theorem sum_Ej_collected (K : ℝ) (hK : 0 ≤ K) (P1 Jb : ℕ) (hP1 : (0 : ℝ) < (P1 : ℝ))
    (E R : ℕ → ℝ)
    (hE : ∀ j ∈ Finset.Icc 2 Jb, E j ≤ K * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) + R j) :
    ∑ j ∈ Finset.Icc 2 Jb, E j ≤ K * (1 / (P1 : ℝ)) + ∑ j ∈ Finset.Icc 2 Jb, R j := by
  refine le_trans (Finset.sum_le_sum hE) ?_
  rw [Finset.sum_add_distrib]
  have hid : ∀ j ∈ Finset.Icc 2 Jb,
      K * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ))) = K * (1 / (P1 : ℝ)) * ((1 : ℝ) / (j : ℝ) ^ 2) := by
    intro j _
    rw [one_div, one_div, one_div, mul_inv]
    ring
  have h1 : ∑ j ∈ Finset.Icc 2 Jb, K * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
      = K * (1 / (P1 : ℝ)) * ∑ j ∈ Finset.Icc 2 Jb, (1 : ℝ) / (j : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hid
  have h2 := sum_inv_sq_Icc_le 2 Jb (le_refl 2)
  have hK0 : (0 : ℝ) ≤ K * (1 / (P1 : ℝ)) := by positivity
  have h3 : K * (1 / (P1 : ℝ)) * ∑ j ∈ Finset.Icc 2 Jb, (1 : ℝ) / (j : ℝ) ^ 2
      ≤ K * (1 / (P1 : ℝ)) * (1 / (((2 : ℕ) : ℝ) - 1)) := mul_le_mul_of_nonneg_left h2 hK0
  have h4 : K * (1 / (P1 : ℝ)) * (1 / (((2 : ℕ) : ℝ) - 1)) = K * (1 / (P1 : ℝ)) := by
    norm_num
  linarith [h1.le, h1.ge, h3, h4.le, h4.ge]

set_option maxHeartbeats 800000 in
-- the leg splits at `j = 1`, applies two landed pages under a `Finset.sum_le_sum`, and
-- carries Lemma 12's rows level by level; the assembled row expressions are large
/-- **H-3 — THE GRADED `𝒯`-LEG** (`TLeg_bound`).  The whole second summand of the graded seam
row, bounded:

  `∫_{(Ann∖ball) ∩ 𝒯totG}‖F(1+it)‖² dt`
    `≤ 2(H₁ log Q₁ + 1)(TQ₁/X_d + 1)P₁^{−2α₁}(4(H₁/(1−2α₁))e^{(1−2α₁)/H₁}`
    `      + 60(H₁/α₁)e^{4α₁/H₁})`                                        ← MR §8.1, level 1
    `  + 1536·C·e³·(2T/X_d + 240)/P₁`                                      ← MR §8.2, `j ≥ 2`
    `  + Σ_{j=1}^{J} E_j`                                                  ← Lemma 12's rows.

`SeamGraded.seam_T_additivityG` splits the union into the disjoint levels; `TLegE1.E1_pin`
prices `j = 1`; `Ej_bound` prices each `j ≥ 2`; `sum_Ej_collected` collects them.  At MR's own
pins the level-1 term is `(log Q₁)^{1/3}/P₁^{1/6−η}` (`TLegE1`'s verdict) and the level-`j`
block is `O(1/P₁)`, so the leg is `o(1)` exactly when §8.1's is — which is MR p.25's claim.

Every gate rides the statement: the per-level bundle `LevelGates … j` for `2 ≤ j ≤ J`, level
1's own four, the Lemma-12 data at every level, `η ∈ (0,1/6)` (which supplies `α`'s numerals
through `alpha_gates_from_eta`), and the measure frame. -/
theorem TLeg_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jb N Xd P1 : ℕ) (X T t₁ : ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jb → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ T → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jb, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
        a (p * m) = b j m * c p) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jb, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ seamTtotG c Pseq Qseq Hseq (mrAlpha η) Jb,
          ‖spoly N a t‖ ^ 2)
        ≤ 2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
              * (T * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
              * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
              * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                    * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                  + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
          + 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) * (1 / (P1 : ℝ))
          + ∑ j ∈ Finset.Icc 1 Jb,
              lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c := by
  obtain ⟨C, hC, hEj⟩ := Ej_bound
  refine ⟨C, hC, ?_⟩
  intro c a b Pseq Qseq Hseq η Jb N Xd P1 X T t₁ hη h6 hJb hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  obtain ⟨hα1, hα1', -⟩ := alpha_gates_from_eta η hη h6
  -- ⟦THE SPLIT OVER THE DISJOINT LEVELS⟧
  have hAm : MeasurableSet (seamAnn X T \ seamBall X t₁) :=
    (measurableSet_seamAnn X T).diff (measurableSet_seamBall X t₁)
  have hAsub : seamAnn X T \ seamBall X t₁ ⊆ Set.Icc (-T) T :=
    fun _ ht => seamAnn_subset_Icc X T ht.1
  have hadd := seam_T_additivityG (f := c) (Pseq := Pseq) (Qseq := Qseq) (Hseq := Hseq)
    (αseq := mrAlpha η) (J := Jb) (F := fun t : ℝ => ‖spoly N a t‖ ^ 2)
    ((continuous_spoly N a).norm.pow 2) hT hAm hAsub
  have hIcc : Finset.Icc 1 Jb = insert 1 (Finset.Icc 2 Jb) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : (1 : ℕ) ∉ Finset.Icc 2 Jb := by simp
  -- ⟦LEVEL 1: MR §8.1 at the pins⟧
  have h1 := E1_pin c Pseq Qseq Hseq (mrAlpha η) Jb hH1 hα1 hα1' N Xd hXd hN hP1s hPQ1 a (b 1)
    (hcoef 1 (by simp [Finset.mem_Icc]; omega)) (hb 1) hc
    (hwin 1 (by simp [Finset.mem_Icc]; omega)) X T t₁ hT hbot1
  -- ⟦LEVELS `j ≥ 2`: MR §8.2⟧
  have h2 : ∀ j ∈ Finset.Icc 2 Jb,
      (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
          ‖spoly N a t‖ ^ 2)
        ≤ (1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)) * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
          + lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c := by
    intro j hj
    have hj1 : j ∈ Finset.Icc 1 Jb := by
      rw [Finset.mem_Icc] at hj ⊢
      omega
    have h := hEj c a (b j) Pseq Qseq Hseq η Jb j N Xd P1 X T t₁ (hG j hj) hXd hN hT
      (hcoef j hj1) (hb j) hc (hwin j hj1)
    calc (∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
            ‖spoly N a t‖ ^ 2)
        ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)
              * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
            + lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c := h
      _ = (1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)) * (1 / ((j : ℝ) ^ 2 * (P1 : ℝ)))
            + lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c := by ring
  have hK0 : (0 : ℝ) ≤ 1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240) := by
    have hTX0 : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) + 240 := by
      have h : (0 : ℝ) ≤ 2 * T / (Xd : ℝ) := div_nonneg (by linarith) hXdR.le
      linarith
    exact mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1536 * C) (Real.exp_pos 3).le) hTX0
  have hcol := sum_Ej_collected (1536 * C * Real.exp 3 * (2 * T / (Xd : ℝ) + 240)) hK0 P1 Jb hP1
    (fun j => ∫ t in (seamAnn X T \ seamBall X t₁) ∩ TsetG c Pseq Qseq Hseq (mrAlpha η) Jb j,
      ‖spoly N a t‖ ^ 2)
    (fun j => lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) T a (b j) c) h2
  -- ⟦THE ASSEMBLY⟧
  rw [hadd, hIcc, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, lemma12Rows]
  linarith [h1, hcol]

/-! ## §10 — H-4: the feed into the graded capstone's `𝒯`-slot -/

/-- **H-4 — THE SEAM ROW IN CLOSED SHAPE** (`TLeg_feeds_capstone`).

`GradedCapstone.hUG34_unconditional`'s exit is

  `∫_{Ann}‖F‖² ≤ 8S² + ∫_{(Ann∖ball) ∩ 𝒯totG fb Pseq Qseq Hseq αseq Jset}‖F‖²
                    + 2(T_ann/X + 1)(log X)^{−θ₂₉₃+ε}`,

i.e. the `𝒯`-leg is the row's ONLY remaining unbounded summand.  This theorem consumes that
exit **at the graded `𝒯`-leg's own instantiation** — `fb := c` (the coefficient seam: the
partition datum must be the Ramaré prime coefficient the block factor carries, or MR (21)'s
gain does not bite) and `αseq := mrAlpha η` (eq (20)) — and replaces the integral by
`TLeg_bound`'s bound.  The result is the seam row with NO integral on the right:

  `∫_{Ann}‖F‖² ≤ 8S² + (§8.1's level-1 term + 1536·C·e³(2T/X_d+240)/P₁ + Σ_j E_j)
                    + 2(T_ann/X + 1)(log X)^{−θ₂₉₃+ε}`.

**What the kernel certifies here, exactly** (the honest scope): the row hypothesis `hcap` is
`hUG34_unconditional`'s conclusion transcribed verbatim at `fb := c`, `αseq := mrAlpha η`,
`T := Tann`, so the two SHAPES fit and the composition type-checks.  What is NOT certified
here is the simultaneous satisfiability of that theorem's own ~60 gates with `TLeg_bound`'s
(they live in different parameter families — the `𝒰`-side's `H₈₃`/`θ₂₉₃` pins versus the
graded `H_j`/`P_j`/`Q_j` ladder); wiring those is a station-level reconciliation, not a
statement fit, and is recorded as `G5`'s residual rather than hidden inside a
`sorry`-free-but-vacuous instance. -/
theorem TLeg_feeds_capstone :
    ∃ C : ℝ, 0 < C ∧ ∀ (c a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq : ℕ → ℝ)
      (η : ℝ) (Jset N Xd P1 : ℕ) (X Tann t₁ S ε : ℝ),
      0 < η → η < 1 / 6 → 1 ≤ Jset → 1 ≤ Xd → 2 * Xd ≤ N → 0 ≤ Tann → (0 : ℝ) < (P1 : ℝ) →
      (∀ j ∈ Finset.Icc 2 Jset, LevelGates Pseq Qseq Hseq η P1 Xd j) →
      2 ≤ Hseq 1 → 1 ≤ Pseq 1 → Pseq 1 ≤ Qseq 1 →
      (∀ v ∈ ramI (Hseq 1) (Pseq 1) (Qseq 1), 1 ≤ ramRbot (Hseq 1) Xd v) →
      (∀ j ∈ Finset.Icc 1 Jset, ∀ p m, p.Prime → Pseq j ≤ p → p ≤ Qseq j → ¬ p ∣ m →
        a (p * m) = b j m * c p) →
      (∀ j m, ‖b j m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ j ∈ Finset.Icc 1 Jset, ∀ p m : ℕ, p.Prime → Pseq j ≤ p → p ≤ Qseq j →
        c p * b j m ≠ 0 →
        (Xd : ℝ) ≤ (p : ℝ) * (m : ℝ) ∧ (p : ℝ) * (m : ℝ) ≤ 2 * (Xd : ℝ)) →
      -- ⟦THE CAPSTONE ROW⟧ `GradedCapstone.hUG34_unconditional`'s conclusion, verbatim,
      -- at `fb := c` and `αseq := mrAlpha η`
      (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
          ≤ 8 * S ^ 2
            + (∫ t in (seamAnn X Tann \ seamBall X t₁)
                ∩ seamTtotG c Pseq Qseq Hseq (mrAlpha η) Jset, ‖spoly N a t‖ ^ 2)
            + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) →
      (∫ t in seamAnn X Tann, ‖spoly N a t‖ ^ 2)
        ≤ 8 * S ^ 2
          + (2 * (Hseq 1 * Real.log (Qseq 1 : ℝ) + 1)
                * (Tann * (Qseq 1 : ℝ) / (Xd : ℝ) + 1)
                * (Pseq 1 : ℝ) ^ (-(2 * mrAlpha η 1))
                * (4 * (Hseq 1 / (1 - 2 * mrAlpha η 1))
                      * Real.exp ((1 - 2 * mrAlpha η 1) / Hseq 1)
                    + 60 * (Hseq 1 / mrAlpha η 1) * Real.exp (4 * mrAlpha η 1 / Hseq 1))
              + 1536 * C * Real.exp 3 * (2 * Tann / (Xd : ℝ) + 240) * (1 / (P1 : ℝ))
              + ∑ j ∈ Finset.Icc 1 Jset,
                  lemma12Rows N Xd (Pseq j) (Qseq j) (Hseq j) Tann a (b j) c)
          + 2 * ((Tann / X + 1) * (Real.log X) ^ (-theta293 + ε)) := by
  obtain ⟨C, hC, hleg⟩ := TLeg_bound
  refine ⟨C, hC, ?_⟩
  intro c a b Pseq Qseq Hseq η Jset N Xd P1 X Tann t₁ S ε hη h6 hJ hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin hcap
  have h := hleg c a b Pseq Qseq Hseq η Jset N Xd P1 X Tann t₁ hη h6 hJ hXd hN hT hP1 hG
    hH1 hP1s hPQ1 hbot1 hcoef hb hc hwin
  linarith [hcap, h]

end Salt.MR
