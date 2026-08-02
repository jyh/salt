/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S15SelLinearWide

/-!
# `FlatFloorBump` — THE TWO FLOOR BUMPS THE FLAT RE-FIRE OWES

⟦LADDER-L G4⟧  `S15SelLinearWide.s15_sel''_L_gk_witness_flat_wide` produces the linear-door
register at the flat design point, but two of its hypotheses are NOT discharged there — they
are `M`-floor demands the caller must meet:

* `hbfl : 24·Cg/δ₀ ≤ flatDoorM A` — the register's `bfloor` line;
* `hMfl : Mfl ≤ flatDoorM A` — the graded twin's `ℕ`-floor.

At the flat TERMINAL's own pins (`S16FlatTerminal.logChowla2_witnessed_scale_flat`:
`Cg ≤ 2·10¹²`, `1/838400 ≤ δ₀`, `Mfl ≤ 2^355`) both are pure `A`-arithmetic, and this page
kernelizes them.  The verdicts:

| demand | value | needs `e^{1.6A} ≥` | least integer `A` |
|---|---|---|---|
| `24·Cg/δ₀` | `4.02432·10¹⁹` | `1.2488·10²⁵` | `A ≥ 36.117`, so **37** |
| `Mfl` | `7.3379·10¹⁰⁶` | `2.2770·10¹¹²` | `A ≥ 161.696`, so **162** |

So `162 ≤ A` clears both, and the flat terminal chain's design floor is raised from `26` to
`162` in place (`HloExportMRFlatRoot` §1–§3, `S16FlatTerminal` §5–§7).  `162 ≥ 26`, so
`S15SelLinearWide.flat_linear_joint_point`'s uniform `A ≥ 26` is untouched, as is every other
`26`-floored statement: the bump only STRENGTHENS the hypothesis the terminal asks its caller
for, and the terminal's own export `162 ≤ A` is what the re-fire reads.

⟦THE EXPONENTIAL LADDER⟧ the bumps are `Nat.le_floor` against `flatDoorM`'s definition, so
the whole cost is one lower bound on `Real.exp`.  At `A = 37` the crude `2.7 < e` suffices
(`2.7^59 ≈ 2.85·10²⁵` against `1.2488·10²⁵`); at `A = 162` it does NOT — `2.7^259 ≈ 5.3·10¹¹¹`
falls short of `2.2770·10¹¹²` by a factor `4.3`, because `(e/2.7)^259 = 5.7`.  So the second
bump is routed through `e^4 ≥ 54.598` (`Real.exp_one_gt_d9` to the fourth power, exact to
`5·10⁻⁵`), giving `e^259 ≥ 54.598^64·2.718^3 ≈ 3.03·10¹¹²` — a `1.33×` margin, and numerals
of ~300 digits rather than ~2850.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the two exponential floors -/

/-- `e^4 ≥ 54.598` — `Real.exp_one_gt_d9` raised to the fourth (`e^4 = 54.59815003…`). -/
private theorem flat_exp_four_ge : (54.598 : ℝ) ≤ Real.exp 4 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hp : (2.7182818283 : ℝ) ^ (4 : ℕ) ≤ (Real.exp 1) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he.le 4
  have hE : (Real.exp 1) ^ (4 : ℕ) = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [hE] at hp
  have hn : (54.598 : ℝ) ≤ (2.7182818283 : ℝ) ^ (4 : ℕ) := by norm_num
  linarith

/-- `e^59 ≥ 1.3·10²⁵` — the `bfloor` bump's exponential floor, at the crude `2.7 < e`
(`2.7^59 ≈ 2.85·10²⁵`, better than twice what is asked). -/
theorem flat_exp_59_ge : (13 : ℝ) * 10 ^ 24 ≤ Real.exp 59 := by
  have he : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hp : (2.7 : ℝ) ^ (59 : ℕ) ≤ (Real.exp 1) ^ (59 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he.le 59
  have hE : (Real.exp 1) ^ (59 : ℕ) = Real.exp 59 := by rw [← Real.exp_nat_mul]; norm_num
  rw [hE] at hp
  have hn : (13 : ℝ) * 10 ^ 24 ≤ (2.7 : ℝ) ^ (59 : ℕ) := by norm_num
  linarith

/-- `e^259 ≥ 3·10¹¹²` — the `Mfl` bump's exponential floor.  Routed through `e^4 ≥ 54.598`
because the crude `2.7 < e` loses a factor `(e/2.7)^259 = 5.7` and misses by `4.3×`. -/
theorem flat_exp_259_ge : (3 : ℝ) * 10 ^ 112 ≤ Real.exp 259 := by
  have h4 : (54.598 : ℝ) ≤ Real.exp 4 := flat_exp_four_ge
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h256 : (54.598 : ℝ) ^ (64 : ℕ) ≤ Real.exp 256 := by
    have hid : (Real.exp 4) ^ (64 : ℕ) = Real.exp 256 := by rw [← Real.exp_nat_mul]; norm_num
    calc (54.598 : ℝ) ^ (64 : ℕ) ≤ (Real.exp 4) ^ (64 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) h4 64
      _ = Real.exp 256 := hid
  have h3 : (2.718 : ℝ) ^ (3 : ℕ) ≤ Real.exp 3 := by
    have hid : (Real.exp 1) ^ (3 : ℕ) = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    calc (2.718 : ℝ) ^ (3 : ℕ) ≤ (Real.exp 1) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h1 3
      _ = Real.exp 3 := hid
  have hsplit : Real.exp 259 = Real.exp 256 * Real.exp 3 := by rw [← Real.exp_add]; norm_num
  have hprod : (54.598 : ℝ) ^ (64 : ℕ) * (2.718 : ℝ) ^ (3 : ℕ) ≤ Real.exp 256 * Real.exp 3 :=
    mul_le_mul h256 h3 (by positivity) (le_trans (by positivity) h256)
  have hn : (3 : ℝ) * 10 ^ 112 ≤ (54.598 : ℝ) ^ (64 : ℕ) * (2.718 : ℝ) ^ (3 : ℕ) := by
    norm_num
  rw [hsplit]
  linarith

/-! ## §1 — ⟦BUMP 1⟧ the `bfloor` line at the terminal's constant pins -/

/-- **THE DOOR MODULUS CLEARS `4.02432·10¹⁹` AT `A ≥ 37`** — `310301·(4.02432·10¹⁹+1)
≈ 1.2488·10²⁵ ≤ e^{59.2}`, and `flatDoorM_ge` pays the `−1`. -/
theorem flatDoorM_ge_bfloorConst {A : ℝ} (hA : 37 ≤ A) :
    (40243200000000000000 : ℝ) ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have hmono : Real.exp 59 ≤ Real.exp (3.2 * A / 2) := Real.exp_le_exp.mpr (by linarith)
  have hexp : (13 : ℝ) * 10 ^ 24 ≤ Real.exp (3.2 * A / 2) := le_trans flat_exp_59_ge hmono
  have hge : Real.exp (3.2 * A / 2) / 310301 - 1 ≤ ((flatDoorM A : ℕ) : ℝ) := flatDoorM_ge A
  have hdiv : (40243200000000000001 : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 310301)]
    nlinarith [hexp]
  linarith

/-- **⟦BUMP 1, AT THE TERMINAL'S OWN PINS⟧** — `s15_sel''_L_gk_witness_flat_wide`'s `hbfl`
slot, discharged from `Cg ≤ 2·10¹²` and `1/838400 ≤ δ₀` at any `A ≥ 37`.  The two sides meet
EXACTLY at the pins (`24·2·10¹²·838400 = 4.02432·10¹⁹`), so no numeral here is slack. -/
theorem flatDoorM_bfloor_bump {A Cg δ₀ : ℝ} (hA : 37 ≤ A) (hδ : 0 < δ₀)
    (hδb : 1 / 838400 ≤ δ₀) (hCg : Cg ≤ 2 * 10 ^ 12) :
    24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have hstep : 24 * Cg / δ₀ ≤ (40243200000000000000 : ℝ) := by
    rw [div_le_iff₀ hδ]
    nlinarith [hδb, hCg]
  exact le_trans hstep (flatDoorM_ge_bfloorConst hA)

/-! ## §2 — ⟦BUMP 2⟧ the `Mfl` floor at the terminal's `2^355` -/

set_option exponentiation.threshold 4000 in
/-- **THE DOOR MODULUS CLEARS `2^355` AT `A ≥ 162`** — `310301·(2^355+1) ≈ 2.2770·10¹¹²`
against `e^{259.2} ≥ e^{259} ≥ 3·10¹¹²`, a `1.32×` margin.  `A ≥ 161.696` is the exact
threshold, so `162` is the least integer that works. -/
theorem flatDoorM_ge_pow355 {A : ℝ} (hA : 162 ≤ A) : (2 : ℕ) ^ 355 ≤ flatDoorM A := by
  refine Nat.le_floor ?_
  have hmono : Real.exp 259 ≤ Real.exp (3.2 * A / 2) := Real.exp_le_exp.mpr (by linarith)
  have hexp : (3 : ℝ) * 10 ^ 112 ≤ Real.exp (3.2 * A / 2) := le_trans flat_exp_259_ge hmono
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 310301)]
  have hn : (((2 : ℕ) ^ 355 : ℕ) : ℝ) * 310301 ≤ (3 : ℝ) * 10 ^ 112 := by
    push_cast
    norm_num
  linarith

/-- **⟦BUMP 2, AT THE TERMINAL'S OWN PIN⟧** — `s15_sel''_L_gk_witness_flat_wide`'s `hMfl`
slot, discharged from the terminal's `Mfl ≤ 2^355` at any `A ≥ 162`. -/
theorem flatDoorM_Mfl_bump {A : ℝ} {Mfl : ℕ} (hA : 162 ≤ A) (hMfl : Mfl ≤ 2 ^ 355) :
    Mfl ≤ flatDoorM A := le_trans hMfl (flatDoorM_ge_pow355 hA)

/-- **⟦THE DESIGN FLOOR THE FLAT TERMINAL NOW CARRIES⟧** — `162 ≤ A` implies both bumps'
hypotheses at once (`37 ≤ 162`), which is why the terminal chain's `26` is replaced by `162`
rather than by two separate floors. -/
theorem flat162_ge_37 {A : ℝ} (hA : 162 ≤ A) : (37 : ℝ) ≤ A := by linarith

/-- `162 ≤ A → 26 ≤ A` — the compatibility with every `26`-floored flat statement
(`flat_linear_joint_point`, `s15_sel''_L_witness_flat`, `flat_exp_half_ge`, …). -/
theorem flat162_ge_26 {A : ℝ} (hA : 162 ≤ A) : (26 : ℝ) ≤ A := by linarith

/-- **⟦THE BUMPED WITNESS⟧** — `s15_sel''_L_gk_witness_flat_wide` with its two `M`-floor
hypotheses DISCHARGED, at the flat terminal's own constant pins.  This is the exact shape the
re-fire consumes: nothing about `Cg`, `δ₀`, `Mfl` is left for the caller beyond the pins the
terminal already exports. -/
theorem s15_sel''_L_gk_witness_flat_bumped {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 838400 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ 2 ^ 355)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) :=
  s15_sel''_L_gk_witness_flat_wide (flat162_ge_26 hA) Klev hKle hδ
    (by nlinarith [hδb] : (1 : ℝ) / 2 ^ 20 ≤ δ₀) hK hKb hCt hCtb
    (flatDoorM_bfloor_bump (flat162_ge_37 hA) hδ hδb hCg)
    (flatDoorM_Mfl_bump hA hMfl) hx0win heps hlo hhi

end Salt.MR

end
