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

set_option exponentiation.threshold 4000 in
/-- **⟦BUMP 1, AT THE TERMINAL'S OWN PINS⟧** — `s15_sel''_L_gk_witness_flat_wide`'s `hbfl`
slot, discharged from `Cg ≤ 2·10¹²` and `1/838400 ≤ δ₀` at any `A ≥ 37`.  The two sides meet
EXACTLY at the pins (`24·2·10¹²·838400 = 4.02432·10¹⁹`), so no numeral here is slack. -/
theorem flatDoorM_bfloor_bump {A Cg δ₀ : ℝ} {c : ℕ} (hc1 : 1 ≤ c) (hcb : c ≤ 1096)
    (hA : 162 ≤ A) (hδ : 0 < δ₀)
    (hδb : 1 / (838400 * (c : ℝ) ^ 2) ≤ δ₀) (hCg : Cg ≤ 2 * 10 ^ 12) :
    24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have hcR1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
  have hcRb : (c : ℝ) ≤ 1096 := by exact_mod_cast hcb
  have hcsqb : (c : ℝ) ^ 2 ≤ 1201216 := by nlinarith [hcR1, hcRb]
  have hcsq1 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by nlinarith [hcR1]
  -- ⟦THE ROUTE CHANGE⟧ the landed bump lands on `flatDoorM_ge_bfloorConst`
  -- (`4.02432·10^19`, ZERO slack).  At the shift the demand is `4.02432·10^19·c²
  -- ≤ 4.84·10^25`, which that constant cannot cover — so the bump is re-routed through
  -- `flatDoorM_ge_pow355` (`2^355 ≈ 7.3·10^106`), clearing by 81 orders.
  have hcsqpos : (0 : ℝ) < (c : ℝ) ^ 2 := by nlinarith [hcR1]
  have hkey : (1 : ℝ) / 838400 ≤ (c : ℝ) ^ 2 * δ₀ := by
    have h := mul_le_mul_of_nonneg_left hδb hcsqpos.le
    calc (1 : ℝ) / 838400 = (c : ℝ) ^ 2 * (1 / (838400 * (c : ℝ) ^ 2)) := by field_simp
      _ ≤ (c : ℝ) ^ 2 * δ₀ := h
  have hstep : 24 * Cg / δ₀ ≤ (40243200000000000000 : ℝ) * (c : ℝ) ^ 2 := by
    rw [div_le_iff₀ hδ]
    nlinarith [hkey, hCg]
  have hcap : (40243200000000000000 : ℝ) * (c : ℝ) ^ 2 ≤ (2 : ℝ) ^ (355 : ℕ) := by
    have h355 : (48345000000000000000000000 : ℝ) ≤ (2 : ℝ) ^ (355 : ℕ) := by norm_num
    nlinarith [hcsqb, h355]
  have hpow : (2 : ℝ) ^ (355 : ℕ) ≤ ((flatDoorM A : ℕ) : ℝ) := by
    exact_mod_cast flatDoorM_ge_pow355 hA
  linarith [hstep, hcap, hpow]

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

/-! ## §2b — ⟦THE `A`-WINDOW⟧ THE PARAMETRIC FLOOR AND THE BAND-LANE TOLERANCE

⟦BAND-WINDOW, 2026-08-02⟧  §2's `flatDoorM_ge_pow355` spends the `2^355` pin at ONE place —
the graded twin's `Mfl` floor — and that pin is itself the image of the band-lane rider
`log Cband ≤ 40` under `S11HoistGrade.s11_grade_floor_hoistCb_prod_le`.  CMU-HUNT traced the
constant the corpus's own chain actually produces (`log Cband ≈ 22 661`, dominated by
`PowRegion`'s literal double-exponential `T₀`), so the `40` is unsatisfiable AT `40` while the
door modulus `flatDoorM A = ⌊e^{1.6A}/310301⌋₊` grows without bound in `A`.  This section
prices the trade: **how large a band constant does a given design constant `A` tolerate?**

⟦THE WINDOW, PROVEN HERE⟧ `flatDoorM_gradeFloor_win`:

> `162 ≤ A`, `0 < C`, `log C ≤ 0.64·A − 20`  ⟹  `s11GradeFloor Cb(C) ≤ flatDoorM A`.

The accounting, all of it inside `exp` (no numeral `rpow` anywhere): `8·Cb ≤ e^{62}·e^{W}`
(`W := log C`'s ceiling), charged against the discarded numeral `N ≥ e^{48}`, gives
`u ≤ e^{14+W}`; the grade floor's `5/2` power gives `Mfl ≤ e^{35+2.5W} + 2`; and
`35 + 2.5W = 1.6A − 15` at `W = 0.64A − 20`, so `310301·Mfl ≤ 0.11·e^{1.6A} + 620602
≤ e^{1.6A}` — a `10.5×` margin on the leading term.  The ideal (constants unrounded) tolerance
is `0.64·A − 4.2`; this proof's honest one is `0.64·A − 20`, i.e. **15.8 nats of rounding**.

⟦WHAT IT BUYS⟧ at the design floor `A = 162` the tolerance is `log C ≤ 83.68` (the corpus asks
`40`); the traced ceiling `22 661` needs `A ≥ 35 439`, so CMU-HUNT's recommended `A₀ = 36 000`
clears it by `359` nats.  And `A` is symbolic in the flat terminal, so raising it is free.
`flatDoorM_ge_pow` is the same trade stated in the `2^n` currency the landed pin uses. -/

/-- `e^{15} ≥ 3·10⁶` (true value `3.269·10⁶`) — the window's leading-term floor. -/
theorem flat_exp_15_ge : (3 : ℝ) * 10 ^ 6 ≤ Real.exp 15 := by
  have h4 : (54.598 : ℝ) ≤ Real.exp 4 := flat_exp_four_ge
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h12 : (54.598 : ℝ) ^ (3 : ℕ) ≤ Real.exp 12 := by
    have hid : (Real.exp 4) ^ (3 : ℕ) = Real.exp 12 := by rw [← Real.exp_nat_mul]; norm_num
    calc (54.598 : ℝ) ^ (3 : ℕ) ≤ (Real.exp 4) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h4 3
      _ = Real.exp 12 := hid
  have h3 : (2.718 : ℝ) ^ (3 : ℕ) ≤ Real.exp 3 := by
    have hid : (Real.exp 1) ^ (3 : ℕ) = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    calc (2.718 : ℝ) ^ (3 : ℕ) ≤ (Real.exp 1) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) h1 3
      _ = Real.exp 3 := hid
  have hsplit : Real.exp 15 = Real.exp 12 * Real.exp 3 := by rw [← Real.exp_add]; norm_num
  have hprod : (54.598 : ℝ) ^ (3 : ℕ) * (2.718 : ℝ) ^ (3 : ℕ) ≤ Real.exp 12 * Real.exp 3 :=
    mul_le_mul h12 h3 (by positivity) (le_trans (by positivity) h12)
  have hn : (3 : ℝ) * 10 ^ 6 ≤ (54.598 : ℝ) ^ (3 : ℕ) * (2.718 : ℝ) ^ (3 : ℕ) := by norm_num
  rw [hsplit]; linarith

/-- `e^{62} ≥ 4.6·10²⁵` (true value `8.44·10²⁶`) — the numerator's ceiling, at `e^4 ≥ 54.598`
raised to the fifteenth times `e^2`. -/
theorem flat_exp_62_ge : (46 : ℝ) * 10 ^ 25 ≤ Real.exp 62 := by
  have h4 : (54.598 : ℝ) ≤ Real.exp 4 := flat_exp_four_ge
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h60 : (54.598 : ℝ) ^ (15 : ℕ) ≤ Real.exp 60 := by
    have hid : (Real.exp 4) ^ (15 : ℕ) = Real.exp 60 := by rw [← Real.exp_nat_mul]; norm_num
    calc (54.598 : ℝ) ^ (15 : ℕ) ≤ (Real.exp 4) ^ (15 : ℕ) := pow_le_pow_left₀ (by norm_num) h4 15
      _ = Real.exp 60 := hid
  have h2 : (2.718 : ℝ) ^ (2 : ℕ) ≤ Real.exp 2 := by
    have hid : (Real.exp 1) ^ (2 : ℕ) = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    calc (2.718 : ℝ) ^ (2 : ℕ) ≤ (Real.exp 1) ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) h1 2
      _ = Real.exp 2 := hid
  have hsplit : Real.exp 62 = Real.exp 60 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hprod : (54.598 : ℝ) ^ (15 : ℕ) * (2.718 : ℝ) ^ (2 : ℕ) ≤ Real.exp 60 * Real.exp 2 :=
    mul_le_mul h60 h2 (by positivity) (le_trans (by positivity) h60)
  have hn : (46 : ℝ) * 10 ^ 25 ≤ (54.598 : ℝ) ^ (15 : ℕ) * (2.718 : ℝ) ^ (2 : ℕ) := by norm_num
  rw [hsplit]; linarith

/-- `e^{48} ≤ 1.6·10²¹` (true value `7.017·10²⁰`) — the discarded numeral
`N = (4·10^{10})^{2.501} ≥ 1.6·10²¹` dominates `e^{48}`, which is what turns the ratio bound
into a pure exponent subtraction. -/
theorem flat_exp_48_le : Real.exp 48 ≤ 1600000000000000000000 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpow : (Real.exp 1) ^ (48 : ℕ) ≤ (2.7182818286 : ℝ) ^ (48 : ℕ) :=
    pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 48
  have hE : (Real.exp 1) ^ (48 : ℕ) = Real.exp 48 := by rw [← Real.exp_nat_mul]; norm_num
  have hn : (2.7182818286 : ℝ) ^ (48 : ℕ) ≤ 1600000000000000000000 := by norm_num
  rw [hE] at hpow; linarith

set_option exponentiation.threshold 4000 in
/-- **⟦THE DOOR MODULUS AT AN ARBITRARY BINARY PIN⟧** (`flatDoorM_ge_pow`) —
`flatDoorM_ge_pow355` with the `355` freed: `2^n ≤ flatDoorM A` as soon as

> `A ≥ (n·log 2 + log 310301 + 1)/1.6`.

The `+1` is the `−1` of `flatDoorM_ge` paid in the exponent (`e·310301·2^n ≥ 310301·(2^n+1)`),
which is why this is stated with a whole extra nat of slack rather than at the exact threshold
`(n·log 2 + log 310301)/1.6`.  At `n = 355` it asks `A ≥ 162.32` where §2's hand-tuned route
asks `162`; every consumer of the pin is `A`-symbolic, so the third of a nat is free. -/
theorem flatDoorM_ge_pow (n : ℕ) {A : ℝ}
    (hA : ((n : ℝ) * Real.log 2 + Real.log 310301 + 1) / 1.6 ≤ A) :
    (2 : ℕ) ^ n ≤ flatDoorM A := by
  refine Nat.le_floor ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 310301)]
  have hcast : (((2 : ℕ) ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hprod : (((2 : ℕ) ^ n : ℕ) : ℝ) * 310301
      = Real.exp ((n : ℝ) * Real.log 2 + Real.log 310301) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 310301), hcast,
      ← Real.log_pow, Real.exp_log h2pos]
  have hlin : (n : ℝ) * Real.log 2 + Real.log 310301 + 1 ≤ 1.6 * A := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1.6)] at hA; linarith
  rw [hprod]
  exact Real.exp_le_exp.mpr (by linarith)

set_option exponentiation.threshold 4000 in
/-- **⟦THE BAND-LANE `A`-WINDOW⟧** (`flatDoorM_gradeFloor_win`) — the graded twin's `Mfl`
floor clears the door modulus at every design constant `A ≥ 162` whose window contains the
band-lane constant:

> `log C ≤ 0.64·A − 20  ⟹  s11GradeFloor (C·4^{Aexp}·(e^{52.5}·4^{1.05}) + 1) ≤ flatDoorM A`.

This is `s11_grade_floor_hoistCb_prod_le` (which fixes `log C ≤ 40` and lands on the numeral
pin `2^355`) with the numeral pin removed and the tolerance made linear in `A`.  At `A = 162`
it is STRICTLY WEAKER than the landed route in the constant it admits (`83.68` against the
`40` the corpus asks) and strictly stronger in reach: the window is unbounded in `A`. -/
theorem flatDoorM_gradeFloor_win {A C : ℝ} (hA : 162 ≤ A) (hC0 : 0 < C)
    (hC : Real.log C ≤ 0.64 * A - 20) :
    s11GradeFloor (C * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1)
      ≤ flatDoorM A := by
  set W : ℝ := 0.64 * A - 20 with hWdef
  have hW0 : (0 : ℝ) ≤ W := by rw [hWdef]; linarith
  have hexpW : (0 : ℝ) < Real.exp W := Real.exp_pos W
  have hexpW1 : (1 : ℝ) ≤ Real.exp W := Real.one_le_exp hW0
  have hCle : C ≤ Real.exp W := by
    calc C = Real.exp (Real.log C) := (Real.exp_log hC0).symm
      _ ≤ Real.exp W := Real.exp_le_exp.mpr hC
  set Cb : ℝ := C * (4 : ℝ) ^ (s13Aexp) * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ)) + 1 with hCbdef
  set N : ℝ := (40000000000 : ℝ) ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000)) with hNdef
  have hN : (1600000000000000000000 : ℝ) ≤ N := s11_grade_numeral_ge
  have hN0 : (0 : ℝ) < N := by linarith
  -- ⟦THE NUMERATOR⟧ `8·Cb ≤ e^{62}·e^{W}` (the true ratio is `4.51·10²⁶` against `8.44·10²⁶`)
  have hE0 : (0 : ℝ) ≤ Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) := by positivity
  have hE : Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ) ≤ 880000000000000000000000 := by
    nlinarith [s11_exp525_le, s11_rpow4_le, Real.exp_pos (52.5 : ℝ),
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (1.05 : ℝ)]
  have hCE : C * (Real.exp 52.5 * (4 : ℝ) ^ (1.05 : ℝ))
      ≤ Real.exp W * 880000000000000000000000 :=
    mul_le_mul hCle hE hE0 (le_of_lt hexpW)
  have hkey : (46 : ℝ) * 10 ^ 25 * Real.exp W ≤ Real.exp 62 * Real.exp W :=
    mul_le_mul_of_nonneg_right flat_exp_62_ge (le_of_lt hexpW)
  have hnum : 8 * Cb ≤ Real.exp 62 * Real.exp W := by
    rw [hCbdef, s11_four_rpow_aexp]
    nlinarith [hCE, hexpW1, hkey]
  -- ⟦THE RATIO⟧ `8·Cb/N ≤ e^{14+W}`
  have hratio : 8 * Cb / N ≤ Real.exp (14 + W) := by
    rw [div_le_iff₀ hN0]
    have hsplit : Real.exp 62 * Real.exp W = Real.exp (14 + W) * Real.exp 48 := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc 8 * Cb ≤ Real.exp 62 * Real.exp W := hnum
      _ = Real.exp (14 + W) * Real.exp 48 := hsplit
      _ ≤ Real.exp (14 + W) * N :=
          mul_le_mul_of_nonneg_left (le_trans flat_exp_48_le hN)
            (le_of_lt (Real.exp_pos _))
  -- ⟦THE `5/2` POWER⟧ `u^{2.5} ≤ e^{35+2.5W}`
  have hu : max 1 (8 * Cb / N) ≤ Real.exp (14 + W) :=
    max_le (Real.one_le_exp (by linarith)) hratio
  have hu1 : (1 : ℝ) ≤ max 1 (8 * Cb / N) := le_max_left _ _
  have hpow : (max 1 (8 * Cb / N)) ^ (2.5 : ℝ) ≤ Real.exp (35 + 2.5 * W) := by
    have h1 : (max 1 (8 * Cb / N)) ^ (2.5 : ℝ) ≤ (Real.exp (14 + W)) ^ (2.5 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hu (by norm_num)
    have h2 : (Real.exp (14 + W)) ^ (2.5 : ℝ) = Real.exp (35 + 2.5 * W) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]; congr 1; ring
    rw [h2] at h1; exact h1
  -- ⟦THE FLOOR, READ OFF⟧ `Mfl < u^{2.5} + 2`
  have hcast : ((s11GradeFloor Cb : ℕ) : ℝ)
      = (⌈(max 1 (8 * Cb / N)) ^ (2.5 : ℝ)⌉₊ : ℝ) + 1 := by
    rw [s11GradeFloor, ← hNdef]; push_cast; ring
  have hcl : ((⌈(max 1 (8 * Cb / N)) ^ (2.5 : ℝ)⌉₊ : ℕ) : ℝ)
      < (max 1 (8 * Cb / N)) ^ (2.5 : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  -- ⟦THE DOOR⟧ `35 + 2.5·W = 1.6A − 15`, and `310301 ≤ 0.11·e^{15}`
  refine Nat.le_floor ?_
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 310301)]
  have hEq : Real.exp (35 + 2.5 * W) = Real.exp (3.2 * A / 2 - 15) := by
    congr 1; rw [hWdef]; ring
  have hE15 : Real.exp (3.2 * A / 2) = Real.exp (3.2 * A / 2 - 15) * Real.exp 15 := by
    rw [← Real.exp_add]; congr 1; ring
  have hYpos : (0 : ℝ) < Real.exp (3.2 * A / 2 - 15) := Real.exp_pos _
  have hbig : (3 : ℝ) * 10 ^ 6 * Real.exp (3.2 * A / 2 - 15) ≤ Real.exp (3.2 * A / 2) := by
    rw [hE15]; nlinarith [flat_exp_15_ge, hYpos]
  have hXbig : (3 : ℝ) * 10 ^ 112 ≤ Real.exp (3.2 * A / 2) :=
    le_trans flat_exp_259_ge (Real.exp_le_exp.mpr (by linarith))
  rw [hEq] at hpow
  linarith [hcast, hcl, hpow, hbig, hXbig]

/-- **⟦THE BUMPED WITNESS, AT THE WINDOW⟧** (`s15_sel''_L_gk_witness_flat_bumped_win`) —
`s15_sel''_L_gk_witness_flat_bumped` with its `Mfl` slot taken DIRECTLY at the door modulus
instead of through the `2^355` pin.  The `bfloor` bump is unchanged (it reads only the `Cg`/`δ₀`
pins, which no window touches). -/
theorem s15_sel''_L_gk_witness_flat_bumped_win {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl c : ℕ}
    {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcb : c ≤ 1096) (hh7c : Real.log (c : ℝ) ≤ 7)
    (hδ : 0 < δ₀) (hδb : 1 / (838400 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) :=
  s15_sel''_L_gk_witness_flat_wide (flat162_ge_26 hA) Klev hKle hc1 hcb hh7c hδ
    (by
      have h1 : (0 : ℝ) < (c : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
        positivity
      have : (1 : ℝ) / (2 ^ 20 * (c : ℝ) ^ 2) ≤ 1 / (838400 * (c : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1]
      linarith [hδb] : (1 : ℝ) / (2 ^ 20 * (c : ℝ) ^ 2) ≤ δ₀) hK hKb hCt hCtb
    (flatDoorM_bfloor_bump hc1 hcb hA hδ hδb hCg)
    hMfl hx0win heps hlo hhi

/-- **⟦THE BUMPED WITNESS⟧** — `s15_sel''_L_gk_witness_flat_wide` with its two `M`-floor
hypotheses DISCHARGED, at the flat terminal's own constant pins.  This is the exact shape the
re-fire consumes: nothing about `Cg`, `δ₀`, `Mfl` is left for the caller beyond the pins the
terminal already exports. -/
theorem s15_sel''_L_gk_witness_flat_bumped {A : ℝ} (hA : 162 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl c : ℕ}
    {R : ChowlaRegime}
    (hc1 : 1 ≤ c) (hcb : c ≤ 1096) (hh7c : Real.log (c : ℝ) ≤ 7)
    (hδ : 0 < δ₀) (hδb : 1 / (838400 * (c : ℝ) ^ 2) ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 539)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 23)
    (hCg : Cg ≤ 2 * 10 ^ 12) (hMfl : Mfl ≤ 2 ^ 355)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / (2 ^ 9 * (c : ℚ)) ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    -- amended per REF-FLAT-SAT: the `Λ` slot carries the `Nat.ceil` overshoot factor `2`
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 2 * Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) :=
  s15_sel''_L_gk_witness_flat_wide (flat162_ge_26 hA) Klev hKle hc1 hcb hh7c hδ
    (by
      have h1 : (0 : ℝ) < (c : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
        positivity
      have : (1 : ℝ) / (2 ^ 20 * (c : ℝ) ^ 2) ≤ 1 / (838400 * (c : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [h1]
      linarith [hδb] : (1 : ℝ) / (2 ^ 20 * (c : ℝ) ^ 2) ≤ δ₀) hK hKb hCt hCtb
    (flatDoorM_bfloor_bump hc1 hcb hA hδ hδb hCg)
    (flatDoorM_Mfl_bump hA hMfl) hx0win heps hlo hhi

end Salt.MR

end
