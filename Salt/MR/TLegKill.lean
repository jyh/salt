/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TLegCover
import Salt.MR.MultShiuBridge

/-!
# TLegKill — MR §8.2's `ℓ`-pin, gates and THE KILL (ROUTE G, `G4d`/`G4e`/`G4f`)

`docs/exploration/hsup-design.md` ⟦V6⟧'s Route-G ladder, nodes `G4d` (the `ℓ`-pin
arithmetic), `G4e` (the `(2)`/`(3)` gate collection and the assembled cell) and `G4f` (the
α-decay and the level-`j` kill), on top of `G4a`/`G4b` (`Salt.MR.TLegCover`) and `G4c`
(`Salt.MR.MultShiuBridge`).  Everything here is **parallel and additive**: no landed
statement is touched.

MR p.26–27 closes the level-`j` page of eq (24) in four moves.  `G4a`/`G4b` landed the first
(the covering and the entry ticket); this file lands the rest.

## The device (MR p.26, transcribed)

On the cell `𝒯_{j,r}` the entry ticket inserts `(|Q_{r,H_{j−1}}|e^{α_{j−1}r/H_{j−1}})^{2ℓ} ≥ 1`
for ANY `ℓ ≥ 1`, so

  `E_j ≪ (H_j log Q_j)³·e^{−2α_j v/H_j}·exp(2ℓ_{j,r}α_{j−1}r/H_{j−1})
          ·∫_{𝒯_{j,r}}|Q_{r,H_{j−1}}(1+it)^{ℓ}R_{v,H_j}(1+it)|² dt`.

MR then CHOOSES

  `ℓ_{j,r} := ⌈(v/H_j)/(r/H_{j−1})⌉ ≤ (H_{j−1}/r)·(v/H_j) + 1`.

**THE KEY CANCELLATION** — the whole device rides one line of ceiling arithmetic:

  `ℓ_{j,r}·(r/H_{j−1}) ≤ v/H_j + r/H_{j−1}`,

so that `e^{−2α_j v/H_j}·e^{2ℓ_{j,r}α_{j−1}r/H_{j−1}} ≤ exp(2v(α_{j−1}−α_j)/H_j
+ 2α_{j−1}r/H_{j−1})`: the `v`-dependence collapses onto the α-DIFFERENCE, which eq (20)
makes negative.  That is `ellPin_mul_block_le` / `exp_ellPin_cancel` below.

**THE PIN'S SECOND FACE** — the same ceiling, read the other way (`Nat.le_ceil`), gives
`ℓ_{j,r}·(r/H_{j−1}) ≥ v/H_j`, hence `Y₁^{ℓ}·X_v ≥ e^{v/H_j}·X e^{−v/H_j} = X`: Lemma 13's
`C/(Y₁^ℓ X₀)` denominator is `≥ X`, which is exactly how MR's `T/X` prefactor reappears
(`ellPin_window_bottom_ge`).  One `⌈·⌉` does both jobs.

## The stones

* **G4d** — `ellPin` (the pin), `ellPin_mul_block_le` (THE KEY CANCELLATION),
  `exp_ellPin_alpha_le` / `exp_ellPin_cancel` (its exponential forms),
  `ellPin_window_bottom_ge` (the second face), `factorial_sq_le_exp`
  (`ℓ!² ≤ e^{2ℓ log ℓ}`), `ell_log_ell_le` (MR's `ℓ log ℓ` page) and `factorial_sq_le_pin`
  (the two composed).
* **G4e** — `CellGates` (MR §2's `(2)`/`(3)` as named conjuncts), the two facts `(2)`
  implies (`loglogQ_le_of_gate2`, `logQ_le_rpow_of_gate2`), `gate2_absorb` (the exponent
  absorption), `cell_geometry_collapse` (MR's
  `H_j³(log Q_j)^5Q_{j−1}e^{2α_{j−1}r/H_{j−1}} ≤ j⁶Q_{j−1}³`), the mixed-width moment
  (`mix_moment`, on `mixCoeff` and its support/majorant stones) and the assembled cell
  (`cell_ramR_normalized`, `cell_bound_raw`, and `cell_bound_pinned` — the pinned form whose
  Lemma-13 denominator is `X_d` itself, i.e. MR's `T/X`).
* **G4f** — `mrAlpha` (eq (20)), `mrAlpha_diff` / `mrAlpha_decay_le` (the α-decay, SIGN
  verified against p.24), `level_kill_exponent` / `level_kill_exp` (THE KILL
  `P_j^{−η/(2j²)}`) and `level_kill_collected(_P1)` (gate `(3)` → `1/(j²Q_{j−1})`,
  `1/(j²P₁)`).

## The α-decay: the SIGN (verified, p.24 eq (20))

`α_j := 1/4 − η(1 + 1/(2j))` INCREASES with `j` (`1/4 − (3/2)η = α₁ ≤ … ≤ α_J ≤ 1/4 − η`),
so the difference the device consumes is NEGATIVE:

  `α_{j−1} − α_j = −η/(2j(j−1)) ≤ −η/(2j²)`  for `2 ≤ j`,

exactly (not merely up to a constant).  The `j(j−1)` form is the sharper fact and is stated
(`mrAlpha_diff`); `mrAlpha_decay_le` is the `j²` weakening the kill actually spends.

## Conventions and pins (law #253, byte-checked)

* **Two widths, not one.**  MR §8.2 multiplies `Q_{r,H_{j−1}}` (level `j−1`) against
  `R_{v,H_j}` (level `j`): DIFFERENT `H`, `P`, `Q`.  `G4c`'s `multShiu_moment` fuses the two
  parameter sets into one `(H,P,Q)` and therefore does NOT apply at §8.2's calibration.  The
  mixed-width moment `mix_moment` is re-derived here from `G4c`'s own generic machinery
  (`af_pow_mul_support_*`, `norm_af_mul_le`, `maj_le_factorial_blockDiv`,
  `MomentsA2.lemma13_moment`) with the parameters split; nothing in `MultShiuBridge` is
  touched.
* **Every gate rides the statement.**  `0 < r`, `0 < H`, the block-bottom `log P_{j−1} − 1`,
  the `η`-range, the `H_j` pin of p.24, the `1`-boundedness of the two data: all explicit.
  The `#I_{j−1}` union cost stays `#I_{j−1}` (`G4a`'s posture).
* **`ℓ_{j,r}` is a ℕ.**  `ellPin` returns `⌈·⌉₊`; the casts are explicit and the `0 < r`
  gate (without which the ratio is a division by zero) is carried wherever the pin's
  arithmetic is used.
* **No negation.**  `G0`–`G4c`'s posture is kept.
* **What is NOT closed here.**  See "The G5 handoff" below — the `(v,r)`-sum assembly and
  MR's two `≪`-absorptions are enumerated, not hidden.

## The G5 handoff (the exact residual, enumerated)

1. **The `(v,r)`-sum.**  `cell_bound_raw` prices ONE cell.  The level page needs
   Lemma 12 on `A_j` → the level-`j` graded gain → `G4a`'s covering (`#I_{j−1}`) → the
   `v`-sum over `I_j` — the `E1_bound` route with the extra `r`-index.  Not attempted here.
2. **MR's `2^{ℓ}` absorption.**  `mix_moment`'s second term carries an explicit `2^ℓ`
   (`(2Y₁)^ℓ Mr/(Y₁^ℓ X₀)`); MR absorbs it into `exp(2ℓ log ℓ)` under `≪`.  Honest here:
   the factor is left visible.
3. **MR's `(ℓ+1)!² → exp(2ℓ log ℓ)` absorption.**  Lemma 13 as MR states it carries
   `(ℓ+1)!²`; the corpus' `lemma13_moment` carries `ℓ!²`, and `factorial_sq_le_exp` is proved
   at `ℓ!²` — the cleaner fact.  Any consumer wanting MR's literal `(ℓ+1)!²` must re-pay.
4. **The `v`-floor deficit.**  `v ∈ I_j` gives `v/H_j ≥ log P_j − 1/H_j`, not `≥ log P_j`;
   `level_kill_exp` therefore carries `hv : log P_j ≤ v/H_j` as an in-statement gate rather
   than deriving it from membership.  (MR's `≪` swallows the `1/H_j`.)

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 (the conditions `(2)`, `(3)`, p.6),
§8.2 pp.26–27 (the `ℓ_{j,r}` page, transcribed above), p.24 (eq (20) and the `H_j` table);
`docs/sources/mr_extract.md` §2.7, §6.6; `docs/exploration/hsup-design.md` ⟦V6⟧.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory

/-! ## §1 — G4d-i: the pin `ℓ_{j,r}` -/

/-- **MR p.26's `ℓ_{j,r} := ⌈(v/H_j)/(r/H_{j−1})⌉`.**  The exponent to which the level-`(j−1)`
block polynomial is raised on the cell `𝒯_{j,r}`.  `Hj` is `H_j`, `Hp` is `H_{j−1}`; the
gate `0 < r` (without which the inner division is by zero) rides every statement that uses
the pin's arithmetic, never the definition. -/
noncomputable def ellPin (Hj Hp : ℝ) (v r : ℕ) : ℕ :=
  ⌈((v : ℝ) / Hj) / ((r : ℝ) / Hp)⌉₊

/-- `ℓ_{j,r} ≤ (v/H_j)/(r/H_{j−1}) + 1` — MR's own inequality, the `⌈·⌉` upper face. -/
lemma ellPin_le_add_one (Hj Hp : ℝ) (v r : ℕ)
    (hx : 0 ≤ ((v : ℝ) / Hj) / ((r : ℝ) / Hp)) :
    ((ellPin Hj Hp v r : ℕ) : ℝ) ≤ ((v : ℝ) / Hj) / ((r : ℝ) / Hp) + 1 :=
  (Nat.ceil_lt_add_one hx).le

/-- `(v/H_j)/(r/H_{j−1}) ≤ ℓ_{j,r}` — the `⌈·⌉` lower face, which is what recovers `T/X`. -/
lemma le_ellPin (Hj Hp : ℝ) (v r : ℕ) :
    ((v : ℝ) / Hj) / ((r : ℝ) / Hp) ≤ ((ellPin Hj Hp v r : ℕ) : ℝ) :=
  Nat.le_ceil _

/-- The pin is `≥ 1` exactly when the ratio is positive (MR asks `ℓ_{j,r} ≥ 1`). -/
lemma one_le_ellPin (Hj Hp : ℝ) (v r : ℕ)
    (hx : 0 < ((v : ℝ) / Hj) / ((r : ℝ) / Hp)) : 1 ≤ ellPin Hj Hp v r :=
  Nat.ceil_pos.mpr hx

/-! ## §2 — G4d-ii: THE KEY CANCELLATION -/

/-- **THE KEY CANCELLATION (MR p.26).**  The pin's defining ceiling gives

  `ℓ_{j,r}·(r/H_{j−1}) ≤ v/H_j + r/H_{j−1}`,

i.e. the price `e^{2ℓα_{j−1}r/H_{j−1}}` of the entry ticket costs at most one `e^{2α_{j−1}v/H_j}`
plus one block-width factor.  This single line is the whole reason MR's `ℓ`-power device
closes: it converts the `v`-dependence at level `j−1` into the SAME `v/H_j` the level-`j`
threshold pays, so the two combine into the α-difference (`exp_ellPin_cancel`). -/
theorem ellPin_mul_block_le (Hj Hp : ℝ) (v r : ℕ) (hHj : 0 < Hj) (hHp : 0 < Hp)
    (hr : 0 < r) :
    ((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp) ≤ (v : ℝ) / Hj + (r : ℝ) / Hp := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hs : (0 : ℝ) < (r : ℝ) / Hp := div_pos hrR hHp
  have hu : (0 : ℝ) ≤ (v : ℝ) / Hj := div_nonneg (Nat.cast_nonneg v) hHj.le
  have hx : (0 : ℝ) ≤ ((v : ℝ) / Hj) / ((r : ℝ) / Hp) := div_nonneg hu hs.le
  have hmul := mul_le_mul_of_nonneg_right (ellPin_le_add_one Hj Hp v r hx) hs.le
  have hid : (((v : ℝ) / Hj) / ((r : ℝ) / Hp) + 1) * ((r : ℝ) / Hp)
      = (v : ℝ) / Hj + (r : ℝ) / Hp := by
    rw [add_mul, one_mul, div_mul_cancel₀ _ hs.ne']
  linarith [hmul, hid.le, hid.ge]

/-- The exponential form of the key cancellation: the entry ticket's price at the pin. -/
theorem exp_ellPin_alpha_le (Hj Hp αp : ℝ) (v r : ℕ) (hHj : 0 < Hj) (hHp : 0 < Hp)
    (hr : 0 < r) (hα : 0 ≤ αp) :
    Real.exp (2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * αp * (r : ℝ) / Hp)
      ≤ Real.exp (2 * αp * ((v : ℝ) / Hj) + 2 * αp * ((r : ℝ) / Hp)) := by
  refine Real.exp_le_exp.mpr ?_
  have hkey := ellPin_mul_block_le Hj Hp v r hHj hHp hr
  have hrw : 2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * αp * (r : ℝ) / Hp
      = 2 * αp * (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)) := by ring
  rw [hrw]
  nlinarith [hkey, hα]

/-- **MR p.26's assembled exponential.**  The level-`j` threshold `e^{−2α_j v/H_j}` times the
entry ticket's price at the pin collapses onto the α-DIFFERENCE:

  `e^{−2α_j v/H_j}·e^{2ℓ_{j,r}α_{j−1}r/H_{j−1}} ≤ exp(2v(α_{j−1} − α_j)/H_j + 2α_{j−1}r/H_{j−1})`.

Both exponents are byte-shaped as the landed pieces produce them: the left factor is
`TLegE1.norm_ramMain_sq_le_of_mem_TsetG`'s, the right is `TLegCover.cell_integral_normalized`'s. -/
theorem exp_ellPin_cancel (Hj Hp αj αp : ℝ) (v r : ℕ) (hHj : 0 < Hj) (hHp : 0 < Hp)
    (hr : 0 < r) (hα : 0 ≤ αp) :
    Real.exp (-(2 * αj) * (v : ℝ) / Hj)
        * Real.exp (2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * αp * (r : ℝ) / Hp)
      ≤ Real.exp (2 * (v : ℝ) * (αp - αj) / Hj + 2 * αp * ((r : ℝ) / Hp)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hkey := ellPin_mul_block_le Hj Hp v r hHj hHp hr
  have hrw : -(2 * αj) * (v : ℝ) / Hj
        + 2 * ((ellPin Hj Hp v r : ℕ) : ℝ) * αp * (r : ℝ) / Hp
      = -(2 * αj) * ((v : ℝ) / Hj)
        + 2 * αp * (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp)) := by ring
  have hgoal : 2 * (v : ℝ) * (αp - αj) / Hj + 2 * αp * ((r : ℝ) / Hp)
      = -(2 * αj) * ((v : ℝ) / Hj) + 2 * αp * ((v : ℝ) / Hj + (r : ℝ) / Hp) := by ring
  rw [hrw, hgoal]
  nlinarith [hkey, hα]

/-! ## §3 — G4d-iii: THE PIN'S SECOND FACE (how `T/X` comes back) -/

/-- **THE PIN'S SECOND FACE.**  `Nat.le_ceil` reads the same pin the other way,
`ℓ_{j,r}·(r/H_{j−1}) ≥ v/H_j`, and therefore

  `Y₁^{ℓ}·X_v ≥ e^{v/H_j}·X e^{−v/H_j} = X`  at `Y₁ = ⌈e^{r/H_{j−1}}⌉`, `X_v = ⌈X e^{−v/H_j}⌉`,

so Lemma 13's denominator `Y₁^{ℓ}X₀` is at least the row length `X_d` — which is exactly how
MR's `T/X` prefactor reappears after the moment is applied.  One ceiling does both jobs. -/
theorem ellPin_window_bottom_ge (Hj Hp : ℝ) (v r Xd : ℕ) (hHp : 0 < Hp) (hr : 0 < r) :
    (Xd : ℝ)
      ≤ ((⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
          * ((⌈ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hs : (0 : ℝ) < (r : ℝ) / Hp := div_pos hrR hHp
  -- the ceiling's lower face, cleared of the inner division
  have hratio := le_ellPin Hj Hp v r
  have hmul : (v : ℝ) / Hj ≤ ((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp) := by
    have h := mul_le_mul_of_nonneg_right hratio hs.le
    rwa [div_mul_cancel₀ _ hs.ne'] at h
  -- `Y₁^ℓ ≥ e^{ℓ·r/H_{j−1}} ≥ e^{v/H_j}`
  have hY : Real.exp ((r : ℝ) / Hp) ≤ ((⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hYpow : Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp))
      ≤ ((⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r) := by
    have hexp : Real.exp (((ellPin Hj Hp v r : ℕ) : ℝ) * ((r : ℝ) / Hp))
        = Real.exp ((r : ℝ) / Hp) ^ (ellPin Hj Hp v r) := by
      rw [← Real.exp_nat_mul]
    rw [hexp]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hY _
  have hleft : Real.exp ((v : ℝ) / Hj)
      ≤ ((⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r) :=
    le_trans (Real.exp_le_exp.mpr hmul) hYpow
  -- `X₀ ≥ X_d e^{−v/H_j}`
  have hbot : ramRbot Hj Xd v ≤ ((⌈ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hbot0 : (0 : ℝ) ≤ ramRbot Hj Xd v := by
    rw [ramRbot]; positivity
  have hprod : Real.exp ((v : ℝ) / Hj) * ramRbot Hj Xd v
      ≤ ((⌈Real.exp ((r : ℝ) / Hp)⌉₊ : ℕ) : ℝ) ^ (ellPin Hj Hp v r)
          * ((⌈ramRbot Hj Xd v⌉₊ : ℕ) : ℝ) :=
    mul_le_mul hleft hbot hbot0 (le_trans (Real.exp_pos _).le hleft)
  have hcancel : Real.exp ((v : ℝ) / Hj) * ramRbot Hj Xd v = (Xd : ℝ) := by
    rw [ramRbot, ← mul_assoc, mul_comm (Real.exp ((v : ℝ) / Hj)) (Xd : ℝ), mul_assoc,
      ← Real.exp_add]
    have hz : (v : ℝ) / Hj + -(v : ℝ) / Hj = 0 := by ring
    rw [hz, Real.exp_zero, mul_one]
  linarith [hprod, hcancel.le, hcancel.ge]

/-! ## §4 — G4d-iv: the factorial page -/

/-- **`ℓ!² ≤ e^{2ℓ log ℓ}`** (MR p.26's `(ℓ+1)!² ≪ exp(2ℓ log ℓ)`, at the corpus' cleaner
`ℓ!²`).  The crude route: `ℓ! ≤ ℓ^ℓ` (`Nat.factorial_le_pow`) and `ℓ^ℓ = e^{ℓ log ℓ}`. -/
theorem factorial_sq_le_exp (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ((ℓ.factorial : ℕ) : ℝ) ^ 2 ≤ Real.exp (2 * (ℓ : ℝ) * Real.log (ℓ : ℝ)) := by
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hfac : ((ℓ.factorial : ℕ) : ℝ) ≤ (ℓ : ℝ) ^ ℓ := by
    exact_mod_cast Nat.factorial_le_pow ℓ
  have hnn : (0 : ℝ) ≤ ((ℓ.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpow : Real.exp ((ℓ : ℝ) * Real.log (ℓ : ℝ)) = (ℓ : ℝ) ^ ℓ := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have h2 : Real.exp (2 * (ℓ : ℝ) * Real.log (ℓ : ℝ))
      = Real.exp ((ℓ : ℝ) * Real.log (ℓ : ℝ)) * Real.exp ((ℓ : ℝ) * Real.log (ℓ : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc ((ℓ.factorial : ℕ) : ℝ) ^ 2
      = ((ℓ.factorial : ℕ) : ℝ) * ((ℓ.factorial : ℕ) : ℝ) := pow_two _
    _ ≤ (ℓ : ℝ) ^ ℓ * (ℓ : ℝ) ^ ℓ := mul_le_mul hfac hfac hnn (by positivity)
    _ = Real.exp (2 * (ℓ : ℝ) * Real.log (ℓ : ℝ)) := by rw [h2, hpow]

/-- **MR p.26's `ℓ log ℓ` page.**  At the pin, with `lPp` a lower bound for the block bottom
`r/H_{j−1}` (MR's `log P_{j−1} − 1`) and `llQ` an upper bound for `log(v/H_j + 1)` (MR's
`loglog Q_j`),

  `ℓ_{j,r} log ℓ_{j,r} ≤ (v/H_j)·llQ/lPp + llQ + 1`.

MR cites "the mean value theorem"; the elementary route used here is
`log(x+1) ≤ log x + 1/x` (`Real.log_le_sub_one_of_pos` at `(x+1)/x`), so
`(x+1)log(x+1) ≤ x log x + 1 + log(x+1)`.  Every gate is in-statement: `1 ≤ lPp` is what
makes `x ≤ v/H_j` (and hence `log(x+1) ≤ llQ`) available. -/
theorem ell_log_ell_le (Hj Hp llQ lPp : ℝ) (v r : ℕ) (hHj : 0 < Hj) (hHp : 0 < Hp)
    (hr : 0 < r) (hv : 0 < v) (hlPp : 1 ≤ lPp) (hlow : lPp ≤ (r : ℝ) / Hp)
    (hllQ : Real.log ((v : ℝ) / Hj + 1) ≤ llQ) :
    ((ellPin Hj Hp v r : ℕ) : ℝ) * Real.log ((ellPin Hj Hp v r : ℕ) : ℝ)
      ≤ (v : ℝ) / Hj * llQ / lPp + llQ + 1 := by
  set u : ℝ := (v : ℝ) / Hj with hudef
  set s : ℝ := (r : ℝ) / Hp with hsdef
  set x : ℝ := u / s with hxdef
  have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
  have hu : (0 : ℝ) < u := div_pos hvR hHj
  have hlPp0 : (0 : ℝ) < lPp := by linarith
  have hs : (0 : ℝ) < s := lt_of_lt_of_le hlPp0 hlow
  have hx : (0 : ℝ) < x := div_pos hu hs
  -- `llQ ≥ 0`
  have hllQ0 : (0 : ℝ) ≤ llQ :=
    le_trans (Real.log_nonneg (by linarith)) hllQ
  -- `x ≤ u/lPp ≤ u`
  have hxu' : x ≤ u / lPp := (div_le_div_iff_of_pos_left hu hs hlPp0).mpr hlow
  have hxu : x ≤ u := le_trans hxu' (div_le_self hu.le hlPp)
  -- the ceiling's two faces at the pin
  have hL : ((ellPin Hj Hp v r : ℕ) : ℝ) ≤ x + 1 := ellPin_le_add_one Hj Hp v r hx.le
  have hL1 : (1 : ℝ) ≤ ((ellPin Hj Hp v r : ℕ) : ℝ) := by
    exact_mod_cast one_le_ellPin Hj Hp v r hx
  have hlogL : Real.log ((ellPin Hj Hp v r : ℕ) : ℝ) ≤ Real.log (x + 1) :=
    Real.log_le_log (by linarith) hL
  have hlogL0 : (0 : ℝ) ≤ Real.log ((ellPin Hj Hp v r : ℕ) : ℝ) := Real.log_nonneg hL1
  have hprod : ((ellPin Hj Hp v r : ℕ) : ℝ) * Real.log ((ellPin Hj Hp v r : ℕ) : ℝ)
      ≤ (x + 1) * Real.log (x + 1) :=
    mul_le_mul hL hlogL hlogL0 (by linarith)
  -- `log(x+1) ≤ log x + 1/x`
  have hlogstep : Real.log (x + 1) ≤ Real.log x + 1 / x := by
    have hq : (0 : ℝ) < (x + 1) / x := by positivity
    have h1 := Real.log_le_sub_one_of_pos hq
    have h2 : Real.log ((x + 1) / x) = Real.log (x + 1) - Real.log x :=
      Real.log_div (by linarith) hx.ne'
    have h3 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  -- `(x+1)log(x+1) ≤ x log x + 1 + log(x+1)`
  have hxm : x * Real.log (x + 1) ≤ x * Real.log x + 1 := by
    have h := mul_le_mul_of_nonneg_left hlogstep hx.le
    have he : x * (Real.log x + 1 / x) = x * Real.log x + 1 := by field_simp
    rw [he] at h
    exact h
  have hring : (x + 1) * Real.log (x + 1) = x * Real.log (x + 1) + Real.log (x + 1) := by ring
  -- `x log x ≤ u·llQ/lPp`
  have hlogx : Real.log x ≤ llQ :=
    le_trans (Real.log_le_log hx (by linarith)) hllQ
  have hxlogx : x * Real.log x ≤ u * llQ / lPp := by
    have h1 : x * Real.log x ≤ x * llQ := mul_le_mul_of_nonneg_left hlogx hx.le
    have h2 : x * llQ ≤ (u / lPp) * llQ := mul_le_mul_of_nonneg_right hxu' hllQ0
    have h3 : (u / lPp) * llQ = u * llQ / lPp := by ring
    linarith
  -- `log(x+1) ≤ llQ`
  have hlogx1 : Real.log (x + 1) ≤ llQ :=
    le_trans (Real.log_le_log (by linarith) (by linarith : x + 1 ≤ u + 1)) hllQ
  linarith [hprod, hring.le, hring.ge, hxm, hxlogx, hlogx1]

/-- **G4d's factorial page at the pin** — `factorial_sq_le_exp ∘ ell_log_ell_le`:

  `ℓ_{j,r}!² ≤ exp(2(v/H_j)·llQ/lPp)·(e^{llQ})²·e²`.

At MR's calibration `llQ = loglog Q_j` the middle factor IS `(log Q_j)²`, and the first is
what gate `(2)` absorbs (`gate2_absorb`). -/
theorem factorial_sq_le_pin (Hj Hp llQ lPp : ℝ) (v r : ℕ) (hHj : 0 < Hj) (hHp : 0 < Hp)
    (hr : 0 < r) (hv : 0 < v) (hlPp : 1 ≤ lPp) (hlow : lPp ≤ (r : ℝ) / Hp)
    (hllQ : Real.log ((v : ℝ) / Hj + 1) ≤ llQ) :
    (((ellPin Hj Hp v r).factorial : ℕ) : ℝ) ^ 2
      ≤ Real.exp (2 * ((v : ℝ) / Hj) * llQ / lPp) * Real.exp llQ ^ 2 * Real.exp 2 := by
  have hx : (0 : ℝ) < ((v : ℝ) / Hj) / ((r : ℝ) / Hp) := by
    have hvR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv
    have hlPp0 : (0 : ℝ) < lPp := by linarith
    exact div_pos (div_pos hvR hHj) (lt_of_lt_of_le hlPp0 hlow)
  refine le_trans (factorial_sq_le_exp _ (one_le_ellPin Hj Hp v r hx)) ?_
  have hpage := ell_log_ell_le Hj Hp llQ lPp v r hHj hHp hr hv hlPp hlow hllQ
  have hAeq : 2 * ((v : ℝ) / Hj) * llQ / lPp = 2 * ((v : ℝ) / Hj * llQ / lPp) := by ring
  have hmono : Real.exp (2 * ((ellPin Hj Hp v r : ℕ) : ℝ)
        * Real.log ((ellPin Hj Hp v r : ℕ) : ℝ))
      ≤ Real.exp (2 * ((v : ℝ) / Hj) * llQ / lPp + (llQ + llQ) + 2) := by
    refine Real.exp_le_exp.mpr ?_
    rw [hAeq]
    linarith [hpage]
  refine le_trans hmono (le_of_eq ?_)
  rw [Real.exp_add, Real.exp_add, Real.exp_add]
  ring

/-! ## §5 — G4e-i: MR §2's conditions `(2)` and `(3)`, and what they buy -/

/-- A positive logarithm of a nonnegative real forces the real above `1` — the ℕ-cast
convention guard used throughout `CellGates` (`Real.log` is `0` off `(0,∞)`). -/
private lemma one_lt_of_log_pos {x : ℝ} (hx : 0 ≤ x) (h : 0 < Real.log x) : 1 < x := by
  by_contra hc
  exact absurd (Real.log_nonpos hx (not_lt.mp hc)) (not_le.mpr h)

/-- **MR §2's conditions `(2)`, `(3)` (p.6) at level `j`, plus §8.2's non-degeneracy pins.**

  `(2)  loglog Q_j/(log P_{j−1} − 1) ≤ η/(4j²)`,
  `(3)  8 log Q_{j−1} + 16 log j ≤ (η/j²)·log P_j`.

Transcribed verbatim from `docs/sources/mr_extract.md` §1 (the definition of `S`); `η ∈ (0,1/6)`
is MR's own range.  The three remaining fields are the non-degeneracy the §8.2 page consumes:
`log P_{j−1} > 1` (so `(2)`'s denominator is positive — MR's block bottom `r/H_{j−1} ≥
log P_{j−1} − 1` is what it prices), `log P_{j−1} ≤ log Q_{j−1}`, and `log Q_j ≥ 1` (so
`loglog Q_j ≥ 0`).  `2 ≤ j` is §8.2's own range (`j = 1` is §8.1, node `G3`). -/
structure CellGates (Pseq Qseq : ℕ → ℕ) (η : ℝ) (j : ℕ) : Prop where
  /-- MR's `η ∈ (0,1/6)`, lower end. -/
  eta_pos : 0 < η
  /-- MR's `η ∈ (0,1/6)`, upper end. -/
  eta_lt : η < 1 / 6
  /-- §8.2's range: the level below exists. -/
  two_le_j : 2 ≤ j
  /-- `(2)`'s denominator is positive; MR's block bottom is `log P_{j−1} − 1`. -/
  one_lt_logP : 1 < Real.log (Pseq (j - 1) : ℝ)
  /-- `P_{j−1} ≤ Q_{j−1}` in logarithmic form. -/
  logP_le_logQ : Real.log (Pseq (j - 1) : ℝ) ≤ Real.log (Qseq (j - 1) : ℝ)
  /-- `log Q_j ≥ 1`, so `loglog Q_j ≥ 0`. -/
  one_le_logQ : 1 ≤ Real.log (Qseq j : ℝ)
  /-- **MR (2)**: `loglog Q_j/(log P_{j−1} − 1) ≤ η/(4j²)`. -/
  gate2 : Real.log (Real.log (Qseq j : ℝ)) / (Real.log (Pseq (j - 1) : ℝ) - 1)
            ≤ η / (4 * (j : ℝ) ^ 2)
  /-- **MR (3)**: `8 log Q_{j−1} + 16 log j ≤ (η/j²)·log P_j`. -/
  gate3 : 8 * Real.log (Qseq (j - 1) : ℝ) + 16 * Real.log (j : ℝ)
            ≤ (η / (j : ℝ) ^ 2) * Real.log (Pseq j : ℝ)

namespace CellGates

variable {Pseq Qseq : ℕ → ℕ} {η : ℝ} {j : ℕ}

lemma jR_two (h : CellGates Pseq Qseq η j) : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h.two_le_j

lemma jR_pos (h : CellGates Pseq Qseq η j) : (0 : ℝ) < (j : ℝ) := by
  have := h.jR_two; linarith

lemma logQ_pos (h : CellGates Pseq Qseq η j) : (0 : ℝ) < Real.log (Qseq j : ℝ) :=
  lt_of_lt_of_le one_pos h.one_le_logQ

lemma loglogQ_nonneg (h : CellGates Pseq Qseq η j) :
    (0 : ℝ) ≤ Real.log (Real.log (Qseq j : ℝ)) := Real.log_nonneg h.one_le_logQ

lemma one_lt_Qpred (h : CellGates Pseq Qseq η j) : (1 : ℝ) < (Qseq (j - 1) : ℝ) := by
  refine one_lt_of_log_pos (Nat.cast_nonneg _) ?_
  have h1 := h.one_lt_logP
  have h2 := h.logP_le_logQ
  linarith

/-- **`(2)` implies `loglog Q_j ≤ (1/24)·log P_{j−1}`** (MR p.27).  The numeral is
`η/(4j²) ≤ η/4 < 1/24`, from `η < 1/6` and `j ≥ 2`; the `−1` in `(2)`'s denominator is
discarded (it only helps). -/
theorem loglogQ_le_of_gate2 (h : CellGates Pseq Qseq η j) :
    Real.log (Real.log (Qseq j : ℝ)) ≤ (1 / 24) * Real.log (Pseq (j - 1) : ℝ) := by
  have hden : (0 : ℝ) < Real.log (Pseq (j - 1) : ℝ) - 1 := by have := h.one_lt_logP; linarith
  have hj2 := h.jR_two
  have hnum : η / (4 * (j : ℝ) ^ 2) ≤ 1 / 24 := by
    have h4 : (4 : ℝ) ≤ 4 * (j : ℝ) ^ 2 := by nlinarith
    have hη := h.eta_pos
    have hstep : η / (4 * (j : ℝ) ^ 2) ≤ η / 4 :=
      (div_le_div_iff_of_pos_left hη (by linarith) (by norm_num)).mpr h4
    have hη6 := h.eta_lt
    linarith
  have hsplit : Real.log (Real.log (Qseq j : ℝ))
      = (Real.log (Real.log (Qseq j : ℝ)) / (Real.log (Pseq (j - 1) : ℝ) - 1))
          * (Real.log (Pseq (j - 1) : ℝ) - 1) := (div_mul_cancel₀ _ hden.ne').symm
  have hbound := mul_le_mul_of_nonneg_right (le_trans h.gate2 hnum) hden.le
  have hlogP := h.one_lt_logP
  nlinarith [hsplit.le, hsplit.ge, hbound]

/-- **`(2)` implies `log Q_j ≤ Q_{j−1}^{1/24}`** (MR p.27, the second consequence).
Exponentiate the previous stone through `log P_{j−1} ≤ log Q_{j−1}`. -/
theorem logQ_le_rpow_of_gate2 (h : CellGates Pseq Qseq η j) :
    Real.log (Qseq j : ℝ) ≤ (Qseq (j - 1) : ℝ) ^ ((1 : ℝ) / 24) := by
  have hQp : (1 : ℝ) < (Qseq (j - 1) : ℝ) := h.one_lt_Qpred
  have hstep : Real.log (Real.log (Qseq j : ℝ))
      ≤ (1 / 24) * Real.log (Qseq (j - 1) : ℝ) := by
    have h1 := h.loglogQ_le_of_gate2
    have h2 := h.logP_le_logQ
    linarith
  calc Real.log (Qseq j : ℝ)
      = Real.exp (Real.log (Real.log (Qseq j : ℝ))) := (Real.exp_log h.logQ_pos).symm
    _ ≤ Real.exp ((1 / 24) * Real.log (Qseq (j - 1) : ℝ)) := Real.exp_le_exp.mpr hstep
    _ = (Qseq (j - 1) : ℝ) ^ ((1 : ℝ) / 24) := by
        rw [Real.rpow_def_of_pos (by linarith)]; congr 1; ring

end CellGates

/-- **The exponent absorption `(2)` performs** (MR p.26–27).  With `llQ/lPp ≤ η/(4j²)`
(condition `(2)`) the `ℓ log ℓ` page's leading term is at most `(η/(2j²))·u`:

  `2u·llQ/lPp ≤ (η/(2j²))·u`  for `u ≥ 0`.

Stated on the bare reals so that `G4d`'s `factorial_sq_le_pin` and the gate meet without
either side unfolding the other. -/
theorem gate2_absorb (η llQ lPp u : ℝ) (j : ℕ) (hj : (0 : ℝ) < (j : ℝ))
    (hu : 0 ≤ u) (hg2 : llQ / lPp ≤ η / (4 * (j : ℝ) ^ 2)) :
    2 * u * llQ / lPp ≤ η / (2 * (j : ℝ) ^ 2) * u := by
  have hid : 2 * u * llQ / lPp = 2 * u * (llQ / lPp) := by ring
  have hstep : 2 * u * (llQ / lPp) ≤ 2 * u * (η / (4 * (j : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hg2 (by linarith)
  have hfin : 2 * u * (η / (4 * (j : ℝ) ^ 2)) = η / (2 * (j : ℝ) ^ 2) * u := by
    field_simp
    ring
  rw [hid]
  linarith [hstep, hfin.le, hfin.ge]

/-! ## §6 — G4e-ii: MR's cell geometry collapse -/

/-- **MR p.27's geometry collapse.**  Under `(2)`'s consequence `log Q_j ≤ Q_{j−1}^{1/24}`,
the block-range bound `r ≤ H_{j−1} log Q_{j−1}`, `2α_{j−1} ≤ 1` and the `H_j` pin of p.24
(`H_j = j²P₁^{1/6−η}/(log Q₁)^{1/3}`, so `H_j³ ≤ j⁶P₁^{1/2}`),

  `H_j³(log Q_j)^5·Q_{j−1}·e^{2α_{j−1}r/H_{j−1}} ≤ j⁶·Q_{j−1}³`.

MR's own chain, byte for byte: `e^{2α_{j−1}r/H_{j−1}} ≤ Q_{j−1}^{2α_{j−1}} ≤ Q_{j−1}`,
`(log Q_j)^5 ≤ Q_{j−1}^{5/24}`, `H_j³ ≤ j⁶P₁^{1/2} ≤ j⁶Q_{j−1}^{1/2}`, and
`1/2 + 5/24 + 1 + 1 = 65/24 ≤ 3`.  The `H_j` pin rides as the hypothesis `hH3` rather than a
new definition — `Hseq` is left abstract by every landed `𝒯`-leg stone and `G5` owns the
numerals. -/
theorem cell_geometry_collapse (Hj Hp αp : ℝ) (j r Qp P1 Qj : ℕ) (hHp : 0 < Hp)
    (hα : 0 ≤ αp) (hα1 : 2 * αp ≤ 1)
    (hr : (r : ℝ) ≤ Hp * Real.log (Qp : ℝ)) (hQp : (1 : ℝ) ≤ (Qp : ℝ))
    (hlogQj0 : 0 ≤ Real.log (Qj : ℝ))
    (hlogQj : Real.log (Qj : ℝ) ≤ (Qp : ℝ) ^ ((1 : ℝ) / 24))
    (hH3 : Hj ^ 3 ≤ (j : ℝ) ^ 6 * (P1 : ℝ) ^ ((1 : ℝ) / 2))
    (hP1Qp : (P1 : ℝ) ≤ (Qp : ℝ)) :
    Hj ^ 3 * Real.log (Qj : ℝ) ^ 5 * (Qp : ℝ) * Real.exp (2 * αp * ((r : ℝ) / Hp))
      ≤ (j : ℝ) ^ 6 * (Qp : ℝ) ^ 3 := by
  have hQp0 : (0 : ℝ) < (Qp : ℝ) := by linarith
  -- (a) the block exponential: `e^{2α_{j−1}r/H_{j−1}} ≤ Q_{j−1}^{2α_{j−1}} ≤ Q_{j−1}`
  have hrH : (r : ℝ) / Hp ≤ Real.log (Qp : ℝ) := by
    rw [div_le_iff₀ hHp]; linarith [hr]
  have ha : Real.exp (2 * αp * ((r : ℝ) / Hp)) ≤ (Qp : ℝ) := by
    have h1 : 2 * αp * ((r : ℝ) / Hp) ≤ 2 * αp * Real.log (Qp : ℝ) :=
      mul_le_mul_of_nonneg_left hrH (by linarith)
    calc Real.exp (2 * αp * ((r : ℝ) / Hp))
        ≤ Real.exp (2 * αp * Real.log (Qp : ℝ)) := Real.exp_le_exp.mpr h1
      _ = (Qp : ℝ) ^ (2 * αp) := by rw [Real.rpow_def_of_pos hQp0]; congr 1; ring
      _ ≤ (Qp : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQp hα1
      _ = (Qp : ℝ) := Real.rpow_one _
  -- (b) the fifth power of the logarithm
  have hb : Real.log (Qj : ℝ) ^ 5 ≤ (Qp : ℝ) ^ ((5 : ℝ) / 24) := by
    calc Real.log (Qj : ℝ) ^ 5 ≤ ((Qp : ℝ) ^ ((1 : ℝ) / 24)) ^ 5 :=
          pow_le_pow_left₀ hlogQj0 hlogQj 5
      _ = (Qp : ℝ) ^ ((5 : ℝ) / 24) := by
          rw [← Real.rpow_natCast ((Qp : ℝ) ^ ((1 : ℝ) / 24)) 5, ← Real.rpow_mul hQp0.le]
          norm_num
  -- (c) the `H_j` pin, transported to the `Q_{j−1}` base
  have hc : (P1 : ℝ) ^ ((1 : ℝ) / 2) ≤ (Qp : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hP1Qp (by norm_num)
  have hHpin : Hj ^ 3 ≤ (j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2) := by
    refine le_trans hH3 ?_
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  calc Hj ^ 3 * Real.log (Qj : ℝ) ^ 5 * (Qp : ℝ) * Real.exp (2 * αp * ((r : ℝ) / Hp))
      ≤ ((j : ℝ) ^ 6 * (Qp : ℝ) ^ ((1 : ℝ) / 2)) * (Qp : ℝ) ^ ((5 : ℝ) / 24)
          * (Qp : ℝ) * (Qp : ℝ) := by
        gcongr
    _ = (j : ℝ) ^ 6 * (Qp : ℝ) ^ ((65 : ℝ) / 24) := by
        rw [show ((65 : ℝ) / 24) = (1 : ℝ) / 2 + (5 : ℝ) / 24 + 1 + 1 by norm_num,
          Real.rpow_add hQp0, Real.rpow_add hQp0, Real.rpow_add hQp0, Real.rpow_one]
        ring
    _ ≤ (j : ℝ) ^ 6 * (Qp : ℝ) ^ (3 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hQp (by norm_num)) (by positivity)
    _ = (j : ℝ) ^ 6 * (Qp : ℝ) ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ## §7 — G4f: eq (20), the α-decay, and THE KILL -/

/-- **MR eq (20), p.24**: `α_j := 1/4 − η(1 + 1/(2j))`. -/
noncomputable def mrAlpha (η : ℝ) (j : ℕ) : ℝ := 1 / 4 - η * (1 + 1 / (2 * (j : ℝ)))

/-- **The α-difference, EXACTLY** (eq (20)).  For `2 ≤ j`,

  `α_{j−1} − α_j = −η/(2j(j−1))`.

The sign is the whole point and is verified against p.24: `α_j` INCREASES with `j`
(`1/4 − (3/2)η = α₁ ≤ … ≤ α_J ≤ 1/4 − η`), so the difference the §8.2 device consumes is
NEGATIVE.  `mrAlpha_decay_le` is the `j²` weakening the kill actually spends; this is the
sharper fact. -/
theorem mrAlpha_diff (η : ℝ) {j : ℕ} (hj : 2 ≤ j) :
    mrAlpha η (j - 1) - mrAlpha η j = -(η / (2 * (j : ℝ) * ((j : ℝ) - 1))) := by
  have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    have : (1 : ℕ) ≤ j := by omega
    push_cast [Nat.cast_sub this]
    ring
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjne : ((j : ℝ) - 1) ≠ 0 := ne_of_gt (by linarith)
  have hj0ne : (j : ℝ) ≠ 0 := ne_of_gt (by linarith)
  rw [mrAlpha, mrAlpha, hcast]
  field_simp
  ring

/-- **The α-decay the kill spends.**  For `2 ≤ j` and `η > 0`,
`α_{j−1} − α_j ≤ −η/(2j²)` (from `j(j−1) ≤ j²`). -/
theorem mrAlpha_decay_le (η : ℝ) (hη : 0 < η) {j : ℕ} (hj : 2 ≤ j) :
    mrAlpha η (j - 1) - mrAlpha η j ≤ -(η / (2 * (j : ℝ) ^ 2)) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hstep : η / (2 * (j : ℝ) ^ 2) ≤ η / (2 * (j : ℝ) * ((j : ℝ) - 1)) :=
    (div_le_div_iff_of_pos_left hη (by nlinarith) (by nlinarith)).mpr (by nlinarith)
  rw [mrAlpha_diff η hj]
  linarith

/-- **The SIGN, as a theorem.**  `α_{j−1} < α_j` for `2 ≤ j`, `η > 0` — MR's α-sequence is
INCREASING (p.24), which is why `α_{j−1} − α_j` is a decay and not a growth. -/
theorem mrAlpha_pred_lt (η : ℝ) (hη : 0 < η) {j : ℕ} (hj : 2 ≤ j) :
    mrAlpha η (j - 1) < mrAlpha η j := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hd := mrAlpha_diff η hj
  have hpos : (0 : ℝ) < η / (2 * (j : ℝ) * ((j : ℝ) - 1)) := by
    apply div_pos hη; nlinarith
  linarith

/-- **THE KILL, at the level of exponents.**  The `(2)`-absorbed exponent of MR p.27,

  `2u·(α_{j−1} − α_j + η/(4j²)) ≤ −(η/(2j²))·u`  for `u ≥ 0`, `2 ≤ j`, `η > 0`,

i.e. the `η/(4j²)` that condition `(2)` leaves behind is eaten by HALF the α-decay and the
other half is the kill.  (`mrAlpha_decay_le` gives `−η/(2j²)`; `−η/(2j²) + η/(4j²) =
−η/(4j²)`, and `2u·(−η/(4j²)) = −(η/(2j²))u`.) -/
theorem level_kill_exponent (η u : ℝ) (hη : 0 < η) (hu : 0 ≤ u) {j : ℕ} (hj : 2 ≤ j) :
    2 * u * (mrAlpha η (j - 1) - mrAlpha η j + η / (4 * (j : ℝ) ^ 2))
      ≤ -(η / (2 * (j : ℝ) ^ 2)) * u := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hdec := mrAlpha_decay_le η hη hj
  have hbr : mrAlpha η (j - 1) - mrAlpha η j + η / (4 * (j : ℝ) ^ 2)
      ≤ -(η / (4 * (j : ℝ) ^ 2)) := by
    have hhalf : η / (2 * (j : ℝ) ^ 2) = 2 * (η / (4 * (j : ℝ) ^ 2)) := by
      field_simp; ring
    linarith [hdec, hhalf.le, hhalf.ge]
  have hmul := mul_le_mul_of_nonneg_left hbr (by linarith : (0 : ℝ) ≤ 2 * u)
  have hid : 2 * u * -(η / (4 * (j : ℝ) ^ 2)) = -(η / (2 * (j : ℝ) ^ 2)) * u := by
    field_simp; ring
  linarith [hmul, hid.le, hid.ge]

/-- **THE KILL** (MR p.27).  At `u = v/H_j ≥ log P_j`,

  `exp(2(v/H_j)(α_{j−1} − α_j + η/(4j²))) ≤ P_j^{−η/(2j²)}`.

The `v`-dependence is GONE: what is left is a power of the level-`j` block bottom, which
gate `(3)` then beats (`level_kill_collected`).  `hv` is carried in-statement: membership
`v ∈ I_j` only gives `v/H_j ≥ log P_j − 1/H_j`, and MR's `≪` swallows the `1/H_j`. -/
theorem level_kill_exp (η Hj : ℝ) (hη : 0 < η) {j : ℕ} (hj : 2 ≤ j) (v Pj : ℕ)
    (hHj : 0 < Hj) (hPj : (0 : ℝ) < (Pj : ℝ))
    (hv : Real.log (Pj : ℝ) ≤ (v : ℝ) / Hj) :
    Real.exp (2 * ((v : ℝ) / Hj)
        * (mrAlpha η (j - 1) - mrAlpha η j + η / (4 * (j : ℝ) ^ 2)))
      ≤ (Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hu : (0 : ℝ) ≤ (v : ℝ) / Hj := div_nonneg (Nat.cast_nonneg v) hHj.le
  have hc : (0 : ℝ) < η / (2 * (j : ℝ) ^ 2) := by apply div_pos hη; nlinarith
  have hstep := level_kill_exponent η ((v : ℝ) / Hj) hη hu hj
  have hlast : -(η / (2 * (j : ℝ) ^ 2)) * ((v : ℝ) / Hj)
      ≤ -(η / (2 * (j : ℝ) ^ 2)) * Real.log (Pj : ℝ) := by
    nlinarith [hv, hc]
  calc Real.exp (2 * ((v : ℝ) / Hj)
        * (mrAlpha η (j - 1) - mrAlpha η j + η / (4 * (j : ℝ) ^ 2)))
      ≤ Real.exp (-(η / (2 * (j : ℝ) ^ 2)) * Real.log (Pj : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = (Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2))) := by
        rw [Real.rpow_def_of_pos hPj]; congr 1; ring

/-- **THE COLLECTION** (MR p.27, "by (20) and (3)").  Gate `(3)` turns the kill against the
cell geometry:

  `j⁶·Q_{j−1}³·P_j^{−η/(2j²)} ≤ 1/(j²Q_{j−1})`.

The logarithmic arithmetic is exact: `(3)` reads `8 log Q_{j−1} + 16 log j ≤ (η/j²)log P_j`,
i.e. `4 log Q_{j−1} + 8 log j ≤ (η/(2j²))log P_j`, and
`6 log j + 3 log Q_{j−1} − (η/(2j²))log P_j ≤ −2 log j − log Q_{j−1}`. -/
theorem level_kill_collected (η : ℝ) (j Pj Qp : ℕ) (hj : 2 ≤ j) (hQp : (1 : ℝ) < (Qp : ℝ))
    (hPj : (0 : ℝ) < (Pj : ℝ))
    (hg3 : 8 * Real.log (Qp : ℝ) + 16 * Real.log (j : ℝ)
            ≤ (η / (j : ℝ) ^ 2) * Real.log (Pj : ℝ)) :
    (j : ℝ) ^ 6 * (Qp : ℝ) ^ 3 * (Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))
      ≤ 1 / ((j : ℝ) ^ 2 * (Qp : ℝ)) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj0 : (0 : ℝ) < (j : ℝ) := by linarith
  have hQ0 : (0 : ℝ) < (Qp : ℝ) := by linarith
  have e1 : (j : ℝ) ^ 6 = Real.exp (6 * Real.log (j : ℝ)) := by
    rw [show (6 : ℝ) * Real.log (j : ℝ) = Real.log ((j : ℝ) ^ (6 : ℕ)) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_log (by positivity)]
  have e2 : (Qp : ℝ) ^ 3 = Real.exp (3 * Real.log (Qp : ℝ)) := by
    rw [show (3 : ℝ) * Real.log (Qp : ℝ) = Real.log ((Qp : ℝ) ^ (3 : ℕ)) by
      rw [Real.log_pow]; norm_num]
    rw [Real.exp_log (by positivity)]
  have e3 : (Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))
      = Real.exp (-(η / (2 * (j : ℝ) ^ 2) * Real.log (Pj : ℝ))) := by
    rw [Real.rpow_def_of_pos hPj]; congr 1; ring
  have e4 : Real.exp (-(2 * Real.log (j : ℝ) + Real.log (Qp : ℝ)))
      = 1 / ((j : ℝ) ^ 2 * (Qp : ℝ)) := by
    rw [Real.exp_neg, Real.exp_add,
      show (2 : ℝ) * Real.log (j : ℝ) = Real.log ((j : ℝ) ^ (2 : ℕ)) by
        rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), Real.exp_log hQ0, one_div]
  have hgc : 4 * Real.log (Qp : ℝ) + 8 * Real.log (j : ℝ)
      ≤ η / (2 * (j : ℝ) ^ 2) * Real.log (Pj : ℝ) := by
    have hid : (η / (j : ℝ) ^ 2) * Real.log (Pj : ℝ)
        = 2 * (η / (2 * (j : ℝ) ^ 2) * Real.log (Pj : ℝ)) := by field_simp
    linarith [hg3, hid.le, hid.ge]
  rw [e1, e2, e3, ← e4, ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **The `G5` handoff form** (MR p.27's last step): `Q_{j−1} ≥ P₁` turns the collection into
`1/(j²P₁)`, which is what `Σ_{2≤j≤J−1}` sums against `π²/6`. -/
theorem level_kill_collected_P1 (η : ℝ) (j Pj Qp P1 : ℕ) (hj : 2 ≤ j)
    (hQp : (1 : ℝ) < (Qp : ℝ)) (hPj : (0 : ℝ) < (Pj : ℝ)) (hP1 : (0 : ℝ) < (P1 : ℝ))
    (hP1Qp : (P1 : ℝ) ≤ (Qp : ℝ))
    (hg3 : 8 * Real.log (Qp : ℝ) + 16 * Real.log (j : ℝ)
            ≤ (η / (j : ℝ) ^ 2) * Real.log (Pj : ℝ)) :
    (j : ℝ) ^ 6 * (Qp : ℝ) ^ 3 * (Pj : ℝ) ^ (-(η / (2 * (j : ℝ) ^ 2)))
      ≤ 1 / ((j : ℝ) ^ 2 * (P1 : ℝ)) := by
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  refine le_trans (level_kill_collected η j Pj Qp hj hQp hPj hg3) ?_
  have hden : (0 : ℝ) < (j : ℝ) ^ 2 * (P1 : ℝ) := by positivity
  have hmono : (j : ℝ) ^ 2 * (P1 : ℝ) ≤ (j : ℝ) ^ 2 * (Qp : ℝ) :=
    mul_le_mul_of_nonneg_left hP1Qp (by positivity)
  exact one_div_le_one_div_of_le hden hmono

/-! ## §8 — G4e-iii: the moment at MR §8.2's TWO widths

`G4c`'s `multShiu_moment` prices `∫‖Q_{j,H}^{ℓ}R_{v,H}‖²` with ONE `(H,P,Q)` shared by the
prime fibre and the co-factor window.  MR §8.2 needs `Q_{r,H_{j−1}}^{ℓ}·R_{v,H_j}`: the block
sits at level `j−1`, the co-factor at level `j`.  The two parameter sets are split here and
the moment re-derived from `G4c`'s own generic machinery (`af_pow_mul_support_low`,
`norm_af_mul_le`, `maj_le_factorial_blockDiv`, `spoly_mul`, `MomentsA2.lemma13_moment`);
nothing in `MultShiuBridge` is touched. -/

/-- **The MULT-SHIU coefficient at two widths** — the coefficient function of
`Q_{r,H_{j−1}}(1+it)^{ℓ}·R_{v,H_j}(1+it)`. -/
noncomputable def mixCoeff (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ) (N X Pr Qr v : ℕ)
    (b c : ℕ → ℂ) (ℓ : ℕ) : ArithmeticFunction ℂ :=
  ramQaf Hq Pq Qq r c ^ ℓ * ramRaf Hr N X Pr Qr v b

/-- **The window, low end** at two widths: every frequency is `≥ Y₁^{ℓ}·X₀`. -/
theorem mixCoeff_support_low (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ) (N X Pr Qr v Y₁ X₀ : ℕ)
    (b c : ℕ → ℂ) (ℓ : ℕ) (hQlow : ∀ p ∈ ramQblock Hq Pq Qq r, Y₁ ≤ p)
    (hRlow : ∀ m ∈ ramRrange Hr N X v, X₀ ≤ m) :
    ∀ n, n < Y₁ ^ ℓ * X₀ → (mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ) n = 0 := by
  refine af_pow_mul_support_low (fun n hn => ?_) (fun n hn => ?_) ℓ
  · rw [ramQaf_apply, ramQcoeff, if_neg]
    intro hmem
    exact absurd (hQlow n hmem) (by omega)
  · rw [ramRaf_apply, ramRcoeff, if_neg]
    intro hmem
    exact absurd (hRlow n hmem) (by omega)

/-- **The `ℓ`-fold product IS a `σ = 1` Dirichlet polynomial**, at two widths. -/
theorem ramQ_pow_mul_ramR_eq_spoly_mix (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ)
    (N X Pr Qr v Mq Mr : ℕ) (b c : ℕ → ℂ)
    (hMq : ramQblock Hq Pq Qq r ⊆ Finset.Icc 1 Mq)
    (hMr : ramRrange Hr N X v ⊆ Finset.Icc 1 Mr) (ℓ : ℕ) (t : ℝ) :
    ramQ Hq Pq Qq r c t ^ ℓ * ramR Hr N X Pr Qr v b t
      = spoly (Mq ^ ℓ * Mr) (⇑(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ)) t := by
  have hqsupp : ∀ n, Mq < n → (ramQaf Hq Pq Qq r c) n = 0 := by
    intro n hn
    rw [ramQaf_apply, ramQcoeff, if_neg]
    intro hmem
    have h := Finset.mem_Icc.mp (hMq hmem)
    omega
  have hrsupp : ∀ n, Mr < n → (ramRaf Hr N X Pr Qr v b) n = 0 := by
    intro n hn
    rw [ramRaf_apply, ramRcoeff, if_neg]
    intro hmem
    have h := Finset.mem_Icc.mp (hMr hmem)
    omega
  induction ℓ with
  | zero =>
      rw [mixCoeff, pow_zero, one_mul, pow_zero, one_mul, pow_zero, one_mul]
      exact ramR_eq_spoly Hr N X Pr Qr v Mr b hMr t
  | succ ℓ ih =>
      have hstep : ramQ Hq Pq Qq r c t ^ (ℓ + 1) * ramR Hr N X Pr Qr v b t
          = ramQ Hq Pq Qq r c t
              * (ramQ Hq Pq Qq r c t ^ ℓ * ramR Hr N X Pr Qr v b t) := by ring
      have hmul := spoly_mul (M₁ := Mq) (M₂ := Mq ^ ℓ * Mr) (ramQaf Hq Pq Qq r c)
        (mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ) hqsupp
        (af_pow_mul_support_high hqsupp hrsupp ℓ) t
      have hlen : Mq * (Mq ^ ℓ * Mr) = Mq ^ (ℓ + 1) * Mr := by ring
      have hcoe : ramQaf Hq Pq Qq r c * mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ
          = mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c (ℓ + 1) := by
        rw [mixCoeff, mixCoeff]; ring
      have hfun : (⇑(ramQaf Hq Pq Qq r c) : ℕ → ℂ) = ramQcoeff Hq Pq Qq r c := rfl
      rw [hlen, hcoe, hfun] at hmul
      rw [hstep, ih, ramQ_eq_spoly_bounded Hq Pq Qq r Mq c hMq t, hmul]

/-- **The majorant of the mixed `ℓ`-fold coefficient.**  (The `∀ n` must be inside the
induction — an `n`-fixed IH is dead.) -/
lemma norm_mixCoeff_le (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ) (N X Pr Qr v Y₁ : ℕ) {b c : ℕ → ℂ}
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hblock : ∀ p ∈ ramQblock Hq Pq Qq r, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (ℓ : ℕ) :
    ∀ n, ‖(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ) n‖
      ≤ ((blockPrimeAf Y₁) ^ ℓ * oneAf) n := by
  induction ℓ with
  | zero =>
      intro n
      rw [mixCoeff, pow_zero, one_mul, pow_zero, one_mul]
      exact norm_ramRaf_le Hr N X Pr Qr v hb n
  | succ ℓ ih =>
      intro n
      have hcL : mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c (ℓ + 1)
          = ramQaf Hq Pq Qq r c * mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ := by
        rw [mixCoeff, mixCoeff]; ring
      have hcR : (blockPrimeAf Y₁) ^ (ℓ + 1) * oneAf
          = blockPrimeAf Y₁ * ((blockPrimeAf Y₁) ^ ℓ * oneAf) := by ring
      rw [hcL, hcR]
      exact norm_af_mul_le (norm_ramQaf_le Hq Pq Qq r Y₁ hc hblock) ih n

/-- **M-3 at two widths** — `lemma13_moment`'s `hcoeff`. -/
theorem coeff_bound_mix (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ) (N X Pr Qr v Y₁ : ℕ) {b c : ℕ → ℂ}
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (hblock : ∀ p ∈ ramQblock Hq Pq Qq r, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (ℓ n : ℕ) :
    ‖(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ) n‖
      ≤ (ℓ.factorial : ℝ) * (blockDiv Y₁ n : ℝ) :=
  le_trans (norm_mixCoeff_le Hq Pq Qq r Hr N X Pr Qr v Y₁ hb hc hblock ℓ n)
    (maj_le_factorial_blockDiv Y₁ ℓ n)

/-- **THE MIXED-WIDTH MOMENT** — MR §8.2's application of Lemma 13, at the two widths the
page actually uses.  With the block gate `Y₁ ≤ p ≤ 2Y₁` on the level-`(j−1)` prime fibre and
`X₀ ≤ m ≤ Mr` on the level-`j` co-factor window,

  `∫_{−T}^{T}‖Q_{r,H_{j−1}}(1+it)^{ℓ}R_{v,H_j}(1+it)‖² dt
      ≤ (2T + 20(2Y₁)^{ℓ}M_r)·(ℓ!²·C/(Y₁^{ℓ}X₀))`

with the absolute Shiu constant `C` of `lemma13_moment`.  The denominator `Y₁^{ℓ}X₀` is what
`ellPin_window_bottom_ge` bounds below by `X_d` at the pin — that is how MR's `T/X`
reappears. -/
theorem mix_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (Hq : ℝ) (Pq Qq r : ℕ) (Hr : ℝ) (N X Pr Qr v Y₁ Mr X₀ ℓ : ℕ)
      (b c : ℕ → ℂ) (T : ℝ), 1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T →
      (∀ p ∈ ramQblock Hq Pq Qq r, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange Hr N X v, X₀ ≤ m) →
      ramRrange Hr N X v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in (-T)..T, ‖ramQ Hq Pq Qq r c t ^ ℓ * ramR Hr N X Pr Qr v b t‖ ^ 2)
        ≤ (2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
            * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := by
  obtain ⟨C, hC, hL13⟩ := lemma13_moment
  refine ⟨C, hC, ?_⟩
  intro Hq Pq Qq r Hr N X Pr Qr v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  have hMq : ramQblock Hq Pq Qq r ⊆ Finset.Icc 1 (2 * Y₁) := by
    intro p hp
    obtain ⟨hlo, hhi⟩ := hblock p hp
    exact Finset.mem_Icc.mpr ⟨by omega, hhi⟩
  have hint : (∫ t in (-T)..T, ‖ramQ Hq Pq Qq r c t ^ ℓ * ramR Hr N X Pr Qr v b t‖ ^ 2)
      = ∫ t in (-T)..T,
          ‖spoly ((2 * Y₁) ^ ℓ * Mr)
            (⇑(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ)) t‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [ramQ_pow_mul_ramR_eq_spoly_mix Hq Pq Qq r Hr N X Pr Qr v (2 * Y₁) Mr b c hMq hMr ℓ t]
  rw [hint]
  have hXpos : 1 ≤ Y₁ ^ ℓ * X₀ := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (pow_ne_zero ℓ (by omega)) (by omega))
  exact hL13 Y₁ (Y₁ ^ ℓ * X₀) ((2 * Y₁) ^ ℓ * Mr) ℓ
    (⇑(mixCoeff Hq Pq Qq r Hr N X Pr Qr v b c ℓ)) T hY₁ hXpos hT
    (mixCoeff_support_low Hq Pq Qq r Hr N X Pr Qr v Y₁ X₀ b c ℓ
      (fun p hp => (hblock p hp).1) hRlow)
    (coeff_bound_mix Hq Pq Qq r Hr N X Pr Qr v Y₁ hb hc hblock ℓ)

/-! ## §9 — G4e-iv: the assembled cell -/

/-- `‖z‖^{2ℓ}·‖w‖² = ‖z^{ℓ}w‖²` — the shape change from `G4b`'s entry ticket to Lemma 13's
integrand. -/
lemma norm_pow_mul_sq (z w : ℂ) (ℓ : ℕ) : ‖z‖ ^ (2 * ℓ) * ‖w‖ ^ 2 = ‖z ^ ℓ * w‖ ^ 2 := by
  rw [norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm ℓ 2]

/-- **`G4b`'s entry ticket, with the co-factor as the integrand.**  `TLegCover`'s
`cell_integral_normalized` inserts the `2ℓ`-th power under `‖spoly‖²`; MR §8.2 needs it under
`‖R_{v,H_j}‖²` (the co-factor that survives Lemma 12's split).  Same proof, same pointwise
stone (`one_le_ramQ_pow_mul_exp`), different integrand; integrability is discharged
internally from continuity on `[−T,T]`. -/
theorem cell_ramR_normalized (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
    (J j r ℓ N Xd v : ℕ) {T : ℝ} (hT : 0 ≤ T) (A : Set ℝ) (hAm : MeasurableSet A)
    (hAsub : A ⊆ Set.Icc (-T) T) (hAT : A ⊆ TsetGr c Pseq Qseq Hseq αseq J j r) :
    (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
          * ∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
              * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
  have hcontL : Continuous
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) :=
    (continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2
  have hcontG : Continuous fun t : ℝ =>
      ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    ((continuous_ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c).norm.pow
      (2 * ℓ)).mul hcontL
  have hcontR : Continuous fun t : ℝ =>
      Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) := continuous_const.mul hcontG
  have hIntL : IntegrableOn
      (fun t : ℝ => ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) A volume :=
    integrableOn_of_continuous_subset_Icc hcontL hT hAm hAsub
  have hIntR : IntegrableOn (fun t : ℝ =>
      Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)) A volume :=
    integrableOn_of_continuous_subset_Icc hcontR hT hAm hAsub
  have hpt : (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ ∫ t in A, Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
          * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
              * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2) := by
    refine setIntegral_mono_on hIntL hIntR hAm (fun t ht => ?_)
    have h1 := one_le_ramQ_pow_mul_exp (hAT ht) ℓ
    have h2 : (0 : ℝ) ≤ ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := sq_nonneg _
    nlinarith [h1, h2]
  have hconst : (∫ t in A, Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * (‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2))
      = Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
        * ∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  rw [hconst] at hpt
  exact hpt

/-- **G4e — THE ASSEMBLED CELL (raw composed form).**  On any measurable window
`A ⊆ [−T,T]` inside the cell `𝒯_{j,r}`, the co-factor's mean square is priced by the entry
ticket times the mixed-width moment:

  `∫_{A}‖R_{v,H_j}(1+it)‖² dt
     ≤ e^{2ℓα_{j−1}r/H_{j−1}}·(2T + 20(2Y₁)^{ℓ}M_r)·(ℓ!²·C/(Y₁^{ℓ}X₀))`,

for EVERY `ℓ : ℕ` (the pin `ℓ = ℓ_{j,r}` is the consumer's choice — `ellPin`).  This is MR
p.26's second display, with `C` the absolute Shiu constant.  Every gate is in-statement: the
block gate `Y₁ ≤ p ≤ 2Y₁` on the level-`(j−1)` fibre, the co-factor window's two ends, the
`1`-boundedness of `b` and `c`, and the measure frame.  Nothing is absorbed into a numeral
(law #253); in particular the `2^{ℓ}` hiding in `(2Y₁)^{ℓ}/Y₁^{ℓ}` is left visible (MR
absorbs it under `≪`). -/
theorem cell_bound_raw :
    ∃ C : ℝ, 0 < C ∧ ∀ (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
      (J j r ℓ N Xd v Y₁ Mr X₀ : ℕ) (T : ℝ) (A : Set ℝ),
      1 ≤ Y₁ → 1 ≤ X₀ → 0 ≤ T → MeasurableSet A → A ⊆ Set.Icc (-T) T →
      A ⊆ TsetGr c Pseq Qseq Hseq αseq J j r →
      (∀ p ∈ ramQblock (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r, Y₁ ≤ p ∧ p ≤ 2 * Y₁) →
      (∀ m ∈ ramRrange (Hseq j) N Xd v, X₀ ≤ m) →
      ramRrange (Hseq j) N Xd v ⊆ Finset.Icc 1 Mr →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
        ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1))
            * ((2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
                * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ)))) := by
  obtain ⟨C, hC, hmom⟩ := mix_moment
  refine ⟨C, hC, ?_⟩
  intro c b Pseq Qseq Hseq αseq J j r ℓ N Xd v Y₁ Mr X₀ T A hY₁ hX₀ hT hAm hAsub hAT
    hblock hRlow hMr hb hc
  -- the entry ticket at the cell
  have hstep := cell_ramR_normalized c b Pseq Qseq Hseq αseq J j r ℓ N Xd v hT A hAm hAsub hAT
  -- the integrand is Lemma 13's, and `A ⊆ [−T,T]` transfers to the full range
  have hcontG : Continuous fun t : ℝ =>
      ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    ((continuous_ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c).norm.pow
      (2 * ℓ)).mul ((continuous_ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b).norm.pow 2)
  have hmono : (∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
        * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ ∫ t in Set.Icc (-T) T,
          ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
            * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    setIntegral_mono_set hcontG.integrableOn_Icc
      (Filter.Eventually.of_forall (fun t => by positivity)) hAsub.eventuallyLE
  have hfull : (∫ t in Set.Icc (-T) T,
        ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      = ∫ t in (-T)..T, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-T : ℝ) ≤ T)]
  have hshape : (∫ t in (-T)..T,
        ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      = ∫ t in (-T)..T,
          ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t ^ ℓ
            * ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => norm_pow_mul_sq _ _ ℓ)
  have hL13 := hmom (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r (Hseq j) N Xd
    (Pseq j) (Qseq j) v Y₁ Mr X₀ ℓ b c T hY₁ hX₀ hT hblock hRlow hMr hb hc
  have hE0 : (0 : ℝ)
      ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hseq (j - 1)) := (Real.exp_pos _).le
  refine le_trans hstep (mul_le_mul_of_nonneg_left ?_ hE0)
  calc (∫ t in A, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
      ≤ ∫ t in (-T)..T, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t‖ ^ (2 * ℓ)
          * ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := by
        rw [← hfull]; exact hmono
    _ = ∫ t in (-T)..T, ‖ramQ (Hseq (j - 1)) (Pseq (j - 1)) (Qseq (j - 1)) r c t ^ ℓ
          * ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2 := hshape
    _ ≤ (2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ))
          * ((ℓ.factorial : ℝ) ^ 2 * (C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ))) := hL13

/-- **G4e — THE ASSEMBLED CELL AT THE PIN: MR's `T/X` recovered.**  `cell_bound_raw` at
`ℓ = ℓ_{j,r}` and MR's own calibration `Y₁ = ⌈e^{r/H_{j−1}}⌉`, `X₀ = ⌈X_d e^{−v/H_j}⌉`,
`M_r = ⌈2X_d e^{−v/H_j}⌉`:

  `∫_{A}‖R_{v,H_j}(1+it)‖² dt
     ≤ e^{2ℓ_{j,r}α_{j−1}r/H_{j−1}}·(2T + 20(2Y₁)^{ℓ}M_r)·(ℓ_{j,r}!²·C/X_d)`.

The denominator is `X_d`, not `Y₁^{ℓ}X₀` — THE PIN'S SECOND FACE
(`ellPin_window_bottom_ge`) is what buys it, and it is exactly MR's `T/X` prefactor.  All
three of `mix_moment`'s window gates are DISCHARGED here from the calibration
(`ramQblock_subset_dyadic_block` at `H_{j−1} ≥ 2`, `ramRrange_ceil_bot_le`,
`ramRrange_subset_Icc_sharp`); the caller carries only `2 ≤ H_{j−1}`, `0 < r`, `1 ≤ X_d`,
the measure frame and the `1`-boundedness of the two data. -/
theorem cell_bound_pinned :
    ∃ C : ℝ, 0 < C ∧ ∀ (c b : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (Hseq αseq : ℕ → ℝ)
      (J j r N Xd v : ℕ) (T : ℝ) (A : Set ℝ),
      2 ≤ Hseq (j - 1) → 0 < r → 1 ≤ Xd → 0 ≤ T →
      MeasurableSet A → A ⊆ Set.Icc (-T) T → A ⊆ TsetGr c Pseq Qseq Hseq αseq J j r →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∫ t in A, ‖ramR (Hseq j) N Xd (Pseq j) (Qseq j) v b t‖ ^ 2)
        ≤ Real.exp (2 * ((ellPin (Hseq j) (Hseq (j - 1)) v r : ℕ) : ℝ) * αseq (j - 1)
              * (r : ℝ) / Hseq (j - 1))
            * ((2 * T + 20 * (((2 * ⌈Real.exp ((r : ℝ) / Hseq (j - 1))⌉₊)
                      ^ (ellPin (Hseq j) (Hseq (j - 1)) v r)
                    * ⌈2 * ramRbot (Hseq j) Xd v⌉₊ : ℕ) : ℝ))
                * ((((ellPin (Hseq j) (Hseq (j - 1)) v r).factorial : ℕ) : ℝ) ^ 2
                    * (C / (Xd : ℝ)))) := by
  obtain ⟨C, hC, hraw⟩ := cell_bound_raw
  refine ⟨C, hC, ?_⟩
  intro c b Pseq Qseq Hseq αseq J j r N Xd v T A hHp2 hr hXd hT hAm hAsub hAT hb hc
  set Hp : ℝ := Hseq (j - 1) with hHpdef
  set ℓ : ℕ := ellPin (Hseq j) Hp v r with hℓdef
  set Y₁ : ℕ := ⌈Real.exp ((r : ℝ) / Hp)⌉₊ with hY₁def
  set X₀ : ℕ := ⌈ramRbot (Hseq j) Xd v⌉₊ with hX₀def
  set Mr : ℕ := ⌈2 * ramRbot (Hseq j) Xd v⌉₊ with hMrdef
  have hHp0 : (0 : ℝ) < Hp := by rw [hHpdef]; linarith
  have hXdR : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have hbot : 0 < ramRbot (Hseq j) Xd v := by rw [ramRbot]; positivity
  have hY₁1 : 1 ≤ Y₁ := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hX₀1 : 1 ≤ X₀ := Nat.ceil_pos.mpr hbot
  have hstep := hraw c b Pseq Qseq Hseq αseq J j r ℓ N Xd v Y₁ Mr X₀ T A hY₁1 hX₀1 hT
    hAm hAsub hAT (ramQblock_subset_dyadic_block Hp hHp2 (Pseq (j - 1)) (Qseq (j - 1)) r)
    (ramRrange_ceil_bot_le (Hseq j) N Xd v)
    (ramRrange_subset_Icc_sharp (Hseq j) N Xd v Mr (Nat.le_ceil _)) hb hc
  refine le_trans hstep ?_
  -- THE PIN'S SECOND FACE: the Lemma-13 denominator is at least the row length
  have hden : (Xd : ℝ) ≤ ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) := by
    have h := ellPin_window_bottom_ge (Hseq j) Hp v r Xd hHp0 hr
    push_cast
    exact h
  have hdenpos : (0 : ℝ) < ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) := lt_of_lt_of_le hXdR hden
  have hCdiv : C / ((Y₁ ^ ℓ * X₀ : ℕ) : ℝ) ≤ C / (Xd : ℝ) :=
    (div_le_div_iff_of_pos_left hC hdenpos hXdR).mpr hden
  have hfacnn : (0 : ℝ) ≤ ((ℓ.factorial : ℕ) : ℝ) ^ 2 := by positivity
  have hprenn : (0 : ℝ) ≤ 2 * T + 20 * (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ (((2 * Y₁) ^ ℓ * Mr : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hE0 : (0 : ℝ) ≤ Real.exp (2 * (ℓ : ℝ) * αseq (j - 1) * (r : ℝ) / Hp) :=
    (Real.exp_pos _).le
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hprenn) hE0
  exact mul_le_mul_of_nonneg_left hCdiv hfacnn

end Salt.MR
