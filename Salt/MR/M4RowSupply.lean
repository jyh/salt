/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TypicalPrice
import Salt.MR.USetPins
import Salt.MR.FrameWitness

/-!
# `M4RowSupply` — R3's row-side supply: the COPRIME-TAIL MASS at the relaxed regularity gate

⟦R3a⟧ replaced the capstone's coprime-tail PIN (`homega : a n ≠ 0 → 1 ≤ blockOmega P Q n`,
which the door's band datum cannot inhabit) by a priced tail: `M4ErrRewire.E_priced_mr` now
carries a named mass binder

  `Σ_{n ≤ N, ω(n;P,Q) = 0} ‖aₙ‖²/n² ≤ M_tail`

and pays `(2T + 20N)·M_tail` into the ε-graded `EP₂` slot (⟦R3c⟧'s room).  ⟦R3b⟧ then
relaxed `TypicalDensity`'s regularity gate from MR's `log Q ≤ √log W` to `100·log Q ≤ log W`,
which is exactly what a §8.3-WINDOW band needs: `log Q₈₃ = log X/loglog X` is far above
`√log X`, so the landed gate is unavailable at the door and the relaxed one is free.

This file is the supply side that follows: the gate at the pins, the mass at a band, and the
grade the two §8.3 pins would deliver.

## ⚠ THE POINT-vs-BAND WALL — **REPAIRED** (⟦THE BAND RE-CUT⟧, §4 below)

`blockfree_sum_le` prices the tail at `C·(log P/log Q)/W + 1/W²`.  That is small exactly
when the band `[P,Q]` is WIDE on the log scale.  The M4 capstone's row USED TO BE pinned at
`P = Q` (`m4_meansq_per_chi_gen` read `ramI (H83 X θ₂₉₃) P P`), where

  `log P/log Q = 1`   and hence   `M_tail ≍ 1/X_d`,

so `(2X + 20N)·M_tail ≍ 42` — an `O(1)` charge, which no ε-window absorbs.  The relaxed gate
buys nothing AT A POINT; it buys the whole `[P₈₃, Q₈₃]` band, where `m4_tail_grade_at_pins`
gives the genuinely small `loglog X·(log X)^{−θ₂₉₃}`.

The repair was route (a), the mathematically forced one: `FrameWitness` §2′/§3′ re-cut the
witness chain at the BAND (the `ramQbase` sandwich `P ≤ ramQbase H P j ≤ Q` in place of the
singleton collapse; the band `h`-ceiling in place of the point one), and `M4MeanSq` §4 carried
`Q` into the capstone.  §4 below is what the band then buys: the whole `EP₂` budget line.

## The stones

* `m4_tail_gate_at_pins` — `100·log Q ≤ log X_d` from `Q ≤ Q₈₃ X`, `100 ≤ loglog X` and the
  dyadic pin `X ≤ X_d`.  **This is R3b's payoff**: the landed pair `log Q ≤ √log X ∧
  100 ≤ √log X` is FALSE at `Q = Q₈₃ X` for every large `X`.
* `m4_tail_mass_at_band` — `TypicalPrice.blockfree_sum_le` read at the relaxed gate, in the
  exact shape `M4ErrRewire.E_priced_mr`'s `hMtail` slot wants.
* `m4_tail_grade_at_pins` — `log(P₈₃ X θ)/log(Q₈₃ X) = loglog X·(log X)^{−θ}`, the grade a
  band-blocked row would enjoy.

Source pins (D5): MR arXiv **v4** (`1501.04585v4`) §2 p.6 (Lemma 2.2), §8.3 p.27 (the
station pins); `docs/blueprints/flags.md` — the R3-SCOPE anatomy and the two Fable rulings.
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the relaxed gate, at the §8.3 window -/

/-- **⟦R3b's PAYOFF⟧ the relaxed regularity gate holds at the `§8.3` window top**
(`m4_tail_gate_at_pins`).  For a band ceiling `Q ≤ Q₈₃ X = exp(log X/loglog X)` and
`100 ≤ loglog X`, the relaxed gate `100·log Q ≤ log X_d` follows from the dyadic pin
`X ≤ X_d`.

The LANDED pair cannot do this: `log Q₈₃ X = log X/loglog X` exceeds `√log X` as soon as
`loglog X < √log X`, i.e. for every large `X`.  That is why `TypicalDensity`'s gate had to
move before the door's tail could be priced at all. -/
theorem m4_tail_gate_at_pins {X : ℝ} {Q Xd : ℕ}
    (hX0 : 0 < X) (hL0 : 0 < Real.log X) (hLL : (100 : ℝ) ≤ Real.log (Real.log X))
    (hQ1 : 1 ≤ Q) (hQ : (Q : ℝ) ≤ Q83 X) (hXd : X ≤ (Xd : ℝ)) :
    100 * Real.log Q ≤ Real.log Xd := by
  have hLL0 : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ1
  have hlogQ : Real.log Q ≤ Real.log X / Real.log (Real.log X) := by
    have h := Real.log_le_log hQ0 hQ
    rwa [Q83, Real.log_exp] at h
  have hXdL : Real.log X ≤ Real.log Xd := Real.log_le_log hX0 hXd
  have hfrac : 100 * (Real.log X / Real.log (Real.log X)) ≤ Real.log X := by
    rw [← sub_nonneg]
    have hid : Real.log X - 100 * (Real.log X / Real.log (Real.log X))
        = Real.log X * (Real.log (Real.log X) - 100) / Real.log (Real.log X) := by
      field_simp
    rw [hid]
    exact div_nonneg (mul_nonneg hL0.le (by linarith)) hLL0.le
  linarith

/-! ## §2 — the tail mass at a band, in the `hMtail` shape -/

/-- **THE COPRIME-TAIL MASS AT A BAND** (`m4_tail_mass_at_band`).
`TypicalPrice.blockfree_sum_le` read at ⟦R3b⟧'s relaxed gate, in exactly the shape
`M4ErrRewire.E_priced_mr`'s `hMtail` binder consumes:

  `Σ_{n ≤ N, ω(n;P,Q) = 0} ‖aₙ‖²/n² ≤ C·(log P/log Q)/X_d + 1/X_d²`

for a `1`-bounded `a` supported on the dyadic window `[X_d, 2X_d]`.  The nonnegativity of the
right-hand side (`E_priced_mr`'s other new binder, `0 ≤ M_tail`) is `m4_tail_mass_nonneg`. -/
theorem m4_tail_mass_at_band :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd →
      100 * Real.log Q ≤ Real.log Xd →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) →
      (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2 :=
  blockfree_sum_le

/-- The tail budget is nonnegative — `E_priced_mr`'s `0 ≤ M_tail` at the band value. -/
theorem m4_tail_mass_nonneg {C : ℝ} (hC : 0 < C) {P Q Xd : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q)
    (hXd : 1 ≤ Xd) :
    0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2 := by
  have hQ2 : 2 ≤ Q := hP.trans hPQ
  have hlogP : 0 < Real.log P := Real.log_pos (by exact_mod_cast hP)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by exact_mod_cast hQ2)
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by exact_mod_cast hXd
  have h1 : (0 : ℝ) ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) :=
    div_nonneg (mul_nonneg hC.le (div_nonneg hlogP.le hlogQ.le)) hXd0.le
  have h2 : (0 : ℝ) ≤ 1 / (Xd : ℝ) ^ 2 := by positivity
  linarith

/-! ## §3 — the grade the two `§8.3` pins deliver -/

/-- **THE BAND GRADE AT THE `§8.3` PINS** (`m4_tail_grade_at_pins`).

  `log(P₈₃ X θ)/log(Q₈₃ X) = loglog X · (log X)^{−θ}`,

since `log P₈₃ = (log X)^{1−θ}` and `log Q₈₃ = log X/loglog X`.  This is the tail grade a
row blocked on the WHOLE band `[P₈₃, Q₈₃]` would enjoy — small, by a full `(log X)^{−θ}`
against a single `loglog`.  At the capstone's `P = Q` pin the same ratio is `1`; see the
header's point-vs-band note. -/
theorem m4_tail_grade_at_pins {X θ : ℝ} (hL0 : 0 < Real.log X)
    (hLL0 : 0 < Real.log (Real.log X)) :
    Real.log (P83 X θ) / Real.log (Q83 X)
      = Real.log (Real.log X) * (Real.log X) ^ (-θ) := by
  have hP : Real.log (P83 X θ) = (Real.log X) ^ (1 - θ) := by rw [P83, Real.log_exp]
  have hQ : Real.log (Q83 X) = Real.log X / Real.log (Real.log X) := by
    rw [Q83, Real.log_exp]
  have hsplit : (Real.log X) ^ (1 - θ) = (Real.log X) ^ (-θ) * Real.log X := by
    rw [show (1 : ℝ) - θ = -θ + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
  rw [hP, hQ, hsplit]
  field_simp

/-! ## §4 — ⟦THE BAND RE-CUT⟧'s TAIL SUPPLY: the `EP₂` budget line at the two `§8.3` pins

The wall of the header is now REPAIRED upstream (`FrameWitness` §2′/§3′, `M4MeanSq` §4): the
capstone's Ramaré block is the BAND `ramI (H83 X θ₂₉₃) P Q`.  This section supplies what the
band buys — the whole `EP₂` budget line, at

  `P := ⌈P₈₃ X θ₂₉₃⌉₊`,  `Q := ⌊Q₈₃ X⌋₊`,  `X_d = X`,  `N = 2X`,
  `M_tail := C·(log P/log Q)/X_d + 1/X_d²`   (`m4_tail_mass_at_band`'s own value).

**THE ARITHMETIC, IN FULL.**  At the two pins `12·witEP₂ = 10752·log₂(2X)/P`, which
`FrameWitness.witEP2_gate` already carries under `10752·log₂(2X) ≤ (log X)²`; and

  `12·(4/3)·(2X + 20N)·M_tail = 672·C·(log P/log Q) + 672/X`

(the `4/3` bump doubled the `336` of the un-inflated row).  The second term is free
(`(log X)^{θ₂₉₃} ≤ log X ≤ X`), the first is the whole content: at the grade
`log P/log Q ≍ loglog X·(log X)^{−θ₂₉₃}` it is `≍ C·loglog X·(log X)^{−θ₂₉₃}`, and the
ε-window absorbs it under **THE ONE NEW NAMED THRESHOLD**

  `2688·C·loglog X ≤ (log X)^ε`   (⟹ `loglog X ≳ 6.6·10⁴` at door numerology),

the same genre as the landed `6412.6`/`9.1·10³` gates (law #253: carried symbolically).

⚠ **THE ROUNDING FINDING** (a correction to the wave brief's `1344`).  The EXACT grade
`log P₈₃/log Q₈₃` is unattainable at any admissible ℕ-band: `P₈₃ ≤ P` forces
`log P₈₃ ≤ log P` and `Q ≤ Q₈₃` forces `log Q ≤ log Q₈₃`, so the ratio only ever moves UP
from the real-endpoint value.  `m4_tail_grade_rounded` prices the rounding at a clean factor
`2`, and the threshold constant is therefore `2688 = 2·1344`, not `1344`. -/

/-- **THE ROUNDED BAND GRADE** (`m4_tail_grade_rounded`).  At the ℕ-pins
`P = ⌈P₈₃⌉₊`, `Q = ⌊Q₈₃⌋₊` the grade is at most TWICE `m4_tail_grade_at_pins`' real value:

  `log⌈P₈₃⌉₊/log⌊Q₈₃⌋₊ ≤ (log P₈₃ + 1)/(log Q₈₃ − 1) ≤ 2·log P₈₃/log Q₈₃`,

the last step being `b + 2a ≤ ab` at `a, b ≥ 4`.  Both roundings are absorbed by ONE factor
of `e`: `⌈y⌉₊ < y + 1 ≤ y·e` and `⌊y⌋₊ > y − 1 ≥ y/e`, at `y ≥ 5`. -/
theorem m4_tail_grade_rounded {X : ℝ} (hL0 : 0 < Real.log X)
    (hLL0 : 0 < Real.log (Real.log X))
    (hP4 : 4 ≤ Real.log (P83 X theta293)) (hQ4 : 4 ≤ Real.log (Q83 X)) :
    Real.log ((⌈P83 X theta293⌉₊ : ℕ) : ℝ) / Real.log ((⌊Q83 X⌋₊ : ℕ) : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he3 : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  set a := Real.log (P83 X theta293) with ha
  set b := Real.log (Q83 X) with hb
  have hP0 : (0 : ℝ) < P83 X theta293 := by rw [P83]; exact Real.exp_pos _
  have hQ0 : (0 : ℝ) < Q83 X := by rw [Q83]; exact Real.exp_pos _
  -- ⟦both pins are ≥ 5⟧ `e^y ≥ y + 1`
  have hP5 : (5 : ℝ) ≤ P83 X theta293 := by
    have h := Real.add_one_le_exp a
    rw [ha, Real.exp_log hP0] at h
    linarith
  have hQ5 : (5 : ℝ) ≤ Q83 X := by
    have h := Real.add_one_le_exp b
    rw [hb, Real.exp_log hQ0] at h
    linarith
  -- ⟦the ceiling, up by one factor of `e`⟧
  have hcU : ((⌈P83 X theta293⌉₊ : ℕ) : ℝ) ≤ P83 X theta293 * Real.exp 1 := by
    have h1 : ((⌈P83 X theta293⌉₊ : ℕ) : ℝ) < P83 X theta293 + 1 :=
      Nat.ceil_lt_add_one hP0.le
    nlinarith
  have hc1 : (1 : ℝ) ≤ ((⌈P83 X theta293⌉₊ : ℕ) : ℝ) :=
    le_trans (by linarith) (Nat.le_ceil (P83 X theta293))
  have hnum : Real.log ((⌈P83 X theta293⌉₊ : ℕ) : ℝ) ≤ a + 1 := by
    have h2 : Real.log (P83 X theta293 * Real.exp 1) = a + 1 := by
      rw [Real.log_mul hP0.ne' (Real.exp_ne_zero 1), Real.log_exp]
    calc Real.log ((⌈P83 X theta293⌉₊ : ℕ) : ℝ)
        ≤ Real.log (P83 X theta293 * Real.exp 1) := Real.log_le_log (by linarith) hcU
      _ = a + 1 := h2
  -- ⟦the floor, down by one factor of `e`⟧
  have hfL : Q83 X / Real.exp 1 < ((⌊Q83 X⌋₊ : ℕ) : ℝ) := by
    have h1 : Q83 X - 1 < ((⌊Q83 X⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
    have h2 : Q83 X / Real.exp 1 ≤ Q83 X - 1 := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    linarith
  have hden : b - 1 ≤ Real.log ((⌊Q83 X⌋₊ : ℕ) : ℝ) := by
    have hq0 : (0 : ℝ) < Q83 X / Real.exp 1 := by positivity
    have h3 : Real.log (Q83 X / Real.exp 1) ≤ Real.log ((⌊Q83 X⌋₊ : ℕ) : ℝ) :=
      Real.log_le_log hq0 hfL.le
    rwa [Real.log_div hQ0.ne' (Real.exp_ne_zero 1), Real.log_exp] at h3
  -- ⟦the ratio⟧
  have hb0 : (0 : ℝ) < b := by linarith
  have hfl0 : (0 : ℝ) < Real.log ((⌊Q83 X⌋₊ : ℕ) : ℝ) := by linarith
  rw [← m4_tail_grade_at_pins (θ := theta293) hL0 hLL0, ← ha, ← hb, div_le_iff₀ hfl0]
  have hab : (a + 1) * b ≤ 2 * a * (b - 1) := by nlinarith
  have hstep : a + 1 ≤ 2 * (a / b) * (b - 1) := by
    have hid : 2 * (a / b) * (b - 1) = 2 * a * (b - 1) / b := by field_simp
    rw [hid, le_div_iff₀ hb0]
    linarith
  have hpos : (0 : ℝ) ≤ 2 * (a / b) := by positivity
  calc Real.log ((⌈P83 X theta293⌉₊ : ℕ) : ℝ) ≤ a + 1 := hnum
    _ ≤ 2 * (a / b) * (b - 1) := hstep
    _ ≤ 2 * (a / b) * Real.log ((⌊Q83 X⌋₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hpos

/-- **THE BAND `EP₂` BUDGET LINE** (`m4_ep2_budget_at_band`).  The capstone's Perron gate
`12·EP₂ ≤ (log X)^{−θ₂₉₃+ε}` at `EP₂ = witEP₂ + (4/3)(2X+20N)·M_tail`, the band's own tail
mass, under the one new threshold `2688·C·loglog X ≤ (log X)^ε`. -/
theorem m4_ep2_budget_at_band {C X ε : ℝ} {N Xd P Q : ℕ}
    (hC0 : 0 < C) (hXd : (Xd : ℝ) = X) (hN : (N : ℝ) = 2 * X) (hX0 : 0 < X)
    (hL : 256 ≤ Real.log X) (hP83 : P83 X theta293 ≤ (P : ℝ))
    (hthr : 10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ))
    (habs : 8640 ≤ (Real.log X) ^ ε)
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)))
    (hband : 2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε) :
    12 * (witEP2 X N Xd P
        + 4 / 3 * ((2 * X + 20 * (N : ℝ))
          * (C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
      ≤ (Real.log X) ^ (-theta293 + ε) := by
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hT0 : (0 : ℝ) < (Real.log X) ^ (-theta293) := Real.rpow_pos_of_pos hL0 _
  -- ⟦the `p²` half⟧ the landed `EP2` gate at the band bottom
  have hwit : 12 * witEP2 X N Xd P ≤ (Real.log X) ^ (-theta293) :=
    witEP2_gate hXd hN hX0 hL hP83 le_rfl hthr
  -- ⟦the tail half⟧ evaluated at the two pins
  have htail : 12 * (4 / 3 * ((2 * X + 20 * (N : ℝ))
      * (C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
      = 672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) + 672 / X := by
    rw [hN, hXd]
    field_simp
    ring
  -- ⟦the grade, into the ε-window⟧
  have hcT : 672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ))
      ≤ (1344 * C * Real.log (Real.log X)) * (Real.log X) ^ (-theta293) := by
    have hc0 : (0 : ℝ) ≤ 672 * C := by positivity
    calc 672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ))
        ≤ 672 * C * (2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) :=
          mul_le_mul_of_nonneg_left hgrade hc0
      _ = (1344 * C * Real.log (Real.log X)) * (Real.log X) ^ (-theta293) := by ring
  have hhalf : (1344 * C * Real.log (Real.log X)) * (Real.log X) ^ (-theta293)
      ≤ (1 / 2 * (Real.log X) ^ ε) * (Real.log X) ^ (-theta293) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0.le
  -- ⟦the `672/X` crumb⟧ `(log X)^{θ₂₉₃} ≤ log X ≤ X`
  have hpow0 : (0 : ℝ) < (Real.log X) ^ theta293 := Real.rpow_pos_of_pos hL0 _
  have hpowX : (Real.log X) ^ theta293 ≤ X := by
    have h1 : (Real.log X) ^ theta293 ≤ (Real.log X) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1
        (le_of_lt (lt_trans theta293_lt_one_div_32 (by norm_num)))
    rw [Real.rpow_one] at h1
    have h2 : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hX0
    linarith
  have hXrec : 672 / X ≤ 672 * (Real.log X) ^ (-theta293) := by
    have hinv : (1 : ℝ) / X ≤ 1 / (Real.log X) ^ theta293 :=
      one_div_le_one_div_of_le hpow0 hpowX
    have hneg : (Real.log X) ^ (-theta293) = 1 / (Real.log X) ^ theta293 := by
      rw [Real.rpow_neg hL0.le, one_div]
    have h672 : (672 : ℝ) / X = 672 * (1 / X) := by ring
    rw [h672, hneg]
    exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  -- ⟦the ε-window closes⟧ `673 ≤ (log X)^ε/2`
  have h673 : (673 : ℝ) * (Real.log X) ^ (-theta293)
      ≤ (1 / 2 * (Real.log X) ^ ε) * (Real.log X) ^ (-theta293) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0.le
  have hsplit : (Real.log X) ^ (-theta293 + ε)
      = (Real.log X) ^ (-theta293) * (Real.log X) ^ ε := Real.rpow_add hL0 _ _
  have hexpand : 12 * (witEP2 X N Xd P
      + 4 / 3 * ((2 * X + 20 * (N : ℝ))
        * (C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
      = 12 * witEP2 X N Xd P
        + (672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) + 672 / X) := by
    rw [← htail]; ring
  rw [hexpand, hsplit]
  linarith

/-- **THE BAND `EP₂` BUDGET LINE, WITH THE ENDPOINT CRUMB** (`m4_ep2_budget_at_band_end`).
`m4_ep2_budget_at_band` with ⟦THE ENDPOINT WALL⟧'s extra `hEP2` summand
`(4/3)(2X+20N)·M_end` (`M4ErrRewire.endMass`).  At the two pins the crumb is exactly
`2688·(log₂ 2X)²/X`, and it is covered by the A-class stone `3(log X)³ ≤ X` derived INLINE
from the existing `hL : 256 ≤ log X` (five applications of `u/5 ≤ e^{u/5}`) — **no new named
threshold**.  The ε-ledger goes `673 → 673 + 2688 = 3361 ≤ 4320`, i.e. still inside `habs`'s
own half `8640/2`. -/
theorem m4_ep2_budget_at_band_end {C X ε : ℝ} {N Xd P Q : ℕ}
    (hC0 : 0 < C) (hXd : (Xd : ℝ) = X) (hN : (N : ℝ) = 2 * X) (hX0 : 0 < X)
    (hL : 256 ≤ Real.log X) (hP83 : P83 X theta293 ≤ (P : ℝ))
    (hthr : 10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ))
    (habs : 8640 ≤ (Real.log X) ^ ε)
    (hgrade : Real.log (P : ℝ) / Real.log (Q : ℝ)
      ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)))
    (hband : 2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε) :
    12 * (witEP2 X N Xd P
        + 4 / 3 * ((2 * X + 20 * (N : ℝ))
          * (C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2))
        + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd))
      ≤ (Real.log X) ^ (-theta293 + ε) := by
  have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hT0 : (0 : ℝ) < (Real.log X) ^ (-theta293) := Real.rpow_pos_of_pos hL0 _
  have hXne : X ≠ 0 := ne_of_gt hX0
  -- ⟦the `p²` half⟧ the landed `EP2` gate at the band bottom
  have hwit : 12 * witEP2 X N Xd P ≤ (Real.log X) ^ (-theta293) :=
    witEP2_gate hXd hN hX0 hL hP83 le_rfl hthr
  -- ⟦the tail half⟧ evaluated at the two pins
  have htail : 12 * (4 / 3 * ((2 * X + 20 * (N : ℝ))
      * (C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
      = 672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) + 672 / X := by
    rw [hN, hXd]
    field_simp
    ring
  -- ⟦THE ENDPOINT CRUMB⟧ `12·(4/3)·(2X+40X)·4L²/X² = 2688·L²/X`
  have hcrumb : 12 * (4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd))
      = 2688 * (Real.logb 2 (2 * X)) ^ 2 / X := by
    rw [endMass, hXd, hN]
    field_simp
    ring
  -- ⟦the grade, into the ε-window⟧
  have hcT : 672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ))
      ≤ (1344 * C * Real.log (Real.log X)) * (Real.log X) ^ (-theta293) := by
    have hc0 : (0 : ℝ) ≤ 672 * C := by positivity
    calc 672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ))
        ≤ 672 * C * (2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293))) :=
          mul_le_mul_of_nonneg_left hgrade hc0
      _ = (1344 * C * Real.log (Real.log X)) * (Real.log X) ^ (-theta293) := by ring
  have hhalf : (1344 * C * Real.log (Real.log X)) * (Real.log X) ^ (-theta293)
      ≤ (1 / 2 * (Real.log X) ^ ε) * (Real.log X) ^ (-theta293) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0.le
  -- ⟦the `672/X` crumb⟧ `(log X)^{θ₂₉₃} ≤ log X ≤ X`
  have hpow0 : (0 : ℝ) < (Real.log X) ^ theta293 := Real.rpow_pos_of_pos hL0 _
  have hpowle : (Real.log X) ^ theta293 ≤ Real.log X := by
    have h1 : (Real.log X) ^ theta293 ≤ (Real.log X) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1
        (le_of_lt (lt_trans theta293_lt_one_div_32 (by norm_num)))
    rwa [Real.rpow_one] at h1
  have hpowX : (Real.log X) ^ theta293 ≤ X := by
    have h2 : Real.log X ≤ X - 1 := Real.log_le_sub_one_of_pos hX0
    linarith
  have hneg : (Real.log X) ^ (-theta293) = 1 / (Real.log X) ^ theta293 := by
    rw [Real.rpow_neg hL0.le, one_div]
  have hXrec : 672 / X ≤ 672 * (Real.log X) ^ (-theta293) := by
    have hinv : (1 : ℝ) / X ≤ 1 / (Real.log X) ^ theta293 :=
      one_div_le_one_div_of_le hpow0 hpowX
    have h672 : (672 : ℝ) / X = 672 * (1 / X) := by ring
    rw [h672, hneg]
    exact mul_le_mul_of_nonneg_left hinv (by norm_num)
  -- ⟦THE INLINE A-CLASS STONE⟧ `3(log X)³ ≤ X`, from `hL` alone: `e^{u/5} ≥ u/5`, five-fold
  have hpow5 : ∀ t : ℝ, Real.exp t ^ 5 = Real.exp (5 * t) := by
    intro t
    rw [show (5 : ℝ) * t = t + t + t + t + t by ring, Real.exp_add, Real.exp_add,
      Real.exp_add, Real.exp_add]
    ring
  have hXeq : Real.exp (Real.log X / 5) ^ 5 = X := by
    rw [hpow5, show (5 : ℝ) * (Real.log X / 5) = Real.log X by ring, Real.exp_log hX0]
  have hfive : Real.log X / 5 ≤ Real.exp (Real.log X / 5) := by
    have h := Real.add_one_le_exp (Real.log X / 5)
    linarith
  have hcube : 3 * (Real.log X) ^ 3 ≤ X := by
    have h1 : (Real.log X / 5) ^ 5 ≤ X := by
      calc (Real.log X / 5) ^ 5 ≤ Real.exp (Real.log X / 5) ^ 5 :=
            pow_le_pow_left₀ (by linarith) hfive 5
        _ = X := hXeq
    have hu2 : (9375 : ℝ) ≤ (Real.log X) ^ 2 := by nlinarith [hL, hL0]
    have hprod := mul_le_mul_of_nonneg_left hu2 (pow_pos hL0 3).le
    have hid : (Real.log X / 5) ^ 5 = (Real.log X) ^ 5 / 3125 := by ring
    rw [hid] at h1
    linarith
  -- ⟦the crumb's grade⟧ `L² ≤ (1.5 log X)²` and `(log X)^θ ≤ log X`, so `L²(log X)^θ ≤ X`
  have hXbig : (1 : ℝ) ≤ 2 * X := by
    have := Real.log_le_sub_one_of_pos hX0
    linarith
  have hLnn : (0 : ℝ) ≤ Real.logb 2 (2 * X) :=
    Real.logb_nonneg (by norm_num) hXbig
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLbound : Real.logb 2 (2 * X) ≤ 3 / 2 * Real.log X := by
    have hgt2 := Real.log_two_gt_d9
    have hlt2 := Real.log_two_lt_d9
    have hprod : (0 : ℝ) ≤ (Real.log X - 256) * (Real.log 2 - 0.6931471803) :=
      mul_nonneg (by linarith) (by linarith)
    have hlogb : Real.logb 2 (2 * X) = (Real.log 2 + Real.log X) / Real.log 2 := by
      rw [Real.logb, Real.log_mul (by norm_num) hXne]
    rw [hlogb, div_le_iff₀ hl2]
    linarith
  have hkey : (Real.logb 2 (2 * X)) ^ 2 * (Real.log X) ^ theta293 ≤ X := by
    have hsq : (Real.logb 2 (2 * X)) ^ 2 ≤ (3 / 2 * Real.log X) ^ 2 :=
      pow_le_pow_left₀ hLnn hLbound 2
    have h1 : (Real.logb 2 (2 * X)) ^ 2 * (Real.log X) ^ theta293
        ≤ (3 / 2 * Real.log X) ^ 2 * (Real.log X) ^ theta293 :=
      mul_le_mul_of_nonneg_right hsq hpow0.le
    have h2 : (3 / 2 * Real.log X) ^ 2 * (Real.log X) ^ theta293
        ≤ (3 / 2 * Real.log X) ^ 2 * Real.log X :=
      mul_le_mul_of_nonneg_left hpowle (by positivity)
    have h3 : (0 : ℝ) ≤ (Real.log X) ^ 3 := (pow_pos hL0 3).le
    linarith
  have hcrumbgrade : 2688 * (Real.logb 2 (2 * X)) ^ 2 / X
      ≤ 2688 * (Real.log X) ^ (-theta293) := by
    rw [hneg, show (2688 : ℝ) * (1 / (Real.log X) ^ theta293)
        = 2688 / (Real.log X) ^ theta293 by ring, div_le_div_iff₀ hX0 hpow0]
    linarith [hkey]
  -- ⟦the ε-window closes⟧ `673 + 2688 = 3361 ≤ (log X)^ε/2`
  have h3361 : (3361 : ℝ) * (Real.log X) ^ (-theta293)
      ≤ (1 / 2 * (Real.log X) ^ ε) * (Real.log X) ^ (-theta293) :=
    mul_le_mul_of_nonneg_right (by linarith) hT0.le
  have hsplit : (Real.log X) ^ (-theta293 + ε)
      = (Real.log X) ^ (-theta293) * (Real.log X) ^ ε := Real.rpow_add hL0 _ _
  have hexpand : 12 * (witEP2 X N Xd P
      + 4 / 3 * ((2 * X + 20 * (N : ℝ))
        * (C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2))
      + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd))
      = 12 * witEP2 X N Xd P
        + (672 * C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) + 672 / X)
        + 2688 * (Real.logb 2 (2 * X)) ^ 2 / X := by
    rw [← htail, ← hcrumb]; ring
  rw [hexpand, hsplit]
  linarith

/-- **THE BAND TAIL SUPPLY** (`m4_tail_supply_at_band`) — the tail MASS, its nonnegativity
and the `EP₂` budget line, all three inside `TypicalPrice.blockfree_sum_le`'s own `∃ C`
scope.  ⟦THE K6 PATTERN⟧: `C` is opaque, so its gate (the new `2688` threshold) can only be
stated where `C` is bound; a consumer instantiates it there.

This is the exact triple `M4MeanSq.m4_meansq_per_chi_gen` wants at `M_tail :=
C·(log P/log Q)/X_d + 1/X_d²` — `hMtail`, `hMtail0`, and `hEP2` at `EP2 := witEP₂ +
(4/3)(2X+20N)·M_tail` (where `hEP2w` is then `le_rfl`). -/
theorem m4_tail_supply_at_band :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        (∀ n, ‖a n‖ ≤ 1) → (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        -- ⟦THE ONE NEW NAMED THRESHOLD⟧
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hmass⟩ := m4_tail_mass_at_band
  refine ⟨C, hC0, ?_⟩
  intro P Q Xd N a X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom ha1 hasupp hP83 hthr habs
    hgrade hband
  refine ⟨hmass P Q Xd N a hP2 hPQ hXd1 hgate hdom ha1 hasupp,
    m4_tail_mass_nonneg hC0 hP2 hPQ hXd1, ?_⟩
  exact m4_ep2_budget_at_band hC0 hXd hN hX0 hL hP83 hthr habs hgrade hband

/-- **THE BAND TAIL SUPPLY, WITH THE ENDPOINT CRUMB** (`m4_tail_supply_at_band_end`) —
`m4_tail_supply_at_band` whose `EP₂` budget line is ⟦THE ENDPOINT WALL⟧'s, i.e. carrying the
extra `(4/3)(2X+20N)·M_end` summand.  The mass and nonnegativity conjuncts are the landed
ones verbatim; the threshold list does not grow. -/
theorem m4_tail_supply_at_band_end :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ) (X ε : ℝ),
        (Xd : ℝ) = X → (N : ℝ) = 2 * X → 0 < X → 256 ≤ Real.log X →
        2 ≤ P → P ≤ Q → 1 ≤ Xd →
        100 * Real.log Q ≤ Real.log Xd →
        ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
            ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
        (∀ n, ‖a n‖ ≤ 1) → (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
        P83 X theta293 ≤ (P : ℝ) →
        10752 * Real.logb 2 (2 * X) ≤ (Real.log X) ^ (2 : ℝ) →
        8640 ≤ (Real.log X) ^ ε →
        Real.log (P : ℝ) / Real.log (Q : ℝ)
          ≤ 2 * (Real.log (Real.log X) * (Real.log X) ^ (-theta293)) →
        2688 * C * Real.log (Real.log X) ≤ (Real.log X) ^ ε →
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
              ‖a n‖ ^ 2 / (n : ℝ) ^ 2
            ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
          ∧ 0 ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2
          ∧ 12 * (witEP2 X N Xd P
              + 4 / 3 * ((2 * X + 20 * (N : ℝ))
                * (C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2))
              + 4 / 3 * ((2 * X + 20 * (N : ℝ)) * endMass Xd))
            ≤ (Real.log X) ^ (-theta293 + ε) := by
  obtain ⟨C, hC0, hmass⟩ := m4_tail_mass_at_band
  refine ⟨C, hC0, ?_⟩
  intro P Q Xd N a X ε hXd hN hX0 hL hP2 hPQ hXd1 hgate hdom ha1 hasupp hP83 hthr habs
    hgrade hband
  refine ⟨hmass P Q Xd N a hP2 hPQ hXd1 hgate hdom ha1 hasupp,
    m4_tail_mass_nonneg hC0 hP2 hPQ hXd1, ?_⟩
  exact m4_ep2_budget_at_band_end hC0 hXd hN hX0 hL hP83 hthr habs hgrade hband

end Salt.MR
