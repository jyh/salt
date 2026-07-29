/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TypicalPrice
import Salt.MR.USetPins

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

## ⚠ THE POINT-vs-BAND WALL (the residue R3a/R3b leave, recorded — NOT repaired here)

`blockfree_sum_le` prices the tail at `C·(log P/log Q)/W + 1/W²`.  That is small exactly
when the band `[P,Q]` is WIDE on the log scale.  The M4 capstone's row, however, is pinned at
`P = Q` (`m4_meansq_per_chi_gen` reads `ramI (H83 X θ₂₉₃) P P`), where

  `log P/log Q = 1`   and hence   `M_tail ≍ 1/X_d`,

so `(2X + 20N)·M_tail ≍ 42` — an `O(1)` charge, which no ε-window absorbs.  The relaxed gate
buys nothing AT A POINT; it buys the whole `[P₈₃, Q₈₃]` band, where `m4_tail_grade_at_pins`
gives the genuinely small `loglog X·(log X)^{−θ₂₉₃}`.

So the remaining design question is the one the R3-SCOPE named as its item (4), now sharp:
**the capstone's Ramaré block is a POINT and the tail's pricing engine needs a BAND.**  Either
the row is re-cut at a band block (`ramI H P Q` with `Q ≥ Q₈₃`, which moves `A2Frame3`'s
`P = Q` convention), or the door datum supplies its own tail mass by a route other than
`typical_density_le`.  Nothing here assumes either; the three stones below are unconditional
and are what a repair on either route will consume.

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

end Salt.MR
