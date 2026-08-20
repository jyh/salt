/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Wall
import Salt.SW.MobiusRateClose

/-!
# THE PARITY WALL, UNCONDITIONAL (sprint-2 Track A trophy discharge)

`Salt.SW.mmuRate_holds` (the 1/ζ Perron contour chain: `zeta_lower_shallow` →
`zeta_inv_shallow` → `mmu1_eq_integral`/`mmu_rectBI_eq_zero` → the budget at
`log T = (log x)^{1/10}`) discharges `MmuRate` — the single analytic hypothesis
the twinbar wall shipped conditional on (the registered Q6a debt, the Rb-4
obstruction).  This file is the house wiring pass: the two conditional
headlines of `Salt/TwinBar/Wall.lean` restated with the hypothesis GONE.

No proof content here — pure composition through
`LambdaSummatory_of_MmuRate`.  The wall's mathematics is unchanged; its
conditionality is over.
-/

namespace Salt.TwinBar

open Filter

/-- ⭐ **THE UNTWISTED λ TROPHY, NAMED.**  `LambdaSummatory` at every `A > 0`,
unconditional: the `MmuRate` slot is discharged by the landed nullary
`Salt.SW.mmuRate_holds` (`Salt/SW/MobiusRateClose.lean:1059`).

Before this, the composition `LambdaSummatory_of_MmuRate Salt.SW.mmuRate_holds`
was re-spelled inline at four discharge sites (`:39`, `:50`,
`WallCorr.lean:151`, `:227`).  Naming it once is the restatement-renames law:
the wall's mathematics is unchanged and the constant now has a name a consumer
can cite.  QUEUE.md P1 fill 5b. -/
theorem lambdaSummatory_holds (A : ℝ) (hA : 0 < A) : LambdaSummatory A :=
  LambdaSummatory_of_MmuRate Salt.SW.mmuRate_holds A hA

/-- **The effective parity wall, UNCONDITIONAL.**  `parity_wall_effective`
with the `LambdaSummatory` slot discharged by the landed
`Salt.SW.mmuRate_holds`. -/
theorem parity_wall_unconditional (A : ℝ) (hA : 0 < A)
    (Φ : BoundingSieve → ℝ)
    (htol : ∀ (D : ℕ) (B : ℝ), ∀ s t, SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    ∃ (C : ℝ) (x₀ : ℕ), 0 < C ∧ ∀ x : ℕ, x₀ ≤ x →
      Φ (sMinus x)
        ≤ 2 + 2 * ((Nat.sqrt x : ℝ) + C * x * (1 + Real.log x) / (Real.log x) ^ A) :=
  parity_wall_effective A hA
    (lambdaSummatory_holds A hA) Φ htol hcert

/-- **No parity-beating certificate, UNCONDITIONAL.**  The Q6a headline with
its last hypothesis discharged: no tolerant certificate lower-bounds a
positive fraction of the sifted sum, full stop. -/
theorem no_parity_beating_certificate_unconditional (A : ℝ) (hA : 2 < A)
    (D : ℕ) (hD : 2 ≤ D) (Φ : BoundingSieve → ℝ)
    (htol : ∀ s t (B : ℝ), SieveAgree s t D B → |Φ s - Φ t| ≤ 2 * B)
    (hcert : ∀ s, Φ s ≤ s.siftedSum) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in atTop, c * (sMinus x).siftedSum ≤ Φ (sMinus x) :=
  no_parity_beating_certificate A hA
    (lambdaSummatory_holds A (by linarith)) D hD Φ htol hcert

end Salt.TwinBar
