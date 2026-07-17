/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The entropy endpoints of the decrement contradiction (Chowla / Liouville spine)

Wave IV of the Tao 1509.05422 §3 entropy-decrement spine consumes exactly two
scalar endpoints of the per-symbol entropy `e(H) = ℍ(X_H)/H`:

* **the ceiling** `e(H) ≤ log 2` (`entropy_per_symbol_le`, dividing the landed
  `entropy_liouvilleWindow_le` by `H > 0`); and
* **the floor** `0 ≤ e(H)` (`entropy_nonneg_per_symbol`, `entropy_nonneg` needs
  NO probability measure — it is `measureEntropy_nonneg`).

Together with the mutual-information nonnegativity `0 ≤ I(X_H : Y_H)`
(`mutualInfo_window_nonneg`) and the pure-logic failure-branch extraction
(`decrement_of_not_forall`), these assemble the contradiction skeleton
(`decrement_exists_of_tower`): IF the mutual-information bound fails at every
tower level `j < J`, the telescope (`htele`, wave III's frozen output) forces
`e(H_J) ≤ e(H_0) − towerDropSum < log 2 − log 2 = 0`, contradicting the floor.

The barely-divergent series `log 2 < towerDropSum` is NOT proven here: it is the
regime field `ChowlaRegime.hJcon` (its docstring RELOCATES the divergence to the
anti-vacuity node that constructs a `ChowlaRegime`).  So the assembly is
hypothesis-parametric on the telescope `htele` and the tower-range facts `hmono`
— it composes with wave III (`Salt/Entropy/Chowla/Tower.lean`) the moment those
land, without this file's depending on that in-flight subtree.
-/
import Mathlib
import Salt.Entropy.Chowla.Step

open MeasureTheory ProbabilityTheory Real

namespace Salt.Entropy.Chowla

/-! ### Endpoint 1 — the per-symbol entropy ceiling `e(H) ≤ log 2` -/

/-- **The per-symbol entropy ceiling** (the (3.8) Liouville form, divided by `H`).
For any tower width `H ≥ 1`, the Liouville window's entropy-per-symbol is at most
`log 2`, since `ℍ(X_H) ≤ H·log 2` (the range sits in `{-1,1}^H`). -/
theorem entropy_per_symbol_le (R : ChowlaRegime) (H : ℕ) (hH : 1 ≤ H) :
    H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ) ≤ Real.log 2 := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  rw [div_le_iff₀ hHpos, mul_comm]
  exact entropy_liouvilleWindow_le H (logMeasure R.x R.ω)

/-! ### Endpoint 2 — the per-symbol entropy floor `0 ≤ e(H)` -/

/-- **The per-symbol entropy floor.** Entropy is nonnegative (`entropy_nonneg`,
no probability-measure hypothesis needed) and `H ≥ 0`, so `0 ≤ ℍ(X_H)/H`. -/
theorem entropy_nonneg_per_symbol (R : ChowlaRegime) (H : ℕ) :
    0 ≤ H[liouvilleWindow H ; logMeasure R.x R.ω] / (H : ℝ) :=
  div_nonneg (entropy_nonneg _ _) (Nat.cast_nonneg _)

/-! ### The mutual-information nonnegativity `0 ≤ I(X_H : Y_H)` -/

/-- **Mutual-information nonnegativity** at the window/residue pair.  Both windows
are measurable (`measurable_liouvilleWindow`, `measurable_residueWindow`) with
finite range (the registered `FiniteRange` instances), so `mutualInfo_nonneg`
applies on `logMeasure R.x R.ω`. -/
theorem mutualInfo_window_nonneg (R : ChowlaRegime) (H : ℕ) :
    0 ≤ I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω] :=
  mutualInfo_nonneg (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H)
    (logMeasure R.x R.ω)

/-! ### The failure-branch extraction (pure logic) -/

/-- **The failure-branch extraction.**  If it is not the case that the bound
fails at every `j < J`, then the bound holds at some `j < J`.  Pure logic
(`push_neg`); wave IV instantiates `P j` with the mutual-information bound at the
tower level `H_j = chowlaTower ..j`. -/
lemma decrement_of_not_forall {J : ℕ} {P : ℕ → Prop}
    (h : ¬ ∀ j < J, ¬ P j) : ∃ j < J, P j := by
  push Not at h
  exact h

/-! ### The contradiction assembly skeleton (hypothesis-parametric on wave III) -/

/-- The per-tower-level mutual-information bound predicate; `decrement_exists_of_tower`
extracts the tower level at which it holds.  Reducible, hence defeq to the explicit
inequality of the `entropy_decrement` headline. -/
private abbrev MIbound (R : ChowlaRegime) (H : ℕ) : Prop :=
  I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]
    ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H)))

/-- **The contradiction assembly** (the wave-IV endpoint of Lemma 3.1).
Hypothesis-parametric on wave III's two frozen outputs:

* `htele` — the telescope: IF the mutual-information bound fails at every tower
  level `j < J`, the per-symbol entropy drops by `towerDropSum` from `H_0` to
  `H_J` (wave III fuses `step_ineq_3_11` over the tower with `k_j = ⌊C₀·…⌋`); and
* `hmono` — the tower stays in `[H₋, H₊]` on `j < J`.

The contradiction: assuming the bound fails everywhere, `htele` plus the ceiling
(`e(H_0) ≤ log 2`), the floor (`0 ≤ e(H_J)`) and `R.hJcon` (`log 2 < towerDropSum`)
force `0 ≤ e(H_J) ≤ log 2 − towerDropSum < 0`.  Hence the bound holds at some
`j < J`; that `H_j` is the witness (`dvd_chowlaTower` supplies `a ∣ H_j`). -/
theorem decrement_exists_of_tower (R : ChowlaRegime)
    (htele :
      (∀ j < R.J, ¬ MIbound R (chowlaTower R.C0 R.a R.Hlo j)) →
        H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo R.J); logMeasure R.x R.ω]
            / (chowlaTower R.C0 R.a R.Hlo R.J : ℝ)
          ≤ H[liouvilleWindow (chowlaTower R.C0 R.a R.Hlo 0); logMeasure R.x R.ω]
              / (chowlaTower R.C0 R.a R.Hlo 0 : ℝ)
            - towerDropSum R.C0 R.a R.Hlo R.J)
    (hmono : ∀ j, j < R.J →
      R.Hlo ≤ chowlaTower R.C0 R.a R.Hlo j ∧ chowlaTower R.C0 R.a R.Hlo j ≤ R.Hhi) :
    ∃ H, R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ R.a ∣ H ∧
      I[liouvilleWindow H : residueWindow R.eps H ; logMeasure R.x R.ω]
        ≤ (H : ℝ) / (Real.log H * Real.log (Real.log (Real.log H))) := by
  -- the base width `H_0 = a·H₋ ≥ 1`
  have hbase : 1 ≤ chowlaTower R.C0 R.a R.Hlo 0 := by
    have ha := R.ha
    have hlo := R.hHlo_floor
    change 1 ≤ R.a * R.Hlo
    exact Nat.mul_pos (by omega) (by omega)
  -- the bound cannot fail at every level: else the telescope beats the floor
  have hnotall : ¬ ∀ j < R.J, ¬ MIbound R (chowlaTower R.C0 R.a R.Hlo j) := by
    intro hall
    have hdrop := htele hall
    have hceil := entropy_per_symbol_le R (chowlaTower R.C0 R.a R.Hlo 0) hbase
    have hfloor := entropy_nonneg_per_symbol R (chowlaTower R.C0 R.a R.Hlo R.J)
    have hcon := R.hJcon
    linarith
  -- extract the good level and package the witness
  obtain ⟨j, hjJ, hb⟩ := decrement_of_not_forall hnotall
  exact ⟨chowlaTower R.C0 R.a R.Hlo j, (hmono j hjJ).1, (hmono j hjJ).2,
    dvd_chowlaTower R.C0 R.a R.Hlo j, hb⟩

end Salt.Entropy.Chowla
