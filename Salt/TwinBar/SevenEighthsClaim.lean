/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SiegelTwin

/-!
# OpenAI's 7/8 statement, restated, and what it gives `NoSiegelZeros` (dated 2026-10-22)

`DirichletSevenEighths` restates, at this repository's mathlib, the statement of OpenAI's
theorem `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (file
`lean/ComparatorChallenges/DirichletSevenEighths.lean` of `github.com/openai/math` at
`1581d4cbdd69`). This repository does not import OpenAI's proof, so nothing here depends on it:
`DirichletSevenEighths` is a hypothesis in this file, and the theorem below is an implication.

`noSiegelZeros_of_sevenEighths` proves that the statement implies `NoSiegelZeros`, with the
constant `c = (log 2)/8`: a real zero `β < 1` of a nontrivial character has `β ≤ 7/8`, and
`7/8 ≤ 1 − c/log q` for every `q ≥ 2`.

The restatement follows OpenAI's text, except that `q` is explicit here; the two were compared by
hand, not mechanically. OpenAI's theorem is over mathlib `d13f23b7`
and this file is over this repository's mathlib (`360da6fa`); the two agree on the
definitions the statement names directly, but below them 591 definitions differ structurally and
their equivalence has not been checked, so OpenAI's theorem does not discharge
`DirichletSevenEighths` here.
-/

open Complex DirichletCharacter

namespace Salt.TwinBar

/-- OpenAI's 7/8 statement: no Dirichlet L-function vanishes at any `s` with `7/8 < Re s`,
except at the pole of the trivial character at `s = 1`. -/
def DirichletSevenEighths : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    (7 / 8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → LFunction χ s ≠ 0

/-- **The 7/8 statement implies `NoSiegelZeros`**, with `c = (log 2)/8`. -/
theorem noSiegelZeros_of_sevenEighths (h : DirichletSevenEighths) : NoSiegelZeros := by
  refine ⟨Real.log 2 / 8, by positivity, ?_⟩
  intro q _ χ hq _ _ hχ β hβ _
  have h78 : β ≤ 7 / 8 := by
    by_contra hlt
    exact h q χ (s := (β : ℂ)) (by simpa using not_le.mp hlt) (fun h1 => hχ h1.1) hβ
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogq : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2
  have hlogqpos : 0 < Real.log q := lt_of_lt_of_le hlog2 hlogq
  have hc : Real.log 2 / 8 / Real.log q ≤ 1 / 8 := by
    rw [div_le_iff₀ hlogqpos]
    linarith
  linarith

end Salt.TwinBar
