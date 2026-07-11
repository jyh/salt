/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# W5 carriers — the Chebyshev-ψ counting functions (Fable-frozen)

Design: `docs/blueprints/largesieve.md`, wave W5. The three counting
functions BDH is stated over. Conventions (frozen):
* summation range `Finset.Icc 1 x` (`Λ 0 = 0` regardless; `Icc` avoids `n = 0`
  case fuss);
* residue classes via `n % q = a % q` (the `Salt/Maynard` congruence style);
* `ψ(x, χ)` is ℂ-valued (characters are ℂ-valued), `ψ(x; q, a)` and `ψ(x)`
  are ℝ-valued.
-/

namespace Salt.LS

open ArithmeticFunction

/-- The character-twisted Chebyshev function `ψ(x, χ) = ∑_{n ≤ x} Λ(n) χ(n)`. -/
noncomputable def psiChi {q : ℕ} (x : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x, (vonMangoldt n : ℂ) * χ (n : ZMod q)

/-- The progression Chebyshev function
`ψ(x; q, a) = ∑_{n ≤ x, n ≡ a mod q} Λ(n)`. -/
noncomputable def psiAP (x q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a % q), vonMangoldt n

/-- The Chebyshev function `ψ(x) = ∑_{n ≤ x} Λ(n)`. -/
noncomputable def psiTot (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, vonMangoldt n

end Salt.LS
