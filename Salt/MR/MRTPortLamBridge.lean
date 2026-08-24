/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RHSGrade
import Salt.MR.NonPret
import Salt.MR.M4Exit

/-!
# Item 15, node N3 — the `lam` / `lamCoeff` bridge for `pretDistSq`

The MRT port (arXiv:1503.05121, Thm 1.7 / Prop 2.4) states its pretentious
distance at the honest Liouville coefficient `lamCoeff`, while this corpus's
non-pretentiousness stone S5 (`Salt/MR/NonPret.lean`) states it at `lam`, the
**constant `−1`**.  This module is the sanctioned bridge between the two.

## Why the bridge is legitimate — and why it is NOT a crossing

⚠️ The corpus carries a standing warning at ~15 sites (e.g. `M4Close.lean:590`,
"the two must never be crossed") against conflating `lam` with the true Liouville
function: `lam = fun _ => −1` (`NonPret.lean:48`) and `lamCoeff = λ`
(`M4Window.lean:74`) agree **only on primes** and differ everywhere else — most
visibly at `1`, where `λ(1) = 1 ≠ −1`.  Any statement summing over ALL `m`
(`sum_lam_residue_eq` vs `sum_liou_residue_eq`) genuinely must not cross them.

`pretDistSq` is not such a statement.  It sums over
`(Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime` — **primes only** (`Dist.lean:59-61`)
— and `pretDistSq_congr_primes` (`RHSGrade.lean:137-141`) reads its left datum at
primes and nowhere else.  So on this one object the two spellings are
interchangeable, and the exchange is a theorem rather than a confusion.

## Structure

* `lam_eq_lamCoeff_of_prime` — the pointwise fact: `lam p = lamCoeff p` for prime
  `p`, discharged by `lamCoeff_eq_liouvilleC` (`M4Exit.lean:99`, `rfl`) together
  with `liouvilleC_prime` (`M4Residue.lean:109`).  `pretDistSq_congr_primes`
  alone has nothing to feed it; this is the missing half.
* `pretDistSq_lam_eq_lamCoeff` — **the node**: the two distances are equal.
-/

namespace Salt.MR

/-- **The two λ-spellings agree at primes.**  `lam` is the constant `−1`
(`NonPret.lean:48`) and `lamCoeff` is the honest Liouville function
(`M4Window.lean:74`); at a prime `p` we have `Ω(p) = 1`, so `λ(p) = −1` and the
two coincide.  They do NOT coincide off the primes — see the module docstring. -/
theorem lam_eq_lamCoeff_of_prime {p : ℕ} (hp : p.Prime) : lam p = lamCoeff p := by
  have hlam : lam p = -1 := rfl
  have hliou : lamCoeff p = -1 := by
    rw [lamCoeff_eq_liouvilleC]
    exact liouvilleC_prime hp
  rw [hlam, hliou]

/-- **N3 — the `lam`/`lamCoeff` bridge for the pretentious distance.**
`𝔻(lam, g; X)² = 𝔻(lamCoeff, g; X)²`.  Legitimate because `pretDistSq` reads its
left datum only at primes (`Dist.lean:59-61`), where the constant `−1` and the
Liouville function agree.  This lets the S5 non-pretentiousness stone (stated at
`lam`) and the MRT port (stated at `lamCoeff`) meet on the same object. -/
theorem pretDistSq_lam_eq_lamCoeff (g : ℕ → ℂ) (X : ℝ) :
    pretDistSq lam g X = pretDistSq lamCoeff g X :=
  pretDistSq_congr_primes (fun _ hp => lam_eq_lamCoeff_of_prime hp) X

end Salt.MR
