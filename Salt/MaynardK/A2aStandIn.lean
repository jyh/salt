/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.BudgetPoly
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.Order.Antidiag.Finsupp
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# A stand-in for the three DEFINITIONS of `SeriesM`/`BasisM` (node A2a), to be deleted at its merge

`SquareM` and `JMainM` (node A2b) are built on the general-`M` series `GM`, its `weight`, and the
basis `basisPolyM`, which node A2a lands in `SeriesM`/`BasisM` on a separate branch. Until that
merge, this module carries the three definitions VERBATIM (and nothing else): no theorem of A2a is
proved here. A2a's two results that A2b consumes, `eval_basisPolyM` and `simplexInt_basisPolyM`,
enter `SquareM`/`JMainM` as the explicit hypotheses `BasisEvalM` and `BasisIntM`.

At the merge: delete this module, import `Salt.MaynardK.BasisM` in `SquareM` in its place, and
discharge the hypotheses with `eval_basisPolyM M k` and `simplexInt_basisPolyM M k`. Importing both
this module and `SeriesM` in one build is a duplicate-declaration error, by design.
Pure polynomial algebra: nothing here bears on twin primes.
-/

open Finset Nat Salt.Twelve

namespace Salt.MaynardK

/-- The weight of an exponent vector, `Σ_m 2(m+1)·j m`: the degree of `Π_m P_{2(m+1)}^{j m}`. -/
def weight {M : ℕ} (j : Fin M → ℕ) : ℕ := ∑ m : Fin M, 2 * ((m : ℕ) + 1) * j m

/-- `GM M = Σ_j (weight j)! / Π_m (j m)! · xʲ`, the `M`-variable twin of `G`. -/
noncomputable def GM (M : ℕ) : MvPowerSeries (Fin M) ℚ :=
  fun j => (((weight ⇑j)! : ℕ) : ℚ) / ∏ m, (((j m)! : ℕ) : ℚ)

/-- `(1 − P₁)^a · Π_m P_{2(m+1)}^{C m}` on `k` coordinates, as a budget polynomial: the
concatenation, over the assignment tuples `e` (one antidiagonal of `C m` per `m`), of the monomial
`Π_i t_i^{Σ_m 2(m+1)·e m i} · (1 − Σt)^a` with coefficient `Π_m multinomial (e m)`. -/
noncomputable def basisPolyM (M k a : ℕ) (C : Fin M → ℕ) : BPoly k :=
  (Fintype.piFinset fun m => piAntidiag (univ : Finset (Fin k)) (C m)).toList.map
    fun e => ((fun i => ∑ m : Fin M, 2 * ((m : ℕ) + 1) * e m i), a,
      ((∏ m, Nat.multinomial univ (e m) : ℕ) : ℚ))

end Salt.MaynardK
