import Salt.MaynardK.ControlsSeriesM
import Salt.MaynardK.ControlsSquareM

/-!
# BridgeM — the general-`M` certificate bridge, closed

`SquareM`/`JMainM` (A2b) were written while `SeriesM`/`BasisM` (A2a) were in flight, so
they take A2a's two basis facts as the hypotheses `BasisEvalM` and `BasisIntM`, and their
`M = 1` Controls take `GMOneEq`. This module discharges all three from A2a's theorems and
restates the two Controls with no hypothesis, so a consumer at a concrete `M` and `k` (the
`k = 54` certificate) needs nothing extra.

Nothing here bears on twin primes.
-/

open Finset

namespace Salt.MaynardK

/-- A2a's `eval_basisPolyM`, in A2b's hypothesis form. -/
theorem basisEvalM_holds (M k : ℕ) : BasisEvalM M k :=
  fun a C t => eval_basisPolyM M k a C t

/-- A2a's `simplexInt_basisPolyM`, in A2b's hypothesis form (`closedM` is its right-hand side). -/
theorem basisIntM_holds (M k : ℕ) : BasisIntM M k := by
  intro a C
  rw [simplexInt_basisPolyM]
  rfl

/-- A2a's `coeff_GM_one_pow`, in A2b's indexing (`equivFunOnFinite.symm` of a constant tuple). -/
theorem gmOneEq_holds : GMOneEq := by
  intro k c
  rw [equivFunOnFinite_symm_fin_one]
  exact coeff_GM_one_pow k c

/-- CONTROL, unconditional: `Iform_eq`, restated by `type_of%`, from `IformM_eq` at `M = 1`. -/
theorem Iform_eq'' : type_of% @Iform_eq := Iform_eq_ofM gmOneEq_holds

/-- CONTROL, unconditional: `Jform_eq`, restated by `type_of%`, from `JformM_eq` at `M = 1`. -/
theorem Jform_eq'' : type_of% @Jform_eq := Jform_eq_ofM gmOneEq_holds

end Salt.MaynardK
