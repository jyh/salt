/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.RH.Targets
import Salt.TwinBar.SevenEighthsClaim

/-!
# O106 — `GRHDirichlet` gives the 7/8 statement

`Salt.TwinBar.DirichletSevenEighths` (TwinBar/SevenEighthsClaim) asks that no Dirichlet
`L`-function vanish at any `s` with `7/8 < re s`, except at the pole of the trivial character at
`s = 1`. `GRHDirichlet` (Targets) speaks only about zeros in the open strip `0 < re s < 1`, so the
implication is not monotonicity alone. The proof splits at `re s = 1`:
* for `7/8 < re s < 1`, `GRHDirichlet` puts the zero on `re s = 1/2`, a contradiction;
* for `1 ≤ re s`, Mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re` gives
  nonvanishing away from that pole.

Each `*_of_sevenEighths` theorem in this repository then holds under `GRHDirichlet`, by
composition with `sevenEighths_of_GRH`; `noSiegelZeros_of_GRH` below is one such composition.
-/

namespace Salt.RH

open Complex DirichletCharacter

/-- **`GRHDirichlet` gives the 7/8 statement.** A zero with `7/8 < re s < 1` would lie on
`re s = 1/2`; a zero with `1 ≤ re s` is excluded by Mathlib's nonvanishing on `re s ≥ 1`, which
needs only that `(χ, s)` is not the trivial character's pole. -/
theorem sevenEighths_of_GRH (h : GRHDirichlet) : Salt.TwinBar.DirichletSevenEighths := by
  intro q _ χ s h78 hpole hzero
  by_cases hlt : s.re < 1
  · have hhalf : s.re = 1 / 2 := h q χ s hzero (by linarith) hlt
    linarith
  · exact LFunction_ne_zero_of_one_le_re χ (not_and_or.mp hpole) (not_lt.mp hlt) hzero

/-- **`GRHDirichlet` gives `NoSiegelZeros`**, with the constant `(log 2)/8` of
`Salt.TwinBar.noSiegelZeros_of_sevenEighths`. -/
theorem noSiegelZeros_of_GRH (h : GRHDirichlet) : Salt.TwinBar.NoSiegelZeros :=
  Salt.TwinBar.noSiegelZeros_of_sevenEighths (sevenEighths_of_GRH h)

end Salt.RH
