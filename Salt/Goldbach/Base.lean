/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.RazorClose
import Salt.Chen.GlueNormalized
import Salt.Chen.SuperClose
import Salt.Chen.ChainValues
import Salt.Chen.MassLedger
import Salt.Chen.MassLedgerA1
import Salt.Chen.CountFinal
import Salt.Chen.WRatioSharp
import Salt.Chen.BetaSW
import Salt.Chen.LogToolkit
import Salt.Chen.WeightTrivia

/-!
# G-IMPORT — the Goldbach (Chen-2) backbone skeleton

Design: `docs/exploration/q1-design.md` (Q1 DESIGN FREEZE — chen_goldbach,
Chen-2, full in-sprint).  This module is the wave-W0 root of `Salt/Goldbach/`:
it imports the **2A backbone** the later Goldbach waves consume unchanged and
records three cheap smoke assertions witnessing that the reused keystones are
reachable from this new directory.

## The reuse contract (design D1 — what is NOT rewritten)

The chen_goldbach target
`∃ N₀, ∀ N ≥ N₀, Even N → ∃ p q, N = p + q ∧ p.Prime ∧ IsP2 2 q`
reuses the 2A numeric/analytic corpus with NO re-certification: the razor
(`RazorClose`), the Rosser value cascade (`ChainValues`/`SuperClose`,
`fchain ≥ 9779/10000`), the mass ledger (`MassLedger`/`MassLedgerA1`), the
count bridge (`CountFinal`, `c̄`), the sharp W-ratio (`WRatioSharp`), the
Siegel–Walfisz prime indicator (`BetaSW`), `LogToolkit`, and the P₂ carrier
`IsP2` (`WeightTrivia`).  The load-bearing reuse fact is the singular-series
invariance: `𝔖_N` enters only through `W`, `X_W = totalMass·W` cancels in the
normalised bracket, and `c̄` is `N`-free.  Any wave that finds itself editing a
2A file has left the design (design D1 — STOP AND FLAG).

This file imports exactly the razor/values/ledger subset that `Salt/Chen/
FinLed3.lean` and `Salt/Chen/Headline4.lean` pull for the same purpose; it does
NOT import `Salt.Chen.All` (the terminal + axiom audit).

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Salt.Chen

/-! ## Smoke assertions — compile-time evidence the backbone is reachable. -/

/-- The certified scalar razor margin is reachable (`RazorClose`): the frozen
`1/100` lower bound on the normalised constant stack. -/
example :
    (1 : ℝ) / 100
      ≤ 9779 / 10000 - (3 + 43 / 75) * (Real.log 6 / 4) / 2
          - cbar * (3 / 8) * (243 / 100) / 2 :=
  razor_scalar_margin

/-- The switch-constant certificate `c̄ < 363084/1000000` is reachable
(`CbarCert` via `RazorClose`); `c̄` is `N`-free, hence reused verbatim. -/
example : cbar < 363084 / 1000000 := cbar_lt

/-- The A₁ value keystone `9779/10000 ≤ fchain N s` is reachable
(`SuperClose`), here at truncation depth `N = 2` on the A₁ window. -/
example :
    ∀ s ∈ Set.Icc (39992 / 10000 : ℝ) 4, (9779 / 10000 : ℝ) ≤ fchain 2 s :=
  fchain_A1_final 2 (by norm_num)

/-- The P₂ carrier `IsP2 2` (`WeightTrivia`) admits a prime — the target's
`IsP2 2 q` conjunct is the same carrier used by the twin headline. -/
example : IsP2 2 3 := Or.inl Nat.prime_three

-- The normalised ledger package (`GlueNormalized.normalized_package`) is
-- reachable — the F2 ledger floor the Goldbach razor reuses.
#check @normalized_package

end Salt.Goldbach
