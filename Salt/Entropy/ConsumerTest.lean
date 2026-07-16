/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Entropy.Measure

/-!
# Consumer test for the measure-level entropy API (sprint-3 A-R1, wave-1 lane W1-2)

The gate's charge-2 refinement asks each wave to keep one Scratch-grade `example`
compiling that demonstrates the freshly-landed API is *consumable*. This lane
lands `Salt/Entropy/Measure.lean` (PFR's `measureEntropy`, `Hm[·]`), so the
target here is the measure-level surface: `measureEntropy_le_log_card`,
`measureEntropy_dirac`, and `measureEntropy_nonneg`, instantiated at the concrete
finite measure `Measure.dirac (0 : Fin 2)`.

The richer random-variable-level (3.1)/(3.5)/(3.7) triple is pinned to the
Basic.lean path (wave 1.5) per the gate verdict; this file only certifies that
the measure layer this lane delivers is usable downstream.
-/

open MeasureTheory ProbabilityTheory Real

section ConsumerTest

/-- The measure-level entropy of a concrete finite measure is bounded by the log
of the cardinality of its (finite) type — `measureEntropy_le_log_card` is
consumable. -/
example : Hm[(Measure.dirac (0 : Fin 2))] ≤ Real.log (Fintype.card (Fin 2)) :=
  measureEntropy_le_log_card _

/-- The entropy of a Dirac mass vanishes — `measureEntropy_dirac` is consumable. -/
example : Hm[(Measure.dirac (0 : Fin 2))] = 0 :=
  measureEntropy_dirac 0

/-- Measure entropy is nonnegative — `measureEntropy_nonneg` is consumable. -/
example : 0 ≤ Hm[(Measure.dirac (0 : Fin 2))] :=
  measureEntropy_nonneg _

end ConsumerTest
