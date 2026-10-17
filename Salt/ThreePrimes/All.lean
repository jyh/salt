/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ThreePrimes.Ramanujan
import Salt.ThreePrimes.SingularSeries
import Salt.ThreePrimes.SingularIntegral
import Salt.ThreePrimes.MajorArc

/-!
# Three primes: the aggregate

Vinogradov's three-primes theorem, written for human readers. The plan, with the proof in prose, is
`docs/plans/three-primes-PLAN.md`. The modules follow its steps: Ramanujan sums (L5), the singular
series (L11–L13), the singular integral (L9–L10) and the major-arc approximation (L8). The minor arcs
and the assembly are still to come.
-/
