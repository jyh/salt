/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ThreePrimes.Ramanujan
import Salt.ThreePrimes.SingularSeries
import Salt.ThreePrimes.SingularIntegral
import Salt.ThreePrimes.MajorArc
import Salt.ThreePrimes.MinorArc
import Salt.ThreePrimes.Arcs
import Salt.ThreePrimes.Count
import Salt.ThreePrimes.Assembly

/-!
# Three primes: the aggregate

Vinogradov's three-primes theorem, written for human readers. The plan, with the proof in prose, is
`docs/plans/three-primes-PLAN.md`. The modules follow its steps: Ramanujan sums (L5), the singular
series (L11–L13), the singular integral (L9–L10), the major-arc approximation (L8), Vinogradov's
minor-arc estimate (L19), the arcs (L4), counting with weights (L1–L3), and the assembly (L20–L21),
which proves `three_primes`.
-/
