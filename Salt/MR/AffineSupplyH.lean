/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦AFFINE SUPPLY AT `a = 1`⟧ — the `(1, 0)` producer of `LogChowlaAffSupply` and the
integration control, λ-BV wave 2-W, 2026-09-03

Two names, in `Salt/MR` because the producer is the landed prize `logChowla2_v7_rated_h`
(`Salt/MR/V7RatedH.lean:1067`) and `Salt/Entropy` cannot import `Salt/MR`.

* `logChowlaAffSupply_one_zero` — `LogChowlaAffSupply 1 0 h` at every `h` with `log h ≤ 7`,
  by reading three of the prize's conjuncts and transporting the failure Prop through
  `logChowlaFailsAff_one_zero`.
* `oddOmega_twinProd_infinite` — infinitely many `n` with `Ω(n(n+2))` odd, obtained FROM THE
  SPINE at `P = 1, r = 0, h = 2`.  ⛔ An ELEMENTARY fact (three lines by `λ(p) = −1`,
  `λ(pq) = 1` at odd primes); its only value is that it runs the whole consumer chain
  W3–W8 in the kernel against a supply that exists today, so every seam is exercised before
  the `a ≥ 2` supply campaign is priced against them.  The only unconditional theorem wave
  2-W produces.  Nothing bears on twin primes.
-/
import Salt.MR.V7RatedH
import Salt.Entropy.Chowla.AffineFork
import Mathlib

open ArithmeticFunction Finset
open Salt.Entropy.Chowla

namespace Salt.MR

/-- **S2 (class A/B).**  The `a = 1` instance of the supply demand is a corollary of the landed
prize `logChowla2_v7_rated_h` (`V7RatedH.lean:1067`) at every `h ≤ 1096`.  Its `∃ R`
conjunct (`:1075-1082`) carries SIX conjuncts — `R.eps = ε`, `R.Hlo = flatDesignBase A`, two
loglog band conditions, `3.2·A ≤ loglog R.Hlo`, and `¬ logChowlaFails h R.eps R.x R.ω` — so
the `obtain` keeps `162 ≤ A`, `A₀ ≤ A`, `R.Hlo = …` and the last conjunct and discards the
rest; the transfer is `mt (logChowlaFailsAff_one_zero h R.eps R.x R.ω).mp` (the `¬` reverses
the direction: `.mp`, not `.mpr`). -/
theorem logChowlaAffSupply_one_zero (h : ℕ) (hh : 0 < h) (hh7 : Real.log (h : ℝ) ≤ 7) :
    LogChowlaAffSupply 1 0 h := by
  intro A₀
  obtain ⟨-, -, -, -, -, A, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hA162, hAA₀, R, -, hHlo, -, -, -, hnf⟩ :=
    Salt.MR.logChowla2_v7_rated_h h hh hh7 A₀
  exact ⟨A, hA162, hAA₀, R, hHlo, mt (logChowlaFailsAff_one_zero h R.eps R.x R.ω).mp hnf⟩

/-- **W9 — THE `a = 1` INTEGRATION CONTROL (class A).**  `zRough_oddOmega_infinite_of_affSupply`
at `P = 1` (`Nat.one_pos`), `r = 0` (`Nat.coprime_one_right`), with
`logChowlaAffSupply_one_zero 2 (by norm_num) (by … Real.log_two_lt_d9 …)`, then
`Set.Infinite.mono` dropping the (trivial) coprime conjunct. -/
theorem oddOmega_twinProd_infinite :
    {n : ℕ | Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  have h2 : Real.log ((2 : ℕ) : ℝ) ≤ 7 := by
    have hlt := Real.log_two_lt_d9
    have hc : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
    rw [hc]
    linarith
  have hinf := zRough_oddOmega_infinite_of_affSupply (P := 1) (r := 0) Nat.one_pos
    (Nat.coprime_one_right _) (logChowlaAffSupply_one_zero 2 (by norm_num) h2)
  exact hinf.mono (fun n hn => hn.2)

end Salt.MR
