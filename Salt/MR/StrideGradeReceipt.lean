/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F5 (β) — THE GRADED CROWN FED INTO THE GRADED HEAD, THE SUPPLY, THE PRIZE

The one place both sides of the graded lane are in scope.
`log_chowla_aff_of_door_crowned_unslotted_g`
feeds the graded crown `mrtUniformityXiL2AffW_holds_flat_stride_g` (`StridePairReceiptG`) into the
graded, unslotted Entropy head `log_chowla_aff_of_door_unslotted_g` (`StrideShellG`) — the F4-S6 /
F4b-N11b one-liner at the graded names — and its conclusion IS `GradedAffHeadAt a b h A₀`
(`StridePrize.lean:166`): the binder F5-C (`log_chowla_aff_composed_of_headG`) composes at.  Then
`logChowlaAffSupplyW_holds` is F5-S at that discharge — the stride supply at `a ≥ 2` that
`AffineFork.lean:96` records as held by nobody — and `zRough_oddOmega_infinite_primorial` is the
prize, UNCONDITIONAL once the 27 land (statement-only at this freeze): for every `z` with
`primorial z ≤ 548` (`z ≤ 10`; `primorial 8 = primorial 9 = primorial 10 = 210` — the gate is on the
primorial, never on `z`) and every admissible class
`r < primorial z` with `gcd(r(r+2), primorial z) = 1`, infinitely many `n` with `n(n+2)` `z`-rough
and `Ω(n(n+2))` odd — Tao Thm 2.3's consequence at one class, NOT almost-primality.

HONEST LABEL.  Three one-line applications and one numeral (`log(2·primorial z) ≤ 7` from
`primorial z ≤ 548`, since `1096 ≤ e^7 = 1096.63`).  The prize when it lands is `z`-rough + odd
`Ω` at `z ≤ 10`; nothing on the apex; `z ≥ 11` rides on the unproved crown.  Two of the three
one-liners are LANDED AT THE FREEZE as the kernel's own check that the substituted shapes meet
(`unfold GradedAffHeadAt; exact …`); the prize is statement-only.  Nothing here bears on twin
primes.
-/
import Salt.Entropy.Chowla.StrideShellG
import Salt.Entropy.Chowla.StridePrize
import Salt.MR.StridePairReceiptG
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-- **F5-β-S6 (class A, LANDED AT THE FREEZE) — the graded crown fed into the graded unslotted head,
concluding `GradedAffHeadAt`.**  `log_chowla_aff_of_door_crowned_unslotted`
(`StrideEntropyReceipt.lean:74`) at the graded names: `unfold GradedAffHeadAt; exact
log_chowla_aff_of_door_unslotted_g a b h ha hh hba hgcd hah7 (fun A₀' =>
mrtUniformityXiL2AffW_holds_flat_stride_g a b h ha hh hba hah7 A₀') A₀`.  The `unfold` is the
K-check: `GradedAffHeadAt`'s body must be the graded head's conclusion byte for byte. -/
theorem log_chowla_aff_of_door_crowned_unslotted_g (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hgcd : Nat.gcd (b + h) a ∣ h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) (A₀ : ℝ) :
    GradedAffHeadAt a b h A₀ := by
  unfold GradedAffHeadAt
  exact log_chowla_aff_of_door_unslotted_g a b h ha hh hba hgcd hah7
    (fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g a b h ha hh hba hah7 A₀') A₀

/-- **F5-β-S (class A, LANDED AT THE FREEZE) — THE STRIDE SUPPLY AT `a ≥ 2`.**  F5-S
(`logChowlaAffSupplyW_of_headG`, `StridePrize.lean:280`) at the discharge above: for every
`(a, b, h)` with `b < a`, `0 < h`, `gcd(b+h, a) ∣ h`, `log(ah) ≤ 7`, `LogChowlaAffSupplyW a b h`. -/
theorem logChowlaAffSupplyW_holds (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hgcd : Nat.gcd (b + h) a ∣ h) (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7) :
    LogChowlaAffSupplyW a b h :=
  logChowlaAffSupplyW_of_headG a b h ha hh hah7
    (fun A₀ => log_chowla_aff_of_door_crowned_unslotted_g a b h ha hh hba hgcd hah7 A₀)

/-- **F5-β-P (class A) — THE UNCONDITIONAL PRIZE AT `primorial z ≤ 548`.**
`zRough_oddOmega_infinite_of_affSupplyW_primorial hcop (logChowlaAffSupplyW_holds (primorial z) r 2
(primorial_pos z) two_pos hr (gcd_dvd_two_of_coprime hcop) hah7)` with `hah7 : log ((primorial z *
2 : ℕ) : ℝ) ≤ 7` from `hz`: `primorial z * 2 ≤ 1096` and `(1096 : ℝ) ≤ exp 7` (`Real.exp_one_gt_d9`
raised to the 7th, `2.7182818283^7 ≥ 1096`, the move at `StridePairReceipt.lean:1425-1436`), then
`Real.log_le_log` + `Real.log_exp`.  ⚠ `548` is EXACT: `549·2 = 1098 > e^7 = 1096.63`.  The binder
`hr : r < primorial z` is the head's `hba` at `(P, r, 2)`; the set is `r`-free. -/
theorem zRough_oddOmega_infinite_primorial {z r : ℕ} (hz : primorial z ≤ 548)
    (hr : r < primorial z) (hcop : Nat.Coprime (r * (r + 2)) (primorial z)) :
    {n : ℕ | (∀ p ∈ (n * (n + 2)).primeFactors, z < p)
      ∧ Odd (ArithmeticFunction.cardFactors (n * (n + 2)))}.Infinite := by
  sorry

end Salt.MR
