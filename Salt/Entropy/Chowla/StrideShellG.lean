/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# λ-BV wave 2-S, step F5 (β) — THE AFFINE HEAD AT THE GRADED CROWN (the Entropy side of the
# graded sibling lane)

`Salt.Entropy` cannot import `Salt.MR` (the `xceil` fence), so the affine head
`log_chowla_aff_of_door` (`StrideShell.lean:433`) takes the crown's PAYLOAD as a binder `hcrown`
whose shape is the crown's conclusion verbatim, and its own conclusion FORWARDS that payload
beside the entropy half.  The graded crown (`Salt/MR/StridePairReceiptG.lean`,
`mrtUniformityXiL2AffW_holds_flat_stride_g`) hands the door out at `ρ ≤ 1/(837782·2^11·(ah)²)`;
under an `∃` the door and the entropy half compose only through the SAME witness `Ra`, so the
finer grade must enter the head through its binder and leave through its conclusion — this file
is the landed head with `837782 ↦ 837782 · 2^11` in EXACTLY those two places (the `hcrown` binder
and the conclusion; the entropy half's own pin `1/(838400·(ah)²) ≤ δ₀_aff` is the HEAD's demand
and does not move).  The head's proof never reads the ceiling: the crown's `hρle` is obtained
(`StrideShell.lean:501`, the `obtain … hρle …` from `hcrown A₀'`) and re-packaged untouched
(`:581`, the `refine` package) — `grep -n 837782` on the landed file hits :452 and :461 only —
so the body is the landed body VERBATIM.  Its conclusion is `GradedAffHeadAt a b h A₀`
(`StridePrize.lean:166`) byte for byte — the MR one-liner
`StrideGradeReceipt.log_chowla_aff_of_door_crowned_unslotted_g` checks that identity in the kernel
by `unfold GradedAffHeadAt; exact …`.

HONEST LABEL.  Two declarations; nothing new is proved about the entropy half, which is the
landed one.  Statement-only at the freeze (the head's body is a verbatim copy for the executor;
the unslotted twin is its landed one-liner at the graded name).  Nothing here bears on twin primes.
-/
import Salt.Entropy.Chowla.StrideShell
import Salt.Entropy.Chowla.StrideCircle
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ## F5-β-S3 — THE AFFINE HEAD AT THE GRADED CROWN -/

set_option maxHeartbeats 1600000 in
-- THE HEAD is one large elaboration (the crown's payload, the five-wide reduce leaf and the circle
-- slot all in context while the pin's numerals and the budget witness are discharged); the ceiling
-- is the landed head's own (`StrideShell.lean:397`, 1600000) — the body is that head's, verbatim.
/-- **F5-β-S3 (class C by size, mechanically A — a verbatim copy) — `log_chowla_aff_of_door_g`.**
`log_chowla_aff_of_door` (`StrideShell.lean:433-468`, salt `c80481a1`) with `837782 * ((a * h : ℕ) :
ℝ) ^ 2 ↦ 837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2` at source lines 452 (the `hcrown` binder) and
461 (the conclusion).  BODY: `StrideShell.lean:469-649` VERBATIM — `hρle` is obtained from
`hcrown A₀'` (`:501`, the `obtain`) and re-packaged in the `refine` (`:581`); no other line
mentions `ρ`'s ceiling; the `maxHeartbeats 1600000` is the landed head's. -/
theorem log_chowla_aff_of_door_g (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (_hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcm : ∃ C : ℝ, 0 < C ∧ C ≤ (h : ℝ) * (1 + 2 * (2 * Real.log 4)) ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      a ∣ H →
      ((primeWindow eps H).card : ℝ)
          ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          if ((j + 1 : ℕ) : ZMod a) = (((p : ℕ) * b : ℕ) : ZMod a) then
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ) * h) : ℝ) else 0|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXiAff a b h eps H, (1 / (H : ℝ) ^ 2)
                * ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2))
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  sorry

/-! ## F5-β-N11 — THE DISCHARGE: the graded head without its slot -/

/-- **F5-β-N11 (class A) — the graded affine head UNSLOTTED.**  `log_chowla_aff_of_door_unslotted`
(`StrideCircle.lean:1090-1114`) with the ceiling at `837782 * 2 ^ 11` in `hcrown` and the conclusion
(source lines 1098, 1107); the body is the landed one-liner at the graded head, LANDED AT THE
FREEZE as the shape control of the substitution (it elaborates iff the graded head's binder and
conclusion are the graded crown's and `GradedAffHeadAt`'s text). -/
theorem log_chowla_aff_of_door_unslotted_g (a b h : ℕ) (ha : 0 < a) (hh : 0 < h) (hba : b < a)
    (hgcd : Nat.gcd (b + h) a ∣ h)
    (hah7 : Real.log ((a * h : ℕ) : ℝ) ≤ 7)
    (hcrown : ∀ A₀' : ℝ,
      ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
        ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀' ≤ A ∧
        ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
          flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
          ∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
            1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
            E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
                * (Real.log (Ra.ω : ℝ) - 1)) ∧
            MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E))
    (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ Ra : ChowlaRegimeAff, Ra.a = a ∧ Ra.b = b ∧ Ra.eps = ε ∧
        flatDesignBase A ≤ Ra.Hlo ∧ 3.2 * A ≤ Real.log (Real.log (Ra.Hlo : ℝ)) ∧
        (∃ (ρ Zr E : ℝ), 0 < ρ ∧ ρ ≤ 1 / (837782 * 2 ^ 11 * ((a * h : ℕ) : ℝ) ^ 2) ∧
          1 ≤ Zr ∧ Zr ≤ 1.02 ∧ 0 ≤ E ∧
          E ≤ 2 ^ 539 * (a : ℝ) / (((a : ℝ) * ((Ra.x / Ra.ω : ℕ) : ℝ) + 1)
              * (Real.log (Ra.ω : ℝ) - 1)) ∧
          MRTUniformityXiL2AffW h Ra ((a : ℝ) * Zr * ρ + E)) ∧
        ∃ δ₀ : ℝ, 0 < δ₀ ∧ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) ≤ δ₀ ∧
          ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ δ₀ → MRTUniformityXiL2AffW h Ra ρ' →
            ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω := by
  exact log_chowla_aff_of_door_g a b h ha hh hba hah7
    (circle_method_estimate_sq_bounded_aff a b h ha hh hgcd (2 * Real.log 4) (by positivity))
    hcrown A₀

end Salt.Entropy.Chowla
