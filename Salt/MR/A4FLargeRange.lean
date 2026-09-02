/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
import Mathlib
import Salt.MR.A4FThreshold

/-!
# A4F AU — the large-range reduction (D★): A.4(ii) whole at θ = 3/4, in the source's order

The frozen large-range Prop `MRTLargeRangeEquidistributionFixed` (MRTPropA3.lean) claims a
constant `C` UNIFORM down to the bare floor `(log X)^{2/3} ≤ log Y`.  Its ONE consumer,
`mrtLemmaA4iiFixed34T_of_largeRangeFixed` (A4FThreshold.lean), reads it only at
`Y = exp((log X)^{3/4+ε'})` — and at that `Y` the landed mid-range mechanism carries with no
height cap at all: `harmonic_prime_sum_abs_le_vk` and its supplier `zeta_near_logDeriv_bound`
bound every harmonic `|m·u|` above the VK threshold `T₀`, whatever its size, under the window
hypothesis `1/log Y ≤ cR/D(t)`, `D(t) = (log|t|)^{3/4}(loglog|t|)^4`.  The large range changes
ONE number: the harmonic height is `|m·u| ≤ 2·Mcut·X` (so `log|m·u| ≤ 2·log X`) instead of
`Mcut·(log X)^{20}`; the window hypothesis then reads `400·D/cR ≤ log Y` with
`D ≤ 32·(log X)^{3/4}·(loglog X)^4`, met by the floor `(log X)^{3/4}·(loglog X)^5 ≤ log Y`
once `loglog X ≥ 12800/cR`.

**What lands here (the freeze `2026-09-02-math-AU-Dstar-FREEZE.md`, refuter-passed):**

* `mrt_large_range_parametric` — the port of `mrt_mid_range_parametric` (A4FMidRange.lean)
  regime by regime: the height ceiling `|u| ≤ (log X)^{20}` becomes the range
  `(log X)^{20} < |u| ≤ 2X`; the floor becomes `(log X)^{3/4}·(loglog X)^5 ≤ log Y`; the
  bounded-height regime is EMPTY (every harmonic sits above `T₀` once `loglog X ≥ log T₀`),
  so the `|u| ≥ 2` detour and `harmonic_prime_sum_abs_le_bounded_height` are not needed;
  ONE new stone — rpow monotonicity at exponent `3/4` against a floor at the SAME exponent
  (the mid range's crude `(log t)^{3/4} ≤ (log t)^1` would lose the `(log X)^{1/4}` this
  floor cannot pay).  Uniform `C`; `e ≤ Y` carried (mathlib's `log` is even; and the floor
  vanishes at `X = e`, admitting `Y → 1⁺` where the demand is unbounded — the statement
  WITHOUT `e ≤ Y` is refutable at `X = e, Y = e^δ, u = 2`).
* `MRTLargeRangeEquidistributionFixedEps` (D1) — the large-range Prop in the SOURCE'S
  quantifier order `∀ε ∃C`, floor `(log X)^{3/4+ε}`, `e ≤ Y` carried; produced by
  `mrtLargeRangeEquidistributionFixedEps_holds` from the theorem above through the
  `(x/7)^7 ≤ e^x` stone (threshold `(loglog X)^2 ≥ (7/ε)^7`, `pow` arithmetic only).
* `MRTLemmaA4iiFixed34E` (D2) — `MRTLemmaA4iiFixed34T` with `∀ε` BEFORE `∃C₀`; produced
  UNCONDITIONALLY by `mrtLemmaA4iiFixed34E_holds` — **A.4(ii) whole at θ = 3/4**, high-M +
  mid + large arms all closed, in the source's own order ("for any ε > 0", arXiv:1503.05121
  p.22, the `O(1)` absorbed for `X` large in `ε`).
* The pins `largeRangeFixedEps_of_fixed` and `lemmaA4iiFixed34E_of_fixed34T`: the frozen
  strong forms IMPLY the new ones (never the reverse), so nothing downstream of D1/D2 is
  stronger than what the frozen targets would have given.

**What does NOT land, on purpose (flags record, the S2(iii) shape):** the frozen
`MRTLargeRangeEquidistributionFixed` and the T-form's large arm demand a uniform `C` at a
BARE exponent; every ζ'/ζ route needs `log Y ≥ K·(log t)^θ·(loglog t)^a` with `a > 0`, and
the T-form's own threshold admits `ε ≈ C₀/loglog X`, i.e. `log Y = (log X)^{3/4}·e^{O(1)}`,
where the deficit is `≥ (1−2/π)·4·logloglog X − O(1)` against an allowance `C₀/2`.  NOT
refuted (under RH both hold); STATEMENT-BLOCKED.  The source never claims the uniformity.
The bytes of both frozen statements are untouched; the honest family lands beside them.

Nothing here bears on twin primes: A.4(ii) is one floor inside the E-ladder's A.3 engine.
-/

namespace Salt.MR

/-! ## D1 and D2 — the statements in the source's quantifier order -/

/-- **D1 — the large-range Prop in the source's order.**  For every `ε > 0` a constant
`C = C(ε)` with, for `e ≤ X`, `e ≤ Y`, `(log X)^{20} < |u| ≤ 2X` and the floor
`(log X)^{3/4+ε} ≤ log Y`, `(1 − 2/π)·log(log X/log Y) − C ≤ Σ_{Y<p≤X}(1 − |cos(u·log p/2)|)/p`.
Weaker than the frozen `MRTLargeRangeEquidistributionFixed` in exactly two ways (the floor
exponent `3/4 + ε` vs the bare `2/3`, and `∀ε ∃C` vs `∃C ∀`), see `largeRangeFixedEps_of_fixed`;
`e ≤ Y` is carried because mathlib's `log` is even.  The floor exponent is the landed region's
θ = 3/4 (A.4(ii)'s (A.5) is written at `2/3 + ε` in the source; a `2/3` region moves this one
numeral through the same port).  Statement act: the freeze §4, Fable-tier. -/
def MRTLargeRangeEquidistributionFixedEps : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Y u : ℝ), Real.exp 1 ≤ X → Real.exp 1 ≤ Y →
    |u| ≤ 2 * X → (Real.log X) ^ (20 : ℕ) < |u| →
    (Real.log X) ^ ((3 : ℝ) / 4 + ε) ≤ Real.log Y →
      (1 - 2 / Real.pi) * Real.log (Real.log X / Real.log Y) - C
        ≤ ∑ p ∈ ((Finset.range (⌊X⌋₊ + 1)).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)),
            (1 - |Real.cos (u * Real.log p / 2)|) / (p : ℝ)

/-- **D2 — the threshold producer with `∀ε` BEFORE `∃C₀`.**  `MRTLemmaA4iiFixed34T`'s binders
and hypotheses byte-for-byte, with the `ε` binder and its `0 < ε` moved out in front of the
existential: `C₀ = C₀(ε)`, the source's `≪_ε`.  The threshold `C₀/ε ≤ loglog X` is kept (it is
`X ≥ X₀(ε)` in the corpus's idiom and composes with `far34_threshold_close` unchanged).
Statement act: the freeze §4, Fable-tier. -/
def MRTLemmaA4iiFixed34E : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (f : ℕ → ℂ) (Pseq Qseq : ℕ → ℕ) (𝒥 : Finset ℕ) (X t t₁ : ℝ),
    (∀ n, ‖f n‖ ≤ 1) → Real.exp 1 ≤ X → |t| ≤ X →
    |t₁| ≤ X → pretDistSq f (costwist t₁) X = mrtM f X →
    ((1 / 8) * Real.log (Real.log X) ≤ mrtM f X
      ∨ (Real.log X) ^ ((1 : ℝ) / 16) / 2 < |t - t₁|) →
    C₀ / ε ≤ Real.log (Real.log X) →
      (1 / 8 - 1 / (4 * Real.pi) - ε) * Real.log (Real.log X)
        ≤ pretDistSq (fun n => f n * gJ 𝒥 Pseq Qseq n) (costwist t) X

/-! ## The pins: the frozen strong forms imply the new ones -/

/-- **Pin.**  The frozen uniform-`C` Prop at the bare floor `2/3` implies D1: instantiate its
`C` for every `ε` and discharge the bare floor from the higher one by rpow monotonicity.
The reverse is NOT derivable (D1 has no uniformity clause, and no `ε > 0` makes
`3/4 + ε ≤ 2/3`). -/
theorem largeRangeFixedEps_of_fixed (hFix : MRTLargeRangeEquidistributionFixed) :
    MRTLargeRangeEquidistributionFixedEps := by
  intro ε hε
  obtain ⟨C, hC, h⟩ := hFix
  refine ⟨C, hC, ?_⟩
  intro X Y u hXe _heY hu2X hulo hfl
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  exact h X Y u hXe hu2X hulo
    (le_trans (Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)) hfl)

/-- **Pin.**  The uniform-`C₀` T-form implies the E-form: pure instantiation, the
`ε`-independent `C₀` reused.  The reverse would need `sup_ε C₀(ε) < ∞`, which the E-form
does not assert. -/
theorem lemmaA4iiFixed34E_of_fixed34T (hT : MRTLemmaA4iiFixed34T) : MRTLemmaA4iiFixed34E := by
  intro ε hε
  obtain ⟨C₀, h0, h⟩ := hT
  exact ⟨C₀, h0, fun f Pseq Qseq 𝒥 X t t₁ hf hXe htX ht₁X hmin harm hthr =>
    h f Pseq Qseq 𝒥 X t t₁ ε hf hXe htX hε ht₁X hmin harm hthr⟩

end Salt.MR
