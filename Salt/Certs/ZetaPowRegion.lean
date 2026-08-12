/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.GrowthPow

/-!
# COMPREHENSIBILITY CERTIFICATE — the power-saving zero-free region (θ = 3/4)

Campaign: `saltworks/docs/cert-layer-design-0811.md` (the fifth deliverable).
Landed theorem certified: `Salt.Vk.zeta_zero_free_region_pow`
(`Salt/Vk/GrowthPow.lean:1044`). Paper: Theorem `thm:pow`.

## WHAT THE THEOREM SAYS, in one sentence
**There is a region hugging the line `Re s = 1` that contains no zero of `ζ`** — and it
is wider than the classical one, by a *power* of `log|t|` rather than a logarithm.

## THE READABLE FORM (what this certificate adds)
The landed statement is phrased as a bound **on every zero**: *if `ζ ρ = 0` and
`|Im ρ|` is large, then `Re ρ ≤ 1 − c/(…)`.* This certificate states the
**contrapositive**, which is what the phrase *"zero-free region"* actually means:

  **if `Re ρ` is ABOVE that curve and `|Im ρ| ≥ T₀`, then `ζ ρ ≠ 0`.**

Same content, but the reader sees a *region without zeros* rather than an inequality
satisfied by zeros.

## THE SHAPE OF THE CURVE
`Re s > 1 − c / ( (log|t|)^{3/4} · (log log|t|)^3 )`, `|t| = |Im s|`.
* The exponent **`3/4` is the power saving** — a Vinogradov–Korobov-type region. The
  classical (de la Vallée Poussin) region has `1 − c/log|t|`; this one is wider.
* The secondary factor `(log log|t|)^3` is Pi's `(log log|t|)^{−O(1)}` **pinned
  at exponent 3** (Appendix A records this; the `O(1)` is not left open in Lean).

## ⭐ THE CONSTANTS ARE EFFECTIVE — and the statement alone does not show it
The landed statement begins `∃ c T₀ : ℝ`, which on its face says only that *some*
constants exist. **Pi calls them "effective", and that is correct**: the proof
constructs them, and the chain bottoms out in explicit numbers.
```
zeta_growth_pow  supplies  K = 8104,  t₀ = exp (exp 100)     (GrowthPow.lean:978)
zeta_zero_free_region_pow_of_growth  then sets
                 A = 8 · log (20000 · K) + 1100              (PowRegion.lean:360)
                 and derives c, T₀ from A.
```
⇒ **an `∃` in the statement is not evidence of inexplicitness.** *Effectivity is a
property of the PROOF, not of the proposition, and here it is witnessed by numerals.*

## DIRECTION (rule 3)
`cert_zeta_zero_free_pow` is the **contrapositive** of the landed theorem — logically
equivalent, proved from it. **No generality is traded.**

## WHAT THIS CERTIFICATE DOES NOT CLAIM
* **Not a claim that `c` and `T₀` are small or optimal.** `t₀ = exp(exp 100)` is enormous;
  the theorem is qualitative in reach, effective in principle.
* **Not a priority claim.** Priority statements about this result live in the Pi flagship under
  the surveyed as-of form; this file asserts none.

## AXIOMS
`[propext, Classical.choice, Quot.sound]` — the standard three; verified at landing.
-/

namespace Salt.Certs

open Salt.Vk

/-- **THE CERTIFICATE — the zero-free region, stated as a region.**
There are constants `c > 0` and `T₀ ≥ 3` such that **no** `ρ` with `|Im ρ| ≥ T₀` lying
above the curve `1 − c/((log|Im ρ|)^{3/4} · (log log|Im ρ|)^3)` is a zero of `ζ`. -/
theorem cert_zeta_zero_free_pow :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, T₀ ≤ |ρ.im| →
      1 - c / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) < ρ.re →
      riemannZeta ρ ≠ 0 := by
  obtain ⟨c, T₀, hc, hT₀, hzero⟩ := zeta_zero_free_region_pow
  refine ⟨c, T₀, hc, hT₀, ?_⟩
  intro ρ hT hlt hz
  exact absurd (hzero ρ hz hT) (not_le.mpr hlt)

#print axioms cert_zeta_zero_free_pow

end Salt.Certs
