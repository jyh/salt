/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MRTPortA1Tail
import Salt.MR.MRTPortMLower

/-!
# The MRT port (item 15) — A.1's whole right-hand side below a fixed constant (node E5)

Dispatched from the frozen executor brief
`seat/briefs/2026-08-25-item15-WAVE-B-ARC-OUT-OF-SCOPE-FROZEN.md`, node **E5**.  The
single statement below is the door-wave gate's own, copied verbatim from that brief; it is
not the maestro's or this executor's paraphrase.

## What this composes

Four landed pieces, no analysis of its own:

| input | site | role |
|---|---|---|
| `mrtThmA1_at_lamCoeff` (D4) | `MRTPortA1.lean:91` | A.1 instantiated at `lamCoeff` |
| `mul_exp_neg_le_two_div` (D5) | `MRTPortA1Tail.lean:35` | `exp(−M)·M ≤ 2/M`, needs `0 < M` |
| `mrtA1_rhs_tail_le` (D6) | `MRTPortA1Tail.lean:43` | the other two summands below any `δ > 0` |
| `mrtM_lamCoeff_ge` (E3) | `MRTPortMLower.lean:190` | `M(λ; X)` eventually above any constant |

E3 is what makes D5 usable at all: D5's `0 < M` binder — and the quantitative floor
`4C/c ≤ M` that turns `2/M` into `c/(2C)` — is exactly what E3 supplies.  Before E3, D5
was inert.  Each of the three A.1 summands is driven below `c/(2C)`, `c/(2C)` and
(jointly with the middle term) `c/(2C)`; the sum is `≤ c/C`, and `C · (c/C) = c`.

⚠️ The middle right-hand term is `(log log h)^2 / (log h)^2` — **squared** denominator.
`MRTThmA1`'s transcription was repaired to the source's form (`1503.05121v3` p.20) at
commit `46b7a5a9`; D6's statement already carries the corrected byte, so the two match
with no repair.  Nothing in this file assumes the older unsquared form.

## ⛔ SCOPE — stated so no landing can be inflated

* This is an **implication from** `MRTThmA1 C`.  `MRTThmA1` is a `def … : Prop` with **no
  producer** in the corpus (`MRTPortA1.lean:38` says so in its own header) — **GAP A.1 is
  open and class D**.  Nothing here asserts A.1 holds, and this file does not produce A.1.
* **GAP α (the major arc) is untouched.**  The conclusion is the *unphased* mean square
  `(1/X)∫‖mrtShortMean lamCoeff h x‖²`; the door's datum is phased
  (`doorCoeffPhase lamCoeff α`).  This is **not** node E4's input: the bridge to it needs
  the window-convention mirror, the seam cap, and the phase, none of which is in this wave.
  E5 and E4 are the two *ends* of the port stated in one currency, not a chain.
* **GAP X (the output-side scale quantifier) is untouched** — see the council register's
  Amendment 2 (`seat/briefs/2026-08-25-COUNCIL-decision-register.md`).
* No new unconditional analytic bound is produced here.  What this file adds is the
  *currency*: whatever A.1 supplies, it supplies it below any fixed constant `c`.

**Not rooted.**  This module is imported by nothing; build it targeted
(`../saltbuild.sh Salt.MR.MRTPortA1Const`).  Rooting it in an aggregate is maestro-tier.
-/

namespace Salt.MR

/-- **E5 — A.1's whole right-hand side below a fixed constant.**

Given MRT Theorem A.1 at constant `C` and any target `c > 0`, the A.1 mean square at the
Liouville coefficient sequence sits below `c` past explicit floors in both `h` and `X`.

Route: D4 bounds the left-hand side by `C · (exp(−M)·M + (loglog h)²/(log h)² +
(log X)^(−1/50))` with `M := mrtM lamCoeff X`.  E3 at `B := 4C/c` gives `0 < M` and
`4C/c ≤ M`, so D5 gives `exp(−M)·M ≤ 2/M ≤ c/(2C)`; D6 at `δ := c/(2C)` gives the other
two summands.  Sum `≤ c/C`, times `C` is `c`. -/
theorem mrtA1_lamCoeff_le_const {C c : ℝ} (hC : 0 < C) (hA1 : MRTThmA1 C) (hc : 0 < c) :
    ∃ h₀ X₀ : ℝ, 0 < h₀ ∧ 0 < X₀ ∧ ∀ h X : ℝ, h₀ ≤ h → X₀ ≤ X → h ≤ X →
      (1 / X) * (∫ x in X..(2 * X), ‖mrtShortMean lamCoeff h x‖ ^ 2) ≤ c := by
  have h2C : (0 : ℝ) < 2 * C := by linarith
  -- D6 at `δ := c / (2C)`: the middle and last A.1 summands.
  obtain ⟨h₁, hh₁pos, htail⟩ := mrtA1_rhs_tail_le (δ := c / (2 * C)) (div_pos hc h2C)
  -- E3 at `B := log(2C/c)`: the quality floor that makes `exp(−M)` itself small.
  -- ⛔ 2026-08-25: the old route went through D5 (`exp(−M)·M ≤ 2/M`) at `B := 4C/c`.
  -- That step consumed the `· M` factor which A.1 no longer carries — the source's
  -- remark form is `exp(−M)` alone (see `MRTThmA1.lean`'s erratum: the `· M` form is
  -- FALSE for every `C`, by `f ≡ 1` at `M = 0`).  E3 holds for ANY `B`, so the floor
  -- can be placed where it kills `exp(−M)` directly, and the route gets shorter.
  obtain ⟨X₁, hX₁pos, hM⟩ := mrtM_lamCoeff_ge (Real.log (2 * C / c))
  refine ⟨max h₁ 10, X₁, lt_of_lt_of_le hh₁pos (le_max_left _ _), hX₁pos, ?_⟩
  intro h X hh hX hhX
  have hh10 : (10 : ℝ) ≤ h := le_trans (le_max_right _ _) hh
  have hh1 : h₁ ≤ h := le_trans (le_max_left _ _) hh
  -- FIRST SUMMAND: `exp(−M) ≤ exp(−log(2C/c)) = c/(2C)`.
  have hMge : Real.log (2 * C / c) ≤ mrtM lamCoeff X := hM X hX
  have hratio : (0 : ℝ) < 2 * C / c := div_pos h2C hc
  have hfirst : Real.exp (-(mrtM lamCoeff X)) ≤ c / (2 * C) := by
    have hstep : Real.exp (-(mrtM lamCoeff X)) ≤ Real.exp (-(Real.log (2 * C / c))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log (2 * C / c))) = c / (2 * C) := by
      rw [Real.exp_neg, Real.exp_log hratio]
      field_simp
    linarith [hstep, hval.le, hval.ge]
  -- THE OTHER TWO SUMMANDS, jointly, from D6.
  have hrest : Real.log (Real.log h) ^ 2 / Real.log h ^ 2
      + 1 / Real.log X ^ ((1 : ℝ) / 50) ≤ c / (2 * C) := htail h X hh1 hhX
  -- D4: A.1 at `lamCoeff`.
  have hA := mrtThmA1_at_lamCoeff hA1 hh10 hhX
  -- Sum the three, multiply by `C`.
  have hsum : Real.exp (-(mrtM lamCoeff X))
      + Real.log (Real.log h) ^ 2 / Real.log h ^ 2
      + 1 / Real.log X ^ ((1 : ℝ) / 50) ≤ c / C := by
    have htwo : c / (2 * C) + c / (2 * C) = c / C := by field_simp; ring
    linarith
  have hscale : C * (Real.exp (-(mrtM lamCoeff X))
      + Real.log (Real.log h) ^ 2 / Real.log h ^ 2
      + 1 / Real.log X ^ ((1 : ℝ) / 50)) ≤ C * (c / C) :=
    mul_le_mul_of_nonneg_left hsum hC.le
  have hCc : C * (c / C) = c := by field_simp
  linarith

end Salt.MR
