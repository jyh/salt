/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.TierSBandU
import Salt.MR.StridePairReceiptG12b
import Salt.Entropy.Chowla.StrideShellBand
import Salt.TwinBar.TwinParityAtomClasses
import Mathlib

/-!
# ⟦TIER S — S-4⟧ THE BRIDGE: S-3's BAND THROUGH THE ARROW (`TierSBridge`)

**S-4 (desk NE) — FROZEN STATEMENT-ONLY.  HONEST LABEL, FIRST LINE: NO NEW UNCONDITIONAL
THEOREM.**  The one place both sides of Tier S are in scope: S-3's class-uniform crown band
(`mrtUniformityXiL2AffW_holds_flat_stride_g12b_band_bU`, `TierSBandU.lean`, PROVED on `main`) is
fed through S-4's arrow at every regime (`log_chowla_aff_of_door_at_regime_g12b`,
`StrideShellBand.lean`, FROZEN) with the grade composed at each band regime
(`affGrade_composes_g12b`, FROZEN), and the result is the sentence D12's `hwin` needs: for every
class `b < a` with `gcd (b + h) a ∣ h` and every `y` in ONE band `[x₀, exp(31·Hhi₀/ε)/a]`,
log-Chowla does not fail at `(a, b, h, ε, y, ω₀)`.  The control K2 (PROVED) then reads that
sentence into D12 (`abs_sum_Icc_le_of_windows`, `TwinParityAtomClasses.lean:678`) and out as
`AffFullRangeAt` at every
`N` in the band — the demand object D5 — so the bridge's shape is D12's demand as a kernel fact and
not as prose.  The binder `a ≤ 2310` is the composition's (the Captain's granted binder, council
2026-09-13 A② clause 2), inherited and not added here.  Nothing here bears on twin primes.

What this does NOT buy: D10 wants ONE `(ε, A)` over an INFINITE set of scales; one band is a finite
interval and its D12 constant `ε·log ω₀ + log x₀ + 1` is the band's.  The `(2ε, 1)`-normalisation
inside a band (S-3 freeze §5) and the ladder of bands over `A₀ → ∞` are the next link, named in the
freeze and not stated here.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory
open Salt.Entropy.Chowla
open Salt.TwinBar

namespace Salt.MR

/-! ## §0 — the conservativity control K1, crowned (PROVED; reads no `sorry`) -/

/-- **⟦S-4 K1′⟧ (class A, PROVED) — K1 WITH THE LANDED CROWN IN THE BINDER.**
`gradedAffHeadAt_g12b_of_at_regime` (`StrideShellBand.lean`) at
`hcrown := fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g12b a b h … A₀'`
(`StridePairReceiptG12b.lean:1140`, the landed crown): the `∀ Ra` arrow, as a hypothesis,
recovers the landed graded head at every class and every `A₀` with nothing else assumed.  The
landed consumers of `GradedAffHeadAt_g12b` can therefore be served through S-4. -/
theorem gradedAffHeadAt_g12b_of_at_regime_crowned (a b h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hba : b < a) (hgcd : Nat.gcd (b + h) a ∣ h) (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9)
    (hS4 : ∃ A₁ : ℝ, 162 ≤ A₁ ∧
      ∀ b : ℕ, b < a → Nat.gcd (b + h) a ∣ h →
      ∀ Ra : ChowlaRegimeAff, Ra.a = a → Ra.b = b →
        Ra.eps = 1 / (500 * ((a * h : ℕ) : ℚ)) → flatDesignBase A₁ ≤ Ra.Hlo →
        ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / (838400 * ((a * h : ℕ) : ℝ) ^ 2) →
          MRTUniformityXiL2AffW h Ra ρ' → ¬ logChowlaFailsAff a b h Ra.eps Ra.x Ra.ω)
    (A₀ : ℝ) : GradedAffHeadAt_g12b a b h A₀ :=
  gradedAffHeadAt_g12b_of_at_regime a b h ha hh hba hgcd hS4
    (fun A₀' => mrtUniformityXiL2AffW_holds_flat_stride_g12b a b h ha hh hba hah9 A₀') A₀

/-! ## §1 — THE BRIDGE: every class, every scale in one band, no failure -/

/-- **⟦S-4 B⟧ (class A, THE BRIDGE) — S-3's BAND THROUGH THE ARROW.**  S-3's statement
(`TierSBandU.lean` §2) with the per-regime door package replaced by its consequence under S-4 and
the composition: `∃ ε A`, the band `∃ x₀ ω₀ Hhi₀` with its three ceilings, then `∀ b < a` (now
carrying the entropy side's `hgcd`) and `∀ y` in the band, `¬ logChowlaFailsAff a b h ε y ω₀`.  The
`A₀ ≤ A` export is kept so the ladder over `A₀ → ∞` (S-3 freeze §5.4) can be climbed.

Route (not fired): `obtain ⟨A₁, _, harrow⟩ := log_chowla_aff_of_door_at_regime_g12b a h ha hh hah9`;
S-3 at `max A₀ A₁`; the band witnesses and ceilings forwarded; `intro b hba hgcd y hy hlogy`; S-3's
regime `Ra` with `Ra.eps = ε`, `Ra.x = y`, `Ra.ω = ω₀`, `flatDesignBase A ≤ Ra.Hlo` and the door at
`a·Zr·ρ + E`; `affGrade_composes_g12b` gives `0 < a·Zr·ρ + E ≤ floor`; `harrow b hba hgcd Ra …` at
`flatDesignBase_mono (A₁ ≤ A)`; `rwa [hReps, hRx, hRω] at hnf`. -/
theorem band_not_logChowlaFailsAff_g12b (a h : ℕ) (ha : 0 < a) (hh : 0 < h)
    (hah9 : Real.log ((a * h : ℕ) : ℝ) ≤ 9) (ha2310 : a ≤ 2310) (A₀ : ℝ) :
    ∃ (ε : ℚ) (A : ℝ), 0 < ε ∧ 1 / (500 * ((a * h : ℕ) : ℚ)) ≤ ε ∧
      ε = 1 / (500 * ((a * h : ℕ) : ℚ)) ∧ 162 ≤ A ∧ A₀ ≤ A ∧
      ∃ (x₀ ω₀ Hhi₀ : ℕ), 2 ≤ x₀ ∧ 8 ≤ ω₀ ∧ 4000000 ≤ Hhi₀ ∧
        Real.log ((ω₀ : ℕ) : ℝ) ≤ xTightCeil ε Hhi₀ ∧
        Real.log ((x₀ : ℕ) : ℝ) ≤ xTightCeilArm ε Hhi₀ ∧
        Real.log ((a * x₀ : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) ∧
        ∀ b : ℕ, b < a → Nat.gcd (b + h) a ∣ h →
        ∀ y : ℕ, x₀ ≤ y → Real.log ((a * y : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) →
          ¬ logChowlaFailsAff a b h ε y ω₀ := by
  sorry

/-! ## §2 — the demand-fit control K2 (PROVED; reads no `sorry`) -/

/-- **⟦S-4 K2⟧ (class A/B, PROVED) — THE BRIDGE'S SENTENCE IS D12's `hwin`, AND D12 RETURNS THE
DEMAND OBJECT.**  From the bridge's per-class conclusion (as a hypothesis, statement spelled out)
at one class `b`, D12 `abs_sum_Icc_le_of_windows` (`TwinParityAtomClasses.lean:678`) with
`f n := λ(a·n+b)·λ(a·n+b+h)` (`|f| ≤ 1` by `abs_liouville_le_one` twice), width `ω₀ ≥ 2`, bottom
`x₀ ≥ 1`, gives at every `N ∈ [x₀, roof]` the full-range bound `AffFullRangeAt a b h ε (ε·log ω₀ +
log x₀ + 1) N` (`TwinParityAtomClasses.lean:494`, the demand D5) — `N ≥ x₀` is not needed: below
`x₀` the window range is empty and D12's tail bound stands alone.  The window bound at `x ≤ N` is
`¬ logChowlaFailsAff` read through `not_lt`; `x` is in the band because `log (a·x) ≤ log (a·N)`.
Stated with the hypothesis spelled out, so its axiom audit is the kernel's three. -/
theorem affFullRangeAt_band_of_not_fails (a b h : ℕ) (ha : 0 < a) (ε : ℚ) (hε : 0 < ε)
    (x₀ ω₀ Hhi₀ : ℕ) (hx₀ : 2 ≤ x₀) (hω₀ : 8 ≤ ω₀)
    (hwin : ∀ y : ℕ, x₀ ≤ y → Real.log ((a * y : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) →
      ¬ logChowlaFailsAff a b h ε y ω₀)
    (N : ℕ) (hNroof : Real.log ((a * N : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ)) :
    AffFullRangeAt a b h (ε : ℝ) ((ε : ℝ) * Real.log (ω₀ : ℝ) + Real.log (x₀ : ℝ) + 1) N := by
  unfold AffFullRangeAt
  have hε' : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε.le
  have hf : ∀ n : ℕ, |(ArithmeticFunction.liouville (a * n + b) : ℝ)
      * (ArithmeticFunction.liouville (a * n + b + h) : ℝ)| ≤ 1 := by
    intro n
    rw [abs_mul]
    exact mul_le_one₀ (abs_liouville_le_one _) (abs_nonneg _) (abs_liouville_le_one _)
  have hwin' : ∀ x : ℕ, x₀ ≤ x → x ≤ N →
      |∑ n ∈ Finset.Ioc (x / ω₀) x, (ArithmeticFunction.liouville (a * n + b) : ℝ)
        * (ArithmeticFunction.liouville (a * n + b + h) : ℝ) / (n : ℝ)|
        ≤ (ε : ℝ) * Real.log (ω₀ : ℝ) := by
    intro x hx₀x hxN
    have hxpos : 0 < a * x := Nat.mul_pos ha (by omega)
    have hlogx : Real.log ((a * x : ℕ) : ℝ) ≤ 31 / (ε : ℝ) * ((Hhi₀ : ℕ) : ℝ) := by
      refine le_trans (Real.log_le_log (by exact_mod_cast hxpos) ?_) hNroof
      exact_mod_cast Nat.mul_le_mul_left a hxN
    have hnf := hwin x hx₀x hlogx
    unfold logChowlaFailsAff at hnf
    exact not_lt.mp hnf
  exact abs_sum_Icc_le_of_windows
    (f := fun n => (ArithmeticFunction.liouville (a * n + b) : ℝ)
      * (ArithmeticFunction.liouville (a * n + b + h) : ℝ))
    hf (by omega) (by omega) hε' N hwin'

end Salt.MR

end
