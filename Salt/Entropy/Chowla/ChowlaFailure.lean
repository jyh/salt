/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The (2.4)→(2.11) producer chain, W3-F-EASY cluster (Tao arXiv:1509.05422v2 §2)

The A-grade nodes of the log-Chowla-2 *producer*: the failure hypothesis, its
normalization to a single-correlation lower bound on the `logMeasure`
expectation, the Liouville multiplicativity port, and the hypothesis-parametric
glue that composes into `outer_combine`'s `(c₁, h211)` pair.

* `logChowla2Fails eps x ω` — Tao (2.4) at the Liouville model `a=1,b=0,h=1,
  g₁=g₂=λ`, UNnormalized (RHS `ε·log ω`).
* `singleCorr_of_fails` (Stmt 1, class A) — divide by the normalizer
  `Z = Σ 1/n ∈ [log ω − 1, log ω + 1]` (`harmonic_window_bounds`); for
  `log ω ≥ 2` the `ε/2` margin survives.
* `liouville_mul` / `liouville_prime` (D2, class A) — the multiplicativity facts
  the class-C node (Prop 2.6) consumes; mathlib supplies `liouville_apply_mul`
  unconditionally, so these are thin wrappers.
* `h211_of_logChowla2Fails` (Stmt 3, class A glue) — compose Stmt 1 (`δ := ε/2`)
  with the Prop-2.6 conclusion `hprop26`, yielding the `(c₁, h211)` pair
  byte-identical to `outer_combine`'s hypothesis.

The integral-against-`logMeasure` reduction to the harmonic window sum is not in
the landed API, so `logMeasure_integral_eq` builds it from the measure
definition (`integral_smul_measure`, `integral_finsetSum_measure`,
`integral_dirac`) and the ENNReal→real normalizer bridge `norm_toReal`.
-/
import Salt.Entropy.Chowla.OuterCombine
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-- **The `logMeasure` expectation is the harmonic-weighted window sum ÷ `Z`.**
`∫ f dμ = (Σ 1/n)⁻¹ · Σ f(n)/n` on the window `(x/ω, x]`, from the Dirac
decomposition of `logMeasure` and the ENNReal→real normalizer bridge. -/
private theorem logMeasure_integral_eq (f : ℕ → ℝ) (x ω : ℕ) :
    ∫ n, f n ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x, f n * (n : ℝ)⁻¹ := by
  have hf : ∀ n ∈ Finset.Ioc (x / ω) x,
      Integrable f ((n : ℝ≥0∞)⁻¹ • Measure.dirac n) := fun n hn =>
    (integrable_dirac (by simp)).smul_measure
      (ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.one_le_iff_ne_zero.mp (window_one_le hn)))
  unfold logMeasure
  rw [integral_smul_measure, integral_finsetSum_measure hf]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [norm_toReal]
  congr 1
  exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)

/-- **The failure Prop.** "log-Chowla-2 fails at scale `(x, ω)` with margin `ε`":
Tao (2.4) at the Liouville model `a=1,b=0,h=1,g₁=g₂=λ`.  UNnormalized
(RHS `ε·log ω`). -/
def logChowla2Fails (eps : ℚ) (x ω : ℕ) : Prop :=
  (eps : ℝ) * Real.log (ω : ℝ) <
    |∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) / (n : ℝ)|

/-- **D2 (class A): complete multiplicativity of Liouville**, `λ(mn) = λ(m)λ(n)`.
Mathlib supplies this unconditionally; the wrapper exposes it in the spine. -/
theorem liouville_mul (m n : ℕ) :
    ArithmeticFunction.liouville (m * n)
      = ArithmeticFunction.liouville m * ArithmeticFunction.liouville n :=
  ArithmeticFunction.liouville_apply_mul m n

/-- **D2 (class A): `λ(p) = −1` for a prime `p`** (ported from `Salt/TwinBar`). -/
theorem liouville_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.liouville p = -1 := by
  rw [ArithmeticFunction.liouville_apply hp.pos.ne',
    ArithmeticFunction.cardFactors_apply_prime hp, pow_one]

/-- **Stmt 1 (normalize, class A).**  Tao (2.4) ⟹ (2.6): divide by the normalizer
`Z = Σ 1/n ∈ [log ω − 1, log ω + 1]` (`harmonic_window_bounds`).  For
`log ω ≥ 2`, `Z ≤ 2·log ω`, so `|E λ(n)λ(n+1)| = |Σ λλ/n|/Z > ε·log ω/(2 log ω)
= ε/2`. -/
theorem singleCorr_of_fails (eps : ℚ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ))
    (hfail : logChowla2Fails eps x ω) :
    (eps : ℝ) / 2 ≤
      |∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
  have hint : ∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) / (n : ℝ) := by
    rw [logMeasure_integral_eq
      (fun n => (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ))]
    simp only [div_eq_mul_inv]
  unfold logChowla2Fails at hfail
  rw [hint]
  obtain ⟨hZlo, hZhi⟩ := harmonic_window_bounds hx hω hωx
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  set Nsum : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) / (n : ℝ) with hNsum
  have hZpos : 0 < Z := by linarith
  have key : (eps : ℝ) * Z ≤ 2 * |Nsum| := by
    rcases le_or_gt (eps : ℝ) 0 with hsign | hsign
    · nlinarith [mul_nonneg (neg_nonneg.mpr hsign) hZpos.le, abs_nonneg Nsum]
    · nlinarith [hfail, mul_le_mul_of_nonneg_left hZhi hsign.le,
        mul_nonneg hsign.le (by linarith : (0 : ℝ) ≤ Real.log (ω : ℝ) - 1)]
  rw [abs_mul, abs_inv, abs_of_pos hZpos, mul_comm Z⁻¹ |Nsum|, ← div_eq_mul_inv,
    le_div_iff₀ hZpos]
  nlinarith [key]

/-- **Stmt 3 (compose to `h211`, class A glue).**  Feed Stmt 1 (`δ := ε/2`) into
the Prop-2.6 conclusion `hprop26`; take `c₁ := c/2`.  The `(c₁, h211)` pair is
byte-identical to `outer_combine`'s `h211` hypothesis.  `hprop26` is exactly the
conclusion of the class-C node `fBridge_of_singleCorr` (Stmt 2), abstracted as a
hypothesis so this glue lands ahead of it. -/
theorem h211_of_logChowla2Fails (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ)) (heps : 0 < eps)
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)|)
    (hfail : logChowla2Fails eps x ω) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hseed := singleCorr_of_fails eps hx hω hωx hlog2 hfail
  have hδpos : (0 : ℝ) < (eps : ℝ) / 2 := by linarith
  obtain ⟨c, hc, hbound⟩ := hprop26 hδpos hseed
  refine ⟨c / 2, by linarith, ?_⟩
  have hEq : c / 2 * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      = c * ((eps : ℝ) / 2 * (H : ℝ) / Real.log (H : ℝ)) := by ring
  rw [hEq]
  exact hbound

/-- **Seam kill-check: the producer's output threads THROUGH `outer_combine`.**
Obtain `⟨c₁, hc₁, h211⟩` from `h211_of_logChowla2Fails` and feed both `c₁` and
`h211` into `outer_combine` at the same `c₁`.  Elaboration ⟹ the producer
conclusion is byte-compatible with the consumer's `h211` parameter. -/
example (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x) (hH : 3 ≤ H)
    [IsProbabilityMeasure (logMeasure x ω)]
    (hlog : 1 ≤ Real.log (H : ℝ)) (hlog2 : 2 ≤ Real.log (ω : ℝ))
    (hne : (primeWindow eps H).Nonempty)
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2)
    (hheadC : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)|)
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasure x ω] ≤ κ)
    (hfail : logChowla2Fails eps x ω) :
    True := by
  obtain ⟨c₁, hc₁, h211⟩ :=
    h211_of_logChowla2Fails eps H hx hω hωx hlog2 heps hprop26 hfail
  have _consumed :=
    outer_combine eps H hx hω hωx heps heps1 hne hreg hH hlog hheadC
      ht hg hgle hI hc₁ h211
  trivial

/-! ### W-F3 B-5 — the shift-`h` port of the `(2.4) → (2.11)` producer chain

The `h`-family beside the landed `h = 1` objects.  Nothing below edits or replaces a
landed declaration: every `_h` name is new, and the `_h_one` compats prove the
`h`-family SUBSUMES the frozen one (they are stated at the landed conclusion and
discharged by the `h`-version at `h := 1`).

`logChowlaFails h` (`ShiftFork.lean:62`) is the named Prop for the hypothesis of
`singleCorr_of_fails_h`, but `ShiftFork` IMPORTS this file, so it cannot be named here
without an import cycle.  The hypothesis is therefore spelled as the inequality
`logChowlaFails` unfolds to, which is definitionally that Prop — a consumer holding
`logChowlaFails h eps x ω` passes it directly. -/

/-- **Stmt 1 at shift `h` (normalize).**  The `h`-family port of `singleCorr_of_fails`:
divide the shift-`h` failure inequality by the normalizer `Z = Σ 1/n ∈ [log ω − 1, log ω + 1]`
(`harmonic_window_bounds`).  For `log ω ≥ 2`, `Z ≤ 2·log ω`, so the `ε/2` margin survives on
the gap-`h` correlation `X_h = E[λ(n)λ(n+h)]`.

The hypothesis is `logChowlaFails h eps x ω` unfolded (see the section note); the proof is
the `h = 1` script with the second Liouville index at `n + h`, which the script never reads. -/
theorem singleCorr_of_fails_h (h : ℕ) (eps : ℚ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ))
    (hfail : (eps : ℝ) * Real.log (ω : ℝ) <
      |∑ n ∈ Finset.Ioc (x / ω) x,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) / (n : ℝ)|) :
    (eps : ℝ) / 2 ≤
      |∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| := by
  have hint : ∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)
      = (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)⁻¹
          * ∑ n ∈ Finset.Ioc (x / ω) x,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + h) : ℝ) / (n : ℝ) := by
    rw [logMeasure_integral_eq
      (fun n => (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + h) : ℝ))]
    simp only [div_eq_mul_inv]
  rw [hint]
  obtain ⟨hZlo, hZhi⟩ := harmonic_window_bounds hx hω hωx
  set Z : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ with hZ
  set Nsum : ℝ := ∑ n ∈ Finset.Ioc (x / ω) x,
      (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + h) : ℝ) / (n : ℝ) with hNsum
  have hZpos : 0 < Z := by linarith
  have key : (eps : ℝ) * Z ≤ 2 * |Nsum| := by
    rcases le_or_gt (eps : ℝ) 0 with hsign | hsign
    · nlinarith [mul_nonneg (neg_nonneg.mpr hsign) hZpos.le, abs_nonneg Nsum]
    · nlinarith [hfail, mul_le_mul_of_nonneg_left hZhi hsign.le,
        mul_nonneg hsign.le (by linarith : (0 : ℝ) ≤ Real.log (ω : ℝ) - 1)]
  rw [abs_mul, abs_inv, abs_of_pos hZpos, mul_comm Z⁻¹ |Nsum|, ← div_eq_mul_inv,
    le_div_iff₀ hZpos]
  nlinarith [key]

/-- **C1 — the `h = 1` compat for Stmt 1, and a kill-check that the `h`-family SUBSUMES the
landed node.**  Stated at the LANDED conclusion of `singleCorr_of_fails` with the LANDED
`logChowla2Fails` hypothesis, and discharged by `singleCorr_of_fails_h 1`.  Elaboration is
the proof that `logChowla2Fails` is defeq to the shift-`1` failure inequality and that
`n + 1` is the `h := 1` instance of `n + h` — no rewrite is needed on either side
(contrast `fBridgeF_h_liouville_apply_one` below, where `(p : ℕ) * 1` is STUCK). -/
theorem singleCorr_of_fails_h_one (eps : ℚ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ))
    (hfail : logChowla2Fails eps x ω) :
    (eps : ℝ) / 2 ≤
      |∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| :=
  singleCorr_of_fails_h 1 eps hx hω hωx hlog2 hfail

/-- **Stmt 3 at shift `h` (compose to `h211`).**  The `h`-family port of
`h211_of_logChowla2Fails`: feed Stmt 1 at shift `h` (`δ := ε/2`) into the shift-`h`
Prop-2.6 conclusion `hprop26`, and take `c₁ := c/2`.  The F-bridge is `fBridgeF_h eps H h`
(`FBridge.lean:525`), the offset-`h` member of the family whose `h = 1` compat is
`fBridgeF_h_one`.  The `h`-dependence is entirely inside the two carried objects; the
glue arithmetic is the `h = 1` script verbatim. -/
theorem h211_of_logChowla2Fails_h (h : ℕ) (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    (hlog2 : 2 ≤ Real.log (ω : ℝ)) (heps : 0 < eps)
    (hprop26 : ∀ {δ : ℝ}, 0 < δ →
        δ ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + h) : ℝ) ∂(logMeasure x ω)| →
        ∃ c : ℝ, 0 < c ∧
          c * (δ * (H : ℝ) / Real.log (H : ℝ))
            ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
                ∂(logMeasure x ω)|)
    (hfail : (eps : ℝ) * Real.log (ω : ℝ) <
      |∑ n ∈ Finset.Ioc (x / ω) x,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + h) : ℝ) / (n : ℝ)|) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hseed := singleCorr_of_fails_h h eps hx hω hωx hlog2 hfail
  have hδpos : (0 : ℝ) < (eps : ℝ) / 2 := by linarith
  obtain ⟨c, hc, hbound⟩ := hprop26 hδpos hseed
  refine ⟨c / 2, by linarith, ?_⟩
  have hEq : c / 2 * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
      = c * ((eps : ℝ) / 2 * (H : ℝ) / Real.log (H : ℝ)) := by ring
  rw [hEq]
  exact hbound

end Salt.Entropy.Chowla
