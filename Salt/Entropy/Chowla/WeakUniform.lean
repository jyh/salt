/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# Tao's Lemma 3.2 (weak uniform distribution), Chowla / entropy-decrement spine

This file lands Tao 1509.05422 Lemma 3.2 in the honest, explicit-constant form: for
a conditioning value `x₀` at which the residue datum's conditional entropy is close
to its full entropy (a "good" pattern — the complement of the `decrement_markov`
bad set), and any set `E` of residues that is *exponentially small* relative to the
modulus `P_H`, the conditional probability of landing in `E` is quantitatively small.

## The Pinsker-free chain (Tao p.21)

Write `ν = condDistrib Y X μ x₀` (a law on `ZMod P`), `q = ν E` its `E`-mass.  The
two-outcome grouping of entropy across the partition `{E, Eᶜ}` gives
  `Hm[ν] ≤ h(q) + q·log|E| + (1−q)·log|Eᶜ|`,
where `h(q) = negMulLog q + negMulLog (1−q) ≤ log 2` is the binary entropy.  A good
`x₀` has `Hm[ν] ≥ H[Y] − t`, and (3.9) gives `H[Y] ≥ log P − deficiency`.  With
`log|E| ≤ log P − g` (`|E| ≤ e^{−g}·P`) and `|Eᶜ| ≤ P` the `log P` terms cancel:
  `q·g ≤ t + deficiency + h(q) ≤ t + deficiency + log 2`,
so `q ≤ (t + deficiency + log 2)/g`.  No Pinsker, no KL — pure `negMulLog` concavity.

## Exports (two PB-floors + the spine instantiation)

* `sum_negMulLog_le_card` — the Jensen atom (public re-derivation of the `private`
  `Fannes.nml_jensen`): `∑_{A} negMulLog δ ≤ (∑ δ)·log|A| + negMulLog (∑ δ)`.
* `measureEntropy_split_le` — the **mixture-entropy bound** (PB-floor): for a prob.
  law `ν` on `ZMod P` and a Finset `E`, the two-set grouping of `Hm[ν]`.
* `weakUniform_generic` — the **generic Lemma 3.2** (PB-floor): the abstract mass
  bound `ν E ≤ (s + log 2)/g` from an entropy floor and a log-card gap.
* `weakUniform_spine` — the spine instantiation at `μ = logMeasure`,
  `X = liouvilleWindow`, `Y = residueWindow`, carrying the (3.9) deficiency
  `log(1 + 8·P_H²·ω/x)` symbolically (see the note on the regime field below).

## Note on the regime `hPHheadroom` field (PH-monotonicity / field mismatch)

`weakUniform_spine` deliberately carries the deficiency `log(1 + 8·P_H²·ω/x)`
symbolically rather than discharging it via `ChowlaRegime.hPHheadroom`.  That field
is stated at `Hhi` (`8·(PH eps Hhi)²·ω ≤ x`), whereas the consumer runs at the
decrement's `H ≤ Hhi`.  Since `primeWindow eps H = primes ∈ (ε²H/2, ε²H]` is a
*moving* window, `PH eps H` is NOT monotone in `H`, and the honest majorant route
`PH eps H ≤ 4^{⌊ε²H⌋} ≤ 4^{⌊ε²Hhi⌋}` is INCOMPARABLE with `(PH eps Hhi)²`, so
the field as landed does not compose to a per-`H` bound.  The theorem is therefore stated
so composition needs no field access; a downstream simplification of the deficiency
would need the honest per-`H` hypothesis `8·(PH eps H)²·ω ≤ x` (or a field re-freeze
to `8·(4^{⌊ε²Hhi⌋})²·ω ≤ x`).  This is a house decision, flagged, not silently taken.
-/
import Salt.Entropy.Chowla.MarkovExtract
import Salt.Entropy.Chowla.ResidueUniform
import Salt.Entropy.Chowla.Decrement
import Mathlib

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## The Jensen atom: the `negMulLog` log-sum inequality

Public re-derivation of `Fannes.nml_jensen` (which is `private`), guarded for the
empty set so it can be applied to both blocks of a `{E, Eᶜ}` partition. -/

/-- **Jensen for `negMulLog`.**  For nonnegative weights `δ` on a Finset `A` with total
`D = ∑ δ`, `∑_{s∈A} negMulLog (δ s) ≤ D·log |A| + negMulLog D`.  (Concavity of
`negMulLog` on `[0,∞)` via `ConcaveOn.le_map_sum`.) -/
lemma sum_negMulLog_le_card {S : Type*} (A : Finset S) (δ : S → ℝ)
    (hδ : ∀ s ∈ A, 0 ≤ δ s) :
    ∑ s ∈ A, Real.negMulLog (δ s)
      ≤ (∑ s ∈ A, δ s) * Real.log A.card + Real.negMulLog (∑ s ∈ A, δ s) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  set N : ℝ := (A.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Finset.card_pos.mpr hA
  set D : ℝ := ∑ s ∈ A, δ s with hDdef
  have hD0 : 0 ≤ D := Finset.sum_nonneg hδ
  have hjen : ∑ s ∈ A, N⁻¹ * Real.negMulLog (δ s)
      ≤ Real.negMulLog (∑ s ∈ A, N⁻¹ * δ s) := by
    have h := concaveOn_negMulLog.le_map_sum (t := A) (w := fun _ => N⁻¹) (p := δ)
      (fun i _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, ← hN, mul_inv_cancel₀ hNpos.ne'])
      (fun i hi => hδ i hi)
    simpa using h
  have hstep : ∑ s ∈ A, Real.negMulLog (δ s)
      ≤ N * Real.negMulLog (∑ s ∈ A, N⁻¹ * δ s) := by
    have hrw : ∑ s ∈ A, Real.negMulLog (δ s)
        = N * ∑ s ∈ A, N⁻¹ * Real.negMulLog (δ s) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hjen hNpos.le
  have hsum : ∑ s ∈ A, N⁻¹ * δ s = N⁻¹ * D := by rw [Finset.mul_sum]
  rw [hsum] at hstep
  refine hstep.trans (le_of_eq ?_)
  rcases eq_or_lt_of_le hD0 with hD0' | hDpos
  · rw [← hD0']; simp
  · rw [Real.negMulLog, Real.negMulLog, Real.log_mul (inv_ne_zero hNpos.ne') hDpos.ne',
        Real.log_inv]
    field_simp
    ring

/-! ## The two-set mixture-entropy bound (PB-floor) -/

/-- **The `{E, Eᶜ}` mixture-entropy bound.**  Splitting `Hm[ν]` across a Finset `E` and
its complement and applying the Jensen atom to each block:
`Hm[ν] ≤ (ν E·log|E| + negMulLog (ν E)) + (ν Eᶜ·log|Eᶜ| + negMulLog (ν Eᶜ))`. -/
lemma measureEntropy_split_le {P : ℕ} [NeZero P] (ν : Measure (ZMod P)) [IsProbabilityMeasure ν]
    (E : Finset (ZMod P)) :
    Hm[ν] ≤ (ν.real ↑E * Real.log E.card + Real.negMulLog (ν.real ↑E))
        + (ν.real ↑(Eᶜ) * Real.log (Eᶜ).card + Real.negMulLog (ν.real ↑(Eᶜ))) := by
  classical
  have hsplit : Hm[ν] = (∑ r ∈ E, Real.negMulLog (ν.real {r}))
      + ∑ r ∈ Eᶜ, Real.negMulLog (ν.real {r}) := by
    rw [measureEntropy_of_isProbabilityMeasure_finite
          (A := Finset.univ) (show ν (↑(Finset.univ : Finset (ZMod P)))ᶜ = 0 by simp),
        ← Finset.sum_add_sum_compl E]
  have hE := sum_negMulLog_le_card E (fun r => ν.real {r}) (fun r _ => measureReal_nonneg)
  have hEc := sum_negMulLog_le_card Eᶜ (fun r => ν.real {r}) (fun r _ => measureReal_nonneg)
  simp only [sum_measureReal_singleton] at hE hEc
  rw [hsplit]
  exact add_le_add hE hEc

/-! ## The generic weak-uniformity bound (Tao Lemma 3.2, abstract form) -/

/-- Monotonicity of `log` on the naturals (handling `log 0 = 0`). -/
private lemma log_natCast_mono {a b : ℕ} (h : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · simpa using Real.log_nonneg (by exact_mod_cast hb : (1 : ℝ) ≤ b)
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast h)

/-- **Tao's Lemma 3.2 (generic form, PB-floor).**  Let `ν` be a probability law on
`ZMod P` whose entropy is within `s` of the maximal `log P` (`Real.log P − s ≤ Hm[ν]`),
and let `E` be a residue set that is exponentially small: `log|E| ≤ log P − g` with
`g > 0`.  Then `ν E ≤ (s + log 2)/g`.  Proof: the `{E, Eᶜ}` mixture bound plus the
binary-entropy ceiling `log 2`; the `log P` terms cancel against `|E|,|Eᶜ| ≤ P`. -/
theorem weakUniform_generic {P : ℕ} [NeZero P] (ν : Measure (ZMod P)) [IsProbabilityMeasure ν]
    {s g : ℝ} (hg : 0 < g) (E : Finset (ZMod P))
    (hlb : Real.log P - s ≤ Hm[ν])
    (hE : Real.log (E.card : ℝ) ≤ Real.log P - g) :
    ν.real ↑E ≤ (s + Real.log 2) / g := by
  classical
  have ha0 : 0 ≤ ν.real (↑E : Set (ZMod P)) := measureReal_nonneg
  have hb0 : 0 ≤ ν.real (↑(Eᶜ) : Set (ZMod P)) := measureReal_nonneg
  have huniv : ν.real (Set.univ : Set (ZMod P)) = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hsum : ν.real ↑E + ν.real ↑(Eᶜ) = 1 := by
    have h := measureReal_add_measureReal_compl (μ := ν) (Finset.measurableSet E)
    rw [huniv] at h
    rw [Finset.coe_compl]; exact h
  have hmix := measureEntropy_split_le ν E
  have hcard_le : (Eᶜ).card ≤ P := by
    have h := Finset.card_le_univ (Eᶜ : Finset (ZMod P))
    rwa [ZMod.card] at h
  have hEc_card : Real.log ((Eᶜ).card : ℝ) ≤ Real.log (P : ℝ) := log_natCast_mono hcard_le
  have hterm1 : ν.real ↑E * Real.log (E.card : ℝ)
      ≤ ν.real ↑E * Real.log (P : ℝ) - ν.real ↑E * g := by
    have h := mul_le_mul_of_nonneg_left hE ha0
    rwa [mul_sub] at h
  have hterm2 : ν.real ↑(Eᶜ) * Real.log ((Eᶜ).card : ℝ)
      ≤ ν.real ↑(Eᶜ) * Real.log (P : ℝ) :=
    mul_le_mul_of_nonneg_left hEc_card hb0
  have hbin : Real.negMulLog (ν.real ↑E) + Real.negMulLog (ν.real ↑(Eᶜ))
      ≤ Real.log 2 := by
    have hbeq : ν.real ↑(Eᶜ) = 1 - ν.real ↑E := by linear_combination hsum
    rw [hbeq, ← Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact Real.binEntropy_le_log_two
  have hab : ν.real ↑E * Real.log (P : ℝ) + ν.real ↑(Eᶜ) * Real.log (P : ℝ)
      = Real.log (P : ℝ) := by rw [← add_mul, hsum, one_mul]
  rw [le_div_iff₀ hg]
  linarith [hlb, hmix, hterm1, hterm2, hbin, hab]

/-! ## The spine instantiation (Tao Lemma 3.2 at the Liouville/residue spine) -/

/-- **Tao's Lemma 3.2 at the spine.**  Instantiates `weakUniform_generic` at
`μ = logMeasure x ω`, `X = liouvilleWindow H`, `Y = residueWindow eps H`, with
`ν = condDistrib Y X μ x₀` for a good pattern `x₀` (conditional entropy defect `≤ t`,
the complement of the `decrement_markov` bad set).  For an exponentially small residue
set `E` (`log|E| ≤ log P_H − g`), the conditional `E`-mass is
`≤ (t + log(1 + 8·P_H²·ω/x) + log 2)/g`.  The (3.9) deficiency
`log(1 + 8·P_H²·ω/x)` is carried symbolically (see the module note on `hPHheadroom`). -/
theorem weakUniform_spine {x ω : ℕ} (eps : ℚ) (H : ℕ)
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    {t g : ℝ} (hg : 0 < g) (x₀ : Fin H → ℤ) (E : Finset (ZMod (PH eps H)))
    (hgood : H[residueWindow eps H; logMeasure x ω]
        - Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀] ≤ t)
    (hE : Real.log (E.card : ℝ) ≤ Real.log (PH eps H : ℝ) - g) :
    (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real ↑E
      ≤ (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ))
          + Real.log 2) / g := by
  haveI : IsProbabilityMeasure
      (condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀) :=
    inferInstance
  have hdefic := entropy_residueWindow_ge eps H hx hω hωx
  have hlb : Real.log (PH eps H : ℝ)
        - (t + Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)))
      ≤ Hm[condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀] := by
    linarith [hgood, hdefic]
  exact weakUniform_generic _ hg E hlb hE

end Salt.Entropy.Chowla
