/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The joint-law invariance headline (Chowla / entropy-decrement spine, node D-d)

The JOINT/CONDITIONAL translation invariance of the log-sampled window laws
(Tao arXiv:1509.05422v2 §3, the load-bearing MI-gain step of Lemma 3.1; wave-II gate
block B1).  The conditional gap `ℍ(X_H^{(j)}|Y_H) − ℍ(X_H|Y_H)` equals the
JOINT gap `ℍ(X_H^{(j)},Y_H) − ℍ(X_H,Y_H)` (the common `ℍ(Y_H)` cancels), and the
joint gap reduces to the SAME `ℓ¹` estimate via the exact σ-algebra relabel of
the residue coordinate `r ↦ r + jH (mod P_H)` (a bijection): concretely
`ℍ(X_H^{(j)},Y_H; μ) = ℍ(X_H,Y_H; (T_{jH})_*μ)`.

This file lands the joint-window infrastructure and the residue-relabel identity
(the reduction's algebraic spine): the joint variable `(X_H^{(j)}, Y_H)`, its
finite-range / measurability data, the joint support finset `{-1,1}^H ×ˢ univ`,
and the exact relabel identity `jointWindow 0 ∘ (·+jH) = ψ ∘ jointWindow j`.
-/
import Mathlib
import Salt.Entropy.Basic
import Salt.Entropy.Chowla.Regime
import Salt.Entropy.Chowla.Invariance
import Salt.Entropy.Chowla.Fannes
import Salt.Entropy.Chowla.PrimeWindow
import Salt.Entropy.Chowla.Windows

open MeasureTheory Real ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ### The joint window `(X_H^{(j)}, Y_H)` -/

/-- The joint variable `n ↦ (X_H^{(j)} n, Y_H n)` of the shifted Liouville window
    and the residue datum (AUTO-ETA rule: written `fun n ↦ (X n, Y n)`). -/
def jointWindow (eps : ℚ) (H j : ℕ) : ℕ → (Fin H → ℤ) × ZMod (PH eps H) :=
  fun n => (liouvilleWindowShift H j n, residueWindow eps H n)

@[simp] lemma jointWindow_apply (eps : ℚ) (H j n : ℕ) :
    jointWindow eps H j n = (liouvilleWindowShift H j n, residueWindow eps H n) := rfl

/-- The joint support finset: `{-1,1}^H ×ˢ (all residues of `ZMod P_H`)`. -/
def jointSupport (eps : ℚ) (H : ℕ) : Finset ((Fin H → ℤ) × ZMod (PH eps H)) :=
  (Fintype.piFinset (fun _ : Fin H => ({-1, 1} : Finset ℤ))) ×ˢ Finset.univ

lemma jointWindow_mem_jointSupport (eps : ℚ) (H j n : ℕ) :
    jointWindow eps H j n ∈ jointSupport eps H := by
  rw [jointSupport, Finset.mem_product]
  exact ⟨liouvilleWindowShift_mem_piFinset H j n, Finset.mem_univ _⟩

/-- The joint window has finite range (contained in `{-1,1}^H ×ˢ univ`). -/
instance instFiniteRangeJointWindow (eps : ℚ) (H j : ℕ) : FiniteRange (jointWindow eps H j) :=
  finiteRange_of_finset (jointWindow eps H j) (jointSupport eps H)
    (fun n => jointWindow_mem_jointSupport eps H j n)

/-- The joint window is measurable (its domain `ℕ` is discrete/countable). -/
lemma measurable_jointWindow (eps : ℚ) (H j : ℕ) : Measurable (jointWindow eps H j) :=
  measurable_of_countable _

/-- At `j = 0` the joint window is `(X_H, Y_H)` (the shift is the identity). -/
@[simp] lemma jointWindow_zero (eps : ℚ) (H : ℕ) :
    jointWindow eps H 0 = fun n => (liouvilleWindow H n, residueWindow eps H n) := by
  funext n; simp [jointWindow]

/-! ### The residue relabel `ψ : (v, r) ↦ (v, r + jH)` -/

/-- The residue relabel `ψ : (v, r) ↦ (v, r + (jH mod P_H))` on the joint range —
    the exact σ-algebra relabel of the residue coordinate (a bijection). -/
def jointRelabel (eps : ℚ) (H j : ℕ) :
    (Fin H → ℤ) × ZMod (PH eps H) → (Fin H → ℤ) × ZMod (PH eps H) :=
  fun p => (p.1, p.2 + ((j * H : ℕ) : ZMod (PH eps H)))

/-- The relabel `ψ` is injective (it is `id × (·+c)`, a bijection). -/
lemma jointRelabel_injective (eps : ℚ) (H j : ℕ) :
    Function.Injective (jointRelabel eps H j) := by
  intro p q h
  simp only [jointRelabel, Prod.mk.injEq] at h
  exact Prod.ext h.1 (add_right_cancel h.2)

/-- **The residue-relabel identity** (the reduction's algebraic spine, B1).  The
    unshifted joint window read at the shifted base `n + jH` equals the relabel `ψ`
    applied to the shifted joint window at `n`:
    `(X_H, Y_H)(n+jH) = ψ ((X_H^{(j)}, Y_H)(n))`.  Hence the two joint laws are
    relabels of each other and the joint gap is `ψ`-relabel invariant. -/
lemma jointWindow_zero_shift (eps : ℚ) (H j n : ℕ) :
    jointWindow eps H 0 (n + j * H) = jointRelabel eps H j (jointWindow eps H j n) := by
  simp only [jointWindow, jointRelabel, liouvilleWindowShift, residueWindow, Prod.mk.injEq]
  refine ⟨by ring_nf, ?_⟩
  push_cast
  ring

/-- The function-level form: `jointWindow 0 ∘ (·+jH) = ψ ∘ jointWindow j`. -/
lemma jointWindow_zero_comp_shift (eps : ℚ) (H j : ℕ) :
    (fun n => jointWindow eps H 0 (n + j * H))
      = jointRelabel eps H j ∘ jointWindow eps H j := by
  funext n; exact jointWindow_zero_shift eps H j n

/-! ### The D-d reduction (the spine) and the Fannes bridge -/

/-- **The D-d reduction spine.**  The conditional gap equals the JOINT gap (the
    common `ℍ(Y_H)` cancels by the chain rule), and the joint gap is the entropy
    of the shifted-base joint law minus the base joint law (the residue-relabel `ψ`
    is entropy-invariant):
    `ℍ(X_H^{(j)}|Y_H) − ℍ(X_H|Y_H) = Hm[(T_{jH})_*μ .map (X_H,Y_H)] − Hm[μ .map (X_H,Y_H)]`.
    This reduces the frozen headline `condEntropy_shift_le` to a pure `ℓ¹`-Fannes
    statement on the two joint pushforward laws. -/
theorem condEntropy_shift_reduction (R : ChowlaRegime) (H j : ℕ) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasure R.x R.ω]
      - H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
    = Hm[((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)]
      - Hm[(logMeasure R.x R.ω).map (jointWindow R.eps H 0)] := by
  set μ := logMeasure R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_logMeasure R.hx R.hω
  have hj_cr := chain_rule μ (measurable_liouvilleWindowShift H j)
    (measurable_residueWindow R.eps H)
  have h0_cr := chain_rule μ (measurable_liouvilleWindow H) (measurable_residueWindow R.eps H)
  have hCEj : H[liouvilleWindowShift H j | residueWindow R.eps H ; μ]
      = H[jointWindow R.eps H j ; μ] - H[residueWindow R.eps H ; μ] := by
    rw [show H[jointWindow R.eps H j ; μ]
        = H[(fun n => (liouvilleWindowShift H j n, residueWindow R.eps H n)) ; μ] from rfl,
      hj_cr]; ring
  have hCE0 : H[liouvilleWindow H | residueWindow R.eps H ; μ]
      = H[jointWindow R.eps H 0 ; μ] - H[residueWindow R.eps H ; μ] := by
    rw [jointWindow_zero, h0_cr]; ring
  rw [hCEj, hCE0]
  have hcancel : H[jointWindow R.eps H j ; μ] - H[residueWindow R.eps H ; μ]
      - (H[jointWindow R.eps H 0 ; μ] - H[residueWindow R.eps H ; μ])
      = H[jointWindow R.eps H j ; μ] - H[jointWindow R.eps H 0 ; μ] := by ring
  rw [hcancel]
  have hrelabel : H[jointWindow R.eps H j ; μ]
      = H[(fun n => jointWindow R.eps H 0 (n + j * H)) ; μ] := by
    rw [← entropy_comp_of_injective μ (measurable_jointWindow R.eps H j)
        (jointRelabel R.eps H j) (jointRelabel_injective R.eps H j)]
    congr 1
    rw [jointWindow_zero_comp_shift]
  rw [hrelabel, entropy_def, entropy_def,
    show Measure.map (jointWindow R.eps H 0) (μ.map (fun n => n + j * H))
        = Measure.map (fun n => jointWindow R.eps H 0 (n + j * H)) μ from by
      rw [Measure.map_map (measurable_jointWindow R.eps H 0)
          (measurable_of_countable (fun n : ℕ => n + j * H))]; rfl]

/-- **The Fannes bridge** (the frozen headline modulo the `ℓ¹` bound).  Given the
    joint-law `ℓ¹` distance `d` (as an EQUALITY hypothesis) with `d ≤ 1/e` and the
    Fannes budget `d·log|jointSupport| + binEntropy d ≤ H/(4 logH logloglogH)`, the
    frozen D-d headline `condEntropy_shift_le` holds.  This is the `entropy_sub_le_of_l1`
    plug-in on the two joint pushforward laws, composed with `condEntropy_shift_reduction`.
    D-e/Fable must supply `d ≤ 8·j·H·ω/x` (pushforward `ℓ¹` contraction + base
    telescoping against `harmonic_shift_l1_le`) and discharge the budget via `hheadroom'`. -/
theorem condEntropy_shift_le_of_l1 (R : ChowlaRegime) (H j : ℕ) (d : ℝ)
    (hd : d = ∑ s ∈ jointSupport R.eps H,
      |(((logMeasure R.x R.ω).map (fun n => n + j * H)).map (jointWindow R.eps H 0)).real {s}
        - ((logMeasure R.x R.ω).map (jointWindow R.eps H 0)).real {s}|)
    (hd1 : d ≤ Real.exp (-1))
    (hbudget : d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d
        ≤ (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H)))) :
    H[liouvilleWindowShift H j | residueWindow R.eps H ; logMeasure R.x R.ω]
      ≤ H[liouvilleWindow H | residueWindow R.eps H ; logMeasure R.x R.ω]
        + (H : ℝ) / (4 * Real.log H * Real.log (Real.log (Real.log H))) := by
  set μ := logMeasure R.x R.ω with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_logMeasure R.hx R.hω
  haveI : IsProbabilityMeasure (μ.map (fun n => n + j * H)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  set ν' := μ.map (jointWindow R.eps H 0) with hν'
  set μ' := (μ.map (fun n => n + j * H)).map (jointWindow R.eps H 0) with hμ'
  haveI : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map (measurable_jointWindow R.eps H 0).aemeasurable
  haveI : IsProbabilityMeasure μ' :=
    Measure.isProbabilityMeasure_map (measurable_jointWindow R.eps H 0).aemeasurable
  have hν'null : ν' ((jointSupport R.eps H : Set _))ᶜ = 0 := by
    rw [hν', Measure.map_apply (measurable_jointWindow R.eps H 0) (Finset.measurableSet _).compl]
    convert measure_empty (μ := μ)
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun n hn => hn (jointWindow_mem_jointSupport R.eps H 0 n)
  have hμ'null : μ' ((jointSupport R.eps H : Set _))ᶜ = 0 := by
    rw [hμ', Measure.map_apply (measurable_jointWindow R.eps H 0) (Finset.measurableSet _).compl,
      Measure.map_apply (measurable_of_countable _)
        ((measurable_jointWindow R.eps H 0) (Finset.measurableSet _).compl)]
    convert measure_empty (μ := μ)
    rw [Set.eq_empty_iff_forall_notMem]
    exact fun n hn => hn (jointWindow_mem_jointSupport R.eps H 0 (n + j * H))
  have hfannes := entropy_sub_le_of_l1 μ' ν' (jointSupport R.eps H) hμ'null hν'null d hd hd1
  have hdiff : Hm[μ'] - Hm[ν'] ≤
      d * Real.log ((jointSupport R.eps H).card : ℝ) + Real.binEntropy d :=
    (le_abs_self _).trans hfannes
  have hred := condEntropy_shift_reduction R H j
  rw [← hμ] at hred
  rw [← hμ', ← hν'] at hred
  linarith [hred, hdiff, hbudget]

end Salt.Entropy.Chowla
