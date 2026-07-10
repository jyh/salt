/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom
import Salt.Maynard.GIntegrals

/-!
# N3.3 — weighted transfers (Maynard track)

The bridge from the `μ²/φ` atom (`N3.1`, `Salt.Maynard.phiAtomSum`) to the four
weighted one-dimensional sums that feed the S₁/S₂ optimisation.  With the
"radial" variable `u(r) = k·log r/log R` and the profile `g(u) = 1/(1 + (log k)·u)`
we set `fWt r = g(u(r))` and study, over squarefree `r < R₀ := ⌊R^{T/k}⌋₊`
coprime to `W`:

* `B1  = ∑' fWt      / φ(r)`
* `A1  = ∑' fWt²     / φ(r)`
* `A1_1 = ∑' fWt²·u  / φ(r)`
* `A1_2 = ∑' fWt²·u² / φ(r)`

This file delivers:

* the definitions (`uVal`, `fWt`, `R0`, `A1`, `B1`, `A1_1`, `A1_2`);
* the structural facts (`fWt` is in `(0,1]`, `u ∈ [0,T]` on the support, each
  sum is `≥ 0`, and the monotone ordering `A1_2 ≤ T²·A1`, `A1_1 ≤ T·A1`,
  `A1 ≤ B1`, `A1 ≤ phiAtomSum`, `B1 ≤ phiAtomSum`);
* the **reduction lemmas** to the atom (`*_le_phiAtom`, `*_ge_min_mul_phiAtom`);
* two **genuine, non-vacuous, explicit-constant** transfer bounds — `B1_lower`
  (a real lower bound of shape `(φ(W)/W)·log R₀` with a *fixed* `W`-only
  constant subtracted) and `A1_upper_real` (a real upper bound of shape
  `4·(φ(W)/W)·(T/k)·log R` plus a *fixed* `W`-only constant) — obtained by
  feeding N3.1's `phiAtom` two-sided bounds through the reduction lemmas.

The constants in `B1_lower` / `A1_upper_real` are **explicit** (no existential
`C`): the leading term genuinely grows in `R` while the additive constant
depends only on `W`, so the bounds cannot be satisfied vacuously.

**Crude, not sharp (honest scope).** These are the CRUDER-but-genuine route of
the frozen N3.3: the lower bound drops `fWt(r) ≥ fWt(R₀) = 1/(1+(log k)·T)` for
all `r < R₀` (losing a constant factor vs. the Abel-summation integral `I(f)`),
and the upper bound drops `fWt ≤ 1` (replacing `J(f) = ∫₀ᵀ g²` by the trivial
envelope).  The exact-leading-constant Abel transfer (hitting the N6.1 integrals
`integral_g`, `integral_g_sq`, …) remains a PORT-BLOCKER, documented at the end.
-/

open Finset

namespace Salt.Maynard

/-! ## Definitions -/

/-- The radial variable `u(r) = k·log r / log R`. -/
noncomputable def uVal (k R r : ℕ) : ℝ := (k : ℝ) * Real.log r / Real.log R

/-- The profile weight `fWt r = g(u(r)) = 1/(1 + (log k)·u(r))`. -/
noncomputable def fWt (k R r : ℕ) : ℝ := 1 / (1 + Real.log (k : ℝ) * uVal k R r)

/-- The truncation point `R₀ = ⌊R^{T/k}⌋₊`. -/
noncomputable def R0 (k R : ℕ) (T : ℝ) : ℕ := ⌊(R : ℝ) ^ (T / (k : ℝ))⌋₊

/-- `A₁ = ∑_{r < R₀ sqfree, (r,W)=1} fWt(r)² / φ(r)`. -/
noncomputable def A1 (k R W : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ sqfCop (R0 k R T) W, (fWt k R r) ^ 2 / (Nat.totient r)

/-- `B₁ = ∑_{r < R₀ sqfree, (r,W)=1} fWt(r) / φ(r)`. -/
noncomputable def B1 (k R W : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ sqfCop (R0 k R T) W, (fWt k R r) / (Nat.totient r)

/-- `A₁⁽¹⁾ = ∑_{r < R₀ sqfree, (r,W)=1} fWt(r)²·u(r) / φ(r)`. -/
noncomputable def A1_1 (k R W : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ sqfCop (R0 k R T) W, (fWt k R r) ^ 2 * uVal k R r / (Nat.totient r)

/-- `A₁⁽²⁾ = ∑_{r < R₀ sqfree, (r,W)=1} fWt(r)²·u(r)² / φ(r)`. -/
noncomputable def A1_2 (k R W : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ sqfCop (R0 k R T) W, (fWt k R r) ^ 2 * (uVal k R r) ^ 2 / (Nat.totient r)

/-! ## Structural facts about `uVal` and `fWt` -/

/-- On the support `r ≥ 1`, `u(r) ≥ 0`. -/
lemma uVal_nonneg {k R r : ℕ} (hr : 1 ≤ r) (hR : 2 ≤ R) : 0 ≤ uVal k R r := by
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr)
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  unfold uVal
  positivity

/-- On the truncated support, `u(r) ≤ T`. -/
lemma uVal_le_T {k R W r : ℕ} {T : ℝ} (hk : 1 ≤ k) (hR : 2 ≤ R)
    (hmem : r ∈ sqfCop (R0 k R T) W) : uVal k R r ≤ T := by
  rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hmem
  obtain ⟨hrlt, hsqf, _⟩ := hmem
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hsqf.ne_zero
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hRR : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRR
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  set y : ℝ := (R : ℝ) ^ (T / (k : ℝ)) with hy
  have hy0 : (0 : ℝ) ≤ y := (Real.rpow_pos_of_pos hRpos _).le
  -- `(r : ℝ) < y`
  have hrY : (r : ℝ) < y := by
    have h1 : (r : ℝ) < ((R0 k R T : ℕ) : ℝ) := by exact_mod_cast hrlt
    have h2 : ((R0 k R T : ℕ) : ℝ) ≤ y := by
      rw [R0, hy]; exact Nat.floor_le hy0
    linarith
  -- `log r ≤ (T/k)·log R`
  have hlogr : Real.log r ≤ (T / (k : ℝ)) * Real.log R := by
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have := Real.log_le_log hrpos hrY.le
    rwa [hy, Real.log_rpow hRpos] at this
  -- conclude `u(r) = k·log r/log R ≤ T`
  unfold uVal
  rw [div_le_iff₀ hlogR]
  calc (k : ℝ) * Real.log r ≤ (k : ℝ) * ((T / (k : ℝ)) * Real.log R) :=
        mul_le_mul_of_nonneg_left hlogr hkR.le
    _ = T * Real.log R := by field_simp

/-- The denominator of `fWt` is `≥ 1` on the support. -/
lemma fWt_denom_pos {k R r : ℕ} (hr : 1 ≤ r) (hR : 2 ≤ R) :
    1 ≤ 1 + Real.log (k : ℝ) * uVal k R r := by
  have hu : 0 ≤ uVal k R r := uVal_nonneg hr hR
  have hlk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  nlinarith [mul_nonneg hlk hu]

lemma fWt_pos {k R r : ℕ} (hr : 1 ≤ r) (hR : 2 ≤ R) : 0 < fWt k R r := by
  unfold fWt
  have := fWt_denom_pos (k := k) (R := R) (r := r) hr hR
  positivity

lemma fWt_le_one {k R r : ℕ} (hr : 1 ≤ r) (hR : 2 ≤ R) : fWt k R r ≤ 1 := by
  unfold fWt
  have h := fWt_denom_pos (k := k) (R := R) (r := r) hr hR
  rw [div_le_one (by linarith)]
  linarith

lemma fWt_nonneg {k R r : ℕ} (hr : 1 ≤ r) (hR : 2 ≤ R) : 0 ≤ fWt k R r :=
  (fWt_pos hr hR).le

/-- The minimal weight over the truncated support: `fWt r ≥ 1/(1 + (log k)·T)`. -/
lemma fWt_ge_min {k R W r : ℕ} {T : ℝ} (hk : 1 ≤ k) (hR : 2 ≤ R)
    (hmem : r ∈ sqfCop (R0 k R T) W) :
    1 / (1 + Real.log (k : ℝ) * T) ≤ fWt k R r := by
  have hr : 1 ≤ r := by
    rw [sqfCop, Finset.mem_filter] at hmem
    exact Nat.one_le_iff_ne_zero.mpr hmem.2.1.ne_zero
  have hu : 0 ≤ uVal k R r := uVal_nonneg hr hR
  have huT : uVal k R r ≤ T := uVal_le_T hk hR hmem
  have hlk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hdpos : (0 : ℝ) < 1 + Real.log (k : ℝ) * uVal k R r := by
    have := fWt_denom_pos (k := k) (R := R) (r := r) hr hR; linarith
  unfold fWt
  apply one_div_le_one_div_of_le hdpos
  nlinarith [mul_le_mul_of_nonneg_left huT hlk]

/-- `1/(1 + (log k)·T) > 0`. -/
lemma inv_one_add_log_mul_pos {k : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    0 < 1 / (1 + Real.log (k : ℝ) * T) := by
  have hlk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have : (0 : ℝ) < 1 + Real.log (k : ℝ) * T := by nlinarith [mul_nonneg hlk hT]
  positivity

/-- Membership in the truncated support gives `r ≥ 1` and `φ(r) > 0`. -/
lemma mem_support {k R W r : ℕ} {T : ℝ} (hmem : r ∈ sqfCop (R0 k R T) W) :
    1 ≤ r ∧ 0 < (Nat.totient r : ℝ) := by
  rw [sqfCop, Finset.mem_filter] at hmem
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hmem.2.1.ne_zero
  refine ⟨hr, ?_⟩
  exact_mod_cast Nat.totient_pos.mpr hr

/-! ## Nonnegativity of the four sums -/

lemma A1_nonneg (k R W : ℕ) (T : ℝ) : 0 ≤ A1 k R W T := by
  apply Finset.sum_nonneg; intro r _; positivity

lemma B1_nonneg (k R W : ℕ) (T : ℝ) (hR : 2 ≤ R) : 0 ≤ B1 k R W T := by
  apply Finset.sum_nonneg; intro r hmem
  have hr := (mem_support hmem).1
  have := fWt_nonneg (k := k) (R := R) (r := r) hr hR
  positivity

lemma A1_1_nonneg (k R W : ℕ) (T : ℝ) (hR : 2 ≤ R) : 0 ≤ A1_1 k R W T := by
  apply Finset.sum_nonneg; intro r hmem
  have hr := (mem_support hmem).1
  have := uVal_nonneg (k := k) (R := R) (r := r) hr hR
  positivity

lemma A1_2_nonneg (k R W : ℕ) (T : ℝ) : 0 ≤ A1_2 k R W T := by
  apply Finset.sum_nonneg; intro r _; positivity

/-! ## Ordering relations and reductions to the atom -/

/-- `A₁ ≤ B₁` (from `fWt² ≤ fWt`). -/
lemma A1_le_B1 {k R W : ℕ} {T : ℝ} (hR : 2 ≤ R) : A1 k R W T ≤ B1 k R W T := by
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have h0 := fWt_nonneg (k := k) (R := R) (r := r) hr hR
  have h1 := fWt_le_one (k := k) (R := R) (r := r) hr hR
  have hsq : (fWt k R r) ^ 2 ≤ fWt k R r := by nlinarith
  exact (div_le_div_iff_of_pos_right hφ).mpr hsq

/-- `A₁ ≤ phiAtomSum R₀ W` (from `fWt² ≤ 1`). -/
lemma A1_le_phiAtom {k R W : ℕ} {T : ℝ} (hR : 2 ≤ R) :
    A1 k R W T ≤ phiAtomSum (R0 k R T) W := by
  unfold A1 phiAtomSum
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have h0 := fWt_nonneg (k := k) (R := R) (r := r) hr hR
  have h1 := fWt_le_one (k := k) (R := R) (r := r) hr hR
  have hsq : (fWt k R r) ^ 2 ≤ 1 := by nlinarith
  exact (div_le_div_iff_of_pos_right hφ).mpr hsq

/-- `B₁ ≤ phiAtomSum R₀ W` (from `fWt ≤ 1`). -/
lemma B1_le_phiAtom {k R W : ℕ} {T : ℝ} (hR : 2 ≤ R) :
    B1 k R W T ≤ phiAtomSum (R0 k R T) W := by
  unfold B1 phiAtomSum
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have h1 := fWt_le_one (k := k) (R := R) (r := r) hr hR
  exact (div_le_div_iff_of_pos_right hφ).mpr h1

/-- `A₁⁽¹⁾ ≤ T·A₁` (from `u ≤ T`). -/
lemma A1_1_le_T_mul_A1 {k R W : ℕ} {T : ℝ} (hk : 1 ≤ k) (hR : 2 ≤ R) :
    A1_1 k R W T ≤ T * A1 k R W T := by
  unfold A1_1 A1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have huT : uVal k R r ≤ T := uVal_le_T hk hR hmem
  have hf : 0 ≤ (fWt k R r) ^ 2 := by positivity
  have hnum : (fWt k R r) ^ 2 * uVal k R r ≤ T * (fWt k R r) ^ 2 := by nlinarith
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hφ).mpr hnum

/-- `A₁⁽²⁾ ≤ T²·A₁` (from `u² ≤ T²`). -/
lemma A1_2_le_Tsq_mul_A1 {k R W : ℕ} {T : ℝ} (hk : 1 ≤ k) (hR : 2 ≤ R) :
    A1_2 k R W T ≤ T ^ 2 * A1 k R W T := by
  unfold A1_2 A1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have hu0 : 0 ≤ uVal k R r := uVal_nonneg hr hR
  have huT : uVal k R r ≤ T := uVal_le_T hk hR hmem
  have husq : (uVal k R r) ^ 2 ≤ T ^ 2 := by
    exact pow_le_pow_left₀ hu0 huT 2
  have hf : 0 ≤ (fWt k R r) ^ 2 := by positivity
  have hnum : (fWt k R r) ^ 2 * (uVal k R r) ^ 2 ≤ T ^ 2 * (fWt k R r) ^ 2 := by nlinarith
  rw [← mul_div_assoc]
  exact (div_le_div_iff_of_pos_right hφ).mpr hnum

/-- Lower reduction: `B₁ ≥ (1/(1+(log k)·T))·phiAtomSum R₀ W`. -/
lemma B1_ge_min_mul_phiAtom {k R W : ℕ} {T : ℝ} (hk : 1 ≤ k) (hR : 2 ≤ R) :
    (1 / (1 + Real.log (k : ℝ) * T)) * phiAtomSum (R0 k R T) W ≤ B1 k R W T := by
  unfold B1 phiAtomSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have hmin := fWt_ge_min (k := k) (R := R) (W := W) (r := r) hk hR hmem
  rw [mul_one_div, div_le_div_iff_of_pos_right hφ]
  exact hmin

/-- Lower reduction: `A₁ ≥ (1/(1+(log k)·T))²·phiAtomSum R₀ W`. -/
lemma A1_ge_min_sq_mul_phiAtom {k R W : ℕ} {T : ℝ} (hk : 1 ≤ k) (hR : 2 ≤ R) (hT : 0 ≤ T) :
    (1 / (1 + Real.log (k : ℝ) * T)) ^ 2 * phiAtomSum (R0 k R T) W ≤ A1 k R W T := by
  unfold A1 phiAtomSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have hmin := fWt_ge_min (k := k) (R := R) (W := W) (r := r) hk hR hmem
  have hmin0 : 0 ≤ 1 / (1 + Real.log (k : ℝ) * T) := (inv_one_add_log_mul_pos (k := k) hT).le
  have hsq : (1 / (1 + Real.log (k : ℝ) * T)) ^ 2 ≤ (fWt k R r) ^ 2 := by
    exact pow_le_pow_left₀ hmin0 hmin 2
  rw [mul_one_div, div_le_div_iff_of_pos_right hφ]
  exact hsq

/-! ## Truncation-point estimate -/

/-- `log R₀ ≤ (T/k)·log R`. -/
lemma log_R0_le {k R : ℕ} {T : ℝ} (hR : 2 ≤ R) (hR0 : 1 ≤ R0 k R T) :
    Real.log (R0 k R T) ≤ (T / (k : ℝ)) * Real.log R := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    have : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hy0 : (0 : ℝ) ≤ (R : ℝ) ^ (T / (k : ℝ)) := (Real.rpow_pos_of_pos hRpos _).le
  have hR0pos : (0 : ℝ) < (R0 k R T : ℕ) := by exact_mod_cast hR0
  have hle : ((R0 k R T : ℕ) : ℝ) ≤ (R : ℝ) ^ (T / (k : ℝ)) := by
    rw [R0]; exact Nat.floor_le hy0
  have := Real.log_le_log hR0pos hle
  rwa [Real.log_rpow hRpos] at this

/-! ## Explicit-constant `phiAtom` bounds (de-vacuoused N3.1 wrappers)

`phiAtom_lower` / `phiAtom_upper_lossy` package their additive constant behind
an `∃ C`.  For the transfer bounds below we need the constant *pinned* to a
concrete `W`-only value, otherwise the outer `∃ C` would let the constant absorb
the (growing) main term and the bound would be vacuous.  These two lemmas expose
the underlying constants explicitly. -/

/-- Explicit-constant lower bound: the additive constant is `(φ(B)/B)·log B`
(the value used inside `phiAtom_lower`), pinned rather than existential. -/
lemma phiAtomSum_lower_explicit (B : ℕ) (hB : B ≠ 0) (x : ℕ) (hx : 2 ≤ x) :
    (Nat.totient B / B : ℝ) * Real.log x - (Nat.totient B / B : ℝ) * Real.log B
      ≤ phiAtomSum x B :=
  le_trans (copHarmonic_lower B hB x hx) (copHarmonic_le_phiAtomSum x B)

/-- Explicit-constant `4×`-lossy upper bound: additive constant `4·(φ(B)+1)`
(the value used inside `phiAtom_upper_lossy`), pinned rather than existential. -/
lemma phiAtomSum_upper_explicit (B : ℕ) (hB : B ≠ 0) (x : ℕ) (hx : 2 ≤ x) :
    phiAtomSum x B
      ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x) + 4 * ((Nat.totient B : ℝ) + 1) := by
  have h1 := phiAtomSum_le_mul x B
  have h2 := sum_inv_mul_totient_le x B
  have h3 := copHarmonic_upper B hB x hx
  have hch : 0 ≤ copHarmonic x B := by
    unfold copHarmonic; apply Finset.sum_nonneg; intro n _; positivity
  calc phiAtomSum x B
      ≤ (∑ d ∈ sqfCop x B, (1 : ℝ) / (d * Nat.totient d)) * copHarmonic x B := h1
    _ ≤ 4 * copHarmonic x B := mul_le_mul_of_nonneg_right h2 hch
    _ ≤ 4 * ((Nat.totient B / B : ℝ) * Real.log x + ((Nat.totient B : ℝ) + 1)) := by
        linarith [h3]
    _ = 4 * ((Nat.totient B / B : ℝ) * Real.log x) + 4 * ((Nat.totient B : ℝ) + 1) := by ring

/-! ## The two genuine, non-vacuous transfer bounds

Both use an **explicit** additive constant that depends only on `W` (never on
`R`, `k`, or `T`), so the leading term grows with `R` while the constant stays
fixed: the bounds are genuinely non-vacuous.  They are the CRUDER-but-real
route (drop `fWt ≥ fWt(R₀)` for the lower, `fWt ≤ 1` for the upper), one
constant factor away from the frozen Abel-summation forms. -/

/-- **Genuine lower bound for `B₁`** (crude route, explicit constant).

`B₁ ≥ (1/(1+(log k)·T)) · ((φ(W)/W)·log R₀ − (φ(W)/W)·log W)`.

Leading term `(1/(1+(log k)·T))·(φ(W)/W)·log R₀`: the coefficient
`(φ(W)/W)/(1+(log k)·T)` is a positive constant in `R`, and `log R₀` grows
(≈ `(T/k)·log R`), so this is a real, growing-in-`R`, non-vacuous bound.  The
subtracted `(φ(W)/W)·log W` is a fixed `W`-only constant — it does not absorb
the main term.  Route: `B₁ = ∑' fWt/φ ≥ fWt(R₀)·∑' 1/φ = (1/(1+(log k)·T))·
phiAtomSum R₀ W`, then `phiAtomSum_lower_explicit`. -/
theorem B1_lower (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 1 ≤ k) (hR : 2 ≤ R)
    (hR0 : 2 ≤ R0 k R T) (hT : 0 ≤ T) :
    (1 / (1 + Real.log (k : ℝ) * T)) *
        ((Nat.totient W / W : ℝ) * Real.log (R0 k R T)
          - (Nat.totient W / W : ℝ) * Real.log W)
      ≤ B1 k R W T := by
  have hmin0 : 0 ≤ 1 / (1 + Real.log (k : ℝ) * T) := (inv_one_add_log_mul_pos (k := k) hT).le
  have hlow := phiAtomSum_lower_explicit W hW (R0 k R T) hR0
  calc (1 / (1 + Real.log (k : ℝ) * T)) *
          ((Nat.totient W / W : ℝ) * Real.log (R0 k R T)
            - (Nat.totient W / W : ℝ) * Real.log W)
      ≤ (1 / (1 + Real.log (k : ℝ) * T)) * phiAtomSum (R0 k R T) W :=
        mul_le_mul_of_nonneg_left hlow hmin0
    _ ≤ B1 k R W T := B1_ge_min_mul_phiAtom hk hR

/-- **Genuine upper bound for `A₁`** (crude route, explicit constant).

`A₁ ≤ 4·(φ(W)/W)·(T/k)·log R + 4·(φ(W)+1)`.

Leading term `4·(φ(W)/W)·(T/k)·log R`: coefficient constant in `R`, grows with
`R`.  The additive `4·(φ(W)+1)` is a fixed `W`-only constant, not an
existentially-chosen absorber.  Route: `A₁ = ∑' fWt²/φ ≤ ∑' 1/φ =
phiAtomSum R₀ W` (as `fWt ≤ 1`), then `phiAtomSum_upper_explicit`, then
`log R₀ ≤ (T/k)·log R`. -/
theorem A1_upper_real (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hR : 2 ≤ R)
    (hR0 : 2 ≤ R0 k R T) :
    A1 k R W T
      ≤ 4 * ((Nat.totient W / W : ℝ) * ((T / (k : ℝ)) * Real.log R))
          + 4 * ((Nat.totient W : ℝ) + 1) := by
  have hc0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := by positivity
  have hlog : Real.log (R0 k R T) ≤ (T / (k : ℝ)) * Real.log R := log_R0_le hR (by omega)
  have hstep : 4 * ((Nat.totient W / W : ℝ) * Real.log (R0 k R T))
      ≤ 4 * ((Nat.totient W / W : ℝ) * ((T / (k : ℝ)) * Real.log R)) := by
    have := mul_le_mul_of_nonneg_left hlog hc0; linarith
  calc A1 k R W T
      ≤ phiAtomSum (R0 k R T) W := A1_le_phiAtom hR
    _ ≤ 4 * ((Nat.totient W / W : ℝ) * Real.log (R0 k R T)) + 4 * ((Nat.totient W : ℝ) + 1) :=
        phiAtomSum_upper_explicit W hW (R0 k R T) hR0
    _ ≤ 4 * ((Nat.totient W / W : ℝ) * ((T / (k : ℝ)) * Real.log R))
          + 4 * ((Nat.totient W : ℝ) + 1) := by linarith

/-! ## What did NOT land: the exact-constant Abel transfer

-- PORT-BLOCKER: the frozen exact-leading-constant transfer bounds.
--
-- With `A := Real.log k`, the frozen targets (maynard.md N3.3) are, writing
-- `κ := (Nat.totient W / W) * (Real.log R / k)`:
--
--   B1_lower_exact :  κ * (Real.log (1 + A*T) / A)                 ≤ B1     -- ∫₀ᵀ g
--   A1_lower_exact :  κ * (T / (1 + A*T))                          ≤ A1     -- ∫₀ᵀ g²
--   A1_upper_exact :  A1     ≤ 4 * κ * (T / (1 + A*T))                       -- ∫₀ᵀ g²
--   A1_1_upper_exact: A1_1   ≤ 4 * κ * ((Real.log (1+A*T) - A*T/(1+A*T))/A^2)-- ∫₀ᵀ u·g²
--   A1_2_upper_exact: A1_2   ≤ 4 * κ * (T / A^2)                             -- ∫₀ᵀ u²·g²
--
-- i.e. each sum equals `(φ(W)/W)·(log R/k)` times the corresponding N6.1
-- integral (`integral_g`, `integral_g_sq`, `integral_u_g_sq`,
-- `integral_u_sq_g_sq_le`), up to lower-order `O(1)` and the `4×` atom loss.
--
-- What landed instead (this pass): the two GENUINE crude bounds `B1_lower`
-- (`(1/(1+A·T))·((φW/W)log R₀ − (φW/W)log W) ≤ B1`) and `A1_upper_real`
-- (`A1 ≤ 4·(φW/W)(T/k)log R + 4(φW+1)`), both with EXPLICIT `W`-only additive
-- constants (non-vacuous: the leading term grows in `R`, the constant does
-- not).  These replace the earlier `∃ C`-packaged "bounds", which were vacuous
-- (the outer `∃ C` let `C` absorb the whole main term).
--
-- The obstruction to the SHARP forms, precisely.  Getting the integral (not
-- merely its `T`-power envelope `∫₀ᵀ g^j·u^i ≤ T^{i+1}`, nor the single-point
-- crude drop used above) requires **Abel/partial summation** of the atom
-- increments `a(r) = μ²(r)·[(r,W)=1]/φ(r)` against the decreasing weight
-- `w(r) = fWt(r)^2·u(r)^i`.  With `S(t) := phiAtomSum (⌊t⌋+1) W`,
--
--   ∑_{r≤N} w(r) a(r) = w(N) S(N) − ∫₁^N S(t) w'(t) dt        (summation by parts)
--
-- and then `S(t) = (φ(W)/W) log t + O(1)` (N3.1 two-sided) makes the boundary
-- terms cancel, leaving `(φ(W)/W) ∫₁^N w(t) dt/t` which the substitution
-- `u = k log t/log R`, `dt/t = (log R/k) du` turns into
-- `(φ(W)/W)(log R/k) ∫₀ᵀ (profile) du` — the N6.1 closed forms.
--
-- Formalizing this needs: (a) a Stieltjes/Abel summation lemma over `Finset`
-- (`Finset.sum_Ioc_by_parts` exists but pairing it to a Riemann–Stieltjes
-- integral of a `C¹` weight is not in mathlib in usable form); (b) the
-- monotone `fWt`/`fWt²·uⁱ` derivative bookkeeping; (c) a Riemann-sum ↔
-- `intervalIntegral` comparison for `w(t)/t` against the N6.1 integrals.
-- Each is a substantial C-node; together they are the genuine content of the
-- SHARP N3.3 and remain out of scope for this pass.
-/

end Salt.Maynard
