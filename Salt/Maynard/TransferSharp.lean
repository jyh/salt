/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Transfer
import Salt.Maynard.PhiAtom

/-!
# N3.3-SHARP — exact-constant weighted transfers (Maynard track)

The sharp Abel-summation transfer bounds for the one-dimensional sums
`B1`, `A1`, `A1_1` of `Salt.Maynard.Transfer`, with the EXACT leading
constants (`1` on the lower bounds, `4` — the N3.1 atom loss — on the
uppers) and explicit, `R`-independent additive error terms.

Setup: with `B := bParam k R = k·log k/log R` and `s(t) := 1 + B·log t`,
the weight identity `fWt r = s(r)⁻¹` (`fWt_eq_g1F`) turns each sum into
an Abel sum of the coefficient `aW W r = μ²(r)·[(r,W)=1]·[r ≥ 2]/φ(r)`
against a smooth decreasing weight (`g₁ = s⁻¹` for `B1`, `g₂ = s⁻²` for
`A1`); mathlib's `sum_mul_eq_sub_integral_mul₁` plus the hand-computed
antiderivatives `G₁ = B⁻¹·log s`, `G₂ = −B⁻¹·s⁻¹` (of `g/t`) and the
N3.1 two-sided atom bounds give the four sharp bounds:

* `B1_lower_sharp` : `φW·B⁻¹·log s(R₀−1) − errB1 ≤ B1`
* `B1_upper_sharp` : `B1 ≤ 4·φW·B⁻¹·log s(R₀) + errA1`
* `A1_lower_sharp` : `φW·B⁻¹·(1 − s(R₀−1)⁻¹) − errB1 ≤ A1`
* `A1_upper_sharp` : `A1 ≤ 4·φW·B⁻¹·(1 − s(R₀)⁻¹) + (boundary) + errA1`

with `φW = φ(W)/W` and the EXPLICIT constants
`errB1 k W = φW·(log 2 + log W)`,
`errA1 k W = 1 + 8·φW·log 2 + 4·(φ(W)+1)` — both independent of `R`
(and of `T`); only `R`-independence matters downstream.

Additionally `A1_1_upper_split` : `A1_1 ≤ (log k)⁻¹·(A1 + B1)`, the
pointwise split bound that replaces the frozen sharp `A1_1` upper (it is
consumed identically by the downstream `c = A1_1/A1 ≤ 3/4` mean-check).

The Abel-summation + FTC + `setIntegral_mono_on` idiom follows
`Salt.Maynard.Mertens` (N3.2) step for step.
-/

open Finset MeasureTheory intervalIntegral

namespace Salt.Maynard

/-! ## The `B`-parameter and the substituted weights -/

/-- `B = k·log k/log R`; with `s(t) = 1 + B·log t` one has `fWt r = s(r)⁻¹`. -/
noncomputable def bParam (k R : ℕ) : ℝ := (k : ℝ) * Real.log k / Real.log R

/-- `s(t) = 1 + B·log t` (so `fWt r = s(r)⁻¹`, see `fWt_eq_g1F`). -/
noncomputable def sF (k R : ℕ) (t : ℝ) : ℝ := 1 + bParam k R * Real.log t

/-- `g₁ = s⁻¹`, the Abel weight of `B1`. -/
noncomputable def g1F (k R : ℕ) (t : ℝ) : ℝ := (sF k R t)⁻¹

/-- `g₂ = s⁻²`, the Abel weight of `A1`. -/
noncomputable def g2F (k R : ℕ) (t : ℝ) : ℝ := (sF k R t)⁻¹ ^ 2

/-- `g₁' = −(B/t)·s⁻²`. -/
noncomputable def g1D (k R : ℕ) (t : ℝ) : ℝ := -(bParam k R / t) * (sF k R t)⁻¹ ^ 2

/-- `g₂' = −(2B/t)·s⁻³`. -/
noncomputable def g2D (k R : ℕ) (t : ℝ) : ℝ :=
  -(2 * bParam k R / t) * (sF k R t)⁻¹ ^ 3

/-- Antiderivative of `g₁(t)/t`: `G₁ = B⁻¹·log s`. -/
noncomputable def G1F (k R : ℕ) (t : ℝ) : ℝ := (bParam k R)⁻¹ * Real.log (sF k R t)

/-- Antiderivative of `g₂(t)/t`: `G₂ = −B⁻¹·s⁻¹`. -/
noncomputable def G2F (k R : ℕ) (t : ℝ) : ℝ := -((bParam k R)⁻¹ * (sF k R t)⁻¹)

/-- The explicit `R`-free error constant of the two sharp LOWER bounds. -/
noncomputable def errB1 (_k W : ℕ) : ℝ :=
  (Nat.totient W / W : ℝ) * (Real.log 2 + Real.log W)

/-- The explicit `R`-free error constant of the two sharp UPPER bounds. -/
noncomputable def errA1 (_k W : ℕ) : ℝ :=
  1 + 8 * (Nat.totient W / W : ℝ) * Real.log 2 + 4 * ((Nat.totient W : ℝ) + 1)

lemma bParam_pos {k R : ℕ} (hk : 2 ≤ k) (hR : 2 ≤ R) : 0 < bParam k R := by
  have h1 : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have h2 : 0 < Real.log R := Real.log_pos (by exact_mod_cast (by omega : 1 < R))
  have h3 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  unfold bParam
  positivity

/-- **Fact 0 (bridge).** The profile weight in the `B`-variable:
`fWt r = (1 + B·log r)⁻¹`, unconditionally. -/
lemma fWt_eq_g1F (k R r : ℕ) : fWt k R r = g1F k R r := by
  unfold fWt g1F sF bParam uVal
  rw [one_div]
  congr 1
  ring

lemma fWt_sq_eq_g2F (k R r : ℕ) : fWt k R r ^ 2 = g2F k R r := by
  rw [fWt_eq_g1F]; rfl

lemma one_le_sF {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ sF k R t := by
  have h := mul_nonneg hB (Real.log_nonneg ht)
  unfold sF
  linarith

lemma sF_pos {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    0 < sF k R t :=
  lt_of_lt_of_le one_pos (one_le_sF hB ht)

lemma g1F_nonneg {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ g1F k R t := by
  have := sF_pos hB ht
  unfold g1F
  positivity

lemma g1F_le_one {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    g1F k R t ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_sF hB ht)

lemma g2F_nonneg (k R : ℕ) (t : ℝ) : 0 ≤ g2F k R t := by
  unfold g2F
  positivity

lemma g2F_le_one {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    g2F k R t ≤ 1 := by
  have h0 := g1F_nonneg hB ht
  have h1 := g1F_le_one hB ht
  unfold g2F
  unfold g1F at h0 h1
  nlinarith

/-! ## P4 — the pointwise split bound for `A1_1`

For every `r` in the support, `u·fWt² ≤ (log k)⁻¹·(fWt² + fWt)`: with
`a := (log k)·u` and `d := 1 + a` this is `a/d² ≤ (1 + d)/d²`, i.e.
`a ≤ 2 + a`.  Summing termwise gives the split bound; no Abel summation
is needed.  Downstream this replaces the frozen "`A1⁽¹⁾ ≤ 4×` integral"
statement (equivalent strength for the `c = A1_1/A1 ≤ 3/4` mean-check;
freeze amendment recorded by the driver). -/

/-- **P4.** `A1_1 ≤ (log k)⁻¹·(A1 + B1)` — the pointwise split bound. -/
theorem A1_1_upper_split (k R W : ℕ) (T : ℝ) (hk : 3 ≤ k) (hR : 2 ≤ R) :
    A1_1 k R W T ≤ (Real.log k)⁻¹ * (A1 k R W T + B1 k R W T) := by
  have hA : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  unfold A1_1 A1 B1
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hmem
  obtain ⟨hr, hφ⟩ := mem_support hmem
  have hu : 0 ≤ uVal k R r := uVal_nonneg hr hR
  have hd1 : 1 ≤ 1 + Real.log (k : ℝ) * uVal k R r := fWt_denom_pos hr hR
  -- pointwise: `log k · (fWt²·u) ≤ fWt² + fWt`
  have hkey : Real.log (k : ℝ) * (fWt k R r ^ 2 * uVal k R r)
      ≤ fWt k R r ^ 2 + fWt k R r := by
    unfold fWt
    set d : ℝ := 1 + Real.log (k : ℝ) * uVal k R r with hd
    have hd0 : (0 : ℝ) < d := by linarith
    have e1 : Real.log (k : ℝ) * ((1 / d) ^ 2 * uVal k R r) = (d - 1) / d ^ 2 := by
      have : Real.log (k : ℝ) * uVal k R r = d - 1 := by rw [hd]; ring
      rw [← this]
      field_simp
    have e2 : (1 / d) ^ 2 + 1 / d = (1 + d) / d ^ 2 := by
      field_simp
    rw [e1, e2]
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by linarith)
  -- divide by `φ(r)` and pull out `(log k)⁻¹`
  have h3 : fWt k R r ^ 2 * uVal k R r
      ≤ (Real.log (k : ℝ))⁻¹ * (fWt k R r ^ 2 + fWt k R r) := by
    rw [inv_mul_eq_div, le_div_iff₀ hA, mul_comm]
    exact hkey
  calc fWt k R r ^ 2 * uVal k R r / (Nat.totient r : ℝ)
      ≤ (Real.log (k : ℝ))⁻¹ * (fWt k R r ^ 2 + fWt k R r) / (Nat.totient r : ℝ) :=
        (div_le_div_iff_of_pos_right hφ).mpr h3
    _ = (Real.log (k : ℝ))⁻¹
          * (fWt k R r ^ 2 / (Nat.totient r : ℝ) + fWt k R r / (Nat.totient r : ℝ)) := by
        ring

/-! ## The derivative kit for `g₁`, `g₂` and their antiderivatives

All statements live on `t ≥ 1` (where `s(t) ≥ 1 > 0` for `B ≥ 0`);
trap 2 of the node brief: `s` has a zero at `t = exp(−1/B) ∈ (0,1)`,
so nothing here may wander below `1`. -/

lemma hasDerivAt_sF (k R : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (sF k R) (bParam k R / t) t := by
  have h := ((Real.hasDerivAt_log ht).const_mul (bParam k R)).const_add 1
  rwa [div_eq_mul_inv]

lemma hasDerivAt_g1F {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (g1F k R) (g1D k R t) t := by
  have ht0 : t ≠ 0 := by positivity
  have hsne : sF k R t ≠ 0 := (sF_pos hB ht).ne'
  have h := (hasDerivAt_sF k R ht0).inv hsne
  have hval : -(bParam k R / t) / sF k R t ^ 2 = g1D k R t := by
    unfold g1D
    rw [div_eq_mul_inv, inv_pow]
  rw [hval] at h
  exact h

lemma hasDerivAt_g2F {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (g2F k R) (g2D k R t) t := by
  have h := (hasDerivAt_g1F hB ht).pow 2
  have hval : (2 : ℕ) * g1F k R t ^ (2 - 1) * g1D k R t = g2D k R t := by
    unfold g1F g1D g2D
    ring
  rw [hval] at h
  exact h

lemma hasDerivAt_G1F {k R : ℕ} (hB : 0 < bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (G1F k R) (g1F k R t / t) t := by
  have ht0 : t ≠ 0 := by positivity
  have hsne : sF k R t ≠ 0 := (sF_pos hB.le ht).ne'
  have h := ((Real.hasDerivAt_log hsne).comp t (hasDerivAt_sF k R ht0)).const_mul
    (bParam k R)⁻¹
  have hval : (bParam k R)⁻¹ * ((sF k R t)⁻¹ * (bParam k R / t)) = g1F k R t / t := by
    unfold g1F
    field_simp
  rw [hval] at h
  exact h

lemma hasDerivAt_G2F {k R : ℕ} (hB : 0 < bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt (G2F k R) (g2F k R t / t) t := by
  have h := ((hasDerivAt_g1F hB.le ht).const_mul (bParam k R)⁻¹).neg
  have hval : -((bParam k R)⁻¹ * g1D k R t) = g2F k R t / t := by
    have ht0 : t ≠ 0 := by positivity
    unfold g1D g2F
    field_simp
  rw [hval] at h
  exact h

lemma continuousOn_sF (k R : ℕ) {s : Set ℝ} (hs : ∀ t ∈ s, t ≠ 0) :
    ContinuousOn (sF k R) s :=
  continuousOn_const.add (continuousOn_const.mul (continuousOn_id.log hs))

lemma continuousOn_g1D {k R : ℕ} (hB : 0 ≤ bParam k R) {b : ℝ} :
    ContinuousOn (g1D k R) (Set.Icc 1 b) := by
  have hne0 : ∀ t ∈ Set.Icc (1 : ℝ) b, t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    linarith [ht.1]
  have hsne : ∀ t ∈ Set.Icc (1 : ℝ) b, sF k R t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact (sF_pos hB ht.1).ne'
  exact ((continuousOn_const.div continuousOn_id hne0).neg).mul
    (((continuousOn_sF k R hne0).inv₀ hsne).pow 2)

lemma continuousOn_g2D {k R : ℕ} (hB : 0 ≤ bParam k R) {b : ℝ} :
    ContinuousOn (g2D k R) (Set.Icc 1 b) := by
  have hne0 : ∀ t ∈ Set.Icc (1 : ℝ) b, t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    linarith [ht.1]
  have hsne : ∀ t ∈ Set.Icc (1 : ℝ) b, sF k R t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact (sF_pos hB ht.1).ne'
  exact ((continuousOn_const.div continuousOn_id hne0).neg).mul
    (((continuousOn_sF k R hne0).inv₀ hsne).pow 3)

lemma g1D_nonpos {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    g1D k R t ≤ 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h : 0 ≤ bParam k R / t * (sF k R t)⁻¹ ^ 2 := by positivity
  unfold g1D
  linarith

lemma g2D_nonpos {k R : ℕ} (hB : 0 ≤ bParam k R) {t : ℝ} (ht : 1 ≤ t) :
    g2D k R t ≤ 0 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have h : 0 ≤ 2 * bParam k R / t * (sF k R t)⁻¹ ^ 3 := by
    have hs := (sF_pos hB ht).le
    positivity
  unfold g2D
  linarith

/-! ## Fact 1 — the universal by-parts evaluation

For any weight `w` with derivative `w'` and antiderivative `G` of
`w(t)/t` on `[a, b] ⊆ [1, ∞)`, and any constants `c₁ c₂`, the function
`F(t) = c₁·(G(t) − w(t)·log t) + c₂·w(t)` has derivative
`(−w'(t))·(c₁·log t − c₂)`, so the by-parts integral evaluates to
`F(b) − F(a)` by FTC.  Proved once; instantiated for `g₁` and `g₂`. -/

theorem byparts_transfer {w w' G : ℝ → ℝ} {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hw : ∀ t ∈ Set.Icc a b, HasDerivAt w (w' t) t)
    (hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (w t / t) t)
    (hw'c : ContinuousOn w' (Set.Icc a b)) (c₁ c₂ : ℝ) :
    ∫ t in a..b, -w' t * (c₁ * Real.log t - c₂)
      = (c₁ * (G b - w b * Real.log b) + c₂ * w b)
        - (c₁ * (G a - w a * Real.log a) + c₂ * w a) := by
  have hne0 : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    linarith [ht.1]
  -- the closed-form antiderivative
  have hF : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t => c₁ * (G t - w t * Real.log t) + c₂ * w t)
        (-w' t * (c₁ * Real.log t - c₂)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := hne0 t ht
    have h1 : HasDerivAt (fun t => w t * Real.log t)
        (w' t * Real.log t + w t * t⁻¹) t :=
      (hw t ht).mul (Real.hasDerivAt_log ht0)
    have h2 := (((hG t ht).sub h1).const_mul c₁).add ((hw t ht).const_mul c₂)
    have hval : c₁ * (w t / t - (w' t * Real.log t + w t * t⁻¹)) + c₂ * w' t
        = -w' t * (c₁ * Real.log t - c₂) := by
      rw [div_eq_mul_inv]
      ring
    rwa [hval] at h2
  -- integrability of the integrand
  have hcont : ContinuousOn (fun t => -w' t * (c₁ * Real.log t - c₂))
      (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact (hw'c.neg).mul
      ((continuousOn_const.mul (continuousOn_id.log hne0)).sub continuousOn_const)
  exact integral_eq_sub_of_hasDerivAt hF hcont.intervalIntegrable

/-! ## Fact 2/3 — the Abel coefficient `aW` and the sum bridges

`aW W r` is the `μ²/φ` atom increment with the `r ∈ {0, 1}` terms
removed (trap 1: `sum_mul_eq_sub_integral_mul₁` requires
`c 0 = c 1 = 0`); the excluded `r = 1` term of each original sum is the
explicit `+ 1` in the bridges. -/

/-- The Abel coefficient: `aW W r = μ²(r)·[(r,W)=1]·[r ≥ 2]/φ(r)`. -/
noncomputable def aW (W r : ℕ) : ℝ :=
  if 2 ≤ r ∧ Squarefree r ∧ Nat.Coprime r W then 1 / (Nat.totient r : ℝ) else 0

lemma aW_zero (W : ℕ) : aW W 0 = 0 := by simp [aW]

lemma aW_one (W : ℕ) : aW W 1 = 0 := by simp [aW]

/-- Generic bridge: an `aW`-weighted sum over `Icc 0 (X−1)` is the
corresponding `sqfCop`-sum minus its `r = 1` term. -/
lemma sum_mul_aW_eq (W X : ℕ) (hX : 2 ≤ X) (f : ℝ → ℝ) :
    ∑ r ∈ Finset.Icc 0 (X - 1), f r * aW W r
      = (∑ r ∈ sqfCop X W, f r / (Nat.totient r : ℝ)) - f 1 := by
  have hIcc : Finset.Icc 0 (X - 1) = Finset.range X := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  have h1mem : 1 ∈ sqfCop X W := by
    rw [sqfCop, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, squarefree_one, Nat.coprime_one_left W⟩
  have herase : (Finset.range X).filter
        (fun r => 2 ≤ r ∧ Squarefree r ∧ Nat.Coprime r W)
      = (sqfCop X W).erase 1 := by
    ext r
    rw [sqfCop]
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨hlt, h2, hsq, hcop⟩
      exact ⟨by omega, hlt, hsq, hcop⟩
    · rintro ⟨hne, hlt, hsq, hcop⟩
      have h0 : r ≠ 0 := hsq.ne_zero
      exact ⟨hlt, by omega, hsq, hcop⟩
  have hsum : ∑ r ∈ Finset.range X, f r * aW W r
      = ∑ r ∈ (Finset.range X).filter
          (fun r => 2 ≤ r ∧ Squarefree r ∧ Nat.Coprime r W),
            f r / (Nat.totient r : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r _
    simp only [aW]
    split_ifs with h
    · rw [mul_one_div]
    · rw [mul_zero]
  rw [hIcc, hsum, herase, Finset.sum_erase_eq_sub h1mem, Nat.totient_one,
    Nat.cast_one, div_one]

/-- **Fact 3 (bridge for `B1`).** -/
lemma B1_bridge (k R W : ℕ) (T : ℝ) (hX : 2 ≤ R0 k R T) :
    B1 k R W T
      = (∑ r ∈ Finset.Icc 0 (R0 k R T - 1), g1F k R r * aW W r) + 1 := by
  rw [sum_mul_aW_eq W (R0 k R T) hX (g1F k R)]
  have hsum : ∑ r ∈ sqfCop (R0 k R T) W, g1F k R r / (Nat.totient r : ℝ)
      = B1 k R W T := by
    unfold B1
    exact Finset.sum_congr rfl (fun r _ => by rw [← fWt_eq_g1F])
  have h1 : g1F k R (1 : ℝ) = 1 := by
    simp [g1F, sF, Real.log_one]
  rw [hsum, h1]
  ring

/-- **Fact 3 (bridge for `A1`).** -/
lemma A1_bridge (k R W : ℕ) (T : ℝ) (hX : 2 ≤ R0 k R T) :
    A1 k R W T
      = (∑ r ∈ Finset.Icc 0 (R0 k R T - 1), g2F k R r * aW W r) + 1 := by
  rw [sum_mul_aW_eq W (R0 k R T) hX (g2F k R)]
  have hsum : ∑ r ∈ sqfCop (R0 k R T) W, g2F k R r / (Nat.totient r : ℝ)
      = A1 k R W T := by
    unfold A1
    exact Finset.sum_congr rfl (fun r _ => by rw [← fWt_sq_eq_g2F])
  have h1 : g2F k R (1 : ℝ) = 1 := by
    simp [g2F, sF, Real.log_one]
  rw [hsum, h1]
  ring

/-! ## Fact 4 — the two-sided bounds on the `aW` partial sums -/

/-- The `aW` partial sum is the atom sum at `n + 1` minus its `r = 1` term. -/
lemma sum_aW_eq_phiAtomSum (W n : ℕ) (hn : 1 ≤ n) :
    ∑ r ∈ Finset.Icc 0 n, aW W r = phiAtomSum (n + 1) W - 1 := by
  have h := sum_mul_aW_eq W (n + 1) (by omega) (fun _ => (1 : ℝ))
  simp only [one_mul, Nat.add_sub_cancel] at h
  rw [h]
  rfl

/-- Lower bound on the `aW` partial sums, in the `log t` form used inside
the Abel integral (trap 6: `t < ⌊t⌋₊ + 1` gives the lower direction). -/
lemma sum_aW_floor_lower (W : ℕ) (hW : W ≠ 0) {t : ℝ} (ht : 2 ≤ t) :
    (Nat.totient W / W : ℝ) * Real.log t
        - ((Nat.totient W / W : ℝ) * Real.log W + 1)
      ≤ ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hfl : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  rw [sum_aW_eq_phiAtomSum W ⌊t⌋₊ (by omega)]
  have hlow := phiAtomSum_lower_explicit W hW (⌊t⌋₊ + 1) (by omega)
  have hcast : ((⌊t⌋₊ + 1 : ℕ) : ℝ) = (⌊t⌋₊ : ℝ) + 1 := by push_cast; ring
  have hlog : Real.log t ≤ Real.log ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    rw [hcast]
    exact Real.log_le_log ht0 (Nat.lt_floor_add_one t).le
  have hφ0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := by positivity
  linarith [hlow, mul_le_mul_of_nonneg_left hlog hφ0]

/-- Upper bound on the `aW` partial sums, in the `log t + log 2` form used
inside the Abel integral (trap 6: `⌊t⌋₊ + 1 ≤ 2t` gives the upper). -/
lemma sum_aW_floor_upper (W : ℕ) (hW : W ≠ 0) {t : ℝ} (ht : 2 ≤ t) :
    ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r
      ≤ 4 * (Nat.totient W / W : ℝ) * (Real.log t + Real.log 2)
        + 4 * ((Nat.totient W : ℝ) + 1) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hfl : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  rw [sum_aW_eq_phiAtomSum W ⌊t⌋₊ (by omega)]
  have hup := phiAtomSum_upper_explicit W hW (⌊t⌋₊ + 1) (by omega)
  have hcast : ((⌊t⌋₊ + 1 : ℕ) : ℝ) = (⌊t⌋₊ : ℝ) + 1 := by push_cast; ring
  have hle2t : ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * t := by
    rw [hcast]
    have := Nat.floor_le ht0.le
    linarith
  have hpos : (0 : ℝ) < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos ⌊t⌋₊
  have hlog : Real.log ((⌊t⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log 2 + Real.log t :=
    calc Real.log ((⌊t⌋₊ + 1 : ℕ) : ℝ)
        ≤ Real.log (2 * t) := Real.log_le_log hpos hle2t
      _ = Real.log 2 + Real.log t := Real.log_mul two_ne_zero ht0.ne'
  have hφ0 : (0 : ℝ) ≤ 4 * (Nat.totient W / W : ℝ) := by positivity
  linarith [hup, mul_le_mul_of_nonneg_left hlog hφ0]

/-! ## Fact 2 — the Abel-summation core

`abel_aW_eq` is mathlib's `sum_mul_eq_sub_integral_mul₁` specialised to
`aW`; `abel_aW_lower`/`abel_aW_upper` substitute the Fact-4 bound for
the partial sum under the integral (`setIntegral_mono_on`, both sides
integrable — trap 5) and evaluate by `byparts_transfer`. -/

lemma abel_aW_eq (W N : ℕ) (w w' : ℝ → ℝ)
    (hw : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), HasDerivAt w (w' t) t)
    (hw'c : ContinuousOn w' (Set.Icc (2 : ℝ) (N : ℝ))) :
    ∑ r ∈ Finset.Icc 0 N, w r * aW W r
      = w N * (∑ r ∈ Finset.Icc 0 N, aW W r)
        - ∫ t in Set.Ioc 2 (N : ℝ), w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), DifferentiableAt ℝ w t :=
    fun t ht => (hw t ht).differentiableAt
  have hderiv_eq : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), deriv w t = w' t :=
    fun t ht => (hw t ht).deriv
  have hint : IntegrableOn (deriv w) (Set.Icc 2 (N : ℝ)) := by
    apply (hw'c.integrableOn_compact isCompact_Icc).congr_fun _ measurableSet_Icc
    intro t ht
    exact (hderiv_eq t ht).symm
  have habel := sum_mul_eq_sub_integral_mul₁ (aW W) (aW_zero W) (aW_one W) (N : ℝ)
    hdiff hint
  rw [Nat.floor_natCast] at habel
  rw [habel]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  simp only
  rw [hderiv_eq t (Set.Ioc_subset_Icc_self ht)]

lemma abel_aW_lower (W N : ℕ) (hN : 2 ≤ N) (w w' G : ℝ → ℝ) (c₁ c₂ : ℝ)
    (hw : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), HasDerivAt w (w' t) t)
    (hG : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), HasDerivAt G (w t / t) t)
    (hw'c : ContinuousOn w' (Set.Icc (2 : ℝ) (N : ℝ)))
    (hw'neg : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), w' t ≤ 0)
    (hΦ : ∀ t ∈ Set.Ioc (2 : ℝ) (N : ℝ),
      c₁ * Real.log t - c₂ ≤ ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r) :
    w N * (∑ r ∈ Finset.Icc 0 N, aW W r)
      + ((c₁ * (G N - w N * Real.log N) + c₂ * w N)
        - (c₁ * (G 2 - w 2 * Real.log 2) + c₂ * w 2))
      ≤ ∑ r ∈ Finset.Icc 0 N, w r * aW W r := by
  have hle : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have heq := abel_aW_eq W N w w' hw hw'c
  have hbp := byparts_transfer (a := 2) (b := (N : ℝ)) one_le_two hle hw hG hw'c c₁ c₂
  rw [intervalIntegral.integral_of_le hle] at hbp
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    linarith [ht.1]
  have hint1 : IntegrableOn (fun t => -w' t * (c₁ * Real.log t - c₂))
      (Set.Ioc 2 (N : ℝ)) := by
    have hcont : ContinuousOn (fun t => -w' t * (c₁ * Real.log t - c₂))
        (Set.Icc 2 (N : ℝ)) :=
      (hw'c.neg).mul
        ((continuousOn_const.mul (continuousOn_id.log hne0)).sub continuousOn_const)
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn
      (fun t => -(w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r)) (Set.Ioc 2 (N : ℝ)) :=
    ((integrableOn_mul_sum_Icc (aW W) (m := 0) (by norm_num)
      (hw'c.integrableOn_compact isCompact_Icc)).mono_set
        Set.Ioc_subset_Icc_self).neg
  have hmono : (∫ t in Set.Ioc 2 (N : ℝ), -w' t * (c₁ * Real.log t - c₂))
      ≤ ∫ t in Set.Ioc 2 (N : ℝ), -(w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r) := by
    refine setIntegral_mono_on hint1 hint2 measurableSet_Ioc ?_
    intro t ht
    have hneg : 0 ≤ -w' t := by
      have := hw'neg t (Set.Ioc_subset_Icc_self ht)
      linarith
    linarith [mul_le_mul_of_nonneg_left (hΦ t ht) hneg]
  rw [MeasureTheory.integral_neg] at hmono
  have hfinal : (c₁ * (G N - w N * Real.log N) + c₂ * w N)
        - (c₁ * (G 2 - w 2 * Real.log 2) + c₂ * w 2)
      ≤ -∫ t in Set.Ioc 2 (N : ℝ), w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r := by
    rw [← hbp]
    exact hmono
  rw [heq]
  linarith [hfinal]

lemma abel_aW_upper (W N : ℕ) (hN : 2 ≤ N) (w w' G : ℝ → ℝ) (c₁ c₂ : ℝ)
    (hw : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), HasDerivAt w (w' t) t)
    (hG : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), HasDerivAt G (w t / t) t)
    (hw'c : ContinuousOn w' (Set.Icc (2 : ℝ) (N : ℝ)))
    (hw'neg : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), w' t ≤ 0)
    (hΦ : ∀ t ∈ Set.Ioc (2 : ℝ) (N : ℝ),
      (∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r) ≤ c₁ * Real.log t - c₂) :
    ∑ r ∈ Finset.Icc 0 N, w r * aW W r
      ≤ w N * (∑ r ∈ Finset.Icc 0 N, aW W r)
        + ((c₁ * (G N - w N * Real.log N) + c₂ * w N)
          - (c₁ * (G 2 - w 2 * Real.log 2) + c₂ * w 2)) := by
  have hle : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have heq := abel_aW_eq W N w w' hw hw'c
  have hbp := byparts_transfer (a := 2) (b := (N : ℝ)) one_le_two hle hw hG hw'c c₁ c₂
  rw [intervalIntegral.integral_of_le hle] at hbp
  have hne0 : ∀ t ∈ Set.Icc (2 : ℝ) (N : ℝ), t ≠ 0 := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    linarith [ht.1]
  have hint1 : IntegrableOn (fun t => -w' t * (c₁ * Real.log t - c₂))
      (Set.Ioc 2 (N : ℝ)) := by
    have hcont : ContinuousOn (fun t => -w' t * (c₁ * Real.log t - c₂))
        (Set.Icc 2 (N : ℝ)) :=
      (hw'c.neg).mul
        ((continuousOn_const.mul (continuousOn_id.log hne0)).sub continuousOn_const)
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hint2 : IntegrableOn
      (fun t => -(w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r)) (Set.Ioc 2 (N : ℝ)) :=
    ((integrableOn_mul_sum_Icc (aW W) (m := 0) (by norm_num)
      (hw'c.integrableOn_compact isCompact_Icc)).mono_set
        Set.Ioc_subset_Icc_self).neg
  have hmono : (∫ t in Set.Ioc 2 (N : ℝ), -(w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r))
      ≤ ∫ t in Set.Ioc 2 (N : ℝ), -w' t * (c₁ * Real.log t - c₂) := by
    refine setIntegral_mono_on hint2 hint1 measurableSet_Ioc ?_
    intro t ht
    have hneg : 0 ≤ -w' t := by
      have := hw'neg t (Set.Ioc_subset_Icc_self ht)
      linarith
    linarith [mul_le_mul_of_nonneg_left (hΦ t ht) hneg]
  rw [MeasureTheory.integral_neg] at hmono
  have hfinal : -(∫ t in Set.Ioc 2 (N : ℝ), w' t * ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r)
      ≤ (c₁ * (G N - w N * Real.log N) + c₂ * w N)
        - (c₁ * (G 2 - w 2 * Real.log 2) + c₂ * w 2) := by
    rw [← hbp]
    exact hmono
  rw [heq]
  linarith [hfinal]

/-! ## Boundary-at-2 bounds

The `t = 2` ends of the by-parts evaluations, bounded by `R`-free
quantities: `B⁻¹·log s(2) ≤ log 2` and `B⁻¹·(1 − s(2)⁻¹) ≤ log 2`
(both via `log(1+x) ≤ x`-type inequalities at `x = B·log 2`). -/

lemma inv_mul_log_sF_two_le {k R : ℕ} (hB : 0 < bParam k R) :
    (bParam k R)⁻¹ * Real.log (sF k R 2) ≤ Real.log 2 := by
  have hs2pos : (0 : ℝ) < sF k R 2 := sF_pos hB.le one_le_two
  have h1 : Real.log (sF k R 2) ≤ bParam k R * Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos hs2pos
    have h2 : sF k R 2 - 1 = bParam k R * Real.log 2 := by
      unfold sF
      ring
    linarith
  calc (bParam k R)⁻¹ * Real.log (sF k R 2)
      ≤ (bParam k R)⁻¹ * (bParam k R * Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hB.le)
    _ = Real.log 2 := by field_simp

lemma inv_mul_one_sub_inv_sF_two_le {k R : ℕ} (hB : 0 < bParam k R) :
    (bParam k R)⁻¹ * (1 - (sF k R 2)⁻¹) ≤ Real.log 2 := by
  have hs2 : 1 ≤ sF k R 2 := one_le_sF hB.le one_le_two
  have hs2pos : (0 : ℝ) < sF k R 2 := by linarith
  have hinv : sF k R 2 * (sF k R 2)⁻¹ = 1 := mul_inv_cancel₀ hs2pos.ne'
  have h1 : 1 - (sF k R 2)⁻¹ ≤ bParam k R * Real.log 2 := by
    have h2 : 1 - (sF k R 2)⁻¹ ≤ sF k R 2 - 1 := by
      nlinarith [sq_nonneg (sF k R 2 - 1)]
    have h3 : sF k R 2 - 1 = bParam k R * Real.log 2 := by
      unfold sF
      ring
    linarith
  calc (bParam k R)⁻¹ * (1 - (sF k R 2)⁻¹)
      ≤ (bParam k R)⁻¹ * (bParam k R * Real.log 2) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hB.le)
    _ = Real.log 2 := by field_simp

/-! ## P1 — the sharp lower bound for `B1` -/

/-- **P1 (`B1_lower_sharp`).**  Exact-leading-constant lower bound
`φW·B⁻¹·log s(R₀−1) − errB1 ≤ B1`, with `s(t) = 1 + B·log t`,
`B = k·log k/log R`, and the explicit `R`-free error
`errB1 k W = (φ(W)/W)·(log 2 + log W)`. -/
theorem B1_lower_sharp (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 3 ≤ k)
    (hR : 2 ≤ R) (_hT : 1 ≤ T) (hX : 4 ≤ R0 k R T) :
    (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
        * Real.log (1 + bParam k R * Real.log (R0 k R T - 1))
      - errB1 k W ≤ B1 k R W T := by
  have hB : 0 < bParam k R := bParam_pos (by omega) hR
  have hB0 : 0 ≤ bParam k R := hB.le
  have hN2 : 2 ≤ R0 k R T - 1 := by omega
  have hNr : (2 : ℝ) ≤ ((R0 k R T - 1 : ℕ) : ℝ) := by exact_mod_cast hN2
  have hcastN : ((R0 k R T - 1 : ℕ) : ℝ) = (R0 k R T : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← hcastN, B1_bridge k R W T (by omega)]
  -- the Abel kit for `g₁` on `[2, N]`
  have hw : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (g1F k R) (g1D k R t) t :=
    fun t ht => hasDerivAt_g1F hB0 (le_trans one_le_two ht.1)
  have hG : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (G1F k R) (g1F k R t / t) t :=
    fun t ht => hasDerivAt_G1F hB (le_trans one_le_two ht.1)
  have hw'c : ContinuousOn (g1D k R) (Set.Icc 2 ((R0 k R T - 1 : ℕ) : ℝ)) :=
    (continuousOn_g1D hB0).mono (Set.Icc_subset_Icc_left one_le_two)
  have hw'neg : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ), g1D k R t ≤ 0 :=
    fun t ht => g1D_nonpos hB0 (le_trans one_le_two ht.1)
  have hΦ : ∀ t ∈ Set.Ioc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      (Nat.totient W / W : ℝ) * Real.log t
          - ((Nat.totient W / W : ℝ) * Real.log W + 1)
        ≤ ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r :=
    fun t ht => sum_aW_floor_lower W hW (le_of_lt ht.1)
  have hcore := abel_aW_lower W (R0 k R T - 1) hN2 (g1F k R) (g1D k R) (G1F k R)
    ((Nat.totient W / W : ℝ)) ((Nat.totient W / W : ℝ) * Real.log W + 1)
    hw hG hw'c hw'neg hΦ
  -- boundary term: substitute the Fact-4 lower bound at `t = N`
  have hSN := sum_aW_floor_lower W hW (t := ((R0 k R T - 1 : ℕ) : ℝ)) hNr
  rw [Nat.floor_natCast] at hSN
  have hg1N0 : 0 ≤ g1F k R ((R0 k R T - 1 : ℕ) : ℝ) :=
    g1F_nonneg hB0 (by linarith)
  have hbdry := mul_le_mul_of_nonneg_left hSN hg1N0
  -- `t = 2` boundary pieces, all `R`-free
  have hφ0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := by positivity
  have hg120 : 0 ≤ g1F k R 2 := g1F_nonneg hB0 one_le_two
  have hg121 : g1F k R 2 ≤ 1 := g1F_le_one hB0 one_le_two
  have hlogW : 0 ≤ Real.log (W : ℝ) := Real.log_natCast_nonneg W
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hclo0 : 0 ≤ (Nat.totient W / W : ℝ) * Real.log W + 1 := by positivity
  have hclog12 : ((Nat.totient W / W : ℝ) * Real.log W + 1) * g1F k R 2
      ≤ (Nat.totient W / W : ℝ) * Real.log W + 1 :=
    mul_le_of_le_one_right hclo0 hg121
  have hprod0 : 0 ≤ (Nat.totient W / W : ℝ) * (g1F k R 2 * Real.log 2) :=
    mul_nonneg hφ0 (mul_nonneg hg120 hlog2)
  have hs2' := mul_le_mul_of_nonneg_left (inv_mul_log_sF_two_le hB) hφ0
  -- expose the `log s` atoms and assemble
  simp only [G1F, sF] at hcore
  simp only [sF] at hs2'
  simp only [errB1]
  linarith [hcore, hbdry, hs2', hclog12, hprod0]

/-! ## P5 — the sharp upper bound for `B1` -/

/-- **P5 (`B1_upper_sharp`).**  Exact-leading-constant upper bound
`B1 ≤ 4·φW·B⁻¹·log s(R₀) + errA1` with the explicit `R`-free error
`errA1 k W = 1 + 8·(φ(W)/W)·log 2 + 4·(φ(W)+1)` (the constant `4` is
the N3.1 atom loss).  No `R`-damped boundary term is needed: the
boundary cancels against the by-parts endpoint exactly. -/
theorem B1_upper_sharp (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 3 ≤ k)
    (hR : 2 ≤ R) (_hT : 1 ≤ T) (hX : 4 ≤ R0 k R T) :
    B1 k R W T
      ≤ 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
            * Real.log (1 + bParam k R * Real.log (R0 k R T))
        + errA1 k W := by
  have hB : 0 < bParam k R := bParam_pos (by omega) hR
  have hB0 : 0 ≤ bParam k R := hB.le
  have hN2 : 2 ≤ R0 k R T - 1 := by omega
  have hNr : (2 : ℝ) ≤ ((R0 k R T - 1 : ℕ) : ℝ) := by exact_mod_cast hN2
  rw [B1_bridge k R W T (by omega)]
  -- the Abel kit for `g₁` on `[2, N]`
  have hw : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (g1F k R) (g1D k R t) t :=
    fun t ht => hasDerivAt_g1F hB0 (le_trans one_le_two ht.1)
  have hG : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (G1F k R) (g1F k R t / t) t :=
    fun t ht => hasDerivAt_G1F hB (le_trans one_le_two ht.1)
  have hw'c : ContinuousOn (g1D k R) (Set.Icc 2 ((R0 k R T - 1 : ℕ) : ℝ)) :=
    (continuousOn_g1D hB0).mono (Set.Icc_subset_Icc_left one_le_two)
  have hw'neg : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ), g1D k R t ≤ 0 :=
    fun t ht => g1D_nonpos hB0 (le_trans one_le_two ht.1)
  have hΦ : ∀ t ∈ Set.Ioc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      (∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r)
        ≤ 4 * (Nat.totient W / W : ℝ) * Real.log t
            - (-(4 * (Nat.totient W / W : ℝ) * Real.log 2
                + 4 * ((Nat.totient W : ℝ) + 1))) := by
    intro t ht
    have h := sum_aW_floor_upper W hW (le_of_lt ht.1)
    linarith
  have hcore := abel_aW_upper W (R0 k R T - 1) hN2 (g1F k R) (g1D k R) (G1F k R)
    (4 * (Nat.totient W / W : ℝ))
    (-(4 * (Nat.totient W / W : ℝ) * Real.log 2 + 4 * ((Nat.totient W : ℝ) + 1)))
    hw hG hw'c hw'neg hΦ
  -- boundary term: substitute the Fact-4 upper bound at `t = N`
  have hSNu := sum_aW_floor_upper W hW (t := ((R0 k R T - 1 : ℕ) : ℝ)) hNr
  rw [Nat.floor_natCast] at hSNu
  have hg1N0 : 0 ≤ g1F k R ((R0 k R T - 1 : ℕ) : ℝ) :=
    g1F_nonneg hB0 (by linarith)
  have hbdry := mul_le_mul_of_nonneg_left hSNu hg1N0
  -- `t = 2` boundary pieces, all `R`-free
  have hφ0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := by positivity
  have hg120 : 0 ≤ g1F k R 2 := g1F_nonneg hB0 one_le_two
  have hg121 : g1F k R 2 ≤ 1 := g1F_le_one hB0 one_le_two
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hchi0 : (0 : ℝ) ≤ 4 * (Nat.totient W / W : ℝ) * Real.log 2
      + 4 * ((Nat.totient W : ℝ) + 1) := by positivity
  have hcg12 : (4 * (Nat.totient W / W : ℝ) * Real.log 2
        + 4 * ((Nat.totient W : ℝ) + 1)) * g1F k R 2
      ≤ 4 * (Nat.totient W / W : ℝ) * Real.log 2 + 4 * ((Nat.totient W : ℝ) + 1) :=
    mul_le_of_le_one_right hchi0 hg121
  have hprod2 : (Nat.totient W / W : ℝ) * (g1F k R 2 * Real.log 2)
      ≤ (Nat.totient W / W : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hlog2 hg121) hφ0
  -- `φW·B⁻¹·log s(2) ≥ 0` (drop the `−4φW·B⁻¹·log s(2)` endpoint)
  have hlogs2 : 0 ≤ (Nat.totient W / W : ℝ)
      * ((bParam k R)⁻¹ * Real.log (sF k R 2)) :=
    mul_nonneg hφ0 (mul_nonneg (inv_nonneg.mpr hB0)
      (Real.log_nonneg (one_le_sF hB0 one_le_two)))
  -- monotone weakening `log s(N) ≤ log s(R₀)`
  have hXpos : (0 : ℝ) < ((R0 k R T - 1 : ℕ) : ℝ) := by linarith
  have hNX : ((R0 k R T - 1 : ℕ) : ℝ) ≤ (R0 k R T : ℝ) := by
    exact_mod_cast (by omega : R0 k R T - 1 ≤ R0 k R T)
  have hsmono : Real.log (sF k R ((R0 k R T - 1 : ℕ) : ℝ))
      ≤ Real.log (sF k R (R0 k R T : ℝ)) := by
    apply Real.log_le_log (sF_pos hB0 (by linarith))
    unfold sF
    have := mul_le_mul_of_nonneg_left (Real.log_le_log hXpos hNX) hB0
    linarith
  have hsmono' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hsmono (inv_nonneg.mpr hB0)) (by positivity :
      (0 : ℝ) ≤ 4 * (Nat.totient W / W : ℝ))
  -- expose the `log s` atoms and assemble
  simp only [G1F, sF] at hcore hsmono' hlogs2
  simp only [errA1]
  linarith [hcore, hbdry, hcg12, hprod2, hlogs2, hsmono']

/-! ## P2 — the sharp upper bound for `A1` -/

/-- **P2 (`A1_upper_sharp`).**  Exact-leading-constant upper bound
`A1 ≤ 4·φW·B⁻¹·(1 − s(R₀)⁻¹) + (R-damped boundary term) + errA1`.
The middle term is the explicit boundary allowance of the node brief
(nonnegative, `s⁻²`-damped, lower-order); the proof actually
establishes the stronger form without it and weakens. -/
theorem A1_upper_sharp (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 3 ≤ k)
    (hR : 2 ≤ R) (_hT : 1 ≤ T) (hX : 4 ≤ R0 k R T) :
    A1 k R W T
      ≤ 4 * (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
            * (1 - (1 + bParam k R * Real.log (R0 k R T))⁻¹)
        + 4 * (Nat.totient W / W : ℝ)
            * Real.log (R0 k R T)
            * ((1 + bParam k R * Real.log (R0 k R T - 1))⁻¹) ^ 2
        + errA1 k W := by
  have hB : 0 < bParam k R := bParam_pos (by omega) hR
  have hB0 : 0 ≤ bParam k R := hB.le
  have hN2 : 2 ≤ R0 k R T - 1 := by omega
  have hNr : (2 : ℝ) ≤ ((R0 k R T - 1 : ℕ) : ℝ) := by exact_mod_cast hN2
  have hcastN : ((R0 k R T - 1 : ℕ) : ℝ) = (R0 k R T : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← hcastN, A1_bridge k R W T (by omega)]
  -- the Abel kit for `g₂` on `[2, N]`
  have hw : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (g2F k R) (g2D k R t) t :=
    fun t ht => hasDerivAt_g2F hB0 (le_trans one_le_two ht.1)
  have hG : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (G2F k R) (g2F k R t / t) t :=
    fun t ht => hasDerivAt_G2F hB (le_trans one_le_two ht.1)
  have hw'c : ContinuousOn (g2D k R) (Set.Icc 2 ((R0 k R T - 1 : ℕ) : ℝ)) :=
    (continuousOn_g2D hB0).mono (Set.Icc_subset_Icc_left one_le_two)
  have hw'neg : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ), g2D k R t ≤ 0 :=
    fun t ht => g2D_nonpos hB0 (le_trans one_le_two ht.1)
  have hΦ : ∀ t ∈ Set.Ioc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      (∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r)
        ≤ 4 * (Nat.totient W / W : ℝ) * Real.log t
            - (-(4 * (Nat.totient W / W : ℝ) * Real.log 2
                + 4 * ((Nat.totient W : ℝ) + 1))) := by
    intro t ht
    have h := sum_aW_floor_upper W hW (le_of_lt ht.1)
    linarith
  have hcore := abel_aW_upper W (R0 k R T - 1) hN2 (g2F k R) (g2D k R) (G2F k R)
    (4 * (Nat.totient W / W : ℝ))
    (-(4 * (Nat.totient W / W : ℝ) * Real.log 2 + 4 * ((Nat.totient W : ℝ) + 1)))
    hw hG hw'c hw'neg hΦ
  -- boundary term: substitute the Fact-4 upper bound at `t = N`
  have hSNu := sum_aW_floor_upper W hW (t := ((R0 k R T - 1 : ℕ) : ℝ)) hNr
  rw [Nat.floor_natCast] at hSNu
  have hg2N0 : 0 ≤ g2F k R ((R0 k R T - 1 : ℕ) : ℝ) := g2F_nonneg k R _
  have hbdry := mul_le_mul_of_nonneg_left hSNu hg2N0
  -- `t = 2` boundary pieces, all `R`-free
  have hφ0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := by positivity
  have hg220 : 0 ≤ g2F k R 2 := g2F_nonneg k R 2
  have hg221 : g2F k R 2 ≤ 1 := g2F_le_one hB0 one_le_two
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hchi0 : (0 : ℝ) ≤ 4 * (Nat.totient W / W : ℝ) * Real.log 2
      + 4 * ((Nat.totient W : ℝ) + 1) := by positivity
  have hcg22 : (4 * (Nat.totient W / W : ℝ) * Real.log 2
        + 4 * ((Nat.totient W : ℝ) + 1)) * g2F k R 2
      ≤ 4 * (Nat.totient W / W : ℝ) * Real.log 2 + 4 * ((Nat.totient W : ℝ) + 1) :=
    mul_le_of_le_one_right hchi0 hg221
  have hprod2 : (Nat.totient W / W : ℝ) * (g2F k R 2 * Real.log 2)
      ≤ (Nat.totient W / W : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hlog2 hg221) hφ0
  -- `s(2)⁻¹ ≤ 1` (the `+4φW·B⁻¹·s(2)⁻¹` endpoint)
  have hs2prod := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (inv_le_one_of_one_le₀ (one_le_sF hB0 one_le_two)) (inv_nonneg.mpr hB0)) hφ0
  -- monotone weakening `s(N)⁻¹ ≥ s(R₀)⁻¹`
  have hXpos : (0 : ℝ) < ((R0 k R T - 1 : ℕ) : ℝ) := by linarith
  have hNX : ((R0 k R T - 1 : ℕ) : ℝ) ≤ (R0 k R T : ℝ) := by
    exact_mod_cast (by omega : R0 k R T - 1 ≤ R0 k R T)
  have hsNpos : 0 < sF k R ((R0 k R T - 1 : ℕ) : ℝ) := sF_pos hB0 (by linarith)
  have hsFNX : sF k R ((R0 k R T - 1 : ℕ) : ℝ) ≤ sF k R (R0 k R T : ℝ) := by
    unfold sF
    have := mul_le_mul_of_nonneg_left (Real.log_le_log hXpos hNX) hB0
    linarith
  have hinv : (sF k R (R0 k R T : ℝ))⁻¹ ≤ (sF k R ((R0 k R T - 1 : ℕ) : ℝ))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hsNpos hsFNX
  have hinv4 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr hB0)) hφ0
  -- the stated (nonnegative) boundary-allowance term
  have hbnd0 : 0 ≤ 4 * (Nat.totient W / W : ℝ) * Real.log (R0 k R T : ℝ)
      * ((1 + bParam k R * Real.log ((R0 k R T - 1 : ℕ) : ℝ))⁻¹) ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) (Real.log_natCast_nonneg _)) (sq_nonneg _)
  -- expose the `s` atoms and assemble
  simp only [G2F, sF] at hcore
  simp only [sF] at hs2prod hinv4
  simp only [errA1]
  linarith [hcore, hbdry, hcg22, hprod2, hs2prod, hinv4, hbnd0]

/-! ## P3 — the sharp lower bound for `A1` -/

/-- **P3 (`A1_lower_sharp`).**  Exact-leading-constant lower bound
`φW·B⁻¹·(1 − s(R₀−1)⁻¹) − errB1 ≤ A1` (same machinery as P1 with
`g₂ = s⁻²` and antiderivative `G₂ = −B⁻¹·s⁻¹`; same error constant). -/
theorem A1_lower_sharp (k R W : ℕ) (T : ℝ) (hW : W ≠ 0) (hk : 3 ≤ k)
    (hR : 2 ≤ R) (_hT : 1 ≤ T) (hX : 4 ≤ R0 k R T) :
    (Nat.totient W / W : ℝ) * (bParam k R)⁻¹
        * (1 - (1 + bParam k R * Real.log (R0 k R T - 1))⁻¹)
      - errB1 k W ≤ A1 k R W T := by
  have hB : 0 < bParam k R := bParam_pos (by omega) hR
  have hB0 : 0 ≤ bParam k R := hB.le
  have hN2 : 2 ≤ R0 k R T - 1 := by omega
  have hNr : (2 : ℝ) ≤ ((R0 k R T - 1 : ℕ) : ℝ) := by exact_mod_cast hN2
  have hcastN : ((R0 k R T - 1 : ℕ) : ℝ) = (R0 k R T : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [← hcastN, A1_bridge k R W T (by omega)]
  -- the Abel kit for `g₂` on `[2, N]`
  have hw : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (g2F k R) (g2D k R t) t :=
    fun t ht => hasDerivAt_g2F hB0 (le_trans one_le_two ht.1)
  have hG : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      HasDerivAt (G2F k R) (g2F k R t / t) t :=
    fun t ht => hasDerivAt_G2F hB (le_trans one_le_two ht.1)
  have hw'c : ContinuousOn (g2D k R) (Set.Icc 2 ((R0 k R T - 1 : ℕ) : ℝ)) :=
    (continuousOn_g2D hB0).mono (Set.Icc_subset_Icc_left one_le_two)
  have hw'neg : ∀ t ∈ Set.Icc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ), g2D k R t ≤ 0 :=
    fun t ht => g2D_nonpos hB0 (le_trans one_le_two ht.1)
  have hΦ : ∀ t ∈ Set.Ioc (2 : ℝ) ((R0 k R T - 1 : ℕ) : ℝ),
      (Nat.totient W / W : ℝ) * Real.log t
          - ((Nat.totient W / W : ℝ) * Real.log W + 1)
        ≤ ∑ r ∈ Finset.Icc 0 ⌊t⌋₊, aW W r :=
    fun t ht => sum_aW_floor_lower W hW (le_of_lt ht.1)
  have hcore := abel_aW_lower W (R0 k R T - 1) hN2 (g2F k R) (g2D k R) (G2F k R)
    ((Nat.totient W / W : ℝ)) ((Nat.totient W / W : ℝ) * Real.log W + 1)
    hw hG hw'c hw'neg hΦ
  -- boundary term: substitute the Fact-4 lower bound at `t = N`
  have hSN := sum_aW_floor_lower W hW (t := ((R0 k R T - 1 : ℕ) : ℝ)) hNr
  rw [Nat.floor_natCast] at hSN
  have hg2N0 : 0 ≤ g2F k R ((R0 k R T - 1 : ℕ) : ℝ) := g2F_nonneg k R _
  have hbdry := mul_le_mul_of_nonneg_left hSN hg2N0
  -- `t = 2` boundary pieces, all `R`-free
  have hφ0 : (0 : ℝ) ≤ (Nat.totient W / W : ℝ) := by positivity
  have hg220 : 0 ≤ g2F k R 2 := g2F_nonneg k R 2
  have hg221 : g2F k R 2 ≤ 1 := g2F_le_one hB0 one_le_two
  have hlogW : 0 ≤ Real.log (W : ℝ) := Real.log_natCast_nonneg W
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hclo0 : 0 ≤ (Nat.totient W / W : ℝ) * Real.log W + 1 := by positivity
  have hclog22 : ((Nat.totient W / W : ℝ) * Real.log W + 1) * g2F k R 2
      ≤ (Nat.totient W / W : ℝ) * Real.log W + 1 :=
    mul_le_of_le_one_right hclo0 hg221
  have hprod0 : 0 ≤ (Nat.totient W / W : ℝ) * (g2F k R 2 * Real.log 2) :=
    mul_nonneg hφ0 (mul_nonneg hg220 hlog2)
  have hs2' := mul_le_mul_of_nonneg_left (inv_mul_one_sub_inv_sF_two_le hB) hφ0
  -- expose the `s` atoms and assemble
  simp only [G2F, sF] at hcore
  simp only [sF] at hs2'
  simp only [errB1]
  linarith [hcore, hbdry, hs2', hclog22, hprod0]

end Salt.Maynard
