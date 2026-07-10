/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.TensorA1
import Salt.Maynard.Overshoot

/-!
# C3b — the S₂ tensor lower bound (SUM-LEVEL coprimality, Maynard Lemma 6.3)

This file assembles the S₂ diagonal main-term lower bound for the concrete
tensor weight `yTensor`.  Starting from the abstract main term
`∑_{u:uₘ=1} (contraction u)² / ∏ᵢ φ(uᵢ)` (the load-bearing term of
`s2main_lower`), we lower-bound it by `c₀·B₁²·A₁^{k-1}` with an **explicit**
`c₀ = 1/4 > 0`.

## Why the coprimality correction is handled at the SUM level

For `u` with `uₘ = 1`, the contraction of the concrete tensor factorises as
`S(u) = P(u)·Q(u)`, where `P(u) = ∏_{i≠m} fTilde(uᵢ)` is the "off-`m`" tensor
mass and `Q(u) = ∑_{aₘ<R} [update u m aₘ ∈ 𝒟]·fTilde(aₘ)/φ(aₘ)` is the
coprime/threshold-restricted 1-dimensional `m`-contraction
(`contraction_factor`, **landed exactly**).

On the clean region `Good` the guard `update u m aₘ ∈ 𝒟` is *implied by*
`aₘ ∈ sqfCop R₀ W ∧ aₘ ⊥ ∏_{i≠m} uᵢ` (the `∏ < R` clause is automatic from the
`uVal`-threshold `Σ_{i≠m} uVal(uᵢ) < k − T` together with `uVal(aₘ) ≤ T`).  So

`Q(u) ≥ B₁ − omitMass(u)`,  where  `omitMass(u) = ∑_{aₘ∈sqfCop, aₘ ∤⊥ ∏uᵢ} fWt/φ`

is the mass *omitted* by the coprimality constraint.  Crucially `omitMass`
is **not** bounded per-`u` (its per-`u` size grows with `ω(∏uᵢ)`); instead the
lower bound uses `(B₁ − omitMass)² ≥ B₁² − 2·B₁·omitMass` and controls
`Σ_u omitMass(u)·weight(u)` at the **sum level** (`H_omit`).

## Structure

1. **Restrict** the outer `u`-sum to `Good`, dropping the nonnegative complement.
2. **Factorise & bound below** `S(u)²/∏φ = Q(u)²·W(u) ≥ (B₁² − 2 B₁·omitMass(u))·W(u)`,
   where `W(u) = ∏_{i≠m}(fTilde(uᵢ)²/φ(uᵢ)) ≥ 0` and `Q(u) ≥ B₁ − omitMass(u) ≥ 0`.
3. **Sum** and split: `≥ B₁²·Σ_u W(u) − 2 B₁·Σ_u omitMass(u)·W(u)`.
4. Apply the two SUM-LEVEL atoms and combine:
   `≥ B₁²·(½ A₁^{k-1}) − 2 B₁·(⅛ B₁·A₁^{k-1}) = ¼·B₁²·A₁^{k-1}`.

## The two SUM-LEVEL atoms (both quantified over `Σ_{u∈Good}`, both satisfiable)

* `H_main` — the `(k-1)`-dim truncated, off-`m` tensor mass over `Good` is
  `≥ (1/2)·A₁^{k-1}`.  (No `B₁`, no contraction, no coprimality omission.)
* `H_omit` — the **average** coprimality-omitted mass is small:
  `Σ_{u∈Good} omitMass(u)·W(u) ≤ (1/8)·B₁·A₁^{k-1}`.  (The `log R₀` in
  `omitMass` cancels against the `log R₀` in `B₁`; `Σ_p 1/(p−1)²` converges,
  unlike the per-`u` `ω` which grows — this is why the *sum* atom is provable
  where the old per-`u` `H_contract` atom was false.)

Both are discharged in follow-on nodes; here they are hypotheses.
-/

open Finset

namespace Salt.Maynard

/-- Nonnegativity of the truncated coordinate weight `fTilde`. -/
lemma fTilde_nonneg (k R : ℕ) (T : ℝ) (r : ℕ) (hR : 2 ≤ R) : 0 ≤ fTilde k R T r := by
  unfold fTilde
  split_ifs with h
  · have hr : 1 ≤ r := by
      rw [sqfCop, Finset.mem_filter] at h
      exact Nat.one_le_iff_ne_zero.mpr h.2.1.ne_zero
    exact fWt_nonneg hr hR
  · exact le_refl 0

/-- The clean sub-region `Good`: sieve tuples with `uₘ = 1`, squarefree coprime
off-`m` coordinates, below the threshold `Σ_{i≠m} uVal(uᵢ) < k − T`. -/
noncomputable def Good (k R : ℕ) (m : Fin k) (T : ℝ) : Finset (Fin k → ℕ) :=
  (kSieveIndex k R (W k)).filter (fun u => u m = 1
    ∧ (∀ i, i ≠ m → u i ∈ sqfCop (R0 k R T) (W k))
    ∧ (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)

/-- **The contraction factorisation (landed exactly).** For `uₘ = 1`, the concrete
tensor `m`-contraction factors as the off-`m` tensor mass `P(u) = ∏_{i≠m} fTilde(uᵢ)`
times the coprime/threshold-restricted 1-dimensional sum
`Q(u) = ∑_{aₘ<R} [update u m aₘ ∈ 𝒟]·fTilde(aₘ)/φ(aₘ)`. -/
theorem contraction_factor (k R : ℕ) (m : Fin k) (T : ℝ) (u : Fin k → ℕ) (_hum : u m = 1) :
    (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      = (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
        * ∑ am ∈ Finset.range R,
            (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
              / (Nat.totient am : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro am _
  rw [yTensor]
  have hprod : (∏ i, fTilde k R T (Function.update u m am i))
      = fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ
        (fun i => fTilde k R T (Function.update u m am i)) (Finset.mem_univ m),
        Function.update_self]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
  by_cases hguard : Function.update u m am ∈ kSieveIndex k R (W k)
  · rw [if_pos hguard, if_pos hguard, hprod]; ring
  · rw [if_neg hguard, if_neg hguard]; simp

/-- The coprimality-**omitted** mass at `u`: the `B₁`-summands over `sqfCop R₀ W`
whose index is *not* coprime to `∏_{i≠m} uᵢ`.  This is the mass that the sieve
guard `update u m aₘ ∈ 𝒟` removes from `B₁`, so `Q(u) ≥ B₁ − omitMass(u)`.
Its per-`u` size grows with `ω(∏uᵢ)`, but its `weight`-average over `Good` is
small (`H_omit`) — Maynard Lemma 6.3. -/
noncomputable def omitMass (k R : ℕ) (m : Fin k) (T : ℝ) (u : Fin k → ℕ) : ℝ :=
  ∑ am ∈ sqfCop (R0 k R T) (W k),
    (if ¬ Nat.Coprime am (∏ i ∈ Finset.univ.erase m, u i)
      then fWt k R am / (Nat.totient am : ℝ) else 0)

/-- **`uVal`-threshold ⇒ product bound.** If every coordinate is `≥ 1` and the
total `uVal`-mass is `< k`, then `∏ᵢ rᵢ < R`.  (The forward half of the sieve
identity `Σᵢ uVal(rᵢ) < k ⟺ ∏ᵢ rᵢ < R`, since `uVal(r) = k·log r / log R`.) -/
lemma prod_lt_of_sum_uVal_lt {k R : ℕ} (hk : 1 ≤ k) (hR : 2 ≤ R) (r : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ r i) (hsum : (∑ i, uVal k R (r i)) < (k : ℝ)) :
    (∏ i, r i) < R := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hRR : (1 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRR
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin k)), ((r i : ℝ)) ≠ 0 := by
    intro i _
    exact_mod_cast Nat.one_le_iff_ne_zero.mp (hpos i)
  set L : ℝ := Real.log (∏ i, (r i : ℝ)) with hLdef
  -- `Σᵢ uVal(rᵢ) = (k / log R) · log(∏ rᵢ)`
  have hrw : (∑ i, uVal k R (r i)) = (k : ℝ) / Real.log R * L := by
    have hlp : L = ∑ i, Real.log (r i) := by rw [hLdef, Real.log_prod hne]
    rw [hlp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold uVal
    ring
  rw [hrw] at hsum
  -- divide out `k / log R > 0` to get `L < log R`
  have hLlt : L < Real.log R := by
    have hpos' : 0 < (k : ℝ) / Real.log R := div_pos hkR hlogR
    have : (k : ℝ) / Real.log R * L < (k : ℝ) / Real.log R * Real.log R := by
      calc (k : ℝ) / Real.log R * L < (k : ℝ) := hsum
        _ = (k : ℝ) / Real.log R * Real.log R := by field_simp
    exact lt_of_mul_lt_mul_left this hpos'.le
  -- exponentiate: `∏ rᵢ = exp L < exp (log R) = R`
  have hprodpos : (0 : ℝ) < ∏ i, (r i : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hpos i)
  have hRpos : (0 : ℝ) < (R : ℝ) := by linarith
  have hlt : ∏ i, (r i : ℝ) < (R : ℝ) := by
    have hexp := Real.exp_lt_exp.mpr hLlt
    rwa [hLdef, Real.exp_log hprodpos, Real.exp_log hRpos] at hexp
  exact_mod_cast hlt

/-- **Guard implication (⊇ direction).** On `Good`, any squarefree coprime index
`aₘ ∈ sqfCop R₀ W` that is coprime to `∏_{i≠m} uᵢ` lands in the sieve guard:
`update u m aₘ ∈ 𝒟`.  The delicate `∏ < R` clause is automatic from the
`uVal`-threshold defining `Good`, via `prod_lt_of_sum_uVal_lt`. -/
lemma update_mem_kSieveIndex_of_Good {k R : ℕ} {m : Fin k} {T : ℝ} (hR : 2 ≤ R)
    {u : Fin k → ℕ} (hu : u ∈ Good k R m T) {am : ℕ}
    (ham : am ∈ sqfCop (R0 k R T) (W k))
    (hcop : Nat.Coprime am (∏ i ∈ Finset.univ.erase m, u i)) :
    Function.update u m am ∈ kSieveIndex k R (W k) := by
  have hk : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; exact m.elim0)
  rw [Good, Finset.mem_filter] at hu
  obtain ⟨huks, _hum, hthr⟩ := hu
  rw [mem_kSieveIndex_iff] at huks
  obtain ⟨hsq_u, hpc_u, hcw_u, _⟩ := huks
  rw [sqfCop, Finset.mem_filter, Finset.mem_range] at ham
  obtain ⟨_ham_lt, hsq_am, hcw_am⟩ := ham
  -- positivity of every coordinate of `update u m am`
  have hpos_u : ∀ i, 1 ≤ u i := fun i => Squarefree.pos (hsq_u i)
  have hpos_am : 1 ≤ am := Squarefree.pos hsq_am
  have hupd_pos : ∀ i, 1 ≤ Function.update u m am i := by
    intro i
    rcases eq_or_ne i m with rfl | hi
    · rw [Function.update_self]; exact hpos_am
    · rw [Function.update_of_ne hi]; exact hpos_u i
  rw [mem_kSieveIndex_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- squarefree
    intro i
    rcases eq_or_ne i m with rfl | hi
    · rw [Function.update_self]; exact hsq_am
    · rw [Function.update_of_ne hi]; exact hsq_u i
  · -- pairwise coprime
    intro i j hij
    have hcop_am : ∀ l, l ≠ m → Nat.Coprime am (u l) := by
      intro l hl
      exact hcop.coprime_dvd_right
        (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩))
    rcases eq_or_ne i m with rfl | hi
    · rw [Function.update_self, Function.update_of_ne (Ne.symm hij)]
      exact hcop_am j (Ne.symm hij)
    · rcases eq_or_ne j m with rfl | hj
      · rw [Function.update_of_ne hi, Function.update_self]
        exact (hcop_am i hi).symm
      · rw [Function.update_of_ne hi, Function.update_of_ne hj]
        exact hpc_u i j hij
  · -- coprime to `W`
    intro i
    rcases eq_or_ne i m with rfl | hi
    · rw [Function.update_self]; exact hcw_am
    · rw [Function.update_of_ne hi]; exact hcw_u i
  · -- `∏ᵢ (update u m am)ᵢ < R`, from the `uVal`-threshold
    apply prod_lt_of_sum_uVal_lt hk hR _ hupd_pos
    -- `Σᵢ uVal(update i) = uVal(am) + Σ_{i≠m} uVal(uᵢ) < T + (k − T) = k`
    have hsplit : (∑ i, uVal k R (Function.update u m am i))
        = uVal k R am + ∑ i ∈ Finset.univ.erase m, uVal k R (u i) := by
      rw [← Finset.add_sum_erase Finset.univ (fun i => uVal k R (Function.update u m am i))
          (Finset.mem_univ m), Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hsplit]
    have ham_mem : am ∈ sqfCop (R0 k R T) (W k) := by
      rw [sqfCop, Finset.mem_filter, Finset.mem_range]
      exact ⟨_ham_lt, hsq_am, hcw_am⟩
    have ham_le : uVal k R am ≤ T := uVal_le_T hk hR ham_mem
    linarith

/-- **`Q(u) ≥ B₁ − omitMass(u)`.** On `Good`, the coprime/threshold-restricted
`m`-contraction dominates `B₁` minus the coprimality-omitted mass.  Only the
⊇ direction of the guard is used, so a one-sided bound suffices. -/
lemma contraction_ge_B1_sub_omit {k R : ℕ} {m : Fin k} {T : ℝ} (hR : 2 ≤ R)
    {u : Fin k → ℕ} (hu : u ∈ Good k R m T) :
    B1 k R (W k) T - omitMass k R m T u
      ≤ ∑ am ∈ Finset.range R,
          (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
            / (Nat.totient am : ℝ) := by
  -- `B₁ − omitMass = Σ_{aₘ∈sqfCop, coprime} fWt/φ`
  have hBsub : B1 k R (W k) T - omitMass k R m T u
      = ∑ am ∈ sqfCop (R0 k R T) (W k),
          (if Nat.Coprime am (∏ i ∈ Finset.univ.erase m, u i)
            then fWt k R am / (Nat.totient am : ℝ) else 0) := by
    rw [B1, omitMass, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro am _
    by_cases hc : Nat.Coprime am (∏ i ∈ Finset.univ.erase m, u i)
    · rw [if_pos hc, if_neg (not_not.mpr hc)]; ring
    · rw [if_neg hc, if_pos hc]; ring
  rw [hBsub]
  -- `Good`-membership gives `sqfCop R₀ W ⊆ range R`
  have hsub : sqfCop (R0 k R T) (W k) ⊆ Finset.range R := by
    intro am ham
    rw [Finset.mem_range]
    have hk : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; exact m.elim0)
    have hu' := hu
    rw [Good, Finset.mem_filter] at hu'
    obtain ⟨huks, _hum, hthr⟩ := hu'
    have hpos_u : ∀ i, 1 ≤ u i := fun i =>
      Squarefree.pos (((mem_kSieveIndex_iff u).mp huks).1 i)
    rw [sqfCop, Finset.mem_filter, Finset.mem_range] at ham
    obtain ⟨_am_lt, hsq_am, hcw_am⟩ := ham
    have hpos_am : 1 ≤ am := Squarefree.pos hsq_am
    have hupd_pos : ∀ i, 1 ≤ Function.update u m am i := by
      intro i
      rcases eq_or_ne i m with rfl | hi
      · rw [Function.update_self]; exact hpos_am
      · rw [Function.update_of_ne hi]; exact hpos_u i
    have hprod : (∏ i, Function.update u m am i) < R := by
      apply prod_lt_of_sum_uVal_lt hk hR _ hupd_pos
      have hsplit : (∑ i, uVal k R (Function.update u m am i))
          = uVal k R am + ∑ i ∈ Finset.univ.erase m, uVal k R (u i) := by
        rw [← Finset.add_sum_erase Finset.univ (fun i => uVal k R (Function.update u m am i))
            (Finset.mem_univ m), Function.update_self]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hsplit]
      have ham_mem : am ∈ sqfCop (R0 k R T) (W k) := by
        rw [sqfCop, Finset.mem_filter, Finset.mem_range]
        exact ⟨_am_lt, hsq_am, hcw_am⟩
      have ham_le : uVal k R am ≤ T := uVal_le_T hk hR ham_mem
      linarith
    -- `am = update m ≤ ∏ update < R`
    have : am ≤ ∏ i, Function.update u m am i := by
      have := Finset.single_le_prod' (f := fun i => Function.update u m am i)
        (fun i _ => hupd_pos i) (Finset.mem_univ m)
      rwa [Function.update_self] at this
    omega
  -- termwise: on `sqfCop`, coprime-indicator ≤ guarded `fTilde`-summand;
  -- then extend `sqfCop ⊆ range R` (dropped terms `≥ 0`).
  have hnn_range : ∀ am ∈ Finset.range R,
      0 ≤ (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
            / (Nat.totient am : ℝ) := by
    intro am _
    apply div_nonneg _ (Nat.cast_nonneg _)
    split_ifs
    · exact fTilde_nonneg k R T am hR
    · exact le_refl 0
  calc (∑ am ∈ sqfCop (R0 k R T) (W k),
          (if Nat.Coprime am (∏ i ∈ Finset.univ.erase m, u i)
            then fWt k R am / (Nat.totient am : ℝ) else 0))
      ≤ ∑ am ∈ sqfCop (R0 k R T) (W k),
          (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
            / (Nat.totient am : ℝ) := by
        apply Finset.sum_le_sum
        intro am ham
        by_cases hc : Nat.Coprime am (∏ i ∈ Finset.univ.erase m, u i)
        · rw [if_pos hc]
          have hguard : Function.update u m am ∈ kSieveIndex k R (W k) :=
            update_mem_kSieveIndex_of_Good hR hu ham hc
          have hfT : fTilde k R T am = fWt k R am := by rw [fTilde, if_pos ham]
          rw [if_pos hguard, hfT]
        · rw [if_neg hc]
          exact hnn_range am (hsub ham)
    _ ≤ ∑ am ∈ Finset.range R,
          (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
            / (Nat.totient am : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun am ha _ => hnn_range am ha)

/-- **C3b — the S₂ tensor lower bound (SUM-LEVEL coprimality).**  The abstract S₂
main term for the concrete tensor `yTensor` is bounded below by `(1/4)·B₁²·A₁^{k-1}`,
an explicit positive multiple of the frozen target `B₁²·A₁^{k-1}`.

The coprimality correction is handled at the **sum level** through two hypotheses,
each a bound on a `Σ_{u∈Good}` (never per-`u`):

* `H_main` — the `(k-1)`-dim off-`m` truncated tensor mass over `Good` is
  `≥ (1/2)·A₁^{k-1}`;
* `H_omit` — the `weight`-averaged coprimality-omitted mass is
  `≤ (1/8)·B₁·A₁^{k-1}`.

Everything else — the factorisation `S = P·Q`, `Q ≥ B₁ − omitMass`, the algebraic
lower bound `(B₁ − omitMass)² ≥ B₁² − 2 B₁·omitMass`, the clean-region restriction,
the `φ(1)=1` product collapse, and the sum split — is proved here. -/
theorem s2_tensor_lower (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R)
    (hB1 : 0 ≤ B1 k R (W k) T)
    (H_main : (1 / 2 : ℝ) * (A1 k R (W k) T) ^ (k - 1)
          ≤ ∑ u ∈ Good k R m T,
              ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ))
    (H_omit : ∑ u ∈ Good k R m T,
          omitMass k R m T u
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
        ≤ (1 / 8 : ℝ) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1)) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  rw [ge_iff_le]
  set c : ℝ := B1 k R (W k) T with hc
  set a : ℝ := (A1 k R (W k) T) ^ (k - 1) with ha
  -- abbreviations for the two sum-level quantities appearing in `H_main`/`H_omit`
  set SW : ℝ := ∑ u ∈ Good k R m T,
      ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) with hSW
  set OW : ℝ := ∑ u ∈ Good k R m T,
      omitMass k R m T u
        * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) with hOW
  -- `Good ⊆ {u : uₘ = 1}`
  have hsubset : Good k R m T ⊆ (kSieveIndex k R (W k)).filter (fun u => u m = 1) := by
    intro u hu
    rw [Good, Finset.mem_filter] at hu
    rw [Finset.mem_filter]
    exact ⟨hu.1, hu.2.1⟩
  have hterm_nonneg : ∀ u : Fin k → ℕ,
      0 ≤ (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ) :=
    fun u => div_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
  -- Step 1: drop the complement of `Good` (all terms `≥ 0`)
  have step1 :
      (∑ u ∈ Good k R m T,
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun u _ _ => hterm_nonneg u)
  -- Step 2: the per-`u` lower bound on `Good`
  have per_u : ∀ u ∈ Good k R m T,
      (c ^ 2 - 2 * c * omitMass k R m T u)
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
        ≤ (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ) := by
    intro u hu
    have humem := hu
    rw [Good, Finset.mem_filter] at hu
    have hum : u m = 1 := hu.2.1
    have huks : u ∈ kSieveIndex k R (W k) := hu.1
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    set Q := ∑ am ∈ Finset.range R,
        (if Function.update u m am ∈ kSieveIndex k R (W k) then fTilde k R T am else 0)
          / (Nat.totient am : ℝ) with hQdef
    set W_u := ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
      with hWdef
    have hφpos : 0 < ∏ i, (Nat.totient (u i) : ℝ) :=
      Finset.prod_pos (fun i _ => by
        exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos huks i))
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T (u i) hR)
    have hWnn : 0 ≤ W_u :=
      Finset.prod_nonneg (fun i _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    have homit_nn : 0 ≤ omitMass k R m T u :=
      Finset.sum_nonneg (fun am ham => by
        rw [sqfCop, Finset.mem_filter] at ham
        have hpos : 0 ≤ fWt k R am / (Nat.totient am : ℝ) :=
          div_nonneg (fWt_nonneg (Nat.one_le_iff_ne_zero.mpr ham.2.1.ne_zero) hR)
            (Nat.cast_nonneg _)
        split_ifs <;> first | exact hpos | exact le_rfl)
    have hQnn : 0 ≤ Q :=
      Finset.sum_nonneg (fun am _ => by
        apply div_nonneg _ (Nat.cast_nonneg _)
        split_ifs <;> first | exact fTilde_nonneg k R T am hR | exact le_rfl)
    -- `S = P·Q` (contraction factorisation), rendered on the `set` locals
    have hSval : (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) = P * Q := by
      rw [hPdef, hQdef]; exact contraction_factor k R m T u hum
    -- collapse `∏ᵢ φ` to `∏_{i≠m} φ` using `φ(uₘ) = φ(1) = 1`
    have hφsplit : (∏ i, (Nat.totient (u i) : ℝ))
        = ∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (u i) : ℝ))
          (Finset.mem_univ m)]
      simp [hum]
    have hPW : P ^ 2 / (∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ)) = W_u := by
      rw [hPdef, hWdef, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    -- `S²/∏φ = Q²·W(u)`
    have hid : (∑ am ∈ Finset.range R,
          yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ) = Q ^ 2 * W_u := by
      rw [hSval, hφsplit, mul_pow, ← hPW]; ring
    -- `Q ≥ B₁ − omitMass(u)`
    have hQge : c - omitMass k R m T u ≤ Q := by
      rw [hc, hQdef]; exact contraction_ge_B1_sub_omit hR humem
    -- algebraic lower bound `Q² ≥ c² − 2 c·omitMass`
    have hQsq : c ^ 2 - 2 * c * omitMass k R m T u ≤ Q ^ 2 := by
      have hQom : 0 ≤ Q + omitMass k R m T u - c := by linarith
      nlinarith [sq_nonneg (Q - c), mul_nonneg hB1 hQom]
    -- assemble: `(c² − 2c·omit)·W ≤ Q²·W = S²/∏φ`
    rw [hid]
    exact mul_le_mul_of_nonneg_right hQsq hWnn
  -- Step 3: sum the per-`u` bound and split into the two sum-level atoms
  have hsum_ge : c ^ 2 * SW - 2 * c * OW
      ≤ ∑ u ∈ Good k R m T,
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ) := by
    have hsplit : c ^ 2 * SW - 2 * c * OW
        = ∑ u ∈ Good k R m T,
            (c ^ 2 - 2 * c * omitMass k R m T u)
              * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
      rw [hSW, hOW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro u _; ring
    rw [hsplit]
    exact Finset.sum_le_sum per_u
  -- Step 4: apply `H_main`, `H_omit`, and combine
  have h1 : c ^ 2 * ((1 / 2 : ℝ) * a) ≤ c ^ 2 * SW :=
    mul_le_mul_of_nonneg_left H_main (sq_nonneg c)
  have h2 : 2 * c * OW ≤ 2 * c * ((1 / 8 : ℝ) * c * a) :=
    mul_le_mul_of_nonneg_left H_omit (by linarith)
  have hval : (1 / 4 : ℝ) * c ^ 2 * a
      = c ^ 2 * ((1 / 2 : ℝ) * a) - 2 * c * ((1 / 8 : ℝ) * c * a) := by ring
  have step2 : (1 / 4 : ℝ) * c ^ 2 * a ≤ c ^ 2 * SW - 2 * c * OW := by linarith
  exact le_trans (le_trans step2 hsum_ge) step1

end Salt.Maynard
