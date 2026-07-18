/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.ShiuIV
import Salt.Maynard.ShiuBlocks

/-!
# ShiuS5 — the pinned-scale composition (wave S5)

This file assembles the five per-class τ-in-AP bounds (degenerate + I + II + III +
IV, all landed in `ShiuClose`/`ShiuClasses`/`ShiuFinal`/`ShiuIV`) into the Shiu core
`sum_tau_in_ap_le : ShiuCore` (defined in `ShiuBlocks`).

## The spine

* `sum_union_le` — the nonneg two-set union bound `Σ_{s∪t} f ≤ Σ_s f + Σ_t f`.
* `shiu_partition` — the mechanical 5-way split: for every `w W P₀`,
  `Σ_{n≤z,n≡a} τ ≤ Σ_deg + Σ_I + Σ_II + Σ_III + Σ_IV` via `shiu_class_cover`
  (routing `IIIIV → III (ρ≤P₀) ∨ IV (ρ>P₀)`).

## The pinned scales (`α = 1/8000`)

* `W = ⌊z^{α/6}⌋`, `w = ⌊z^{α/3}⌋` (so `W² ≤ w`, integer-floor), `P₀ = ⌊log z⌋`.

## The corner

For `z` below the (astronomical) threshold `z₀` the crude divisor-summatory
`Σ_{n≤z} τ ≤ z(1+log z)` folds into the constant `C₀ = 3·z₀` because `φ(q) ≤ q ≤ z₀`.
-/

namespace Salt.Maynard

open Finset

/-- **The nonneg two-set union bound.** `Σ_{s∪t} f ≤ Σ_s f + Σ_t f` for `f ≥ 0`. -/
theorem sum_union_le {α : Type*} [DecidableEq α] (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (s t : Finset α) : ∑ i ∈ s ∪ t, f i ≤ ∑ i ∈ s, f i + ∑ i ∈ t, f i := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  have h : ∑ i ∈ t \ s, f i ≤ ∑ i ∈ t, f i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
  linarith

/-- **The S5 partition.**  For every choice of scales `w W P₀`, the τ-mass over a
residue class splits into the five Shiu classes.  Mechanical: the `shiu_class_cover`
routes each `n ≥ 1` to `deg ∨ I ∨ II ∨ IIIIV`, and `IIIIV = III (ρ ≤ P₀) ∨ IV
(ρ > P₀ ≡ ¬III)`; the nonneg union bound folds the cover into a five-term sum. -/
theorem shiu_partition (z q a w W P₀ : ℕ) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
      ≤ (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg w n),
            (n.divisors.card : ℝ))
        + (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassI w W n),
            (n.divisors.card : ℝ))
        + (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassII w W n),
            (n.divisors.card : ℝ))
        + (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIII w W P₀ n),
            (n.divisors.card : ℝ))
        + (∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIV w W P₀ n),
            (n.divisors.card : ℝ)) := by
  classical
  set Sdeg := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg w n) with hSdeg
  set SI := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassI w W n) with hSI
  set SII := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassII w W n) with hSII
  set SIII := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIII w W P₀ n) with hSIII
  set SIV := (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassIV w W P₀ n) with hSIV
  have hnn : ∀ n : ℕ, 0 ≤ (n.divisors.card : ℝ) := fun n => by positivity
  -- the cover: the residue-class set lands in the union of the five class sets.
  have hsub : (Finset.Icc 1 z).filter (fun n => n % q = a)
      ⊆ Sdeg ∪ SI ∪ SII ∪ SIII ∪ SIV := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnz⟩, hnq⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hmem : ∀ (P : ℕ → Prop) [DecidablePred P], P n →
        n ∈ (Finset.Icc 1 z).filter (fun m => m % q = a ∧ P m) := by
      intro P _ hP
      rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hn1, hnz⟩, hnq, hP⟩
    rcases shiu_class_cover hn0 w W with hd | hI | hII | hIIIIV
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (hmem _ hd))))))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (hmem _ hI))))))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr (hmem _ hII))))))
    · rcases lt_or_ge P₀ (shiuD w n).minFac with hρ | hρ
      · -- ρ > P₀ : class IV
        have hIV : shiuClassIV w W P₀ n := ⟨hIIIIV, fun hc => absurd hc.2 (by omega)⟩
        exact Finset.mem_union.mpr (Or.inr (hmem _ hIV))
      · -- ρ ≤ P₀ : class III
        have hIII : shiuClassIII w W P₀ n := ⟨hIIIIV, hρ⟩
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (hmem _ hIII))))
  -- fold the union into a five-term sum.
  calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
      ≤ ∑ n ∈ Sdeg ∪ SI ∪ SII ∪ SIII ∪ SIV, (n.divisors.card : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
    _ ≤ (∑ n ∈ Sdeg, (n.divisors.card : ℝ)) + (∑ n ∈ SI, (n.divisors.card : ℝ))
          + (∑ n ∈ SII, (n.divisors.card : ℝ)) + (∑ n ∈ SIII, (n.divisors.card : ℝ))
          + (∑ n ∈ SIV, (n.divisors.card : ℝ)) := by
        have h1 := sum_union_le (fun n : ℕ => (n.divisors.card : ℝ)) hnn
          (Sdeg ∪ SI ∪ SII ∪ SIII) SIV
        have h2 := sum_union_le (fun n : ℕ => (n.divisors.card : ℝ)) hnn
          (Sdeg ∪ SI ∪ SII) SIII
        have h3 := sum_union_le (fun n : ℕ => (n.divisors.card : ℝ)) hnn
          (Sdeg ∪ SI) SII
        have h4 := sum_union_le (fun n : ℕ => (n.divisors.card : ℝ)) hnn Sdeg SI
        linarith

/-! ## §2  The pinned scales (`α = 1/8000`) -/

/-- The pinned smoothness scale `W = ⌊z^{α/6}⌋ = ⌊z^{1/48000}⌋`. -/
noncomputable def Wp (z : ℕ) : ℕ := ⌊(z : ℝ) ^ ((1 : ℝ) / 48000)⌋₊

/-- The pinned prefix cap `w = ⌊z^{α/3}⌋ = ⌊z^{1/24000}⌋`. -/
noncomputable def wp (z : ℕ) : ℕ := ⌊(z : ℝ) ^ ((1 : ℝ) / 24000)⌋₊

/-- The pinned rough/smooth split `P₀ = ⌊log z⌋`. -/
noncomputable def P0p (z : ℕ) : ℕ := ⌊Real.log z⌋₊

section ScaleFacts

variable {z : ℕ}

/-- `1 ≤ W` for `z ≥ 1`. -/
theorem one_le_Wp (hz : 1 ≤ z) : 1 ≤ Wp z := by
  apply Nat.le_floor
  rw [Nat.cast_one]
  exact Real.one_le_rpow (by exact_mod_cast hz) (by norm_num)

/-- `1 ≤ w` for `z ≥ 1`. -/
theorem one_le_wp (hz : 1 ≤ z) : 1 ≤ wp z := by
  apply Nat.le_floor
  rw [Nat.cast_one]
  exact Real.one_le_rpow (by exact_mod_cast hz) (by norm_num)

/-- `W ≤ z^{1/48000}` (floor). -/
theorem Wp_le : (Wp z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 48000) :=
  Nat.floor_le (by positivity)

/-- `w ≤ z^{1/24000}` (floor). -/
theorem wp_le : (wp z : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 24000) :=
  Nat.floor_le (by positivity)

/-- **The key integer floor relation** `W² ≤ w`.  `W²` is an integer `≤ z^{1/24000}`,
so it is `≤ ⌊z^{1/24000}⌋ = w`. -/
theorem WpSq_le_wp (hz : 1 ≤ z) : Wp z ^ 2 ≤ wp z := by
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  apply Nat.le_floor
  push_cast
  calc (Wp z : ℝ) ^ 2 ≤ ((z : ℝ) ^ ((1 : ℝ) / 48000)) ^ 2 := by
        gcongr
        exact Wp_le
    _ = (z : ℝ) ^ ((1 : ℝ) / 24000) := by
        rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 48000)) 2, ← Real.rpow_mul hzR.le]
        norm_num

/-- `log W ≤ (1/48000)·log z`. -/
theorem logWp_le (hz : 2 ≤ z) :
    Real.log (Wp z) ≤ (1 / 48000 : ℝ) * Real.log z := by
  have hz1 : 1 ≤ z := by omega
  have hWpos : (0 : ℝ) < (Wp z : ℝ) := by exact_mod_cast one_le_Wp hz1
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  calc Real.log (Wp z) ≤ Real.log ((z : ℝ) ^ ((1 : ℝ) / 48000)) :=
        Real.log_le_log hWpos Wp_le
    _ = (1 / 48000 : ℝ) * Real.log z := by rw [Real.log_rpow hzpos]

/-- `log w ≤ (1/24000)·log z`. -/
theorem logwp_le (hz : 2 ≤ z) :
    Real.log (wp z) ≤ (1 / 24000 : ℝ) * Real.log z := by
  have hz1 : 1 ≤ z := by omega
  have hwpos : (0 : ℝ) < (wp z : ℝ) := by exact_mod_cast one_le_wp hz1
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  calc Real.log (wp z) ≤ Real.log ((z : ℝ) ^ ((1 : ℝ) / 24000)) :=
        Real.log_le_log hwpos wp_le
    _ = (1 / 24000 : ℝ) * Real.log z := by rw [Real.log_rpow hzpos]

end ScaleFacts

/-- **The universal denominator bound** `z^{1/8000} ≤ z/φ(q)`, used by every
discharge.  From `φ(q) ≤ q ≤ z^{1−1/8000}`. -/
theorem z_rpow_le_div_phi {z q : ℕ} (hq : 1 ≤ q) (hz1 : 1 ≤ z)
    (hqz : (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000)) :
    (z : ℝ) ^ ((1 : ℝ) / 8000) ≤ (z : ℝ) / (q.totient : ℝ) := by
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hkey : (z : ℝ) ^ ((1 : ℝ) / 8000) = (z : ℝ) / (z : ℝ) ^ (1 - (1 : ℝ) / 8000) := by
    rw [eq_div_iff (by positivity), ← Real.rpow_add hzpos]
    rw [show (1 : ℝ) / 8000 + (1 - 1 / 8000) = 1 by ring, Real.rpow_one]
  rw [hkey]
  calc (z : ℝ) / (z : ℝ) ^ (1 - (1 : ℝ) / 8000)
      ≤ (z : ℝ) / (q : ℝ) := by
        apply div_le_div_of_nonneg_left hzpos.le hqpos hqz
    _ ≤ (z : ℝ) / (q.totient : ℝ) := by
        apply div_le_div_of_nonneg_left hzpos.le hφpos hφq

/-- `1 ≤ 2·log z` for `z ≥ 2` (since `2·log z ≥ log 4 ≥ 1`). -/
theorem one_le_two_log {z : ℕ} (hz : 2 ≤ z) : (1 : ℝ) ≤ 2 * Real.log z := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr
      (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)))
  have hlog2z : Real.log 2 ≤ Real.log z :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hz)
  have h4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  linarith

/-- **The `W` lower bound** `z^{1/96000} ≤ W`.  From `W ≥ z^{1/48000} − 1` and
`u² − 1 ≥ u` for `u = z^{1/96000} ≥ 2`. -/
theorem Wp_ge {z : ℕ} (hL : 96000 * Real.log 2 ≤ Real.log z) :
    (z : ℝ) ^ ((1 : ℝ) / 96000) ≤ (Wp z : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) < 96000 * Real.log 2 := mul_pos (by norm_num) hlog2
  have hlogz : (0 : ℝ) < Real.log z := by linarith
  have hz2 : 2 ≤ z := by
    rcases Nat.lt_or_ge z 2 with h | h
    · interval_cases z <;>
        simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one] at hlogz <;>
        linarith
    · exact h
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  set u := (z : ℝ) ^ ((1 : ℝ) / 96000) with hu
  have hu2 : (2 : ℝ) ≤ u := by
    rw [hu, Real.rpow_def_of_pos hzpos,
      show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have husq : u ^ 2 = (z : ℝ) ^ ((1 : ℝ) / 48000) := by
    rw [hu, ← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 96000)) 2, ← Real.rpow_mul hzpos.le]
    norm_num
  have hfloor : (z : ℝ) ^ ((1 : ℝ) / 48000) < (Wp z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hstep : u ≤ u ^ 2 - 1 := by nlinarith [hu2]
  rw [husq] at hstep
  linarith

/-- `log W ≥ (1/96000)·log z`. -/
theorem logWp_ge {z : ℕ} (hL : 96000 * Real.log 2 ≤ Real.log z) :
    (1 / 96000 : ℝ) * Real.log z ≤ Real.log (Wp z) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) < 96000 * Real.log 2 := mul_pos (by norm_num) hlog2
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rcases Nat.lt_or_ge z 1 with h | h
    · interval_cases z
      simp only [Nat.cast_zero, Real.log_zero] at hL; linarith
    · exact_mod_cast h
  calc (1 / 96000 : ℝ) * Real.log z = Real.log ((z : ℝ) ^ ((1 : ℝ) / 96000)) := by
        rw [Real.log_rpow hzpos]
    _ ≤ Real.log (Wp z) :=
        Real.log_le_log (Real.rpow_pos_of_pos hzpos _) (Wp_ge hL)

/-! ## §3  The corner (crude bound for `z` below the threshold) -/

/-- **The corner.**  For `z < z₀` the crude divisor summatory
`Σ_{n≤z} τ ≤ z(1+log z)` folds into `3·z₀·(z/φ(q))·log z`, because
`φ(q) ≤ q ≤ z < z₀` and `1 + log z ≤ 3 log z`. -/
theorem shiu_corner_le (z₀ z q a : ℕ) (hz : 2 ≤ z) (hq : 1 ≤ q)
    (hqz : (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000)) (hzz0 : z < z₀) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
      ≤ (3 * z₀ : ℝ) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  have hz1 : 1 ≤ z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hL0 : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
  have h2L : (1 : ℝ) ≤ 2 * Real.log z := one_le_two_log hz
  -- crude mass bound
  have hmass : ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
      ≤ (z : ℝ) * (1 + Real.log z) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => by positivity)) ?_
    exact Salt.BV.sum_card_divisors_le z hz1
  -- φ(q) ≤ z₀
  have hφz0 : (q.totient : ℝ) ≤ (z₀ : ℝ) := by
    have h1 : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
    have h2 : (z : ℝ) ^ (1 - (1 : ℝ) / 8000) ≤ (z : ℝ) := by
      calc (z : ℝ) ^ (1 - (1 : ℝ) / 8000) ≤ (z : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hz1) (by norm_num)
        _ = (z : ℝ) := Real.rpow_one _
    have h3 : (z : ℝ) ≤ (z₀ : ℝ) := by exact_mod_cast le_of_lt hzz0
    linarith
  -- fold: φ(q)·(1+log z) ≤ 3·z₀·log z
  have hkey : (q.totient : ℝ) * (1 + Real.log z) ≤ 3 * z₀ * Real.log z := by
    have hstep : (q.totient : ℝ) * (1 + Real.log z) ≤ (z₀ : ℝ) * (1 + Real.log z) :=
      mul_le_mul_of_nonneg_right hφz0 (by linarith)
    have hstep2 : (z₀ : ℝ) * (1 + Real.log z) ≤ (z₀ : ℝ) * (3 * Real.log z) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    linarith
  calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a), (n.divisors.card : ℝ)
      ≤ (z : ℝ) * (1 + Real.log z) := hmass
    _ = ((z : ℝ) / (q.totient : ℝ)) * ((q.totient : ℝ) * (1 + Real.log z)) := by
        field_simp
    _ ≤ ((z : ℝ) / (q.totient : ℝ)) * (3 * z₀ * Real.log z) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (3 * z₀ : ℝ) * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring

/-! ## §4  The degenerate-class discharge -/

/-- **Degenerate discharge.**  `Σ_deg ≤ w(1+log w) ≤ 3·(z/φ(q))·log z` at the pinned
scale `w = ⌊z^{1/24000}⌋`, since `w ≤ z^{1/24000} ≤ z^{1/8000}` and `z^{1/8000} ≤ z/φ(q)`. -/
theorem classDeg_discharge (z q a : ℕ) (hz : 2 ≤ z) (hq : 1 ≤ q)
    (hqz : (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000)) :
    ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg (wp z) n),
        (n.divisors.card : ℝ)
      ≤ 3 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  have hz1 : 1 ≤ z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hL0 : (0 : ℝ) ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz1)
  have h2L : (1 : ℝ) ≤ 2 * Real.log z := one_le_two_log hz
  have hwpos : (0 : ℝ) ≤ (wp z : ℝ) := by positivity
  have hlogw0 : (0 : ℝ) ≤ Real.log (wp z) := Real.log_nonneg (by exact_mod_cast one_le_wp hz1)
  have hzdiv : (z : ℝ) ^ ((1 : ℝ) / 8000) ≤ (z : ℝ) / (q.totient : ℝ) :=
    z_rpow_le_div_phi hq hz1 hqz
  -- class bound
  have hbase : ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassDeg (wp z) n),
      (n.divisors.card : ℝ) ≤ (wp z : ℝ) * (1 + Real.log (wp z)) :=
    classDeg_tau_le (one_le_wp hz1) z q a
  -- fold w(1+log w) ≤ 3·(z/φq)·log z
  have hexp : (z : ℝ) ^ ((1 : ℝ) / 24000) ≤ (z : ℝ) ^ ((1 : ℝ) / 8000) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hz1) (by norm_num)
  have hfold : (wp z : ℝ) * (1 + Real.log (wp z))
      ≤ 3 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    calc (wp z : ℝ) * (1 + Real.log (wp z))
        ≤ (z : ℝ) ^ ((1 : ℝ) / 24000) * (1 + (1 / 24000 : ℝ) * Real.log z) := by
          apply mul_le_mul wp_le _ (by linarith) (by positivity)
          linarith [logwp_le hz]
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 24000) * (3 * Real.log z) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 8000) * (3 * Real.log z) := by
          apply mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ ((z : ℝ) / (q.totient : ℝ)) * (3 * Real.log z) :=
          mul_le_mul_of_nonneg_right hzdiv (by positivity)
      _ = 3 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring
  linarith

/-! ## §5  The Class I discharge -/

/-- **Class I discharge.**  At the pinned scale `W = ⌊z^{1/48000}⌋`, `w = ⌊z^{1/24000}⌋`,
the class-I bound `shiu_classI_le` fires with `K = 96000`, `Kmain = 1`: the four scale
hypotheses (`z ≤ W^K`, `(log w)² ≤ log W·log z`, the `W³w(1+log w)q ≤ z log z` junk) all
follow from `W ≥ z^{1/96000}` and the pinned exponent arithmetic, giving
`Σ_I ≤ CI·(z/φ(q))·log z`. -/
theorem classI_discharge :
    ∃ (CI BI : ℝ), 0 ≤ CI ∧ ∀ (z q a : ℕ), BI ≤ Real.log z → 1 ≤ q →
      Nat.Coprime a q → (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000) →
      ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassI (wp z) (Wp z) n),
          (n.divisors.card : ℝ)
        ≤ CI * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  obtain ⟨C₁, w₀, hC₁, hI⟩ := shiu_classI_le
  refine ⟨C₁ * (2 : ℝ) ^ (96000 : ℕ) * (1 + 1),
      max (96000 * Real.log 2) (24000 * Real.log ((w₀ : ℝ) + 1)),
      mul_nonneg (mul_nonneg hC₁.le (by positivity)) (by norm_num), ?_⟩
  intro z q a hLz hq ha hqz
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) < 96000 * Real.log 2 := mul_pos (by norm_num) hlog2
  have hL1 : 96000 * Real.log 2 ≤ Real.log z := le_trans (le_max_left _ _) hLz
  have hL2 : 24000 * Real.log ((w₀ : ℝ) + 1) ≤ Real.log z := le_trans (le_max_right _ _) hLz
  have hlogzpos : (0 : ℝ) < Real.log z := lt_of_lt_of_le h0 hL1
  have hz2 : 2 ≤ z := by
    rcases Nat.lt_or_ge z 2 with h | h
    · interval_cases z <;>
        simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one] at hlogzpos <;>
        linarith
    · exact h
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  -- W ≥ 2
  have hW2R : (2 : ℝ) ≤ (Wp z : ℝ) := by
    refine le_trans ?_ (Wp_ge hL1)
    rw [Real.rpow_def_of_pos hzpos,
      show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hW2 : 2 ≤ Wp z := by exact_mod_cast hW2R
  -- w₀ ≤ w
  have hw0R : (w₀ : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 24000) := by
    have hstep : ((w₀ : ℝ) + 1) ≤ (z : ℝ) ^ ((1 : ℝ) / 24000) := by
      rw [Real.rpow_def_of_pos hzpos, show ((w₀ : ℝ) + 1)
          = Real.exp (Real.log ((w₀ : ℝ) + 1)) from (Real.exp_log (by positivity)).symm]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hw0le : w₀ ≤ wp z := Nat.le_floor hw0R
  -- z ≤ W^K
  have hzWKR : (z : ℝ) ≤ (Wp z : ℝ) ^ (96000 : ℕ) := by
    calc (z : ℝ) = ((z : ℝ) ^ ((1 : ℝ) / 96000)) ^ (96000 : ℕ) := by
          rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 96000)) 96000, ← Real.rpow_mul hzpos.le,
            show (1 : ℝ) / 96000 * ((96000 : ℕ) : ℝ) = 1 by push_cast; norm_num, Real.rpow_one]
      _ ≤ (Wp z : ℝ) ^ (96000 : ℕ) := by gcongr; exact Wp_ge hL1
  have hzWK : z ≤ Wp z ^ 96000 := by exact_mod_cast hzWKR
  -- (log w)² ≤ log W · log z
  have hsq : (Real.log (wp z)) ^ 2 ≤ ((1 / 24000 : ℝ) * Real.log z) ^ 2 := by
    have h1 := logwp_le hz2
    have h2 : (0 : ℝ) ≤ Real.log (wp z) :=
      Real.log_nonneg (by exact_mod_cast one_le_wp (by omega))
    nlinarith [h1, h2]
  have hmain : (Real.log (wp z)) ^ 2 ≤ 1 * (Real.log (Wp z) * Real.log z) := by
    have h3 := logWp_ge hL1
    have h4 : (0 : ℝ) ≤ Real.log z := hlogzpos.le
    nlinarith [hsq, h3, h4, mul_nonneg h4 h4]
  -- the junk
  have hlog3 : 48000 * Real.log 3 ≤ Real.log z := by
    have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have h4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    nlinarith [hL1, h34, h4eq]
  have h3cut : (3 : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) / 48000) := by
    rw [Real.rpow_def_of_pos hzpos,
      show (3 : ℝ) = Real.exp (Real.log 3) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have hjunk : (Wp z : ℝ) ^ 3 * (wp z : ℝ) * (1 + Real.log (wp z)) * (q : ℝ)
      ≤ (z : ℝ) * Real.log z := by
    have hW3 : (Wp z : ℝ) ^ 3 ≤ (z : ℝ) ^ ((1 : ℝ) / 16000) := by
      calc (Wp z : ℝ) ^ 3 ≤ ((z : ℝ) ^ ((1 : ℝ) / 48000)) ^ 3 := by gcongr; exact Wp_le
        _ = (z : ℝ) ^ ((1 : ℝ) / 16000) := by
            rw [← Real.rpow_natCast ((z : ℝ) ^ ((1 : ℝ) / 48000)) 3, ← Real.rpow_mul hzpos.le]
            norm_num
    have hlogfac0 : (0 : ℝ) ≤ 1 + Real.log (wp z) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ (wp z : ℝ) by exact_mod_cast one_le_wp (by omega))
      linarith
    have hlogfac : (1 + Real.log (wp z)) ≤ 3 * Real.log z := by
      have := logwp_le hz2; have h2L := one_le_two_log hz2; linarith
    have h3logz0 : (0 : ℝ) ≤ 3 * Real.log z := by linarith [hlogzpos.le]
    -- product of factor bounds
    have hprod : (Wp z : ℝ) ^ 3 * (wp z : ℝ) * (1 + Real.log (wp z)) * (q : ℝ)
        ≤ (z : ℝ) ^ ((1 : ℝ) / 16000) * (z : ℝ) ^ ((1 : ℝ) / 24000) * (3 * Real.log z)
            * (z : ℝ) ^ (1 - (1 : ℝ) / 8000) :=
      mul_le_mul
        (mul_le_mul (mul_le_mul hW3 wp_le (by positivity) (by positivity)) hlogfac hlogfac0
          (by positivity)) hqz (by positivity)
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) h3logz0)
    -- collapse the z-powers
    have hzpow : (z : ℝ) ^ ((1 : ℝ) / 16000) * (z : ℝ) ^ ((1 : ℝ) / 24000)
        * (z : ℝ) ^ (1 - (1 : ℝ) / 8000) = (z : ℝ) ^ (1 - (1 : ℝ) / 48000) := by
      rw [← Real.rpow_add hzpos, ← Real.rpow_add hzpos]; norm_num
    have hcut : 3 * (z : ℝ) ^ (1 - (1 : ℝ) / 48000) ≤ (z : ℝ) := by
      calc 3 * (z : ℝ) ^ (1 - (1 : ℝ) / 48000)
          ≤ (z : ℝ) ^ ((1 : ℝ) / 48000) * (z : ℝ) ^ (1 - (1 : ℝ) / 48000) :=
            mul_le_mul_of_nonneg_right h3cut (by positivity)
        _ = (z : ℝ) := by rw [← Real.rpow_add hzpos]; norm_num
    calc (Wp z : ℝ) ^ 3 * (wp z : ℝ) * (1 + Real.log (wp z)) * (q : ℝ)
        ≤ (z : ℝ) ^ ((1 : ℝ) / 16000) * (z : ℝ) ^ ((1 : ℝ) / 24000) * (3 * Real.log z)
            * (z : ℝ) ^ (1 - (1 : ℝ) / 8000) := hprod
      _ = ((z : ℝ) ^ ((1 : ℝ) / 16000) * (z : ℝ) ^ ((1 : ℝ) / 24000)
            * (z : ℝ) ^ (1 - (1 : ℝ) / 8000)) * (3 * Real.log z) := by ring
      _ = (z : ℝ) ^ (1 - (1 : ℝ) / 48000) * (3 * Real.log z) := by rw [hzpow]
      _ = 3 * (z : ℝ) ^ (1 - (1 : ℝ) / 48000) * Real.log z := by ring
      _ ≤ (z : ℝ) * Real.log z := mul_le_mul_of_nonneg_right hcut hlogzpos.le
  -- fire the class-I bound
  exact hI z q a (wp z) (Wp z) 96000 1 hw0le hW2 hq hz2 ha hzWK (by norm_num) hmain hjunk

/-! ## §6  The Class II discharge -/

/-- **Class II discharge.**  At the pinned scale (`W ≥ 4`, `W² ≤ w`) with `ε = 1/192000`,
`shiu_classII_le` gives `Σ_II ≤ Cε·z^ε·(z/q·4/√W + W)`.  Since `√W ≥ z^{1/192000}` the
`z/q·4/√W` term folds to `4(z/φ(q))` and `z^ε·W ≤ z^{5/192000} ≤ z^{1/8000} ≤ z/φ(q)`,
so `Σ_II ≤ 5Cε·(z/φ(q))·log z`. -/
theorem classII_discharge :
    ∃ (CII BII : ℝ), 0 ≤ CII ∧ ∀ (z q a : ℕ), BII ≤ Real.log z → 1 ≤ q →
      Nat.Coprime a q → (q : ℝ) ≤ (z : ℝ) ^ (1 - (1 : ℝ) / 8000) →
      ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassII (wp z) (Wp z) n),
          (n.divisors.card : ℝ)
        ≤ CII * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
  obtain ⟨Cε, hCε, htau⟩ := card_divisors_le_rpow (1 / 192000) (by norm_num)
  refine ⟨5 * Cε, 192000 * Real.log 2, by positivity, ?_⟩
  intro z q a hLz hq ha hqz
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLbig : 192000 * Real.log 2 ≤ Real.log z := hLz
  have hL1 : 96000 * Real.log 2 ≤ Real.log z := by nlinarith [hLbig, hlog2]
  have hlogzpos : (0 : ℝ) < Real.log z := by nlinarith [hLbig, hlog2]
  have hz2 : 2 ≤ z := by
    rcases Nat.lt_or_ge z 2 with h | h
    · interval_cases z <;>
        simp only [Nat.cast_zero, Nat.cast_one, Real.log_zero, Real.log_one] at hlogzpos <;>
        linarith
    · exact h
  have hz1 : 1 ≤ z := by omega
  have hzpos : (0 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have h4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogz1 : (1 : ℝ) ≤ Real.log z := by nlinarith [hLbig, hlog2gt]
  -- W ≥ 4
  have hW4R : (4 : ℝ) ≤ (Wp z : ℝ) := by
    refine le_trans ?_ (Wp_ge hL1)
    rw [Real.rpow_def_of_pos hzpos,
      show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_le_exp.mpr (by rw [h4eq]; nlinarith [hLbig])
  have hW4 : 4 ≤ Wp z := by exact_mod_cast hW4R
  -- fire the class-II bound
  have hbase := shiu_classII_le (z := z) (1 / 192000 : ℝ) Cε hq hW4 (WpSq_le_wp hz1) ha hCε
    (by norm_num) htau
  -- √W ≥ z^{1/192000}
  have hspos : (0 : ℝ) < (z : ℝ) ^ ((1 : ℝ) / 192000) := Real.rpow_pos_of_pos hzpos _
  have hsqrtWp : (z : ℝ) ^ ((1 : ℝ) / 192000) ≤ Real.sqrt (Wp z) := by
    rw [show (z : ℝ) ^ ((1 : ℝ) / 192000)
        = Real.sqrt ((z : ℝ) ^ ((1 : ℝ) / 96000)) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hzpos.le]; norm_num]
    exact Real.sqrt_le_sqrt (Wp_ge hL1)
  have hzq : (z : ℝ) / (q : ℝ) ≤ (z : ℝ) / (q.totient : ℝ) :=
    div_le_div_of_nonneg_left hzpos.le hφpos hφq
  -- term A: z^ε·(z/q·4/√W) ≤ 4(z/φq)log z
  have htermA : (z : ℝ) ^ ((1 : ℝ) / 192000) * ((z : ℝ) / q * (4 / Real.sqrt (Wp z)))
      ≤ 4 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by
    have h4sw : 4 / Real.sqrt (Wp z) ≤ 4 / (z : ℝ) ^ ((1 : ℝ) / 192000) :=
      div_le_div_of_nonneg_left (by norm_num) hspos hsqrtWp
    calc (z : ℝ) ^ ((1 : ℝ) / 192000) * ((z : ℝ) / q * (4 / Real.sqrt (Wp z)))
        ≤ (z : ℝ) ^ ((1 : ℝ) / 192000)
            * ((z : ℝ) / q * (4 / (z : ℝ) ^ ((1 : ℝ) / 192000))) := by
          apply mul_le_mul_of_nonneg_left _ hspos.le
          exact mul_le_mul_of_nonneg_left h4sw (by positivity)
      _ = 4 * ((z : ℝ) / q) := by field_simp
      _ ≤ 4 * ((z : ℝ) / (q.totient : ℝ)) := mul_le_mul_of_nonneg_left hzq (by norm_num)
      _ ≤ 4 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z :=
          le_mul_of_one_le_right (by positivity) hlogz1
  -- term B: z^ε·W ≤ (z/φq)log z
  have htermB : (z : ℝ) ^ ((1 : ℝ) / 192000) * (Wp z : ℝ)
      ≤ (z : ℝ) / (q.totient : ℝ) * Real.log z := by
    have hpoweq : (z : ℝ) ^ ((1 : ℝ) / 192000) * (z : ℝ) ^ ((1 : ℝ) / 48000)
        = (z : ℝ) ^ ((5 : ℝ) / 192000) := by rw [← Real.rpow_add hzpos]; norm_num
    calc (z : ℝ) ^ ((1 : ℝ) / 192000) * (Wp z : ℝ)
        ≤ (z : ℝ) ^ ((1 : ℝ) / 192000) * (z : ℝ) ^ ((1 : ℝ) / 48000) :=
          mul_le_mul_of_nonneg_left Wp_le hspos.le
      _ = (z : ℝ) ^ ((5 : ℝ) / 192000) := hpoweq
      _ ≤ (z : ℝ) ^ ((1 : ℝ) / 8000) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hz1) (by norm_num)
      _ ≤ (z : ℝ) / (q.totient : ℝ) := z_rpow_le_div_phi hq hz1 hqz
      _ ≤ (z : ℝ) / (q.totient : ℝ) * Real.log z :=
          le_mul_of_one_le_right (by positivity) hlogz1
  -- combine
  calc ∑ n ∈ (Finset.Icc 1 z).filter (fun n => n % q = a ∧ shiuClassII (wp z) (Wp z) n),
          (n.divisors.card : ℝ)
      ≤ Cε * (z : ℝ) ^ ((1 : ℝ) / 192000)
          * ((z : ℝ) / q * (4 / Real.sqrt (Wp z)) + (Wp z : ℝ)) := hbase
    _ = Cε * ((z : ℝ) ^ ((1 : ℝ) / 192000) * ((z : ℝ) / q * (4 / Real.sqrt (Wp z)))
          + (z : ℝ) ^ ((1 : ℝ) / 192000) * (Wp z : ℝ)) := by ring
    _ ≤ Cε * (4 * ((z : ℝ) / (q.totient : ℝ)) * Real.log z
          + (z : ℝ) / (q.totient : ℝ) * Real.log z) :=
        mul_le_mul_of_nonneg_left (add_le_add htermA htermB) hCε.le
    _ = 5 * Cε * ((z : ℝ) / (q.totient : ℝ)) * Real.log z := by ring

end Salt.Maynard
