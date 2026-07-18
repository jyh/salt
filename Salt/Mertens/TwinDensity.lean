/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Mertens.Third
import Salt.TwinBar.TwinDoor
import Salt.HardyLittlewood.Frame

/-!
# The twin-density corollary of Mertens' third theorem (MERT-5)

The Hardy–Littlewood twin constant consumes the sharp asymptotic

`∏_{2<p≤n} (1 − 2/p) · (log n)² → 4·twinC2·e^{−2γ}`

with an explicit `C/log n` error.  The route factors the pointwise identity
`(1 − 2/p) = (1 − 1/p)²·(1 − 1/(p−1)²)` over the primes `2 < p ≤ n`, squares
`mertens_third` (contributing `4·e^{−2γ}` after restoring the `p = 2` factor
`1 − 1/2 = 1/2`), and multiplies by the partial `twinC2` product controlled by
its explicit tail.
-/

open Finset Filter
open Salt.TwinBar

namespace Salt.Mertens

/-! ## Part A — the pointwise and finite-product identities -/

/-- The pointwise identity `1 − 2/x = (1 − 1/x)²·(1 − (x−1)⁻²)` for `x ≥ 2`. -/
theorem one_sub_two_div_eq {x : ℝ} (hx : 2 ≤ x) :
    1 - 2 / x = (1 - 1 / x) ^ 2 * (1 - ((x - 1) ^ 2)⁻¹) := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hx1 : x - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- **The finite product split.**  Over a Finset of naturals all `≥ 3`,
`∏ (1 − 2/p) = (∏ (1 − 1/p))²·∏ (1 − (p−1)⁻²)`. -/
theorem prod_one_sub_two_div {S : Finset ℕ} (hS : ∀ p ∈ S, 3 ≤ p) :
    ∏ p ∈ S, (1 - 2 / (p : ℝ))
      = (∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ 2 * ∏ p ∈ S, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : (2 : ℝ) ≤ (p : ℝ) := by
    have : 3 ≤ p := hS p hp
    exact_mod_cast (by omega : 2 ≤ p)
  exact one_sub_two_div_eq hp3

/-! ## Part B — restoring the `p = 2` factor: `∏_{2<p≤n} (1−1/p) = 2·∏_{p≤n} (1−1/p)` -/

/-- The product over `2 < p ≤ n` of `(1 − 1/p)` is twice the full product over `p ≤ n`
(the missing `p = 2` factor is `1 − 1/2 = 1/2`). -/
theorem prod_gt2_one_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    ∏ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (2 < ·), (1 - 1 / (p : ℝ))
      = 2 * ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  set full := (Finset.range (n + 1)).filter Nat.Prime with hfull
  have hsplit :=
    Finset.prod_filter_mul_prod_filter_not full (2 < ·) (fun p => 1 - 1 / (p : ℝ))
  have hcompl : full.filter (fun p => ¬ 2 < p) = {2} := by
    ext p
    simp only [hfull, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, not_lt]
    constructor
    · rintro ⟨⟨_, hp⟩, hp2⟩
      have := hp.two_le
      omega
    · rintro rfl
      exact ⟨⟨by omega, Nat.prime_two⟩, by omega⟩
  rw [hcompl, Finset.prod_singleton] at hsplit
  simp only [Nat.cast_ofNat] at hsplit
  have h12 : (1 : ℝ) - 1 / (2 : ℝ) = 1 / 2 := by norm_num
  rw [h12] at hsplit
  linarith [hsplit]

/-! ## Part C — the partial `twinC2` product and its explicit tail -/

/-- The primes `2 < p ≤ n`, as a `Finset ℕ` (the index of the partial twin product). -/
abbrev gt2Primes (n : ℕ) : Finset ℕ :=
  ((Finset.range (n + 1)).filter Nat.Prime).filter (2 < ·)

theorem mem_gt2Primes {n p : ℕ} : p ∈ gt2Primes n ↔ p ≤ n ∧ p.Prime ∧ 2 < p := by
  simp only [gt2Primes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hr, hp⟩, h2⟩; exact ⟨by omega, hp, h2⟩
  · rintro ⟨hn, hp, h2⟩; exact ⟨⟨by omega, hp⟩, h2⟩

/-- The analytic pointwise bound `−log(1 − y) ≤ (4/3)·y` for `0 ≤ y ≤ 1/4`. -/
theorem neg_log_one_sub_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 4) :
    -Real.log (1 - y) ≤ 4 / 3 * y := by
  have h1y : (0 : ℝ) < 1 - y := by linarith
  have hinv : Real.log (1 - y)⁻¹ ≤ (1 - y)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [← Real.log_inv]
  refine le_trans hinv ?_
  have hzc : (1 - y)⁻¹ * (1 - y) = 1 := inv_mul_cancel₀ (ne_of_gt h1y)
  nlinarith [hzc, h1y, mul_nonneg hy0 (show (0 : ℝ) ≤ 1 - 4 * y by linarith)]

/-- Each ℕ-indexed factor `1 − (p−1)⁻²` is positive for `p ≥ 3`. -/
theorem factorN_pos {p : ℕ} (hp : 3 ≤ p) : 0 < 1 - (((p : ℝ) - 1) ^ 2)⁻¹ := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hz : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hinv : (((p : ℝ) - 1) ^ 2)⁻¹ ≤ (4 : ℝ)⁻¹ := by gcongr
  have : (4 : ℝ)⁻¹ < 1 := by norm_num
  linarith

/-- The value `(p−1)⁻²` lies in `[0, 1/4]` for `p ≥ 3`. -/
theorem factorN_arg_le {p : ℕ} (hp : 3 ≤ p) :
    (0 : ℝ) ≤ (((p : ℝ) - 1) ^ 2)⁻¹ ∧ (((p : ℝ) - 1) ^ 2)⁻¹ ≤ 1 / 4 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hz : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_⟩
  rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num]
  gcongr

/-- The partial twin product as an exponential of the log-sum. -/
theorem prod_factor_eq_exp_sum (n : ℕ) :
    ∏ p ∈ gt2Primes n, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)
      = Real.exp (∑ p ∈ gt2Primes n, Real.log (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have h2 : 2 < p := (mem_gt2Primes.mp hp).2.2
  rw [Real.exp_log (factorN_pos (by omega))]

/-- **The finite-subset tail estimate.**  For any finite set `u` of primes `> n` (packaged
as the complement subtype of `T`), the sum of `−log(1 − (p−1)⁻²)` is `≤ (4/3)/(n−1)`, via the
pointwise log bound, reindexing `p ↦ p−1`, and the `∑ 1/k²` tail `sum_Ioc_inv_sq_le_sub`. -/
theorem tail_finset_bound {n : ℕ} (hn : 4 ≤ n) (T : Finset PrimesGt2)
    (hTgt : ∀ x : PrimesGt2, x ∉ T → n < ((x : PrimesGt2) : ℕ))
    (u : Finset {p : PrimesGt2 // p ∉ T}) :
    ∑ x ∈ u, -Real.log (1 - (((((x : PrimesGt2) : ℕ) : ℝ) - 1) ^ 2)⁻¹)
      ≤ 4 / 3 * ((n : ℝ) - 1)⁻¹ := by
  classical
  set j : {p : PrimesGt2 // p ∉ T} → ℕ := fun x => ((x : PrimesGt2) : ℕ) - 1 with hj
  have hxgt : ∀ x : {p : PrimesGt2 // p ∉ T}, n < ((x : PrimesGt2) : ℕ) := fun x => hTgt x.1 x.2
  have hxge3 : ∀ x : {p : PrimesGt2 // p ∉ T}, 3 ≤ ((x : PrimesGt2) : ℕ) := fun x => x.1.2.2
  -- Step A: pointwise log bound `−log(1−y) ≤ (4/3)y`
  have hstepA : ∑ x ∈ u, -Real.log (1 - (((((x : PrimesGt2) : ℕ) : ℝ) - 1) ^ 2)⁻¹)
      ≤ ∑ x ∈ u, 4 / 3 * (((((x : PrimesGt2) : ℕ) : ℝ) - 1) ^ 2)⁻¹ := by
    refine Finset.sum_le_sum (fun x _ => ?_)
    obtain ⟨hy0, hy⟩ := factorN_arg_le (hxge3 x)
    exact neg_log_one_sub_le hy0 hy
  refine le_trans hstepA ?_
  rw [← Finset.mul_sum]
  -- Step B/C: rewrite `((x:ℕ)−1)⁻²` as `(j x)⁻²`, then reindex over the image
  have hrw : ∀ x ∈ u, (((((x : PrimesGt2) : ℕ) : ℝ) - 1) ^ 2)⁻¹ = ((j x : ℝ) ^ 2)⁻¹ := by
    intro x _
    have h1 : 1 ≤ ((x : PrimesGt2) : ℕ) := by have := hxge3 x; omega
    have hc : (j x : ℝ) = (((x : PrimesGt2) : ℕ) : ℝ) - 1 := by
      simp only [hj]; rw [Nat.cast_sub h1]; push_cast; ring
    rw [hc]
  rw [Finset.sum_congr rfl hrw]
  have hjinj : Set.InjOn j ↑u := by
    intro x _ y _ hxy
    have hx := hxgt x; have hy := hxgt y
    simp only [hj] at hxy
    apply Subtype.ext
    apply Subtype.ext
    omega
  have himage : ∑ x ∈ u, ((j x : ℝ) ^ 2)⁻¹ = ∑ k ∈ u.image j, ((k : ℝ) ^ 2)⁻¹ :=
    (Finset.sum_image (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) hjinj).symm
  rw [himage]
  -- Step D/E: bound the reindexed sum by the `∑ 1/k²` tail on `Ioc (n−1) M`
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rcases Finset.eq_empty_or_nonempty u with hu | hu
  · subst hu
    simp only [Finset.image_empty, Finset.sum_empty, mul_zero]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hn1)
  · set M : ℕ := (u.image j).sup id with hM
    have hsub : u.image j ⊆ Finset.Ioc (n - 1) M := by
      intro k hk
      simp only [Finset.mem_image] at hk
      obtain ⟨x, hxu, rfl⟩ := hk
      have hxg := hxgt x
      rw [Finset.mem_Ioc]
      exact ⟨by simp only [hj]; omega, Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨x, hxu, rfl⟩)⟩
    have hnonneg : ∀ k ∈ Finset.Ioc (n - 1) M, k ∉ u.image j → 0 ≤ ((k : ℝ) ^ 2)⁻¹ :=
      fun k _ _ => by positivity
    refine le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg) (by norm_num)) ?_
    have hMge : n - 1 ≤ M := by
      obtain ⟨x, hxu⟩ := hu
      have hmem : j x ∈ u.image j := Finset.mem_image.mpr ⟨x, hxu, rfl⟩
      have hle : j x ≤ M := Finset.le_sup (f := id) hmem
      have hjx : n ≤ j x := by simp only [hj]; have := hxgt x; omega
      omega
    have hk0 : n - 1 ≠ 0 := by omega
    have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) hk0 hMge
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
    rw [hcast] at htail
    have hMinv : (0 : ℝ) ≤ ((M : ℕ) : ℝ)⁻¹ := by positivity
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4 / 3)
    linarith [htail, hMinv]

/-- **The partial twin product converges to `twinC2` at rate `1/(n−1)`.**
`|∏_{2<p≤n} (1 − (p−1)⁻²) − twinC2| ≤ (8/3)/(n−1)` for `n ≥ 4`, via
`twinC2 = exp(∑' log)`, the tsum split at the primes `≤ n`, and `tail_finset_bound`. -/
theorem abs_prodFactor_sub_twinC2_le {n : ℕ} (hn : 4 ≤ n) :
    |(∏ p ∈ gt2Primes n, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) - twinC2|
      ≤ 8 / 3 * ((n : ℝ) - 1)⁻¹ := by
  classical
  set g : PrimesGt2 → ℝ := fun p => Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) with hg
  have hgsum : Summable g := twinC2_log_summable
  have htwin : twinC2 = Real.exp (∑' p, g p) :=
    (Real.rexp_tsum_eq_tprod twinC2_factor_pos twinC2_log_summable).symm
  -- each log-factor is `≤ 0`
  have hgnonpos : ∀ p : PrimesGt2, g p ≤ 0 := by
    intro p
    have hx3 : 3 ≤ (p : ℕ) := by have := p.2.2; omega
    obtain ⟨hi0, hi4⟩ := factorN_arg_le hx3
    exact Real.log_nonpos (le_of_lt (factorN_pos hx3)) (by linarith)
  -- the subtype of primes `≤ n`; its complement is the primes `> n`
  set T : Finset PrimesGt2 := (gt2Primes n).subtype (fun p => p.Prime ∧ 2 < p) with hT
  have hTgt : ∀ x : PrimesGt2, x ∉ T → n < ((x : PrimesGt2) : ℕ) := by
    intro x hx
    by_contra hle
    push_neg at hle
    exact hx (by rw [hT, Finset.mem_subtype, mem_gt2Primes]; exact ⟨hle, x.2.1, x.2.2⟩)
  -- the partial log-sum equals `L`
  have hLsub : ∑ p ∈ T, g p
      = ∑ p ∈ gt2Primes n, Real.log (1 - (((p : ℝ) - 1) ^ 2)⁻¹) := by
    rw [hT]
    exact Finset.sum_subtype_of_mem (fun k : ℕ => Real.log (1 - (((k : ℝ) - 1) ^ 2)⁻¹))
      (fun x hx => ⟨(mem_gt2Primes.mp hx).2.1, (mem_gt2Primes.mp hx).2.2⟩)
  set L : ℝ := ∑ p ∈ gt2Primes n, Real.log (1 - (((p : ℝ) - 1) ^ 2)⁻¹) with hLdef
  have hQ : (∏ p ∈ gt2Primes n, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) = Real.exp L :=
    prod_factor_eq_exp_sum n
  -- `δ := ∑'_{p ∉ T} (−g p) = L − ∑' g`
  set δ : ℝ := ∑' x : {p : PrimesGt2 // p ∉ T}, -g x with hδ
  have hδeq : δ = L - ∑' p, g p := by
    rw [hδ, tsum_neg]
    have h := hgsum.sum_add_tsum_subtype_compl T
    rw [hLsub] at h
    linarith
  have hδnn : 0 ≤ δ := by
    rw [hδ]
    exact tsum_nonneg (fun x => neg_nonneg.mpr (hgnonpos x))
  have hδle : δ ≤ 4 / 3 * ((n : ℝ) - 1)⁻¹ := by
    rw [hδ]
    exact Real.tsum_le_of_sum_le (fun x => neg_nonneg.mpr (hgnonpos x))
      (fun u => tail_finset_bound hn T hTgt u)
  -- `Q = twinC2 · exp δ`
  have hQval : (∏ p ∈ gt2Primes n, (1 - (((p : ℝ) - 1) ^ 2)⁻¹)) = twinC2 * Real.exp δ := by
    rw [hQ, htwin, ← Real.exp_add]
    congr 1
    rw [hδeq]; ring
  -- `δ ≤ 1` and `twinC2 ≤ 1`
  have hn3 : (3 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hinv3 : ((n : ℝ) - 1)⁻¹ ≤ (3 : ℝ)⁻¹ := by gcongr
  have hδ1 : δ ≤ 1 := le_trans hδle
    (le_trans (mul_le_mul_of_nonneg_left hinv3 (by norm_num)) (by norm_num))
  have htw1 : twinC2 ≤ 1 := by
    rw [htwin, show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact Real.exp_le_exp.mpr (tsum_nonpos hgnonpos)
  -- assemble
  have habs : |Real.exp δ - 1| ≤ 2 * δ := by
    have h := Real.abs_exp_sub_one_le (show |δ| ≤ 1 by rwa [abs_of_nonneg hδnn])
    rwa [abs_of_nonneg hδnn] at h
  rw [hQval, show twinC2 * Real.exp δ - twinC2 = twinC2 * (Real.exp δ - 1) from by ring,
    abs_mul, abs_of_pos twinC2_pos]
  calc twinC2 * |Real.exp δ - 1|
      ≤ twinC2 * (2 * δ) := mul_le_mul_of_nonneg_left habs (le_of_lt twinC2_pos)
    _ ≤ 1 * (2 * δ) := mul_le_mul_of_nonneg_right htw1 (by positivity)
    _ = 2 * δ := by ring
    _ ≤ 8 / 3 * ((n : ℝ) - 1)⁻¹ := by linarith [hδle]

/-- `twinC2 ≤ 1` (each Euler factor is `≤ 1`). -/
theorem twinC2_le_one : twinC2 ≤ 1 := by
  have hnonpos : ∀ p : PrimesGt2, Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹) ≤ 0 := by
    intro p
    have hx3 : 3 ≤ (p : ℕ) := by have := p.2.2; omega
    obtain ⟨hi0, hi4⟩ := factorN_arg_le hx3
    exact Real.log_nonpos (le_of_lt (factorN_pos hx3)) (by linarith)
  calc twinC2 = Real.exp (∑' p : PrimesGt2, Real.log (1 - ((((p : ℕ) : ℝ) - 1) ^ 2)⁻¹)) :=
        (Real.rexp_tsum_eq_tprod twinC2_factor_pos twinC2_log_summable).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (tsum_nonpos hnonpos)
    _ = 1 := Real.exp_zero

/-! ## Part D — the twin-density corollary (MERT-5) -/

/-- **The twin-density corollary of Mertens' third theorem.**  For `n ≥ 4`,
`|∏_{2<p≤n} (1 − 2/p) · (log n)² − 4·twinC2·e^{−2γ}| ≤ C / log n`.  Squares `mertens_third`
(restoring `4` from the `p = 2` factor), multiplies by the partial `twinC2` product, and
assembles the three error pieces. -/
theorem mertens_twin_density :
    ∃ C, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      |(∏ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (2 < ·), (1 - 2 / (p : ℝ)))
            * (Real.log n) ^ 2
          - 4 * Salt.TwinBar.twinC2 * Real.exp (-2 * Real.eulerMascheroniConstant)|
        ≤ C / Real.log n := by
  obtain ⟨C₃, hC₃0, hmt⟩ := mertens_third
  set β : ℝ := 2 * Real.exp (-Real.eulerMascheroniConstant) with hβ
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h2C3 : (0 : ℝ) ≤ 2 * C₃ := mul_nonneg (by norm_num) hC₃0
  set Mα : ℝ := β + 2 * C₃ / Real.log 4 with hMαdef
  have hMα0 : 0 ≤ Mα := by
    rw [hMαdef]; exact add_nonneg hβ0 (div_nonneg h2C3 (le_of_lt hlog4))
  have hβ2 : β ^ 2 = 4 * Real.exp (-2 * Real.eulerMascheroniConstant) := by
    have hexp2 : Real.exp (-Real.eulerMascheroniConstant) ^ 2
        = Real.exp (-2 * Real.eulerMascheroniConstant) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [hβ, mul_pow, hexp2]; norm_num
  refine ⟨Mα ^ 2 * (8 / 3) + 2 * C₃ * (Mα + β),
    add_nonneg (mul_nonneg (sq_nonneg _) (by norm_num))
      (mul_nonneg h2C3 (add_nonneg hMα0 hβ0)), fun n hn => ?_⟩
  set C : ℝ := Mα ^ 2 * (8 / 3) + 2 * C₃ * (Mα + β) with hCdef
  have hn3 : 3 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog4n : Real.log 4 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  -- Pfull, P, and their positivity
  set Pfull : ℝ := ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) with hPfull
  set P : ℝ := ∏ p ∈ gt2Primes n, (1 - (((p : ℝ) - 1) ^ 2)⁻¹) with hPdef
  have hPfullpos : 0 < Pfull := by
    rw [hPfull]
    refine Finset.prod_pos (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
    have : (1 : ℝ) / p ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hp2
    linarith
  -- the twin product identity and the mertens-third estimate
  have hS3 : ∀ p ∈ gt2Primes n, 3 ≤ p := fun p hp => by
    have := (mem_gt2Primes.mp hp).2.2; omega
  have hprod : (∏ p ∈ gt2Primes n, (1 - 2 / (p : ℝ))) = (2 * Pfull) ^ 2 * P := by
    rw [prod_one_sub_two_div hS3, prod_gt2_one_sub_inv hn2, ← hPdef]
  set α : ℝ := 2 * Pfull * Real.log n with hαdef
  have hαnn : 0 ≤ α := by rw [hαdef]; positivity
  have hmtn := hmt n hn3
  rw [← hPfull] at hmtn
  have hαβ : |α - β| ≤ 2 * C₃ / Real.log n := by
    have heq : α - β = 2 * (Pfull * Real.log n - Real.exp (-Real.eulerMascheroniConstant)) := by
      rw [hαdef, hβ]; ring
    rw [heq, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    have := abs_nonneg (Pfull * Real.log n - Real.exp (-Real.eulerMascheroniConstant))
    calc 2 * |Pfull * Real.log n - Real.exp (-Real.eulerMascheroniConstant)|
        ≤ 2 * (C₃ / Real.log n) := by linarith [hmtn]
      _ = 2 * C₃ / Real.log n := by ring
  have hMα : α ≤ Mα := by
    have h1 : α ≤ β + 2 * C₃ / Real.log n := by have := (abs_le.mp hαβ).2; linarith
    have h2 : 2 * C₃ / Real.log n ≤ 2 * C₃ / Real.log 4 :=
      div_le_div_of_nonneg_left h2C3 hlog4 hlog4n
    rw [hMαdef]; linarith
  have hPtw := abs_prodFactor_sub_twinC2_le hn
  rw [← hPdef] at hPtw
  have hconv : ((n : ℝ) - 1)⁻¹ ≤ (Real.log n)⁻¹ := by
    have hle : Real.log n ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    gcongr
  -- rewrite the target into `α²·P − β²·twinC2`
  show |(∏ p ∈ gt2Primes n, (1 - 2 / (p : ℝ))) * (Real.log n) ^ 2
      - 4 * twinC2 * Real.exp (-2 * Real.eulerMascheroniConstant)| ≤ C / Real.log n
  rw [hprod, show 4 * twinC2 * Real.exp (-2 * Real.eulerMascheroniConstant) = β ^ 2 * twinC2 from by
        rw [hβ2]; ring,
    show (2 * Pfull) ^ 2 * P * (Real.log n) ^ 2 = α ^ 2 * P from by rw [hαdef]; ring]
  calc |α ^ 2 * P - β ^ 2 * twinC2|
      ≤ α ^ 2 * |P - twinC2| + |α ^ 2 - β ^ 2| * twinC2 := by
        rw [show α ^ 2 * P - β ^ 2 * twinC2
            = α ^ 2 * (P - twinC2) + (α ^ 2 - β ^ 2) * twinC2 from by ring]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_of_nonneg (sq_nonneg α), abs_mul, abs_of_pos twinC2_pos]
    _ ≤ Mα ^ 2 * (8 / 3) * (Real.log n)⁻¹ + 2 * C₃ * (Mα + β) * (Real.log n)⁻¹ := by
        apply add_le_add
        · calc α ^ 2 * |P - twinC2|
              ≤ Mα ^ 2 * (8 / 3 * ((n : ℝ) - 1)⁻¹) :=
                mul_le_mul (pow_le_pow_left₀ hαnn hMα 2) hPtw (abs_nonneg _) (sq_nonneg _)
            _ ≤ Mα ^ 2 * (8 / 3 * (Real.log n)⁻¹) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hconv (by norm_num)) (sq_nonneg _)
            _ = Mα ^ 2 * (8 / 3) * (Real.log n)⁻¹ := by ring
        · calc |α ^ 2 - β ^ 2| * twinC2
              ≤ 2 * C₃ / Real.log n * (Mα + β) * 1 := by
                apply mul_le_mul _ twinC2_le_one (le_of_lt twinC2_pos)
                  (mul_nonneg (by positivity) (add_nonneg hMα0 hβ0))
                rw [show α ^ 2 - β ^ 2 = (α - β) * (α + β) from by ring, abs_mul]
                exact mul_le_mul hαβ
                  (by rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α + β)]; linarith)
                  (abs_nonneg _) (by positivity)
            _ = 2 * C₃ * (Mα + β) * (Real.log n)⁻¹ := by rw [mul_one, div_eq_mul_inv]; ring
    _ = C / Real.log n := by rw [hCdef, div_eq_mul_inv]; ring

/-- **Twin-density corollary, singular-series form.**  The same estimate with the
Hardy–Littlewood constant `𝔖 = 2·Π₂ = 2·twinC2` in place of `4·twinC2`:
`|∏_{2<p≤n} (1 − 2/p) · (log n)² − 2·𝔖·e^{−2γ}| ≤ C / log n`. -/
theorem mertens_twin_density_singularSeries :
    ∃ C, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n →
      |(∏ p ∈ ((Finset.range (n + 1)).filter Nat.Prime).filter (2 < ·), (1 - 2 / (p : ℝ)))
            * (Real.log n) ^ 2
          - 2 * Salt.HardyLittlewood.twinSingularSeries
              * Real.exp (-2 * Real.eulerMascheroniConstant)|
        ≤ C / Real.log n := by
  obtain ⟨C, hC0, h⟩ := mertens_twin_density
  refine ⟨C, hC0, fun n hn => ?_⟩
  rw [show 2 * Salt.HardyLittlewood.twinSingularSeries = 4 * Salt.TwinBar.twinC2 from by
    unfold Salt.HardyLittlewood.twinSingularSeries Salt.HardyLittlewood.Pi2; ring]
  exact h n hn

end Salt.Mertens
