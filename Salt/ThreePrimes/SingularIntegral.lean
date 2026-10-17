/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ExpSum.Basic
import Salt.LS.Parseval
import Salt.MR.MinorArcVaughan

/-!
# Three primes: the singular integral

These are lemmas L9 and L10 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Step 4a).

On a major arc, `S(a/q + β)` is approximated by `(μ(q)/φ(q)) v(β)`, where

  `v(β) = Σ_{1 ≤ n ≤ N} e(nβ)`

is the same exponential sum with every weight replaced by `1`. When the approximation is cubed and
integrated over the arc, what is left after the arithmetic is the **singular integral**
`∫ v(β)³ e(−Nβ) dβ` over `|β| ≤ δ`, with `δ = P/N` the arc's half-width.

* **Over the whole circle it is a count.** Expanding the cube and integrating term by term,
  orthogonality `∫₀¹ e(mβ) dβ = [m = 0]` keeps exactly the triples with `n₁ + n₂ + n₃ = N`, so
  `∫₀¹ v(β)³ e(−Nβ) dβ = #{(n₁, n₂, n₃) : nᵢ ≥ 1, n₁ + n₂ + n₃ = N} = C(N − 1, 2) = (N−1)(N−2)/2`.
  A reader can check this by hand: it is the number of ways to cut `N` stones into three non-empty
  heaps.
* **Truncating it to the arc costs `O(1/δ²)`.** `v` is a geometric sum, so `|v(β)| ≤ 1/(2|β|)` for
  `0 < |β| ≤ 1/2`, and then `∫_{δ ≤ |β| ≤ 1/2} |v|³ ≤ 1/(8δ²)`. With `δ = P/N` this is
  `O(N²/P²)`, smaller than the main term `N²/2` by the factor `P²`.

The bridge lemma `LS_e_eq_eR` says that the two names this corpus uses for `x ↦ exp(2πix)` (one
from the large-sieve files, one from the exponential-sum files) are the same function, so the
orthogonality proved for one serves the other.
-/

namespace Salt.ThreePrimes

open Salt.ExpSum (eR norm_eR)

/-- The two spellings of `e(x) = exp(2πix)` in this corpus, `Salt.LS.e` and `Salt.ExpSum.eR`, are
the same function. -/
theorem LS_e_eq_eR (x : ℝ) : Salt.LS.e x = eR x := rfl

/-- **The unweighted exponential sum** `v(β) = Σ_{1 ≤ n ≤ N} e(nβ)`. -/
noncomputable def expSumOne (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, eR ((n : ℝ) * β)

/-- **The trivial bound** `|v(β)| ≤ N`: `N` phases of modulus one. -/
theorem norm_expSumOne_le (N : ℕ) (β : ℝ) : ‖expSumOne N β‖ ≤ N := by
  unfold expSumOne
  refine (norm_sum_le _ _).trans ?_
  simp

/-- For `|β| ≤ 1/2` the distance from `β` to the nearest integer is `|β|` itself (here: at
least `|β|`), since every nonzero integer is at least `1/2` away from `β`. -/
theorem abs_le_dist₁_zero {β : ℝ} (hβ' : |β| ≤ 1 / 2) : |β| ≤ Salt.LS.dist₁ β 0 := by
  unfold Salt.LS.dist₁
  rw [sub_zero]
  by_cases hk : round β = 0
  · simp [hk]
  · have h1 : (1 : ℝ) ≤ |((round β : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    have h2 := abs_sub_abs_le_abs_sub ((round β : ℤ) : ℝ) β
    rw [abs_sub_comm] at h2
    linarith

/-- **The geometric-sum bound** `|v(β)| ≤ 1/(2|β|)` for `0 < |β| ≤ 1/2`. The sum is
`e(β)(e(Nβ) − 1)/(e(β) − 1)`, its numerator has modulus at most `2`, and
`|e(β) − 1| = 2|sin(πβ)| ≥ 4|β|` on that range. -/
theorem norm_expSumOne_le_inv (N : ℕ) {β : ℝ} (hβ : 0 < |β|) (hβ' : |β| ≤ 1 / 2) :
    ‖expSumOne N β‖ ≤ 1 / (2 * |β|) := by
  have hd := abs_le_dist₁_zero hβ'
  have hd0 : Salt.LS.dist₁ β 0 ≠ 0 := by linarith
  have hsum : expSumOne N β = ∑ m ∈ Finset.Ioc 0 N, eR (β * (m : ℝ)) := by
    unfold expSumOne
    rw [show Finset.Icc 1 N = Finset.Ioc 0 N by
      ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
    exact Finset.sum_congr rfl (fun m _ => by rw [mul_comm])
  rw [hsum]
  refine (Salt.MR.geom_phase_dist_bound β 0 N hd0).trans ?_
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The arithmetic sum `Σ_{1 ≤ a ≤ n+1} (n − a) = C(n, 2)` (natural subtraction): the last
step of counting the triples. -/
theorem sum_Icc_sub_eq_choose_two (n : ℕ) :
    ∑ a ∈ Finset.Icc 1 (n + 1), (n - a) = n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : ∑ a ∈ Finset.Icc 1 (n + 1 + 1), (n + 1 - a)
        = ∑ a ∈ Finset.Icc 1 (n + 1), (n + 1 - a) := by
      rw [Finset.sum_Icc_succ_top (by omega), show n + 1 - (n + 1 + 1) = 0 by omega, add_zero]
    have e2 : ∑ a ∈ Finset.Icc 1 (n + 1), (n + 1 - a) = ∑ a ∈ Finset.Icc 1 n, (n + 1 - a) := by
      rw [Finset.sum_Icc_succ_top (by omega), show n + 1 - (n + 1) = 0 by omega, add_zero]
    have e3 : ∑ a ∈ Finset.Icc 1 (n + 1), (n - a) = ∑ a ∈ Finset.Icc 1 n, (n - a) := by
      rw [Finset.sum_Icc_succ_top (by omega), show n - (n + 1) = 0 by omega, add_zero]
    have h : ∑ a ∈ Finset.Icc 1 n, (n + 1 - a) = ∑ a ∈ Finset.Icc 1 n, ((n - a) + 1) :=
      Finset.sum_congr rfl (fun a ha => by rw [Finset.mem_Icc] at ha; omega)
    have hs : ∑ a ∈ Finset.Icc 1 n, (1 : ℕ) = n := by simp
    have hc : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
    rw [e1, e2, h, Finset.sum_add_distrib, ← e3, ih, hs, hc, Nat.choose_one_right]
    omega

/-- **Cutting `N` stones into three non-empty heaps:** the number of ordered triples in
`[1, N]³` with `a + b + c = N` is `C(N − 1, 2)`. -/
theorem count_triples (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
      (if a + b + c = N then 1 else 0 : ℕ)) = (N - 1).choose 2 := by
  have hc : ∀ a b : ℕ, (∑ c ∈ Finset.Icc 1 N, (if a + b + c = N then 1 else 0 : ℕ))
      = if a + b + 1 ≤ N then 1 else 0 := by
    intro a b
    rw [Finset.sum_boole]
    split_ifs with h
    · rw [show (Finset.Icc 1 N).filter (fun c => a + b + c = N) = {N - a - b} by
        ext c; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]; omega]
      simp
    · rw [show (Finset.Icc 1 N).filter (fun c => a + b + c = N) = ∅ by
        ext c; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty,
          iff_false]; omega]
      simp
  have hb : ∀ a : ℕ, (∑ b ∈ Finset.Icc 1 N, (if a + b + 1 ≤ N then 1 else 0 : ℕ))
      = N - a - 1 := by
    intro a
    rw [Finset.sum_boole, show (Finset.Icc 1 N).filter (fun b => a + b + 1 ≤ N)
        = Finset.Icc 1 (N - a - 1) by
      ext b; simp only [Finset.mem_filter, Finset.mem_Icc]; omega]
    simp
  simp only [hc, hb]
  rcases N with _ | n
  · simp
  · rw [show n + 1 - 1 = n by omega, ← sum_Icc_sub_eq_choose_two n]
    exact Finset.sum_congr rfl (fun a _ => by omega)

/-- `v` is continuous: a finite sum of continuous phases. -/
theorem continuous_expSumOne (N : ℕ) : Continuous (expSumOne N) := by
  unfold expSumOne
  exact continuous_finsetSum _ fun n _ =>
    Salt.LS.continuous_e.comp (continuous_const.mul continuous_id)

/-- **Expanding the cube:** `v(β)³ e(−Nβ)` is the triple sum of `e((a + b + c − N)β)` over
`a, b, c ∈ [1, N]`. -/
theorem expSumOne_cube_expand (N : ℕ) (β : ℝ) :
    expSumOne N β ^ 3 * eR (-(N : ℝ) * β) = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
      ∑ c ∈ Finset.Icc 1 N, Salt.LS.e ((((a + b + c : ℕ) : ℤ) - N : ℤ) * β) := by
  simp only [expSumOne, pow_three, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  rw [LS_e_eq_eR, ← Salt.ExpSum.eR_add, ← Salt.ExpSum.eR_add, ← Salt.ExpSum.eR_add]
  congr 1
  push_cast
  ring

/-- **The singular integral over the whole circle is a count:** `∫₀¹ v(β)³ e(−Nβ) dβ = C(N − 1, 2)`,
the number of ordered triples of positive integers summing to `N`. -/
theorem integral_expSumOne_cube (N : ℕ) :
    (∫ β in (0 : ℝ)..1, expSumOne N β ^ 3 * eR (-(N : ℝ) * β)) = ((N - 1).choose 2 : ℂ) := by
  have hcont : ∀ k : ℤ, Continuous fun β : ℝ => Salt.LS.e ((k : ℝ) * β) := fun k =>
    Salt.LS.continuous_e.comp (continuous_const.mul continuous_id)
  rw [intervalIntegral.integral_congr (fun β _ => expSumOne_cube_expand N β),
    intervalIntegral.integral_finsetSum fun a _ => (continuous_finsetSum _ fun b _ =>
      continuous_finsetSum _ fun c _ => hcont _).intervalIntegrable _ _]
  have inner : ∀ a : ℕ, (∫ β in (0 : ℝ)..1, ∑ b ∈ Finset.Icc 1 N, ∑ c ∈ Finset.Icc 1 N,
      Salt.LS.e ((((a + b + c : ℕ) : ℤ) - N : ℤ) * β)) = ∑ b ∈ Finset.Icc 1 N,
      ∑ c ∈ Finset.Icc 1 N, ∫ β in (0 : ℝ)..1, Salt.LS.e ((((a + b + c : ℕ) : ℤ) - N : ℤ) * β) := by
    intro a
    rw [intervalIntegral.integral_finsetSum fun b _ =>
      (continuous_finsetSum _ fun c _ => hcont _).intervalIntegrable _ _]
    exact Finset.sum_congr rfl fun b _ =>
      intervalIntegral.integral_finsetSum fun c _ => (hcont _).intervalIntegrable _ _
  have key : ∀ a b c : ℕ, (if ((a + b + c : ℕ) : ℤ) - (N : ℤ) = 0 then (1 : ℂ) else 0)
      = ((if a + b + c = N then 1 else 0 : ℕ) : ℂ) := by
    intro a b c
    split_ifs with h1 h2 h2 <;> first | omega | simp
  simp only [inner, Salt.LS.integral_e_int, key]
  rw [← count_triples]
  simp only [Nat.cast_sum]

/-- The tail profile: if `|G(β)| ≤ 1/(8β³)` on `[δ, 1/2]` then `|∫_δ^{1/2} G| ≤ 1/(16δ²)`, by
integrating the profile exactly (antiderivative `−1/(16β²)`). -/
theorem norm_integral_tail_le {G : ℝ → ℂ} (hG : Continuous G) {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (hb : ∀ β ∈ Set.Icc δ (1 / 2), ‖G β‖ ≤ 1 / (8 * β ^ 3)) :
    ‖∫ β in δ..(1 / 2), G β‖ ≤ 1 / (16 * δ ^ 2) := by
  have hderiv : ∀ x ∈ Set.uIcc δ (1 / 2),
      HasDerivAt (fun x : ℝ => -1 / (16 * x ^ 2)) (1 / (8 * x ^ 3)) x := by
    intro x hx
    rw [Set.uIcc_of_le hδ'] at hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hx.1)
    have h1 := ((hasDerivAt_pow 2 x).inv (pow_ne_zero 2 hx0)).const_mul (-(1 / 16) : ℝ)
    have hfun : (fun x : ℝ => -1 / (16 * x ^ 2)) = fun y => -(1 / 16) * (y ^ 2)⁻¹ := by
      funext y; ring
    rw [hfun]
    refine h1.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (8 * x ^ 3)) MeasureTheory.volume δ (1 / 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    rw [Set.uIcc_of_le hδ'] at hx
    have : 0 < x := lt_of_lt_of_le hδ hx.1
    positivity
  have hcalc : ∫ x in δ..(1 / 2), 1 / (8 * x ^ 3) = -1 / (16 * (1 / 2) ^ 2) - -1 / (16 * δ ^ 2) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h4 : -1 / (16 * (1 / 2 : ℝ) ^ 2) = -1 / 4 := by norm_num
  calc ‖∫ β in δ..(1 / 2), G β‖ ≤ ∫ β in δ..(1 / 2), ‖G β‖ :=
        intervalIntegral.norm_integral_le_integral_norm hδ'
    _ ≤ ∫ x in δ..(1 / 2), 1 / (8 * x ^ 3) :=
        intervalIntegral.integral_mono_on hδ' (hG.norm.intervalIntegrable _ _) hint hb
    _ = -1 / (16 * (1 / 2) ^ 2) - -1 / (16 * δ ^ 2) := hcalc
    _ ≤ 1 / (16 * δ ^ 2) := by
        rw [h4]
        have : 0 < 1 / (16 * δ ^ 2) := by positivity
        have e : -1 / (16 * δ ^ 2) = -(1 / (16 * δ ^ 2)) := by ring
        rw [e]
        linarith

/-- The integrand's pointwise bound `|v(β)³ e(−Nβ)| ≤ 1/(8|β|³)` for `0 < |β| ≤ 1/2`, from the
geometric-sum bound. -/
theorem norm_integrand_le (N : ℕ) {β : ℝ} (hβ : 0 < |β|) (hβ' : |β| ≤ 1 / 2) :
    ‖expSumOne N β ^ 3 * eR (-(N : ℝ) * β)‖ ≤ 1 / (8 * |β| ^ 3) := by
  rw [norm_mul, norm_pow, norm_eR, mul_one]
  calc ‖expSumOne N β‖ ^ 3 ≤ (1 / (2 * |β|)) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_expSumOne_le_inv N hβ hβ') 3
    _ = 1 / (8 * |β| ^ 3) := by ring

/-- **The singular integral truncated to a major arc:** over `|β| ≤ δ` it differs from
`C(N − 1, 2)` by at most `1/(4δ²)`. -/
theorem integral_expSumOne_cube_trunc (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ‖(∫ β in (-δ)..δ, expSumOne N β ^ 3 * eR (-(N : ℝ) * β)) - ((N - 1).choose 2 : ℂ)‖
      ≤ 1 / (4 * δ ^ 2) := by
  set F : ℝ → ℂ := fun β => expSumOne N β ^ 3 * eR (-(N : ℝ) * β) with hF
  have hFc : Continuous F :=
    ((continuous_expSumOne N).pow 3).mul
      (Salt.LS.continuous_e.comp (continuous_const.mul continuous_id))
  have hper : Function.Periodic F 1 := by
    intro β
    simp only [hF]
    congr 1
    · congr 1
      unfold expSumOne
      refine Finset.sum_congr rfl fun n _ => ?_
      have := Salt.MR.eR_add_intCast ((n : ℝ) * β) (n : ℤ)
      rw [Int.cast_natCast] at this
      rw [← this]; congr 1; ring
    · have := Salt.MR.eR_add_intCast (-(N : ℝ) * β) (-(N : ℤ))
      rw [Int.cast_neg, Int.cast_natCast] at this
      rw [← this]; congr 1; ring
  have hwhole : (∫ β in (-(1 / 2))..(1 / 2), F β) = ((N - 1).choose 2 : ℂ) := by
    have h := hper.intervalIntegral_add_eq (-(1 / 2)) 0
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at h
    rw [h]
    exact integral_expSumOne_cube N
  have hsplit : (∫ β in (-(1 / 2))..(1 / 2), F β) = (∫ β in (-(1 / 2))..(-δ), F β)
      + (∫ β in (-δ)..δ, F β) + (∫ β in δ..(1 / 2), F β) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
        (hFc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable _ _)
        (hFc.intervalIntegrable _ _)]
  have hleft : (∫ β in (-(1 / 2))..(-δ), F β) = ∫ β in δ..(1 / 2), F (-β) := by
    rw [intervalIntegral.integral_comp_neg]
  have hpos : ∀ β ∈ Set.Icc δ (1 / 2), 0 < β := fun β hβ => lt_of_lt_of_le hδ hβ.1
  have hR : ‖∫ β in δ..(1 / 2), F β‖ ≤ 1 / (16 * δ ^ 2) := by
    refine norm_integral_tail_le hFc hδ hδ' fun β hβ => ?_
    have h0 := hpos β hβ
    have := norm_integrand_le N (β := β) (by rw [abs_of_pos h0]; exact h0)
      (by rw [abs_of_pos h0]; exact hβ.2)
    rwa [abs_of_pos h0] at this
  have hL : ‖∫ β in δ..(1 / 2), F (-β)‖ ≤ 1 / (16 * δ ^ 2) := by
    refine norm_integral_tail_le (hFc.comp continuous_neg) hδ hδ' fun β hβ => ?_
    have h0 := hpos β hβ
    have := norm_integrand_le N (β := -β) (by rw [abs_neg, abs_of_pos h0]; exact h0)
      (by rw [abs_neg, abs_of_pos h0]; exact hβ.2)
    rwa [abs_neg, abs_of_pos h0] at this
  have hd2 : 0 < δ ^ 2 := by positivity
  calc ‖(∫ β in (-δ)..δ, F β) - ((N - 1).choose 2 : ℂ)‖
      = ‖(∫ β in δ..(1 / 2), F (-β)) + ∫ β in δ..(1 / 2), F β‖ := by
        rw [← hwhole, hsplit, hleft, ← norm_neg]
        congr 1
        ring
    _ ≤ ‖∫ β in δ..(1 / 2), F (-β)‖ + ‖∫ β in δ..(1 / 2), F β‖ := norm_add_le _ _
    _ ≤ 1 / (16 * δ ^ 2) + 1 / (16 * δ ^ 2) := add_le_add hL hR
    _ ≤ 1 / (4 * δ ^ 2) := by
        rw [← add_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

end Salt.ThreePrimes
