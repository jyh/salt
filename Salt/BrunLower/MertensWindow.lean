/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Mertens

/-!
# The windowed Mertens second theorem, upper form (blueprint `p0`, node PM1)

`∑_{w ≤ p < z} 1/p ≤ log(log z / log w) + C₃ / log w` for `2 ≤ w ≤ z`, with `C₃ = 19`
an explicit numeral.  The Mertens constant `M` **cancels** in the window (never defined).

Route (classical Mertens 1874, all elementary):

1. **Mertens-1 LOWER** `∑_{p ≤ N} (log p)/p ≥ log N − C_low` (the genuinely new piece; the
   corpus `Salt/Maynard/Mertens.lean` has only the UPPER `sum_log_div_prime_le`).  Via the
   log-factorial identity `∑_{n ≤ N} log n = log N!`, the Stirling floor
   `log N! ≥ N log N − N` (mathlib `Real.le_log_factorial_stirling`), `⌊N/d⌋ ≤ N/d`, and the
   prime-power strip `∑_{d ≤ N} Λ(d)/d − ∑_{p ≤ N} (log p)/p ≤ 5/2` (geometric comparison +
   `∑ (log n)/n² ≤ 5/4` by an integral bound).
2. **Two-sided `R`** `|∑_{p ≤ t} (log p)/p − log t| ≤ 6` for real `t ≥ 2` (corpus upper + the
   new lower + floor slop).
3. **The Abel windowed pass** (corpus `mF = 1/log t` machinery, difference of two Abel passes):
   the main term telescopes to `∫_w^z dt/(t log t) = log(log z/log w)` exactly; the `R`-terms
   give `≤ 3·6/log w`.

Reuses the corpus Abel machinery (`Salt.Maynard.mF`, `mC`, `hasDerivAt_mF`, `deriv_mF`,
`integral_inv_tlog`, `sum_mC_Icc_eq`, `sum_log_div_prime_le`, …) rather than rebuilding it.
-/

open Finset ArithmeticFunction MeasureTheory Set intervalIntegral

namespace Salt.BrunLower

open Salt.Maynard

/-! ## Section 1 — Mertens' first theorem, LOWER bound -/

/-- `∑_{n ∈ Ioc 0 N} log n = log N!` (the log-factorial identity). -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = Real.log (Nat.factorial N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    ring

/-- **Mertens' first theorem, LOWER bound (von Mangoldt form).**
`∑_{d ≤ N} Λ(d)/d ≥ log N − 1`, for `1 ≤ N`.  From `∑ Λ(d)·⌊N/d⌋ = log N! ≥ N log N − N`. -/
theorem sum_vonMangoldt_div_ge {N : ℕ} (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- Stirling floor: `N log N − N ≤ log N!`
  have hstir : (N : ℝ) * Real.log N - N ≤ Real.log (Nat.factorial N : ℝ) := by
    have h := Stirling.le_log_factorial_stirling (n := N) (by omega)
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have hpi : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      have := Real.pi_gt_three; linarith
    linarith
  -- `∑ log n = log N!`, and `∑ Λ(d)⌊N/d⌋ = ∑ log n`
  rw [← sum_log_eq_log_factorial, sum_log_eq_sum_vonMangoldt_mul_div] at hstir
  -- `∑ Λ(d)⌊N/d⌋ ≤ N · ∑ Λ(d)/d`
  have hup : ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Ioc] at hd
    have hΛ : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hfloor : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left hfloor hΛ
      _ = (N : ℝ) * (Λ d / d) := by ring
  -- combine and divide by N
  have hcomb : (N : ℝ) * Real.log N - N ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d :=
    le_trans hstir hup
  have hfac : (N : ℝ) * (Real.log N - 1) ≤ (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
    nlinarith [hcomb]
  exact le_of_mul_le_mul_left hfac hNr

/-! ## Section 2 — the prime-power strip -/

/-- summand `(log t)/t²`. -/
private noncomputable def lsF (t : ℝ) : ℝ := Real.log t / t ^ 2

/-- antiderivative `-(1+log t)/t`, with `(lsG)' = lsF`. -/
private noncomputable def lsG (t : ℝ) : ℝ := -(1 + Real.log t) / t

private theorem hasDerivAt_lsG {x : ℝ} (hx : 0 < x) : HasDerivAt lsG (lsF x) x := by
  have hx0 : x ≠ 0 := hx.ne'
  have h1 : HasDerivAt (fun t => -(1 + Real.log t)) (-x⁻¹) x :=
    ((Real.hasDerivAt_log hx0).const_add (1 : ℝ)).neg
  have h2 : HasDerivAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) x := hasDerivAt_inv hx0
  have hprod := h1.mul h2
  have heq : -x⁻¹ * x⁻¹ + -(1 + Real.log x) * -(x ^ 2)⁻¹ = lsF x := by
    rw [lsF]; field_simp; ring
  have hmain : HasDerivAt (fun t => -(1 + Real.log t) * t⁻¹) (lsF x) x := by
    rw [← heq]; exact hprod
  have hg : lsG = fun t => -(1 + Real.log t) * t⁻¹ := by
    funext t; rw [lsG]; ring
  rw [hg]; exact hmain

private theorem hasDerivAt_lsF {x : ℝ} (hx : 0 < x) :
    HasDerivAt lsF ((x⁻¹ * x ^ 2 - Real.log x * (2 * x)) / (x ^ 2) ^ 2) x := by
  have hc : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hd : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hd0 : x ^ 2 ≠ 0 := by positivity
  exact hc.div hd hd0

private theorem antitoneOn_lsF {b : ℝ} : AntitoneOn lsF (Set.Icc 2 b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 2 b)
  · apply ContinuousOn.div (continuousOn_id.log ?_) (continuousOn_id.pow 2) ?_
    · intro t ht; simp only [Set.mem_Icc] at ht
      exact (by linarith [ht.1] : (0:ℝ) < t).ne'
    · intro t ht; simp only [Set.mem_Icc] at ht
      have : (0:ℝ) < t := by linarith [ht.1]
      positivity
  · rw [interior_Icc]
    intro x hx
    rw [Set.mem_Ioo] at hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    exact (hasDerivAt_lsF hx0).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    rw [(hasDerivAt_lsF hx0).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx.1.le
      have hl2 : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
      have hxx : x⁻¹ * x ^ 2 = x := by field_simp
      rw [hxx]
      nlinarith [mul_pos hx0 (by linarith [hlog, hl2] : (0:ℝ) < 2 * Real.log x - 1)]
    · positivity

private theorem continuousOn_lsF {b : ℝ} (hb : 2 ≤ b) :
    ContinuousOn lsF (Set.uIcc 2 b) := by
  rw [Set.uIcc_of_le hb]
  apply ContinuousOn.div (continuousOn_id.log ?_) (continuousOn_id.pow 2) ?_
  · intro t ht; simp only [Set.mem_Icc] at ht
    exact (by linarith [ht.1] : (0:ℝ) < t).ne'
  · intro t ht; simp only [Set.mem_Icc] at ht
    have : (0:ℝ) < t := by linarith [ht.1]
    positivity

private theorem integral_lsF {b : ℝ} (hb : 2 ≤ b) :
    ∫ x in (2:ℝ)..b, lsF x = lsG b - lsG 2 := by
  have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) b, HasDerivAt lsG (lsF x) x := by
    intro x hx
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hx
    exact hasDerivAt_lsG (by linarith [hx.1])
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_lsF hb).intervalIntegrable

/-- `∑_{n ∈ Ioc 1 N} (log n)/n² ≤ 5/4`. -/
theorem sum_lsF_le (N : ℕ) : ∑ n ∈ Finset.Ioc 1 N, lsF n ≤ 5/4 := by
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlsF2 : lsF ((2:ℕ):ℝ) ≤ 1/4 := by
    rw [lsF]; push_cast
    rw [div_le_iff₀ (by norm_num)]; nlinarith [hlog2]
  rcases le_or_gt N 2 with hN | hN
  · interval_cases N
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; norm_num
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; norm_num
    · rw [show Finset.Ioc 1 2 = {2} by rfl, Finset.sum_singleton]; linarith
  · have hsplit : ∑ n ∈ Finset.Ioc 1 N, lsF n
        = lsF ((2:ℕ):ℝ) + ∑ n ∈ Finset.Ioc 2 N, lsF n := by
      rw [← Finset.sum_Ioc_consecutive (fun i => lsF (i:ℝ))
        (by norm_num : (1:ℕ) ≤ 2) (by omega : (2:ℕ) ≤ N)]
      rw [show Finset.Ioc 1 2 = {2} by rfl, Finset.sum_singleton]
    have hmap : Finset.Ioc 2 N
        = (Finset.Ico 2 N).map ⟨fun i => i + 1, fun a b h => by simpa using h⟩ := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨n - 1, ⟨by omega, by omega⟩, by omega⟩
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩; omega
    have hreindex : ∑ n ∈ Finset.Ioc 2 N, lsF (n:ℝ)
        = ∑ i ∈ Finset.Ico 2 N, lsF ((i + 1 : ℕ) : ℝ) := by
      rw [hmap, Finset.sum_map]; rfl
    have hcomp : ∑ i ∈ Finset.Ico 2 N, lsF ((i + 1 : ℕ) : ℝ) ≤ ∫ x in (2:ℝ)..(N:ℝ), lsF x :=
      AntitoneOn.sum_le_integral_Ico (by omega : (2:ℕ) ≤ N) antitoneOn_lsF
    have hint : (∫ x in (2:ℝ)..(N:ℝ), lsF x) ≤ (1 + Real.log 2)/2 := by
      rw [integral_lsF (by exact_mod_cast (by omega : (2:ℕ) ≤ N))]
      have hN2 : (2:ℝ) ≤ N := by exact_mod_cast (by omega : (2:ℕ) ≤ N)
      have hlsGN : lsG (N:ℝ) ≤ 0 := by
        rw [lsG]
        apply div_nonpos_of_nonpos_of_nonneg
        · have := Real.log_nonneg (by linarith : (1:ℝ) ≤ N); linarith
        · linarith
      have hg2 : lsG 2 = -(1 + Real.log 2)/2 := by rw [lsG]
      rw [hg2]; linarith
    rw [hsplit, hreindex]
    linarith [hcomp.trans hint, hlsF2]

/-- **The prime-power strip.** `∑_{d ≤ N} Λ(d)/d ≤ ∑_{p ≤ N} (log p)/p + 5/2`. -/
theorem sum_vonMangoldt_div_le_prime (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d
      ≤ (∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p / p) + 5/2 := by
  set P := (Finset.range (N + 1)).filter Nat.Prime with hP
  have hsplit : ∑ d ∈ Finset.Ioc 0 N, Λ d / d
      = (∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / d)
        + ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / d :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hprime : ∑ d ∈ (Finset.Ioc 0 N).filter Nat.Prime, Λ d / d
      = ∑ p ∈ P, Real.log p / p := by
    rw [hP, ← filter_prime_range_eq_Ioc]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  rw [hsplit, hprime]
  suffices hstrip : ∑ d ∈ (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d), Λ d / d ≤ 5/2 by
    linarith [hstrip]
  set S' := (Finset.Ioc 0 N).filter (fun d => ¬ Nat.Prime d) with hS'
  set T := P ×ˢ Finset.Icc 2 N with hT
  set φ : ℕ × ℕ → ℕ := fun pk => pk.1 ^ pk.2 with hφ
  have hzero : ∑ d ∈ S', Λ d / d = ∑ d ∈ S'.filter (fun d => Λ d ≠ 0), Λ d / d := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro d hd hd'
    simp only [Finset.mem_filter, not_and, not_not] at hd'
    rw [hd' hd, zero_div]
  have hsub : S'.filter (fun d => Λ d ≠ 0) ⊆ T.image φ := by
    intro d hd
    rw [Finset.mem_filter, hS', Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨⟨hd0, hdN⟩, hdnp⟩, hdΛ⟩ := hd
    have hpp : IsPrimePow d := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hdΛ
    have hd1 : d ≠ 1 := by
      rintro rfl; exact hdΛ (by simp [ArithmeticFunction.vonMangoldt_apply_one])
    have hpprime : (d.minFac).Prime := Nat.minFac_prime hd1
    have hpk : d.minFac ^ (d.factorization d.minFac) = d := hpp.minFac_pow_factorization_eq
    have hk2 : 2 ≤ d.factorization d.minFac := by
      rcases Nat.lt_or_ge (d.factorization d.minFac) 2 with h | h
      · interval_cases hkk : d.factorization d.minFac
        · rw [pow_zero] at hpk; exact absurd hpk.symm hd1
        · rw [pow_one] at hpk; rw [hpk] at hpprime; exact absurd hpprime hdnp
      · exact h
    have hkN : d.factorization d.minFac ≤ N := by
      have h1 : d.factorization d.minFac < 2 ^ (d.factorization d.minFac) :=
        (d.factorization d.minFac).lt_two_pow_self
      have h2 : 2 ^ (d.factorization d.minFac) ≤ d.minFac ^ (d.factorization d.minFac) :=
        Nat.pow_le_pow_left hpprime.two_le _
      omega
    rw [Finset.mem_image]
    refine ⟨(d.minFac, d.factorization d.minFac), ?_, hpk⟩
    rw [hT, Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    have hpN : d.minFac ≤ N := le_trans (Nat.minFac_le hd0) hdN
    exact ⟨⟨by omega, hpprime⟩, hk2, hkN⟩
  have hle1 : ∑ d ∈ S'.filter (fun d => Λ d ≠ 0), Λ d / d ≤ ∑ d ∈ T.image φ, Λ d / d :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg d))
  have hsumimg : ∑ d ∈ T.image φ, Λ d / d = ∑ pk ∈ T, Λ (φ pk) / (φ pk) := by
    rw [Finset.sum_image]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, hT, Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Icc] at hx hy
    obtain ⟨⟨_, hxp⟩, hxk2, _⟩ := hx
    obtain ⟨⟨_, hyp⟩, hyk2, _⟩ := hy
    simp only [hφ] at hxy
    have hp1 : (x.1 ^ x.2).minFac = x.1 := hxp.pow_minFac (by omega)
    have hp2 : (y.1 ^ y.2).minFac = y.1 := hyp.pow_minFac (by omega)
    have heqbase : x.1 = y.1 := by rw [← hp1, ← hp2, hxy]
    have heqexp : x.2 = y.2 :=
      Nat.pow_right_injective hxp.two_le (by rw [hxy, ← heqbase] : x.1 ^ x.2 = x.1 ^ y.2)
    exact Prod.ext heqbase heqexp
  have hval : ∑ pk ∈ T, Λ (φ pk) / (φ pk) = ∑ pk ∈ T, Real.log pk.1 / (pk.1:ℝ) ^ pk.2 := by
    apply Finset.sum_congr rfl
    intro pk hpk
    rw [hT, Finset.mem_product, hP, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hpk
    obtain ⟨⟨_, hprime⟩, hk2, _⟩ := hpk
    simp only [hφ]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : pk.2 ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hprime, Nat.cast_pow]
  have hprod : ∑ pk ∈ T, Real.log pk.1 / (pk.1:ℝ) ^ pk.2
      = ∑ p ∈ P, ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k := by
    rw [hT, Finset.sum_product]
  have hgeom : ∀ p ∈ P, ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k
      ≤ 2 * (Real.log p / (p:ℝ) ^ 2) := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hfac : ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k
        = Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p:ℝ)⁻¹) ^ k := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [inv_pow]; ring
    rw [hfac]
    have hq0 : (0:ℝ) ≤ (p:ℝ)⁻¹ := by positivity
    have hqhalf : (p:ℝ)⁻¹ ≤ 1/2 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hb : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by linarith
    have hq : ∑ k ∈ Finset.Icc 2 N, ((p:ℝ)⁻¹) ^ k ≤ 2 * ((p:ℝ)⁻¹) ^ 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      have h1 := geom_sum_Ico_le_of_lt_one (m := 2) (n := N + 1) (x := (p:ℝ)⁻¹) hq0 (by linarith)
      have hq1 : ((p:ℝ)⁻¹) ^ 2 / (1 - (p:ℝ)⁻¹) ≤ 2 * ((p:ℝ)⁻¹) ^ 2 := by
        rw [div_le_iff₀ hb]
        nlinarith [mul_nonneg (sq_nonneg ((p:ℝ)⁻¹)) (by linarith : (0:ℝ) ≤ 1 - 2 * (p:ℝ)⁻¹)]
      linarith [h1, hq1]
    calc Real.log p * ∑ k ∈ Finset.Icc 2 N, ((p:ℝ)⁻¹) ^ k
        ≤ Real.log p * (2 * ((p:ℝ)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hq hlogp
      _ = 2 * (Real.log p / (p:ℝ) ^ 2) := by rw [inv_pow]; ring
  have hPsub : P ⊆ Finset.Ioc 1 N := by
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_Ioc]
    exact ⟨hp.2.one_lt, by omega⟩
  have hlsFsum : (2:ℝ) * ∑ p ∈ P, lsF p ≤ 2 * ∑ n ∈ Finset.Ioc 1 N, lsF n := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum_of_subset_of_nonneg hPsub
    intro n hn _
    rw [Finset.mem_Ioc] at hn
    rw [lsF]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) (by positivity)
  calc ∑ d ∈ S', Λ d / d
      = ∑ d ∈ S'.filter (fun d => Λ d ≠ 0), Λ d / d := hzero
    _ ≤ ∑ d ∈ T.image φ, Λ d / d := hle1
    _ = ∑ pk ∈ T, Λ (φ pk) / (φ pk) := hsumimg
    _ = ∑ pk ∈ T, Real.log pk.1 / (pk.1:ℝ) ^ pk.2 := hval
    _ = ∑ p ∈ P, ∑ k ∈ Finset.Icc 2 N, Real.log p / (p:ℝ) ^ k := hprod
    _ ≤ ∑ p ∈ P, 2 * (Real.log p / (p:ℝ) ^ 2) := Finset.sum_le_sum hgeom
    _ = 2 * ∑ p ∈ P, lsF p := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; rw [lsF]
    _ ≤ 2 * ∑ n ∈ Finset.Ioc 1 N, lsF n := hlsFsum
    _ ≤ 2 * (5/4) := by linarith [sum_lsF_le N]
    _ = 5/2 := by norm_num

/-! ## Section 3 — the two-sided estimate `|∑_{p ≤ t} (log p)/p − log t| ≤ 6` -/

/-- The partial-sum function `S(t) = ∑_{p ≤ ⌊t⌋} (log p)/p`, in the corpus' `mC` form. -/
noncomputable def Sfun (t : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k

/-- **The two-sided Mertens-1 estimate.** `|S(t) − log t| ≤ 6` for real `t ≥ 2`; combines the
corpus UPPER bound with the new LOWER bound and the prime-power strip, absorbing the `⌊t⌋`-vs-`t`
slop. -/
theorem abs_Sfun_sub_log_le {t : ℝ} (ht : 2 ≤ t) : |Sfun t - Real.log t| ≤ 6 := by
  have hM2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor (by push_cast; linarith : ((2:ℕ):ℝ) ≤ t)
  have hMt : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htM1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hM2R : (2:ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hM2
  have hMpos : (0:ℝ) < (⌊t⌋₊ : ℝ) := by linarith
  have hSeq : Sfun t = ∑ p ∈ (Finset.range (⌊t⌋₊ + 1)).filter Nat.Prime, Real.log p / p := by
    rw [Sfun, sum_mC_Icc_eq]
  -- `log t ≤ log ⌊t⌋ + 1/2`
  have hlogtM : Real.log t ≤ Real.log ⌊t⌋₊ + 1/2 := by
    have h1 : Real.log t ≤ Real.log ((⌊t⌋₊ : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log ((⌊t⌋₊ : ℝ) + 1) - Real.log ⌊t⌋₊ ≤ 1/2 := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have heq : ((⌊t⌋₊ : ℝ) + 1) / ⌊t⌋₊ = 1 + 1 / ⌊t⌋₊ := by field_simp
      rw [heq]
      have hle := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + 1 / (⌊t⌋₊ : ℝ))
      have hMhalf : 1 / (⌊t⌋₊ : ℝ) ≤ 1/2 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM2)
      linarith
    linarith
  -- UPPER
  have hUp : Sfun t ≤ Real.log t + (Real.log 4 + 4) := by
    rw [hSeq]
    have h := sum_log_div_prime_le (N := ⌊t⌋₊) (by omega)
    have hlogMt : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hMpos hMt
    linarith
  -- LOWER
  have hLow : Real.log t - 4 ≤ Sfun t := by
    rw [hSeq]
    have hge := sum_vonMangoldt_div_ge (N := ⌊t⌋₊) (by omega)
    have hstrip := sum_vonMangoldt_div_le_prime ⌊t⌋₊
    linarith [hge, hstrip, hlogtM]
  -- combine, using `log 4 ≤ 2`
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9; push_cast; nlinarith
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ## Section 4 — real-endpoint integrals and integrability (corpus templates) -/

/-- `deriv mF` is integrable on `[2, b]` (real endpoint). -/
theorem integrableOn_deriv_mF_real {b : ℝ} (_hb : 2 ≤ b) :
    IntegrableOn (deriv mF) (Set.Icc 2 b) := by
  have hne0 : ∀ t ∈ Set.Icc (2:ℝ) b, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  have hcont : ContinuousOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 b) := by
    have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 b) :=
      continuousOn_id.log hne0
    have hbase : ContinuousOn (fun t : ℝ => t * Real.log t ^ 2) (Set.Icc 2 b) :=
      continuousOn_id.mul (hlogcont.pow 2)
    apply ContinuousOn.neg
    apply hbase.inv₀
    intro t ht
    simp only [Set.mem_Icc] at ht
    have hlog : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have ht0 : (0:ℝ) < t := by linarith [ht.1]
    positivity
  have hint : IntegrableOn (fun t : ℝ => -(t * Real.log t ^ 2)⁻¹) (Set.Icc 2 b) :=
    hcont.integrableOn_compact isCompact_Icc
  apply hint.congr_fun _ measurableSet_Icc
  intro t ht
  simp only [Set.mem_Icc] at ht
  rw [deriv_mF ht.1]

theorem continuousOn_inv_tlog_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => (t * Real.log t)⁻¹) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hne0 : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul (continuousOn_id.log hne0))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' hlog

theorem continuousOn_inv_tlogsq_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => (t * Real.log t ^ 2)⁻¹) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  have hne0 : ∀ t ∈ Set.Icc a b, t ≠ 0 := by
    intro t ht; simp only [Set.mem_Icc] at ht; linarith [ht.1]
  apply ContinuousOn.inv₀ (continuousOn_id.mul ((continuousOn_id.log hne0).pow 2))
  intro t ht
  simp only [Set.mem_Icc] at ht
  have hlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  exact mul_ne_zero ht0.ne' (pow_ne_zero 2 hlog)

/-- `∫_a^b 1/(t·log t) dt = log log b − log log a` for `2 ≤ a ≤ b`. -/
theorem integral_inv_tlog_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (t * Real.log t)⁻¹ = Real.log (Real.log b) - Real.log (Real.log a) := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => Real.log (Real.log t)) ((x * Real.log x)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
    have hinner : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have houter : HasDerivAt Real.log (Real.log x)⁻¹ (Real.log x) :=
      Real.hasDerivAt_log (ne_of_gt hlogpos)
    have hcomp := houter.comp x hinner
    have hval : (Real.log x)⁻¹ * x⁻¹ = (x * Real.log x)⁻¹ := by rw [mul_inv]; ring
    rw [hval] at hcomp
    exact hcomp
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_inv_tlog_real ha hab).intervalIntegrable
  simpa using key

/-- `∫_a^b 1/(t·(log t)²) dt = 1/log a − 1/log b` for `2 ≤ a ≤ b`. -/
theorem integral_inv_tlogsq_real {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (t * Real.log t ^ 2)⁻¹ = (Real.log a)⁻¹ - (Real.log b)⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t => -(Real.log t)⁻¹) ((x * Real.log x ^ 2)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
    have hx2 : (2:ℝ) ≤ x := by linarith [hx.1]
    have h := (hasDerivAt_mF hx2).neg
    rwa [neg_neg] at h
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuousOn_inv_tlogsq_real ha hab).intervalIntegrable
  rw [key]; ring

/-! ## Section 5 — the Abel windowed pass (difference of two Abel passes) -/

/-- **The windowed Abel core.** `∑_{p ≤ ⌊z⌋} (log p)/p·(1/log p) − (same at w) ≤ log(log z/log w)
+ 18/log w`, in the `mF·mC` (Abel) form.  The Mertens constant cancels; only the two-sided `R`-term
(`|S(t) − log t| ≤ 6`) survives, weighted to `O(1/log w)`. -/
theorem window_core {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∑ k ∈ Finset.Icc 0 ⌊z⌋₊, mF k * mC k) - (∑ k ∈ Finset.Icc 0 ⌊w⌋₊, mF k * mC k)
      ≤ Real.log (Real.log z / Real.log w) + 18 / Real.log w := by
  have hz : (2:ℝ) ≤ z := le_trans hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlwne : Real.log w ≠ 0 := ne_of_gt hlogw
  have hlzne : Real.log z ≠ 0 := ne_of_gt hlogz
  have hlogwz : Real.log w ≤ Real.log z := Real.log_le_log (by linarith) hwz
  have hinvzw : (Real.log z)⁻¹ ≤ (Real.log w)⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hlogw hlogwz
  have hinvz0 : (0:ℝ) ≤ (Real.log z)⁻¹ := by positivity
  have hinvw0 : (0:ℝ) ≤ (Real.log w)⁻¹ := by positivity
  have hGint_z : IntegrableOn (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      (Set.Icc 2 z) :=
    integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF_real hz)
  have hII_2w : IntervalIntegrable (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      volume 2 w := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hw]
    exact hGint_z.mono_set (Set.Icc_subset_Icc le_rfl hwz)
  have hII_wz : IntervalIntegrable (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      volume w z := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hwz]
    exact hGint_z.mono_set (Set.Icc_subset_Icc hw le_rfl)
  have habelz := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one z
    (fun s hs => differentiableAt_mF (by simp only [Set.mem_Icc] at hs; exact hs.1))
    (integrableOn_deriv_mF_real hz)
  have habelw := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one w
    (fun s hs => differentiableAt_mF (by simp only [Set.mem_Icc] at hs; exact hs.1))
    (integrableOn_deriv_mF_real hw)
  rw [← intervalIntegral.integral_of_le hz,
    show (∑ k ∈ Finset.Icc 0 ⌊z⌋₊, mC k) = Sfun z from rfl] at habelz
  rw [← intervalIntegral.integral_of_le hw,
    show (∑ k ∈ Finset.Icc 0 ⌊w⌋₊, mC k) = Sfun w from rfl] at habelw
  have hadd : (∫ t in (2:ℝ)..w, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      + (∫ t in w..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = ∫ t in (2:ℝ)..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k :=
    intervalIntegral.integral_add_adjacent_intervals hII_2w hII_wz
  have hpt : ∀ t ∈ Set.Icc w z,
      -(t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹
        ≤ deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have ht2 : (2:ℝ) ≤ t := le_trans hw ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hinvnn : (0:ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by positivity
    have hSt : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k) ≤ Real.log t + 6 := by
      have := abs_Sfun_sub_log_le ht2
      rw [abs_le] at this
      have hSeq : Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k := rfl
      linarith [this.2]
    rw [deriv_mF ht2]
    have hkey : (t * Real.log t ^ 2)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
        ≤ (t * Real.log t ^ 2)⁻¹ * (Real.log t + 6) :=
      mul_le_mul_of_nonneg_left hSt hinvnn
    have hsplit : (t * Real.log t ^ 2)⁻¹ * (Real.log t + 6)
        = (t * Real.log t)⁻¹ + 6 * (t * Real.log t ^ 2)⁻¹ := by
      have hne : Real.log t ≠ 0 := ne_of_gt hlogt
      field_simp
    nlinarith [hkey, hsplit]
  have hIntA : (∫ t in w..z, -(t * Real.log t)⁻¹)
      = -(Real.log (Real.log z) - Real.log (Real.log w)) := by
    rw [intervalIntegral.integral_neg, integral_inv_tlog_real hw hwz]
  have hIntB : (∫ t in w..z, 6 * (t * Real.log t ^ 2)⁻¹)
      = 6 * ((Real.log w)⁻¹ - (Real.log z)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_tlogsq_real hw hwz]
  have hAintble : IntervalIntegrable (fun t => -(t * Real.log t)⁻¹) volume w z :=
    ((continuousOn_inv_tlog_real hw hwz).intervalIntegrable).neg
  have hBintble : IntervalIntegrable (fun t => 6 * (t * Real.log t ^ 2)⁻¹) volume w z :=
    ((continuousOn_inv_tlogsq_real hw hwz).intervalIntegrable).const_mul 6
  have hLint : (∫ t in w..z, (-(t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹))
      = -(Real.log (Real.log z) - Real.log (Real.log w))
        - 6 * ((Real.log w)⁻¹ - (Real.log z)⁻¹) := by
    rw [intervalIntegral.integral_sub hAintble hBintble, hIntA, hIntB]
  have hmono : (∫ t in w..z, (-(t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹))
      ≤ ∫ t in w..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k :=
    intervalIntegral.integral_mono_on hwz (hAintble.sub hBintble) hII_wz hpt
  have hSz := abs_Sfun_sub_log_le hz
  have hSw := abs_Sfun_sub_log_le hw
  rw [abs_le] at hSz hSw
  have hAbound : mF z * Sfun z ≤ 1 + 6 * (Real.log w)⁻¹ := by
    have hmFz : mF z = (Real.log z)⁻¹ := rfl
    calc mF z * Sfun z = (Real.log z)⁻¹ * Sfun z := by rw [hmFz]
      _ ≤ (Real.log z)⁻¹ * (Real.log z + 6) := by
          apply mul_le_mul_of_nonneg_left _ hinvz0; linarith [hSz.2]
      _ = 1 + 6 * (Real.log z)⁻¹ := by rw [mul_add, inv_mul_cancel₀ hlzne]; ring
      _ ≤ 1 + 6 * (Real.log w)⁻¹ := by linarith [hinvzw]
  have hBbound : 1 - 6 * (Real.log w)⁻¹ ≤ mF w * Sfun w := by
    have hmFw : mF w = (Real.log w)⁻¹ := rfl
    calc 1 - 6 * (Real.log w)⁻¹ = (Real.log w)⁻¹ * (Real.log w - 6) := by
          rw [mul_sub, inv_mul_cancel₀ hlwne]; ring
      _ ≤ (Real.log w)⁻¹ * Sfun w := by
          apply mul_le_mul_of_nonneg_left _ hinvw0; linarith [hSw.1]
      _ = mF w * Sfun w := by rw [hmFw]
  rw [Real.log_div hlzne hlwne, div_eq_mul_inv]
  linarith [habelz, habelw, hadd, hmono, hLint, hAbound, hBbound]

/-! ## Section 6 — packaging into `primesInWindow` and the PM2-consumable forms -/

/-- The Abel LHS is the prime reciprocal sum `∑_{p ≤ ⌊b⌋} 1/p`. -/
theorem sum_mF_mul_mC_eq (b : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, mF k * mC k
      = ∑ p ∈ (Finset.range (⌊b⌋₊ + 1)).filter Nat.Prime, (1:ℝ) / p := by
  have hIcc : Finset.Icc 0 ⌊b⌋₊ = Finset.range (⌊b⌋₊ + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hIcc, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  unfold mF mC
  by_cases hk : k.Prime
  · simp only [hk, if_true]
    have hk2 : (1:ℝ) < k := by exact_mod_cast hk.one_lt
    have hlogk : Real.log k ≠ 0 := ne_of_gt (Real.log_pos hk2)
    field_simp
  · simp only [hk, if_false, mul_zero]

/-- Primes in the window `[w, z)`, packaged over `range ⌈z⌉₊`.  Since `p ∈ range ⌈z⌉₊ ↔ (p:ℝ) < z`,
this is exactly the set of primes `p` with `w ≤ p < z`. -/
noncomputable def primesInWindow (w z : ℝ) : Finset ℕ :=
  (Finset.range ⌈z⌉₊).filter (fun p => Nat.Prime p ∧ w ≤ (p : ℝ))

/-- **The windowed Mertens bound, general carrier (PM2's consumable form).** Any finite set of
primes `p` with `w ≤ p < z` obeys `∑ 1/p ≤ log(log z/log w) + 19/log w` for `2 ≤ w ≤ z`. -/
theorem sum_inv_le_of_prime_window {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    {S : Finset ℕ} (hS : ∀ p ∈ S, Nat.Prime p ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log z / Real.log w) + 19 / Real.log w := by
  have hz : (2:ℝ) ≤ z := le_trans hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hfloorwz : ⌊w⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hwz
  set Wz := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime with hWz
  set Ww := (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime with hWw
  have hWwWz : Ww ⊆ Wz := by
    rw [hWw, hWz]; apply Finset.filter_subset_filter
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have hSsub : S ⊆ insert ⌊w⌋₊ (Wz \ Ww) := by
    intro p hp
    obtain ⟨hpp, hwp, hpz⟩ := hS p hp
    rw [Finset.mem_insert]
    by_cases hpw : (p : ℝ) ≤ w
    · left
      have heq : (p : ℝ) = w := le_antisymm hpw hwp
      rw [← heq, Nat.floor_natCast]
    · right
      rw [not_le] at hpw
      have hfloorw_lt : ⌊w⌋₊ < p := by
        have h1 : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le (by linarith)
        have : (⌊w⌋₊ : ℝ) < p := by linarith
        exact_mod_cast this
      have hpfloorz : p ≤ ⌊z⌋₊ := Nat.le_floor hpz.le
      rw [Finset.mem_sdiff, hWz, hWw, Finset.mem_filter, Finset.mem_filter, Finset.mem_range,
        Finset.mem_range, not_and]
      exact ⟨⟨by omega, hpp⟩, fun hlt _ => by omega⟩
  have hnn : ∀ p ∈ insert ⌊w⌋₊ (Wz \ Ww), p ∉ S → 0 ≤ (1 : ℝ) / p := fun p _ _ => by positivity
  have hstep1 : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ p ∈ insert ⌊w⌋₊ (Wz \ Ww), (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub hnn
  have hins : ∑ p ∈ insert ⌊w⌋₊ (Wz \ Ww), (1 : ℝ) / p
      ≤ 1 / (⌊w⌋₊ : ℝ) + ∑ p ∈ Wz \ Ww, (1 : ℝ) / p := by
    by_cases hmem : ⌊w⌋₊ ∈ Wz \ Ww
    · rw [Finset.insert_eq_self.mpr hmem]
      have : (0:ℝ) ≤ 1 / (⌊w⌋₊ : ℝ) := by positivity
      linarith
    · rw [Finset.sum_insert hmem]
  have hsdiff : ∑ p ∈ Wz \ Ww, (1 : ℝ) / p
      = (∑ p ∈ Wz, (1 : ℝ) / p) - ∑ p ∈ Ww, (1 : ℝ) / p := by
    rw [eq_sub_iff_add_eq]; exact Finset.sum_sdiff hWwWz
  have hcore := window_core hw hwz
  rw [sum_mF_mul_mC_eq z, sum_mF_mul_mC_eq w, ← hWz, ← hWw] at hcore
  have hfloorlog : Real.log w ≤ (⌊w⌋₊ : ℝ) := by
    have h1 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : w < (⌊w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w
    linarith
  have hfloorinv : 1 / (⌊w⌋₊ : ℝ) ≤ 1 / Real.log w := one_div_le_one_div_of_le hlogw hfloorlog
  have hsplit : (1:ℝ) / Real.log w + 18 / Real.log w = 19 / Real.log w := by
    rw [← add_div]; norm_num
  calc ∑ p ∈ S, (1 : ℝ) / p
      ≤ ∑ p ∈ insert ⌊w⌋₊ (Wz \ Ww), (1 : ℝ) / p := hstep1
    _ ≤ 1 / (⌊w⌋₊ : ℝ) + ∑ p ∈ Wz \ Ww, (1 : ℝ) / p := hins
    _ = 1 / (⌊w⌋₊ : ℝ) + ((∑ p ∈ Wz, (1 : ℝ) / p) - ∑ p ∈ Ww, (1 : ℝ) / p) := by rw [hsdiff]
    _ ≤ 1 / Real.log w + (Real.log (Real.log z / Real.log w) + 18 / Real.log w) := by
        linarith [hcore, hfloorinv]
    _ = Real.log (Real.log z / Real.log w) + 19 / Real.log w := by linarith [hsplit]

/-- **The frozen PM1 target.** `∑_{w ≤ p < z} 1/p ≤ log(log z/log w) + 19/log w` for `2 ≤ w ≤ z`.
`w₀ = 2`, `C₃ = 19`. -/
theorem sum_inv_prime_window_le {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    ∑ p ∈ primesInWindow w z, (1 : ℝ) / p
      ≤ Real.log (Real.log z / Real.log w) + 19 / Real.log w := by
  apply sum_inv_le_of_prime_window hw hwz
  intro p hp
  rw [primesInWindow, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨hp.2.1, hp.2.2, Nat.lt_ceil.mp hp.1⟩

/-- **Subset monotonicity** (what PM2 consumes for `windowPrimes s Lam z n ⊆ …`). -/
theorem sum_inv_le_of_subset_window {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    {S : Finset ℕ} (hS : S ⊆ primesInWindow w z) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ Real.log (Real.log z / Real.log w) + 19 / Real.log w := by
  apply sum_inv_le_of_prime_window hw hwz
  intro p hp
  have hmem := hS hp
  rw [primesInWindow, Finset.mem_filter, Finset.mem_range] at hmem
  exact ⟨hmem.2.1, hmem.2.2, Nat.lt_ceil.mp hmem.1⟩

end Salt.BrunLower
