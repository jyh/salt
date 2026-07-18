/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHExtractW

namespace Salt.SW

open Finset

/-!
# The two-sided LOWER Abel bound via a FREE hyperbola cut (`T-BAL` R5e)

This module lands `dhAbel_inner_ge`: a LOWER bound on the Dirichlet-detector Abel sum
`A(z) = Σ_{n≤z} dhA χ n · n^{−β₀}` whose error, after the crush multiplier `z^{−(1−β₀)}`,
carries only a HALF power of `(1−β₀)` on the deep ray (the naive `√z` cut's corner term
`36M/(1−β₀)` costs a full power and fails coverage).

The engine is an ASYMMETRIC Dirichlet hyperbola cut at a free `D`:
`sum_divisors_eq_hyperbola_asymm` generalizes the landed symmetric `√N` identity to an
arbitrary d-side cut `D` with matching e-side cut `C` (`D·C ≤ N < (D+1)(C+1)`). The cut
is placed at `D = Nat.sqrt (z · min ⌈1/(1−β₀)⌉₊ z) ~ √(z/(1−β₀))`, balancing the d-side
Euler–Maclaurin error `~ D·z^{−β₀}` against the e-side+corner `~ M·z^{1−β₀}/((1−β₀)D)`.
-/

/-- `{e ∈ [1,N] : k·e ≤ N} = [1, N/k]` for `k > 0` (the inner hyperbola block). -/
private lemma Icc_filter_mul_le' (k N : ℕ) (hk : 0 < k) :
    (Finset.Icc 1 N).filter (fun x => k * x ≤ N) = Finset.Icc 1 (N / k) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hx1, _⟩, hkx⟩
    exact ⟨hx1, (Nat.le_div_iff_mul_le hk).mpr (by rwa [Nat.mul_comm] at hkx)⟩
  · rintro ⟨hx1, hxd⟩
    refine ⟨⟨hx1, le_trans hxd (Nat.div_le_self N k)⟩, ?_⟩
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le hk).mp hxd

/-- **The asymmetric Dirichlet hyperbola.** For any `a b : ℕ → A` (`A` a commutative ring)
and cuts `D, C` tiling `[1,N]²` (`D·C ≤ N < (D+1)(C+1)`, `D,C ≤ N`), the convolution sum
splits into a `D`-short d-leg, a `C`-short e-leg, and the doubly-counted corner block.
EXACT — inclusion–exclusion on `{de ≤ N} = {d ≤ D} ∪ {e ≤ C}`. The free-cut generalization
of `sum_divisors_eq_hyperbola_symm` (`D = C = √N`). -/
theorem sum_divisors_eq_hyperbola_asymm {A : Type*} [CommRing A] (a b : ℕ → A) (N D C : ℕ)
    (hDN : D ≤ N) (hCN : C ≤ N) (hDC : D * C ≤ N) (hcov : N < (D + 1) * (C + 1)) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d)
      = (∑ d ∈ Finset.Icc 1 D, a d * ∑ e ∈ Finset.Icc 1 (N / d), b e)
        + (∑ e ∈ Finset.Icc 1 C, b e * ∑ d ∈ Finset.Icc 1 (N / e), a d)
        - (∑ d ∈ Finset.Icc 1 D, a d) * ∑ e ∈ Finset.Icc 1 C, b e := by
  set R := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p => p.1 * p.2 ≤ N) with hRdef
  have hsubD : Finset.Icc 1 D ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hDN
  have hsubC : Finset.Icc 1 C ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hCN
  have bridge : ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d)
      = ∑ p ∈ R, a p.1 * b p.2 := by
    rw [Finset.sum_congr rfl
        (fun n _ => (Nat.sum_divisorsAntidiagonal (fun x y => a x * b y)).symm)]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 N) : Set ℕ)
        (fun n => n.divisorsAntidiagonal) := by
      intro m _ n _ hmn
      simp only [Function.onFun, Finset.disjoint_left, Nat.mem_divisorsAntidiagonal]
      rintro p ⟨hpm, -⟩ ⟨hpn, -⟩
      exact hmn (hpm.symm.trans hpn)
    rw [← Finset.sum_biUnion hdisj, hRdef]
    congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal,
      Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨n, ⟨hn1, hnN⟩, hprod, -⟩
      subst hprod
      have hp1 : 0 < p.1 := by
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · rw [h, Nat.zero_mul] at hn1; omega
        · exact h
      have hp2 : 0 < p.2 := by
        rcases Nat.eq_zero_or_pos p.2 with h | h
        · rw [h, Nat.mul_zero] at hn1; omega
        · exact h
      have hle1 : p.1 ≤ p.1 * p.2 := le_mul_of_one_le_right (Nat.zero_le _) hp2
      have hle2 : p.2 ≤ p.1 * p.2 := le_mul_of_one_le_left (Nat.zero_le _) hp1
      exact ⟨⟨⟨hp1, by omega⟩, hp2, by omega⟩, hnN⟩
    · rintro ⟨⟨⟨hp1, _⟩, hp2, _⟩, hle⟩
      exact ⟨p.1 * p.2, ⟨Nat.mul_pos hp1 hp2, hle⟩, rfl, (Nat.mul_pos hp1 hp2).ne'⟩
  set FA := R.filter (fun p => p.1 ≤ D) with hAdef
  set FB := R.filter (fun p => p.2 ≤ C) with hBdef
  have hunion : FA ∪ FB = R := by
    rw [hAdef, hBdef, ← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro p hp
    have hle : p.1 * p.2 ≤ N := by rw [hRdef, Finset.mem_filter] at hp; exact hp.2
    by_contra h
    have hge : (D + 1) * (C + 1) ≤ p.1 * p.2 := Nat.mul_le_mul (by omega) (by omega)
    have : (D + 1) * (C + 1) ≤ N := le_trans hge hle
    omega
  have hinter : FA ∩ FB = R.filter (fun p => p.1 ≤ D ∧ p.2 ≤ C) := by
    rw [hAdef, hBdef, ← Finset.filter_and]
  have hA : ∑ p ∈ FA, a p.1 * b p.2
      = ∑ d ∈ Finset.Icc 1 D, a d * ∑ e ∈ Finset.Icc 1 (N / d), b e := by
    rw [hAdef, hRdef, Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
    dsimp only
    rw [← Finset.sum_subset hsubD (fun d hdN hdr => ?_)]
    · apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      simp only [hd.2, and_true]
      rw [← Finset.sum_filter, Icc_filter_mul_le' d N hd.1, Finset.mul_sum]
    · rw [Finset.mem_Icc] at hdN
      rw [Finset.mem_Icc] at hdr
      apply Finset.sum_eq_zero
      intro e _
      apply if_neg
      rintro ⟨_, h2⟩; omega
  have hB : ∑ p ∈ FB, a p.1 * b p.2
      = ∑ e ∈ Finset.Icc 1 C, b e * ∑ d ∈ Finset.Icc 1 (N / e), a d := by
    rw [hBdef, hRdef, Finset.filter_filter, Finset.sum_filter, Finset.sum_product_right]
    dsimp only
    rw [← Finset.sum_subset hsubC (fun e heN her => ?_)]
    · apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mem_Icc] at he
      simp only [he.2, and_true]
      rw [← Finset.sum_filter]
      rw [show (Finset.Icc 1 N).filter (fun d => d * e ≤ N) = Finset.Icc 1 (N / e) from by
        ext d
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hd1, _⟩, hde⟩
          exact ⟨hd1, (Nat.le_div_iff_mul_le he.1).mpr hde⟩
        · rintro ⟨hd1, hde⟩
          refine ⟨⟨hd1, le_trans hde (Nat.div_le_self N e)⟩, ?_⟩
          exact (Nat.le_div_iff_mul_le he.1).mp hde]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    · rw [Finset.mem_Icc] at heN
      rw [Finset.mem_Icc] at her
      apply Finset.sum_eq_zero
      intro d _
      apply if_neg
      rintro ⟨_, h2⟩; omega
  have hC : ∑ p ∈ R.filter (fun p => p.1 ≤ D ∧ p.2 ≤ C), a p.1 * b p.2
      = (∑ d ∈ Finset.Icc 1 D, a d) * ∑ e ∈ Finset.Icc 1 C, b e := by
    have hCset : R.filter (fun p => p.1 ≤ D ∧ p.2 ≤ C)
        = Finset.Icc 1 D ×ˢ Finset.Icc 1 C := by
      rw [hRdef]
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨⟨⟨hp1, _⟩, hp2, _⟩, _⟩, hr1, hr2⟩
        exact ⟨⟨hp1, hr1⟩, hp2, hr2⟩
      · rintro ⟨⟨hp1, hr1⟩, hp2, hr2⟩
        exact ⟨⟨⟨⟨hp1, le_trans hr1 hDN⟩, hp2, le_trans hr2 hCN⟩,
          le_trans (Nat.mul_le_mul hr1 hr2) hDC⟩, hr1, hr2⟩
    rw [hCset, Finset.sum_product]
    exact (Finset.sum_mul_sum _ _ _ _).symm
  have hUI : (∑ p ∈ FA ∪ FB, a p.1 * b p.2) + ∑ p ∈ FA ∩ FB, a p.1 * b p.2
      = (∑ p ∈ FA, a p.1 * b p.2) + ∑ p ∈ FB, a p.1 * b p.2 := Finset.sum_union_inter
  rw [hunion, hinter, hA, hB, hC] at hUI
  rw [bridge]
  exact eq_sub_of_add_eq hUI

/-- **The DH-detector asymmetric hyperbola.** `A(z) = Σ_{n≤z} dhA χ n · n^{−β₀}` split at a
free cut `D` (`1 ≤ D ≤ z`), with matching e-cut `C = z/D`: a long d-leg, a short e-leg, and
the corner. The instantiation of `sum_divisors_eq_hyperbola_asymm` at `a_d = χ_ℝ(d)d^{−β₀}`,
`b_e = e^{−β₀}` (using `dhA = χ_ℝ ∗ 1` and `d^{−β₀}(n/d)^{−β₀} = n^{−β₀}`). -/
theorem dhAbel_hyperbola_asymm {q : ℕ} (χ : DirichletCharacter ℂ q) {β₀ : ℝ} (z D : ℕ)
    (hD1 : 1 ≤ D) (hDz : D ≤ z) :
    ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀)
      = (∑ d ∈ Finset.Icc 1 D, (chiRe χ d * (d : ℝ) ^ (-β₀))
            * ∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
        + (∑ e ∈ Finset.Icc 1 (z / D), (e : ℝ) ^ (-β₀)
            * ∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀))
        - (∑ d ∈ Finset.Icc 1 D, chiRe χ d * (d : ℝ) ^ (-β₀))
          * ∑ e ∈ Finset.Icc 1 (z / D), (e : ℝ) ^ (-β₀) := by
  have hDN : D ≤ z := hDz
  have hCN : z / D ≤ z := Nat.div_le_self z D
  have hDC : D * (z / D) ≤ z := by have h := Nat.div_add_mod z D; omega
  have hcov : z < (D + 1) * (z / D + 1) := by
    calc z < D * (z / D + 1) := Nat.lt_mul_div_succ z (by omega : 0 < D)
      _ ≤ (D + 1) * (z / D + 1) := Nat.mul_le_mul (Nat.le_succ D) (le_refl _)
  have hrw : (∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀))
      = ∑ n ∈ Finset.Icc 1 z, ∑ d ∈ n.divisors,
          (chiRe χ d * (d : ℝ) ^ (-β₀)) * ((n / d : ℕ) : ℝ) ^ (-β₀) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    rw [dhA, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hnd : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    have hsplit : (n : ℝ) ^ (-β₀) = (d : ℝ) ^ (-β₀) * ((n / d : ℕ) : ℝ) ^ (-β₀) := by
      rw [← Real.mul_rpow (by positivity) (by positivity), hnd]
    rw [hsplit]; ring
  rw [hrw]
  exact sum_divisors_eq_hyperbola_asymm (fun d => chiRe χ d * (d : ℝ) ^ (-β₀))
    (fun e => (e : ℝ) ^ (-β₀)) z D (z / D) hDN hCN hDC hcov

/-- **The free-cut long-leg extraction.** For a real primitive `χ` at a real zero `β₀` and
`1 ≤ D ≤ z`, the d-leg `Leg₁ = Σ_{d≤D} χ_ℝ(d)d^{−β₀}·T(⌊z/d⌋)` extracts `L(1,χ).re` with
error split cleanly across the cut `D` (no `√z` collapse):
`|Leg₁ − L(1,χ).re·z^{1−β₀}/(1−β₀)| ≤ 6M·z^{1−β₀}/((1−β₀)D) + 34D·z^{−β₀} + 6M(Z₀+1/(1−β₀))D^{−β₀}`.
The `√t`-free generalization of `dhAbel_leg1_le`. -/
theorem dhAbel_leg1_cut_abs_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z D : ℕ} (hD1 : 1 ≤ D) (hDz : D ≤ z) :
    |(∑ d ∈ Finset.Icc 1 D, (chiRe χ d * (d : ℝ) ^ (-β₀))
          * ∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
        - (DirichletCharacter.LFunction χ 1).re * (z : ℝ) ^ (1 - β₀) / (1 - β₀)|
      ≤ 6 * (Real.sqrt q * (1 + Real.log q)) * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ))
        + 34 * (D : ℝ) * (z : ℝ) ^ (-β₀)
        + 6 * (Real.sqrt q * (1 + Real.log q)) * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set Zr : ℝ := (riemannZeta (β₀ : ℂ)).re with hZrdef
  set L₁ : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1def
  have hβ0 : 0 < β₀ := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have hz1 : 1 ≤ z := le_trans hD1 hDz
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hne' : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hZ0nn : 0 ≤ Z₀ := le_trans (norm_nonneg _)
    (hZ (β₀ : ℂ) (by rw [Complex.ofReal_re]; linarith) (by rw [Complex.ofReal_re]; linarith)
      (by rw [Complex.ofReal_im]; simp))
  have hZr_abs : |Zr| ≤ Z₀ + 1 / (1 - β₀) := abs_zeta_re_le hZ hlo hhi
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) < (D : ℝ) := by linarith
  have hPV : ∀ u : ℕ, ‖∑ k ∈ Finset.range u, χ (k : ZMod q)‖ ≤ M :=
    fun u => Salt.BV.polya_vinogradov χ hχ hq u
  -- STEP 1 : clean main
  set Sr : ℝ := ∑ d ∈ Finset.Icc 1 D, chiRe χ d / (d : ℝ) with hSrdef
  have hclean : (∑ d ∈ Finset.Icc 1 D,
        (chiRe χ d * (d : ℝ) ^ (-β₀)) * (((z : ℝ) / (d : ℝ)) ^ (1 - β₀) / (1 - β₀)))
      = (z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr := by
    rw [hSrdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hrp : (d : ℝ) ^ (-β₀) * ((z : ℝ) / (d : ℝ)) ^ (1 - β₀)
        = (z : ℝ) ^ (1 - β₀) * (d : ℝ)⁻¹ := by
      rw [Real.div_rpow hz0.le hd0.le,
        show (d : ℝ) ^ (-β₀) * ((z : ℝ) ^ (1 - β₀) / (d : ℝ) ^ (1 - β₀))
          = (z : ℝ) ^ (1 - β₀) * ((d : ℝ) ^ (-β₀) / (d : ℝ) ^ (1 - β₀)) from by ring,
        ← Real.rpow_sub hd0, show -β₀ - (1 - β₀) = (-1 : ℝ) from by ring, Real.rpow_neg_one]
    rw [show (chiRe χ d * (d : ℝ) ^ (-β₀)) * (((z : ℝ) / (d : ℝ)) ^ (1 - β₀) / (1 - β₀))
        = ((d : ℝ) ^ (-β₀) * ((z : ℝ) / (d : ℝ)) ^ (1 - β₀)) * (chiRe χ d / (1 - β₀)) from by ring,
      hrp]
    ring
  -- STEP 2 : strip engine `|S_D − L₁| ≤ 6M/D`
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hSrL1 : |Sr - L₁| ≤ 6 * M / (D : ℝ) := by
    set Pr : ℂ := ∑ d ∈ Finset.Icc 1 D, χ (d : ZMod q) * (d : ℂ) ^ (-(1 : ℂ)) with hPrdef
    have hMainRe : Sr = Pr.re := by
      rw [hSrdef, hPrdef, Complex.re_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      have hcpow : (d : ℂ) ^ (-(1 : ℂ)) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [Complex.cpow_neg, Complex.cpow_one, Complex.ofReal_inv, Complex.ofReal_natCast]
      rw [hcpow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      simp only [chiRe]; rw [div_eq_mul_inv]
    have hstrip := norm_LFunction_sub_partial_le_strip χ hne' hq hPV (s := (1 : ℂ))
      (by rw [Complex.one_re]; norm_num) (le_of_eq Complex.one_re) hD1
    have hval : 3 * M * (1 + ‖(1 : ℂ)‖ / (1 : ℂ).re) * (D : ℝ) ^ (-(1 : ℂ).re)
        = 6 * M / (D : ℝ) := by
      rw [Complex.one_re, norm_one, Real.rpow_neg (Nat.cast_nonneg D), Real.rpow_one,
        div_eq_mul_inv]
      ring
    rw [hval] at hstrip
    rw [hMainRe]
    calc |Pr.re - L₁| = |(Pr - DirichletCharacter.LFunction χ 1).re| := by rw [Complex.sub_re]
      _ ≤ ‖Pr - DirichletCharacter.LFunction χ 1‖ := Complex.abs_re_le_norm _
      _ = ‖DirichletCharacter.LFunction χ 1 - Pr‖ := by rw [norm_sub_rev]
      _ ≤ 6 * M / (D : ℝ) := hstrip
  -- STEP 3 : `|clean_main − main| ≤ 6M z^{1−β₀}/((1−β₀)D)`
  have hCM : |(z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀)|
      ≤ 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ)) := by
    have heq : (z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀)
        = (z : ℝ) ^ (1 - β₀) / (1 - β₀) * (Sr - L₁) := by ring
    rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (z : ℝ) ^ (1 - β₀) / (1 - β₀))]
    calc (z : ℝ) ^ (1 - β₀) / (1 - β₀) * |Sr - L₁|
        ≤ (z : ℝ) ^ (1 - β₀) / (1 - β₀) * (6 * M / (D : ℝ)) :=
          mul_le_mul_of_nonneg_left hSrL1 (by positivity)
      _ = 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ)) := by
          rw [div_mul_div_comm]; ring
  -- STEP 4 : per-term remainder `|X_d| ≤ 17⌊z/d⌋^{−β₀}`
  have hX : ∀ d ∈ Finset.Icc 1 D,
      |(∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
          - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀) / (1 - β₀) - Zr|
        ≤ 17 * ((z / d : ℕ) : ℝ) ^ (-β₀) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hdt1 : 1 ≤ z / d := (Nat.one_le_div_iff (by omega)).mpr (le_trans hd.2 hDz)
    have hf0 : (0 : ℝ) < ((z / d : ℕ) : ℝ) := by exact_mod_cast hdt1
    have hle : ((z / d : ℕ) : ℝ) ≤ (z : ℝ) / (d : ℝ) := Nat.cast_div_le
    have hFE_nn : 0 ≤ ((z : ℝ) / (d : ℝ)) ^ (1 - β₀) - ((z / d : ℕ) : ℝ) ^ (1 - β₀) := by
      have := Real.rpow_le_rpow hf0.le hle (by linarith : (0 : ℝ) ≤ 1 - β₀); linarith
    have hyx : (z : ℝ) / (d : ℝ) - ((z / d : ℕ) : ℝ) ≤ 1 := by
      have hmod : z < (z / d + 1) * d := by
        have h1 := Nat.div_add_mod z d
        have h2 : z % d < d := Nat.mod_lt z (by omega)
        nlinarith
      have hR : (z : ℝ) < (((z / d : ℕ) : ℝ) + 1) * (d : ℝ) := by exact_mod_cast hmod
      have hdivlt : (z : ℝ) / (d : ℝ) < ((z / d : ℕ) : ℝ) + 1 := (div_lt_iff₀ hd0).mpr hR
      linarith [hdivlt]
    have hFE_le : ((z : ℝ) / (d : ℝ)) ^ (1 - β₀) - ((z / d : ℕ) : ℝ) ^ (1 - β₀)
        ≤ (1 - β₀) * ((z / d : ℕ) : ℝ) ^ (-β₀) := by
      have htan := rpow_sub_le_tangent (c := 1 - β₀) (by linarith) (by linarith) hf0 hle
      rw [show (1 - β₀) - 1 = -β₀ from by ring] at htan
      calc ((z : ℝ) / (d : ℝ)) ^ (1 - β₀) - ((z / d : ℕ) : ℝ) ^ (1 - β₀)
          ≤ (1 - β₀) * ((z / d : ℕ) : ℝ) ^ (-β₀) * ((z : ℝ) / (d : ℝ) - ((z / d : ℕ) : ℝ)) := htan
        _ ≤ (1 - β₀) * ((z / d : ℕ) : ℝ) ^ (-β₀) * 1 :=
            mul_le_mul_of_nonneg_left hyx (by positivity)
        _ = (1 - β₀) * ((z / d : ℕ) : ℝ) ^ (-β₀) := by ring
    have hem := T_em_real hlo hhi hdt1
    have hsplit : (∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
          - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀) / (1 - β₀) - Zr
        = ((∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
              - ((z / d : ℕ) : ℝ) ^ (1 - β₀) / (1 - β₀) - Zr)
          + (((z / d : ℕ) : ℝ) ^ (1 - β₀) - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀)) / (1 - β₀) := by
      field_simp; ring
    rw [hsplit]
    have hFE_bound : |(((z / d : ℕ) : ℝ) ^ (1 - β₀) - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀)) / (1 - β₀)|
        ≤ ((z / d : ℕ) : ℝ) ^ (-β₀) := by
      rw [abs_div, abs_of_pos hu, div_le_iff₀ hu, abs_sub_comm, abs_of_nonneg hFE_nn]
      linarith [hFE_le]
    calc |((∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
              - ((z / d : ℕ) : ℝ) ^ (1 - β₀) / (1 - β₀) - Zr)
          + (((z / d : ℕ) : ℝ) ^ (1 - β₀) - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀)) / (1 - β₀)|
        ≤ |(∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
              - ((z / d : ℕ) : ℝ) ^ (1 - β₀) / (1 - β₀) - Zr|
          + |(((z / d : ℕ) : ℝ) ^ (1 - β₀) - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀)) / (1 - β₀)| :=
          abs_add_le _ _
      _ ≤ 8 * (1 + β₀) * ((z / d : ℕ) : ℝ) ^ (-β₀) + ((z / d : ℕ) : ℝ) ^ (-β₀) := by
          apply add_le_add hem hFE_bound
      _ ≤ 17 * ((z / d : ℕ) : ℝ) ^ (-β₀) := by
          have hpos : (0 : ℝ) ≤ ((z / d : ℕ) : ℝ) ^ (-β₀) := Real.rpow_nonneg hf0.le _
          nlinarith [hpos]
  -- STEP 5 : decompose and bound
  set Br : ℝ := ∑ d ∈ Finset.Icc 1 D, chiRe χ d * (d : ℝ) ^ (-β₀) with hBrdef
  set G : ℝ := ∑ d ∈ Finset.Icc 1 D, (chiRe χ d * (d : ℝ) ^ (-β₀))
      * ((∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
          - ((z : ℝ) / (d : ℝ)) ^ (1 - β₀) / (1 - β₀) - Zr) with hGdef
  have hLeg1eq : (∑ d ∈ Finset.Icc 1 D, (chiRe χ d * (d : ℝ) ^ (-β₀))
        * ∑ e ∈ Finset.Icc 1 (z / d), (e : ℝ) ^ (-β₀))
      = (∑ d ∈ Finset.Icc 1 D, (chiRe χ d * (d : ℝ) ^ (-β₀))
            * (((z : ℝ) / (d : ℝ)) ^ (1 - β₀) / (1 - β₀))) + (G + Zr * Br) := by
    rw [hGdef, hBrdef, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  have hGbound : |G| ≤ 34 * (D : ℝ) * (z : ℝ) ^ (-β₀) := by
    have h1 : |G| ≤ ∑ d ∈ Finset.Icc 1 D, (d : ℝ) ^ (-β₀) * (17 * ((z / d : ℕ) : ℝ) ^ (-β₀)) := by
      rw [hGdef]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun d hd => ?_))
      rw [abs_mul]
      apply mul_le_mul _ (hX d hd) (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      calc |chiRe χ d| * (d : ℝ) ^ (-β₀)
          ≤ 1 * (d : ℝ) ^ (-β₀) :=
            mul_le_mul_of_nonneg_right (chiRe_abs_le_one χ d) (Real.rpow_nonneg (by positivity) _)
        _ = (d : ℝ) ^ (-β₀) := one_mul _
    have h2 : ∑ d ∈ Finset.Icc 1 D, (d : ℝ) ^ (-β₀) * (17 * ((z / d : ℕ) : ℝ) ^ (-β₀))
        ≤ ∑ d ∈ Finset.Icc 1 D, 34 * (z : ℝ) ^ (-β₀) := by
      refine Finset.sum_le_sum (fun d hd => ?_)
      rw [Finset.mem_Icc] at hd
      have htr := term_rpow_le (β := β₀) (by linarith) (by linarith) (e := d) (t := z)
        hd.1 (le_trans hd.2 hDz)
      calc (d : ℝ) ^ (-β₀) * (17 * ((z / d : ℕ) : ℝ) ^ (-β₀))
          = 17 * ((d : ℝ) ^ (-β₀) * ((z / d : ℕ) : ℝ) ^ (-β₀)) := by ring
        _ ≤ 17 * (2 * (z : ℝ) ^ (-β₀)) := by
            apply mul_le_mul_of_nonneg_left htr (by norm_num)
        _ = 34 * (z : ℝ) ^ (-β₀) := by ring
    have h3 : ∑ d ∈ Finset.Icc 1 D, 34 * (z : ℝ) ^ (-β₀) = 34 * ((D : ℝ) * (z : ℝ) ^ (-β₀)) := by
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
    calc |G| ≤ ∑ d ∈ Finset.Icc 1 D, (d : ℝ) ^ (-β₀) * (17 * ((z / d : ℕ) : ℝ) ^ (-β₀)) := h1
      _ ≤ ∑ d ∈ Finset.Icc 1 D, 34 * (z : ℝ) ^ (-β₀) := h2
      _ = 34 * ((D : ℝ) * (z : ℝ) ^ (-β₀)) := h3
      _ = 34 * (D : ℝ) * (z : ℝ) ^ (-β₀) := by ring
  have hBr_bound : |Br| ≤ 6 * M * (D : ℝ) ^ (-β₀) := by
    rw [hBrdef]; exact chiRe_partial_at_zero_le χ hχ hsq hq hzero hβ0 (by linarith) hD1
  have hZrBr : |Zr * Br| ≤ 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀) := by
    rw [abs_mul]
    calc |Zr| * |Br|
        ≤ (Z₀ + 1 / (1 - β₀)) * (6 * M * (D : ℝ) ^ (-β₀)) :=
          mul_le_mul hZr_abs hBr_bound (abs_nonneg _) (by positivity)
      _ = 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀) := by ring
  rw [hLeg1eq, hclean]
  have hsplit2 : (z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr + (G + Zr * Br)
        - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀)
      = ((z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀))
          + (G + Zr * Br) := by ring
  rw [hsplit2]
  calc |((z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀)) + (G + Zr * Br)|
      ≤ |(z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀)|
          + |G + Zr * Br| := abs_add_le _ _
    _ ≤ |(z : ℝ) ^ (1 - β₀) / (1 - β₀) * Sr - L₁ * (z : ℝ) ^ (1 - β₀) / (1 - β₀)|
          + (|G| + |Zr * Br|) := by linarith [abs_add_le G (Zr * Br)]
    _ ≤ 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ))
          + (34 * (D : ℝ) * (z : ℝ) ^ (-β₀)
              + 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀)) := by
        linarith [hCM, hGbound, hZrBr]
    _ = 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ))
          + 34 * (D : ℝ) * (z : ℝ) ^ (-β₀)
          + 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀) := by ring

/-- **The two-sided LOWER Abel bound (free cut, `T-BAL` R5e).** For a real primitive `χ` at a
real zero `β₀`, the Dirichlet-detector Abel sum `A(z) = Σ_{n≤z} dhA χ n · n^{−β₀}` is at least
its `L(1,χ)`-main minus an error placed by the FREE hyperbola cut
`D = Nat.sqrt (z · min ⌈1/(1−β₀)⌉₊ z) ~ √(z/(1−β₀))`. On the deep ray the crushed error carries
one clean power of `(1−β₀)` (the `√z` cut's corner term `36M/(1−β₀)` — a full power — is avoided).
`M = √q(1+log q)`. -/
theorem dhAbel_inner_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {z : ℕ} (hz : 2 ≤ z) :
    (DirichletCharacter.LFunction χ 1).re * (z : ℝ) ^ (1 - β₀) / (1 - β₀)
        - (34 * ((Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) : ℕ) : ℝ) * (z : ℝ) ^ (-β₀)
            + 12 * (Real.sqrt q * (1 + Real.log q)) * (z : ℝ) ^ (1 - β₀)
                / ((1 - β₀) * ((Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) : ℕ) : ℝ))
            + 12 * (Real.sqrt q * (1 + Real.log q)) * (z : ℝ) ^ (1 - β₀)
                / ((Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) : ℕ) : ℝ)
            + 6 * (Real.sqrt q * (1 + Real.log q)) * (Z₀ + 1 / (1 - β₀))
                * ((Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) : ℕ) : ℝ) ^ (-β₀))
      ≤ ∑ n ∈ Finset.Icc 1 z, dhA χ n * (n : ℝ) ^ (-β₀) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set L₁ : ℝ := (DirichletCharacter.LFunction χ 1).re with hL1def
  set D : ℕ := Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) with hDdef
  have hβ0 : 0 < β₀ := by linarith
  have hu : 0 < 1 - β₀ := by linarith
  have hz1 : 1 ≤ z := by omega
  have hz0 : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz1
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  -- cut facts
  have hkpos : 1 ≤ ⌈(1 : ℝ) / (1 - β₀)⌉₊ := Nat.one_le_ceil_iff.mpr (div_pos one_pos hu)
  have hminpos : 1 ≤ min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z := le_min hkpos hz1
  have hN0pos : 1 ≤ z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z := by
    calc 1 = 1 * 1 := (one_mul 1).symm
      _ ≤ z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z := Nat.mul_le_mul hz1 hminpos
  have hD1 : 1 ≤ D := by
    rw [hDdef]
    calc 1 = Nat.sqrt 1 := Nat.sqrt_one.symm
      _ ≤ Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) := Nat.sqrt_le_sqrt hN0pos
  have hzz2 : Nat.sqrt (z * z) = z := by rw [← Nat.pow_two]; exact Nat.sqrt_eq' z
  have hDz : D ≤ z := by
    rw [hDdef]
    have h1 : z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z ≤ z * z :=
      Nat.mul_le_mul (le_refl z) (min_le_right _ _)
    calc Nat.sqrt (z * min ⌈(1 : ℝ) / (1 - β₀)⌉₊ z) ≤ Nat.sqrt (z * z) := Nat.sqrt_le_sqrt h1
      _ = z := hzz2
  have hD1R : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
  have hD0 : (0 : ℝ) < (D : ℝ) := by linarith
  have hDzR : (D : ℝ) ≤ (z : ℝ) := by exact_mod_cast hDz
  set C : ℕ := z / D with hCdef
  have hCz : C ≤ z := by rw [hCdef]; exact Nat.div_le_self z D
  have hCleD : (C : ℝ) ≤ (z : ℝ) / (D : ℝ) := by rw [hCdef]; exact Nat.cast_div_le
  -- LEG 1
  have hleg1 := dhAbel_leg1_cut_abs_le χ hχ hsq hq hzero hlo hhi hZ hD1 hDz
  rw [← hMdef, ← hL1def] at hleg1
  -- LEG 2
  have hleg2raw : |∑ e ∈ Finset.Icc 1 C, (e : ℝ) ^ (-β₀)
        * ∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
      ≤ 12 * M * (C : ℝ) * (z : ℝ) ^ (-β₀) := by
    have hstep : ∀ e ∈ Finset.Icc 1 C,
        |(e : ℝ) ^ (-β₀) * ∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
          ≤ 6 * M * (2 * (z : ℝ) ^ (-β₀)) := by
      intro e he
      rw [Finset.mem_Icc] at he
      have hez : e ≤ z := le_trans he.2 hCz
      have hze1 : 1 ≤ z / e := (Nat.one_le_div_iff (by omega)).mpr hez
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      calc (e : ℝ) ^ (-β₀) * |∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
          ≤ (e : ℝ) ^ (-β₀) * (6 * M * ((z / e : ℕ) : ℝ) ^ (-β₀)) :=
            mul_le_mul_of_nonneg_left
              (chiRe_partial_at_zero_le χ hχ hsq hq hzero hβ0 (by linarith) hze1)
              (Real.rpow_nonneg (by positivity) _)
        _ = 6 * M * ((e : ℝ) ^ (-β₀) * ((z / e : ℕ) : ℝ) ^ (-β₀)) := by ring
        _ ≤ 6 * M * (2 * (z : ℝ) ^ (-β₀)) := by
            apply mul_le_mul_of_nonneg_left
              (term_rpow_le (by linarith) (by linarith) he.1 hez) (by positivity)
    calc |∑ e ∈ Finset.Icc 1 C, (e : ℝ) ^ (-β₀)
            * ∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
        ≤ ∑ e ∈ Finset.Icc 1 C, |(e : ℝ) ^ (-β₀)
            * ∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ Finset.Icc 1 C, 6 * M * (2 * (z : ℝ) ^ (-β₀)) := Finset.sum_le_sum hstep
      _ = (C : ℝ) * (12 * M * (z : ℝ) ^ (-β₀)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
      _ = 12 * M * (C : ℝ) * (z : ℝ) ^ (-β₀) := by ring
  have hzz : (z : ℝ) * (z : ℝ) ^ (-β₀) = (z : ℝ) ^ (1 - β₀) := by
    nth_rewrite 1 [← Real.rpow_one (z : ℝ)]
    rw [← Real.rpow_add hz0, show (1 : ℝ) + -β₀ = 1 - β₀ from by ring]
  have hleg2 : |∑ e ∈ Finset.Icc 1 C, (e : ℝ) ^ (-β₀)
        * ∑ d ∈ Finset.Icc 1 (z / e), chiRe χ d * (d : ℝ) ^ (-β₀)|
      ≤ 12 * M * (z : ℝ) ^ (1 - β₀) / (D : ℝ) := by
    refine le_trans hleg2raw ?_
    calc 12 * M * (C : ℝ) * (z : ℝ) ^ (-β₀) = 12 * M * (z : ℝ) ^ (-β₀) * (C : ℝ) := by ring
      _ ≤ 12 * M * (z : ℝ) ^ (-β₀) * ((z : ℝ) / (D : ℝ)) :=
          mul_le_mul_of_nonneg_left hCleD (by positivity)
      _ = 12 * M * ((z : ℝ) * (z : ℝ) ^ (-β₀)) / (D : ℝ) := by ring
      _ = 12 * M * (z : ℝ) ^ (1 - β₀) / (D : ℝ) := by rw [hzz]
  -- CORNER
  have hcorner : |(∑ d ∈ Finset.Icc 1 D, chiRe χ d * (d : ℝ) ^ (-β₀))
        * ∑ e ∈ Finset.Icc 1 C, (e : ℝ) ^ (-β₀)|
      ≤ 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ)) := by
    rw [abs_mul]
    have hBD : |∑ d ∈ Finset.Icc 1 D, chiRe χ d * (d : ℝ) ^ (-β₀)| ≤ 6 * M * (D : ℝ) ^ (-β₀) :=
      chiRe_partial_at_zero_le χ hχ hsq hq hzero hβ0 (by linarith) hD1
    have hTC : |∑ e ∈ Finset.Icc 1 C, (e : ℝ) ^ (-β₀)| ≤ (C : ℝ) ^ (1 - β₀) / (1 - β₀) := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun e _ => Real.rpow_nonneg (by positivity) _))]
      exact sum_rpow_neg_le (by linarith) hhi C
    have hCrpow : (C : ℝ) ^ (1 - β₀) ≤ (z : ℝ) ^ (1 - β₀) * (D : ℝ) ^ (-(1 - β₀)) := by
      calc (C : ℝ) ^ (1 - β₀) ≤ ((z : ℝ) / (D : ℝ)) ^ (1 - β₀) :=
            Real.rpow_le_rpow (by positivity) hCleD (by linarith)
        _ = (z : ℝ) ^ (1 - β₀) / (D : ℝ) ^ (1 - β₀) := by rw [Real.div_rpow hz0.le hD0.le]
        _ = (z : ℝ) ^ (1 - β₀) * (D : ℝ) ^ (-(1 - β₀)) := by
            rw [Real.rpow_neg hD0.le, div_eq_mul_inv]
    have hkey : (D : ℝ) ^ (-β₀) * (C : ℝ) ^ (1 - β₀) ≤ (z : ℝ) ^ (1 - β₀) / (D : ℝ) := by
      calc (D : ℝ) ^ (-β₀) * (C : ℝ) ^ (1 - β₀)
          ≤ (D : ℝ) ^ (-β₀) * ((z : ℝ) ^ (1 - β₀) * (D : ℝ) ^ (-(1 - β₀))) :=
            mul_le_mul_of_nonneg_left hCrpow (Real.rpow_nonneg hD0.le _)
        _ = (z : ℝ) ^ (1 - β₀) * ((D : ℝ) ^ (-β₀) * (D : ℝ) ^ (-(1 - β₀))) := by ring
        _ = (z : ℝ) ^ (1 - β₀) * (D : ℝ) ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hD0]; congr 2; ring
        _ = (z : ℝ) ^ (1 - β₀) / (D : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    calc |∑ d ∈ Finset.Icc 1 D, chiRe χ d * (d : ℝ) ^ (-β₀)|
            * |∑ e ∈ Finset.Icc 1 C, (e : ℝ) ^ (-β₀)|
        ≤ (6 * M * (D : ℝ) ^ (-β₀)) * ((C : ℝ) ^ (1 - β₀) / (1 - β₀)) :=
          mul_le_mul hBD hTC (abs_nonneg _) (by positivity)
      _ = 6 * M / (1 - β₀) * ((D : ℝ) ^ (-β₀) * (C : ℝ) ^ (1 - β₀)) := by ring
      _ ≤ 6 * M / (1 - β₀) * ((z : ℝ) ^ (1 - β₀) / (D : ℝ)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ)) := by
          rw [div_mul_div_comm]
  -- ASSEMBLE
  rw [dhAbel_hyperbola_asymm χ z D hD1 hDz, ← hCdef]
  have a1 := (abs_le.mp hleg1).1
  have a2 := (abs_le.mp hleg2).1
  have a3 := (abs_le.mp hcorner).2
  have hERR : 34 * (D : ℝ) * (z : ℝ) ^ (-β₀)
        + 12 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ))
        + 12 * M * (z : ℝ) ^ (1 - β₀) / (D : ℝ)
        + 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀)
      = (6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ)) + 34 * (D : ℝ) * (z : ℝ) ^ (-β₀)
          + 6 * M * (Z₀ + 1 / (1 - β₀)) * (D : ℝ) ^ (-β₀))
        + 12 * M * (z : ℝ) ^ (1 - β₀) / (D : ℝ)
        + 6 * M * (z : ℝ) ^ (1 - β₀) / ((1 - β₀) * (D : ℝ)) := by ring
  linarith [a1, a2, a3, hERR]

end Salt.SW
