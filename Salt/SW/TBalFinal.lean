/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHExtractRho
import Salt.SW.TBalClose

/-!
# T-BAL THE FINISH — the ρ-side extraction chain (R6-1@ρ / R6-3@ρ)

The remaining flagged chain from `T-BAL-R6RHO` (`docs/blueprints/flags.md`): the ρ-side
detector bound built on the analytic heart `dhAbel_inner_rho` (`Salt/SW/DHExtractRho.lean`).

Landed here (in order):

* `norm_LFunction_one_eq_re` — the reality micro-lemma `‖L(1,χ)‖ = (L(1,χ)).re` for a real
  primitive `χ` (catch #226/#230): `L(1,χ) > 0` in the `Complex.lt_def` order already carries
  `L(1,χ).im = 0`.
* `sum_mul_index_eq_rho` / `kernel_abel_sum_rho` — R6-1@ρ, the complex-scale kernel-Abel identity
  (the ℂ re-run of `sum_mul_index_eq` / `kernel_abel_sum_real`, pure summation-by-parts).

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`.
-/

open Complex
open Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §0 — the reality micro-lemma (catch #226/#230) -/

/-- **The `L(1,χ)` reality micro-lemma.** For a real primitive `χ` (`χ ≠ 1`, `χ² = 1`),
`‖L(1,χ)‖ = (L(1,χ)).re`. The boundary value `L(1,χ) > 0` in the `Complex.lt_def` order
(`LFunction_apply_one_pos`) already carries `L(1,χ).im = 0` and `(L(1,χ)).re > 0`, so its norm is
its real part. This is the load-bearing u-fact of the ρ-mechanism: it turns the ρ-detector main
`‖L(1,χ)‖·…` into `L₁·…` (`= (L(1,χ)).re ≤ u·25e(1+log q)²`), giving the `u = 1−β₀` decay. -/
theorem norm_LFunction_one_eq_re [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ1 : χ ≠ 1) (hsq : χ ^ 2 = 1) :
    ‖DirichletCharacter.LFunction χ 1‖ = (DirichletCharacter.LFunction χ 1).re := by
  have hpos := LFunction_apply_one_pos hχ1 hsq
  have him : (DirichletCharacter.LFunction χ 1).im = 0 := ((Complex.pos_iff.mp hpos).2).symm
  have hre : 0 ≤ (DirichletCharacter.LFunction χ 1).re := le_of_lt (Complex.pos_iff.mp hpos).1
  have hz : DirichletCharacter.LFunction χ 1 = ((DirichletCharacter.LFunction χ 1).re : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]; exact him
  calc ‖DirichletCharacter.LFunction χ 1‖
      = ‖((DirichletCharacter.LFunction χ 1).re : ℂ)‖ := by rw [← hz]
    _ = ‖(DirichletCharacter.LFunction χ 1).re‖ := Complex.norm_real _
    _ = |(DirichletCharacter.LFunction χ 1).re| := Real.norm_eq_abs _
    _ = (DirichletCharacter.LFunction χ 1).re := abs_of_nonneg hre

/-! ## §1 — R6-1@ρ : the complex-scale kernel-Abel identity -/

/-- **Complex Abel identity (weighted).** `Σ_{1≤n≤y} n·a_n = y·A(y) − Σ_{1≤t≤y−1} A(t)` with
`A(t) = Σ_{1≤n≤t} a_n`, for a ℂ-valued coefficient `a`. The ℂ re-run of `sum_mul_index_eq`
(pure summation by parts, induction on `y ≥ 1`; generic over the commutative ring). -/
lemma sum_mul_index_eq_rho (a : ℕ → ℂ) {y : ℕ} (hy : 1 ≤ y) :
    ∑ n ∈ Finset.Icc 1 y, (n : ℂ) * a n
      = (y : ℂ) * (∑ n ∈ Finset.Icc 1 y, a n)
        - ∑ t ∈ Finset.Icc 1 (y - 1), ∑ n ∈ Finset.Icc 1 t, a n := by
  induction y, hy using Nat.le_induction with
  | base => simp
  | succ y hy ih =>
    have hsucc : y + 1 - 1 = y := by omega
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ y + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ y + 1), hsucc]
    rw [ih]
    have hAsplit : ∑ t ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 t, a n
        = (∑ t ∈ Finset.Icc 1 (y - 1), ∑ n ∈ Finset.Icc 1 t, a n)
          + ∑ n ∈ Finset.Icc 1 y, a n := by
      rcases Nat.lt_or_ge 1 (y + 1) with hy1 | hy1
      · have : y = (y - 1) + 1 := by omega
        rw [this, Finset.sum_Icc_succ_top (by omega : 1 ≤ (y - 1) + 1)]
        congr 1
      · omega
    rw [hAsplit]
    push_cast
    ring

/-- **R6-1@ρ (complex kernel-Abel, real scale).** For any `a : ℕ → ℂ` and real `x ≥ 1`, with
`T = ⌊x⌋`, `Σ_{s≤T} a_s·(1 − s/x) = (1/x)·[(x − T)·A(T) + Σ_{t≤T−1} A(t)]`, `A(t) = Σ_{s≤t} a_s`
(the kernel `1 − s/x` is the real linear kernel cast to `ℂ`). Summation by parts
(`sum_mul_index_eq_rho`) against the linear kernel; the boundary term `(x − T)·A(T)` is the
real-floor correction. The ℂ re-run of `kernel_abel_sum_real`. -/
theorem kernel_abel_sum_rho (a : ℕ → ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ s ∈ Finset.Icc 1 ⌊x⌋₊, a s * ((1 - (s : ℝ) / x : ℝ) : ℂ)
      = (1 / (x : ℂ)) * (((x : ℂ) - (⌊x⌋₊ : ℂ)) * (∑ s ∈ Finset.Icc 1 ⌊x⌋₊, a s)
          + ∑ t ∈ Finset.Icc 1 (⌊x⌋₊ - 1), ∑ s ∈ Finset.Icc 1 t, a s) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hxC0 : (x : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact hx0.ne'
  set T : ℕ := ⌊x⌋₊ with hTdef
  have hT1 : 1 ≤ T := by rw [hTdef, Nat.le_floor_iff (by linarith)]; exact_mod_cast hx
  have hkey := sum_mul_index_eq_rho a hT1
  have hexpand : ∑ s ∈ Finset.Icc 1 T, a s * ((1 - (s : ℝ) / x : ℝ) : ℂ)
      = (∑ s ∈ Finset.Icc 1 T, a s) - (1 / (x : ℂ)) * ∑ s ∈ Finset.Icc 1 T, (s : ℂ) * a s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have hcast : ((1 - (s : ℝ) / x : ℝ) : ℂ) = 1 - (s : ℂ) / (x : ℂ) := by
      push_cast; ring
    rw [hcast]
    field_simp
  rw [hexpand, hkey]
  field_simp
  ring

/-! ## §2 — the complex power-sum sandwich (R6-3@ρ's new analytic sub-lemma, catch #225) -/

/-- **The complex unit-interval tangent.** For `0 < Re ρ < 1` and `t ≥ 2`, the discrete tangent
error of `φ(u) = u^{2−ρ}/(2−ρ)` (`φ' = u^{1−ρ}`) at the unit step `[t−1, t]`:
`‖(t^{2−ρ}/(2−ρ) − (t−1)^{2−ρ}/(2−ρ)) − t^{1−ρ}‖ ≤ 2‖1−ρ‖·(t−1)^{−Re ρ}`. Mean value inequality
for `ψ(u) = φ(u) − u·t^{1−ρ}` on `[t−1, t]` (`ψ' = u^{1−ρ} − t^{1−ρ}`, `ψ(t) − ψ(t−1) =` the
error); the sup of `‖ψ'‖` is bounded by two floor/tangent applications
(`norm_cpow_pos_floor_sub_le`). The complex analog of the real MVT upper tangent. -/
theorem cpow_unit_tangent_bound {ρ : ℂ} (hσ0 : 0 < ρ.re) (hσ1 : ρ.re < 1) {t : ℕ} (ht : 2 ≤ t) :
    ‖((t : ℂ) ^ (2 - ρ) / (2 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (2 - ρ) / (2 - ρ))
        - (t : ℂ) ^ (1 - ρ)‖
      ≤ 2 * ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) := by
  have h2ρne : (2 : ℂ) - ρ ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at h2
    linarith
  have hm1 : 1 ≤ t - 1 := by omega
  have ht2R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hmR : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have htR0 : (0 : ℝ) < (t : ℝ) := by positivity
  have hmR0 : (0 : ℝ) < ((t - 1 : ℕ) : ℝ) := by rw [hmR]; linarith
  -- ψ and its derivative on S = [t-1, t]
  set S : Set ℝ := Set.Icc ((t - 1 : ℕ) : ℝ) (t : ℝ) with hSdef
  have hconv : Convex ℝ S := convex_Icc _ _
  set ψ : ℝ → ℂ := fun u => (u : ℂ) ^ (2 - ρ) / (2 - ρ) - (u : ℂ) * (t : ℂ) ^ (1 - ρ) with hψdef
  have hofReal : ∀ u : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := by
    intro u; simpa using (hasDerivAt_id u).ofReal_comp
  have hderiv : ∀ u ∈ S, HasDerivWithinAt ψ ((u : ℂ) ^ (1 - ρ) - (t : ℂ) ^ (1 - ρ)) S u := by
    intro u hu
    rw [hSdef, Set.mem_Icc] at hu
    have hu0 : (u : ℝ) ≠ 0 := by have := lt_of_lt_of_le hmR0 hu.1; linarith
    have hd1 : HasDerivAt (fun v : ℝ => (v : ℂ) ^ (2 - ρ) / (2 - ρ)) ((u : ℂ) ^ (1 - ρ)) u := by
      have h := (hasDerivAt_ofReal_cpow_const hu0 h2ρne).div_const (2 - ρ)
      have heq : (2 - ρ) * (u : ℂ) ^ ((2 - ρ) - 1) / (2 - ρ) = (u : ℂ) ^ (1 - ρ) := by
        rw [show (2 - ρ) - 1 = 1 - ρ by ring, mul_comm ((2 : ℂ) - ρ), mul_div_assoc,
          div_self h2ρne, mul_one]
      rwa [heq] at h
    have hd2 : HasDerivAt (fun v : ℝ => (v : ℂ) * (t : ℂ) ^ (1 - ρ)) ((t : ℂ) ^ (1 - ρ)) u := by
      have h := (hofReal u).mul_const ((t : ℂ) ^ (1 - ρ)); rwa [one_mul] at h
    exact (hd1.sub hd2).hasDerivWithinAt
  have hbound : ∀ u ∈ S,
      ‖(u : ℂ) ^ (1 - ρ) - (t : ℂ) ^ (1 - ρ)‖ ≤ 2 * ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) := by
    intro u hu
    rw [hSdef, Set.mem_Icc] at hu
    have hA : ‖(u : ℂ) ^ (1 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (1 - ρ)‖
        ≤ ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) :=
      norm_cpow_pos_floor_sub_le hσ0 hσ1 hm1 hu.1 (by rw [hmR]; linarith [hu.2])
    have hB : ‖(t : ℂ) ^ (1 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (1 - ρ)‖
        ≤ ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) :=
      norm_cpow_pos_floor_sub_le hσ0 hσ1 hm1 (by rw [hmR]; linarith)
        (by rw [hmR]; linarith)
    calc ‖(u : ℂ) ^ (1 - ρ) - (t : ℂ) ^ (1 - ρ)‖
        = ‖((u : ℂ) ^ (1 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (1 - ρ))
            - ((t : ℂ) ^ (1 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (1 - ρ))‖ := by congr 1; ring
      _ ≤ ‖(u : ℂ) ^ (1 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (1 - ρ)‖
            + ‖(t : ℂ) ^ (1 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (1 - ρ)‖ := norm_sub_le _ _
      _ ≤ ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re)
            + ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) := add_le_add hA hB
      _ = 2 * ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) := by ring
  have hmS : ((t - 1 : ℕ) : ℝ) ∈ S := by
    rw [hSdef, Set.mem_Icc]; exact ⟨le_refl _, by rw [hmR]; linarith⟩
  have htS : (t : ℝ) ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨by rw [hmR]; linarith, le_refl _⟩
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hmS htS
  -- ψ(t) - ψ(t-1) = the tangent error
  have hψval : ψ (t : ℝ) - ψ ((t - 1 : ℕ) : ℝ)
      = ((t : ℂ) ^ (2 - ρ) / (2 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (2 - ρ) / (2 - ρ))
        - (t : ℂ) ^ (1 - ρ) := by
    have hcast : ((((t - 1 : ℕ) : ℝ)) : ℂ) = ((t - 1 : ℕ) : ℂ) := by push_cast; ring
    have hcastt : (((t : ℝ)) : ℂ) = (t : ℂ) := by push_cast; ring
    have hcastC : ((t - 1 : ℕ) : ℂ) = (t : ℂ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ t)]; push_cast; ring
    simp only [hψdef, hcast, hcastt]
    rw [hcastC]
    ring
  have hwidth : ‖(t : ℝ) - ((t - 1 : ℕ) : ℝ)‖ = 1 := by
    rw [hmR, Real.norm_eq_abs]; rw [show (t : ℝ) - ((t : ℝ) - 1) = 1 by ring]; norm_num
  rw [hψval] at hmvt
  calc ‖((t : ℂ) ^ (2 - ρ) / (2 - ρ) - ((t - 1 : ℕ) : ℂ) ^ (2 - ρ) / (2 - ρ)) - (t : ℂ) ^ (1 - ρ)‖
      ≤ 2 * ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) * ‖(t : ℝ) - ((t - 1 : ℕ) : ℝ)‖ := hmvt
    _ = 2 * ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-ρ.re) := by rw [hwidth, mul_one]

/-- **General complex-cpow segment bound (MVT).** For `s ≠ 0`, `0 < a ≤ b` and a uniform
derivative-norm bound `‖s·w^{s−1}‖ ≤ C` on `[a,b]`, `‖b^s − a^s‖ ≤ C·(b − a)`. Mean value
inequality for `u ↦ (u:ℂ)^s` (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`). -/
theorem norm_ofReal_cpow_seg_le {s : ℂ} (hsne : s ≠ 0) {a b C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hC : ∀ w : ℝ, a ≤ w → w ≤ b → ‖s * (w : ℂ) ^ (s - 1)‖ ≤ C) :
    ‖(b : ℂ) ^ s - (a : ℂ) ^ s‖ ≤ C * (b - a) := by
  set S : Set ℝ := Set.Icc a b with hSdef
  have hconv : Convex ℝ S := convex_Icc _ _
  have hderiv : ∀ w ∈ S,
      HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ s) (s * (w : ℂ) ^ (s - 1)) S w := by
    intro w hw
    rw [hSdef, Set.mem_Icc] at hw
    have hw0 : (w : ℝ) ≠ 0 := by have := lt_of_lt_of_le ha hw.1; linarith
    exact (hasDerivAt_ofReal_cpow_const hw0 hsne).hasDerivWithinAt
  have hbound : ∀ w ∈ S, ‖s * (w : ℂ) ^ (s - 1)‖ ≤ C := by
    intro w hw; rw [hSdef, Set.mem_Icc] at hw; exact hC w hw.1 hw.2
  have haS : a ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨le_refl _, hab⟩
  have hbS : b ∈ S := by rw [hSdef, Set.mem_Icc]; exact ⟨hab, le_refl _⟩
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound haS hbS
  have hw : ‖(b : ℝ) - a‖ = b - a := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rwa [hw] at hmvt

set_option maxHeartbeats 800000 in
-- The telescoping identity + three norm legs (corner, gap, tangent-sum) over the (1−ρ)/(2−ρ)
-- denominators exceed the default heartbeat budget.
/-- **R6-3@ρ's complex power-sum sandwich (catch #225).** For `0 < Re ρ < 1`, real `x ≥ 2` and
`T = ⌊x⌋ ≥ 2`, the complex analog of `sum_rpow_sandwich`:
`‖((x−T)·T^{1−ρ} + Σ_{1≤t≤T−1} t^{1−ρ}) − x^{2−ρ}/(2−ρ)‖ ≤ (5 + 4‖1−ρ‖/(1−Re ρ))·x^{1−Re ρ}`.
The sandwich error carries the extra `1/(1−Re ρ) = L₂/c₀` factor (catch #225) — from the
oscillation of `t^{1−ρ}` — UNLIKE the pure `2x^{1−β₀}` of the real `β₀` template. Route:
telescope `φ(t) = t^{2−ρ}/(2−ρ)` (`φ' = t^{1−ρ}`), the unit tangents (`cpow_unit_tangent_bound`)
summed by `sum_rpow_neg_le`, plus the corner and the `(T−1)→x` gap (`norm_ofReal_cpow_seg_le`). -/
theorem sum_cpow_sandwich_rho {ρ : ℂ} (hσ0 : 0 < ρ.re) (hσ1 : ρ.re < 1) {x : ℝ} (hx : 2 ≤ x)
    {T : ℕ} (hT2 : 2 ≤ T) (hTx : (T : ℝ) ≤ x) (hxT : x < (T : ℝ) + 1) :
    ‖(((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ) + ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℂ) ^ (1 - ρ))
        - (x : ℂ) ^ (2 - ρ) / (2 - ρ)‖
      ≤ (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re) := by
  have h2ρne : (2 : ℂ) - ρ ≠ 0 := by
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at h2
    linarith
  have hu : 0 < 1 - ρ.re := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hT2R : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT2
  have hT0 : (0 : ℝ) < (T : ℝ) := by linarith
  have hxpow_nn : (0 : ℝ) ≤ x ^ (1 - ρ.re) := Real.rpow_nonneg hx0.le _
  set σ : ℝ := ρ.re with hσdef
  set n : ℕ := T - 1 with hndef
  have hn1 : 1 ≤ n := by omega
  have hnR : (n : ℝ) = (T : ℝ) - 1 := by rw [hndef, Nat.cast_sub (by omega)]; push_cast; ring
  -- ψ and the tangent errors
  set ψ : ℕ → ℂ := fun k => (k : ℂ) ^ (2 - ρ) / (2 - ρ) with hψdef
  have hψ0 : ψ 0 = 0 := by rw [hψdef]; simp [Complex.zero_cpow h2ρne]
  set e : ℕ → ℂ := fun t => ψ t - ψ (t - 1) - (t : ℂ) ^ (1 - ρ) with hedef
  -- telescoping
  have htel : ∀ k : ℕ, ∑ t ∈ Finset.Icc 1 k, (ψ t - ψ (t - 1)) = ψ k := by
    intro k
    induction k with
    | zero => simp [hψ0]
    | succ j ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), ih, Nat.add_sub_cancel]
      ring
  have hsum_eq : ∑ t ∈ Finset.Icc 1 n, (t : ℂ) ^ (1 - ρ)
      = ψ n - ∑ t ∈ Finset.Icc 1 n, e t := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    rw [show (∑ t ∈ Finset.Icc 1 n, ((t : ℂ) ^ (1 - ρ) + e t))
        = ∑ t ∈ Finset.Icc 1 n, (ψ t - ψ (t - 1)) from
      Finset.sum_congr rfl (fun t _ => by rw [hedef]; ring)]
    exact htel n
  -- bound the tangent-error sum: ‖Σ e‖ ≤ 2 + 4‖1−ρ‖·(T−1)^{1−σ}/(1−σ)
  have hψ1 : ψ 1 = 1 / (2 - ρ) := by simp only [hψdef, Nat.cast_one, Complex.one_cpow]
  have he1 : ‖e 1‖ ≤ 2 := by
    have heval : e 1 = 1 / (2 - ρ) - 1 := by
      have h0 : e 1 = ψ 1 - ψ 0 - ((1 : ℕ) : ℂ) ^ (1 - ρ) := rfl
      rw [h0, hψ1, hψ0, Nat.cast_one, Complex.one_cpow]; ring
    rw [heval]
    have h2ρ1 : (1 : ℝ) ≤ ‖2 - ρ‖ := by
      have hle : (1 : ℝ) ≤ (2 - ρ).re := by rw [Complex.sub_re, Complex.re_ofNat]; linarith
      exact le_trans hle (Complex.re_le_norm _)
    calc ‖(1 : ℂ) / (2 - ρ) - 1‖ ≤ ‖(1 : ℂ) / (2 - ρ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 / ‖2 - ρ‖ + 1 := by rw [norm_div, norm_one]
      _ ≤ 1 / 1 + 1 := by gcongr
      _ = 2 := by norm_num
  have het : ∀ t ∈ (Finset.Icc 1 n).erase 1,
      ‖e t‖ ≤ 4 * ‖1 - ρ‖ * (t : ℝ) ^ (-σ) := by
    intro t ht
    rw [Finset.mem_erase, Finset.mem_Icc] at ht
    obtain ⟨ht1, ht1', _⟩ := ht
    have ht2 : 2 ≤ t := by omega
    have htR0 : (0 : ℝ) < (t : ℝ) := by positivity
    have htang := cpow_unit_tangent_bound hσ0 hσ1 ht2
    rw [← hσdef] at htang
    -- (t−1)^{−σ} ≤ 2·t^{−σ}
    have hmR : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hstep : ((t - 1 : ℕ) : ℝ) ^ (-σ) ≤ 2 * (t : ℝ) ^ (-σ) := by
      have ht2R : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2
      have hhalf : (t : ℝ) / 2 ≤ ((t - 1 : ℕ) : ℝ) := by rw [hmR]; linarith
      have hpos2 : (0 : ℝ) < (t : ℝ) / 2 := by positivity
      have hmono : ((t - 1 : ℕ) : ℝ) ^ (-σ) ≤ ((t : ℝ) / 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hpos2 hhalf (by linarith)
      have hdiv : ((t : ℝ) / 2) ^ (-σ) = (t : ℝ) ^ (-σ) * (2 : ℝ) ^ σ := by
        rw [Real.div_rpow htR0.le (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
      have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
        calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := by norm_num
      calc ((t - 1 : ℕ) : ℝ) ^ (-σ) ≤ ((t : ℝ) / 2) ^ (-σ) := hmono
        _ = (t : ℝ) ^ (-σ) * (2 : ℝ) ^ σ := hdiv
        _ ≤ (t : ℝ) ^ (-σ) * 2 := by
            apply mul_le_mul_of_nonneg_left h2σ (Real.rpow_nonneg htR0.le _)
        _ = 2 * (t : ℝ) ^ (-σ) := by ring
    calc ‖e t‖ ≤ 2 * ‖1 - ρ‖ * ((t - 1 : ℕ) : ℝ) ^ (-σ) := htang
      _ ≤ 2 * ‖1 - ρ‖ * (2 * (t : ℝ) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 4 * ‖1 - ρ‖ * (t : ℝ) ^ (-σ) := by ring
  have hesum : ‖∑ t ∈ Finset.Icc 1 n, e t‖
      ≤ 2 + 4 * ‖1 - ρ‖ * ((n : ℝ) ^ (1 - σ) / (1 - σ)) := by
    have hsplit : ∑ t ∈ Finset.Icc 1 n, e t = e 1 + ∑ t ∈ (Finset.Icc 1 n).erase 1, e t :=
      (Finset.add_sum_erase _ e (Finset.mem_Icc.mpr ⟨le_refl 1, hn1⟩)).symm
    rw [hsplit]
    calc ‖e 1 + ∑ t ∈ (Finset.Icc 1 n).erase 1, e t‖
        ≤ ‖e 1‖ + ‖∑ t ∈ (Finset.Icc 1 n).erase 1, e t‖ := norm_add_le _ _
      _ ≤ 2 + ∑ t ∈ (Finset.Icc 1 n).erase 1, ‖e t‖ :=
          add_le_add he1 (norm_sum_le _ _)
      _ ≤ 2 + ∑ t ∈ (Finset.Icc 1 n).erase 1, 4 * ‖1 - ρ‖ * (t : ℝ) ^ (-σ) := by
          gcongr with t ht; exact het t ht
      _ ≤ 2 + ∑ t ∈ Finset.Icc 1 n, 4 * ‖1 - ρ‖ * (t : ℝ) ^ (-σ) := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset 1 (Finset.Icc 1 n))
            (fun t _ _ => by positivity :
              ∀ t ∈ Finset.Icc 1 n, t ∉ (Finset.Icc 1 n).erase 1 →
                (0 : ℝ) ≤ 4 * ‖1 - ρ‖ * (t : ℝ) ^ (-σ))
          linarith [hsub]
      _ = 2 + 4 * ‖1 - ρ‖ * ∑ t ∈ Finset.Icc 1 n, (t : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
      _ ≤ 2 + 4 * ‖1 - ρ‖ * ((n : ℝ) ^ (1 - σ) / (1 - σ)) := by
          have hsr := sum_rpow_neg_le hσ0.le hσ1 n
          linarith [mul_le_mul_of_nonneg_left hsr (by positivity : (0:ℝ) ≤ 4 * ‖1 - ρ‖)]
  -- ASSEMBLY
  have hnpos : (0 : ℝ) < (n : ℝ) := by rw [hnR]; linarith
  have hnx : (n : ℝ) ≤ x := by rw [hnR]; linarith
  have h2ρnorm : (0 : ℝ) < ‖2 - ρ‖ := norm_pos_iff.mpr h2ρne
  have hexp : ((2 : ℂ) - ρ - 1).re = 1 - σ := by
    have hh : ((2 : ℂ) - ρ - 1).re = 2 - ρ.re - 1 := by
      rw [Complex.sub_re, Complex.sub_re, Complex.re_ofNat, Complex.one_re]
    rw [hh, ← hσdef]; ring
  have h1ρre : (1 - ρ).re = 1 - σ := by rw [Complex.sub_re, Complex.one_re, ← hσdef]
  rw [hsum_eq]
  have hrw : (((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ) + (ψ n - ∑ t ∈ Finset.Icc 1 n, e t))
        - (x : ℂ) ^ (2 - ρ) / (2 - ρ)
      = ((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ)
        + (ψ n - (x : ℂ) ^ (2 - ρ) / (2 - ρ)) - ∑ t ∈ Finset.Icc 1 n, e t := by ring
  rw [hrw]
  -- corner
  have hCorner : ‖((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ)‖ ≤ x ^ (1 - σ) := by
    rw [norm_mul]
    have hnorm1 : ‖(x : ℂ) - (T : ℂ)‖ = x - (T : ℝ) := by
      rw [show (x : ℂ) - (T : ℂ) = (((x - (T : ℝ)) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hnorm2 : ‖(T : ℂ) ^ (1 - ρ)‖ = (T : ℝ) ^ (1 - σ) := by
      rw [show (T : ℂ) = (((T : ℝ)) : ℂ) from by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos hT0, h1ρre]
    rw [hnorm1, hnorm2]
    calc (x - (T : ℝ)) * (T : ℝ) ^ (1 - σ)
        ≤ 1 * x ^ (1 - σ) :=
          mul_le_mul (by linarith) (Real.rpow_le_rpow hT0.le hTx (by linarith))
            (Real.rpow_nonneg hT0.le _) (by norm_num)
      _ = x ^ (1 - σ) := one_mul _
  -- gap
  have hGap : ‖ψ n - (x : ℂ) ^ (2 - ρ) / (2 - ρ)‖ ≤ 2 * x ^ (1 - σ) := by
    have hncast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have heqg : ψ n - (x : ℂ) ^ (2 - ρ) / (2 - ρ)
        = (((n : ℝ) : ℂ) ^ (2 - ρ) - ((x : ℝ) : ℂ) ^ (2 - ρ)) / (2 - ρ) := by
      simp only [hψdef]; rw [hncast]; ring
    have hseg : ‖((x : ℝ) : ℂ) ^ (2 - ρ) - ((n : ℝ) : ℂ) ^ (2 - ρ)‖
        ≤ (‖2 - ρ‖ * x ^ (1 - σ)) * (x - (n : ℝ)) := by
      apply norm_ofReal_cpow_seg_le h2ρne hnpos hnx
      intro w hw1 hw2
      have hw0 : (0 : ℝ) < w := lt_of_lt_of_le hnpos hw1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw0, hexp]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hw0.le hw2 (by linarith)) (norm_nonneg _)
    rw [heqg, norm_div, norm_sub_rev (((n : ℝ) : ℂ) ^ (2 - ρ)) (((x : ℝ) : ℂ) ^ (2 - ρ)),
      div_le_iff₀ h2ρnorm]
    calc ‖((x : ℝ) : ℂ) ^ (2 - ρ) - ((n : ℝ) : ℂ) ^ (2 - ρ)‖
        ≤ (‖2 - ρ‖ * x ^ (1 - σ)) * (x - (n : ℝ)) := hseg
      _ ≤ (‖2 - ρ‖ * x ^ (1 - σ)) * 2 :=
          mul_le_mul_of_nonneg_left (by rw [hnR]; linarith) (by positivity)
      _ = 2 * x ^ (1 - σ) * ‖2 - ρ‖ := by ring
  -- error sum, in x-grade
  have hxge1 : (1 : ℝ) ≤ x ^ (1 - σ) := Real.one_le_rpow (by linarith) (by linarith)
  have hnxpow : (n : ℝ) ^ (1 - σ) ≤ x ^ (1 - σ) :=
    Real.rpow_le_rpow hnpos.le hnx (by linarith)
  have hSe : ‖∑ t ∈ Finset.Icc 1 n, e t‖
      ≤ 2 * x ^ (1 - σ) + 4 * ‖1 - ρ‖ * x ^ (1 - σ) / (1 - σ) := by
    have hstep : (n : ℝ) ^ (1 - σ) / (1 - σ) ≤ x ^ (1 - σ) / (1 - σ) := by
      rw [div_le_div_iff_of_pos_right hu]; exact hnxpow
    have h2x : (2 : ℝ) ≤ 2 * x ^ (1 - σ) := by nlinarith [hxge1]
    have hcoef : (0 : ℝ) ≤ 4 * ‖1 - ρ‖ := by positivity
    calc ‖∑ t ∈ Finset.Icc 1 n, e t‖ ≤ 2 + 4 * ‖1 - ρ‖ * ((n : ℝ) ^ (1 - σ) / (1 - σ)) := hesum
      _ ≤ 2 * x ^ (1 - σ) + 4 * ‖1 - ρ‖ * (x ^ (1 - σ) / (1 - σ)) := by
          linarith [mul_le_mul_of_nonneg_left hstep hcoef, h2x]
      _ = 2 * x ^ (1 - σ) + 4 * ‖1 - ρ‖ * x ^ (1 - σ) / (1 - σ) := by ring
  -- combine
  calc ‖((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ)
          + (ψ n - (x : ℂ) ^ (2 - ρ) / (2 - ρ)) - ∑ t ∈ Finset.Icc 1 n, e t‖
      ≤ ‖((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ)
            + (ψ n - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖ + ‖∑ t ∈ Finset.Icc 1 n, e t‖ :=
        norm_sub_le _ _
    _ ≤ (‖((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ)‖
            + ‖ψ n - (x : ℂ) ^ (2 - ρ) / (2 - ρ)‖) + ‖∑ t ∈ Finset.Icc 1 n, e t‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ (x ^ (1 - σ) + 2 * x ^ (1 - σ))
          + (2 * x ^ (1 - σ) + 4 * ‖1 - ρ‖ * x ^ (1 - σ) / (1 - σ)) :=
        add_le_add (add_le_add hCorner hGap) hSe
    _ = (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re) := by rw [hσdef]; ring

/-! ## §3 — R6-3@ρ : the complex-scale two-sided extraction -/

/-- The heart's per-`t` constant `C_{w,ρ}` (matching `dhAbel_inner_rho`'s output). -/
noncomputable def CwRho (q : ℕ) (Z₀ : ℝ) (ρ : ℂ) : ℝ :=
  12 * (Real.sqrt q * (1 + Real.log q)) / ‖1 - ρ‖ + 2 * (9 + 8 * ‖ρ‖)
    + 2 * (Z₀ + 1 / ‖1 - ρ‖) * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re))
    + 2 * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re))
    + 2 * (3 * (Real.sqrt q * (1 + Real.log q)) * (1 + ‖ρ‖ / ρ.re)) / (1 - ρ.re)

/-- The R6-3@ρ extraction constant `C₂ρ = 3·Cwρ + (18M/‖1−ρ‖)·(5 + 4‖1−ρ‖/(1−σ))`. Carries exactly
ONE power of `L₂/c₀` (via `1/‖1−ρ‖`, `1/(1−σ)`; catch #225) — re-priced on-ray in
`scripts/tbal_ledgers/reprice_rho_r6rho2.py` (PASS at q=3/10³/10⁶). -/
noncomputable def C2Rho (q : ℕ) (Z₀ : ℝ) (ρ : ℂ) : ℝ :=
  3 * CwRho q Z₀ ρ
    + 18 * (Real.sqrt q * (1 + Real.log q)) / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re))

/-- **The real-scale unmollified ρ-detector.** `D₀^ρ(x) = Σ_{s≤⌊x⌋} dhA χ s·s^{−ρ}·(1 − s/x)`
for real `x` (the complex analog of `dhD0`). -/
noncomputable def dhD0rho (χ : DirichletCharacter ℂ q) (ρ : ℂ) (x : ℝ) : ℂ :=
  ∑ s ∈ Finset.Icc 1 ⌊x⌋₊, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ) * ((1 - (s : ℝ) / x : ℝ) : ℂ)

set_option maxHeartbeats 1600000 in
-- Many error/main legs + field_simp/ring over the (1−ρ)(2−ρ) denominators exceed the default.
/-- **R6-3@ρ (`unmoll_extraction_rho`) — the complex-scale two-sided extraction.** For a primitive
real `χ` at a NON-REAL zero `ρ` (`1/2 ≤ Re ρ < 1`, `|Im ρ| ≤ 1`) and real `x ≥ 2`,
`‖D₀^ρ(x) − L(1,χ)·x^{1−ρ}/((1−ρ)(2−ρ))‖ ≤ C₂ρ·x^{1/2−Re ρ}`. The complex analog of
`unmoll_extraction_abs_real`: the complex kernel-Abel (`kernel_abel_sum_rho`) reduces `D₀^ρ` to
`(1/x)[(x−T)A_ρ(T)+Σ_{t<T}A_ρ(t)]`; the per-`t` heart (`dhAbel_inner_rho`) gives the `3Cwρ` error
legs and the complex power-sum sandwich (`sum_cpow_sandwich_rho`, with `‖L(1,χ)‖ ≤ 18M`) gives the
main leg. -/
theorem unmoll_extraction_rho [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hlo : 1 / 2 ≤ ρ.re) (hhi : ρ.re < 1)
    (him : |ρ.im| ≤ 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {x : ℝ} (hx : 2 ≤ x) :
    ‖dhD0rho χ ρ x
        - DirichletCharacter.LFunction χ 1 * (x : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ))‖
      ≤ C2Rho q Z₀ ρ * x ^ (1 / 2 - ρ.re) := by
  set M : ℝ := Real.sqrt q * (1 + Real.log q) with hMdef
  set L₁ : ℂ := DirichletCharacter.LFunction χ 1 with hL1def
  set Cwρ : ℝ := CwRho q Z₀ ρ with hCwρdef
  set T : ℕ := ⌊x⌋₊ with hTdef
  set main : ℂ := L₁ * (x : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)) with hmaindef
  have hσ0 : 0 < ρ.re := by linarith
  have hu : 0 < 1 - ρ.re := by linarith
  have hu2 : 0 < 2 - ρ.re := by linarith
  have hne : χ ≠ 1 := ne_one_of_isPrimitive χ hχ hq
  haveI : Fact (1 < q) := ⟨by omega⟩
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at hhi; simp at hhi
  have hsne : (1 - ρ) ≠ 0 := sub_ne_zero.mpr (fun h => hρ1 h.symm)
  have h2ρne : (2 - ρ) ≠ 0 := by
    intro h; have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re, Complex.re_ofNat] at this; linarith
  have hnpos : 0 < ‖1 - ρ‖ := norm_pos_iff.mpr hsne
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxC0 : (x : ℂ) ≠ 0 := by simp only [ne_eq, Complex.ofReal_eq_zero]; exact hx0.ne'
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast le_trans (by norm_num : (1 : ℕ) ≤ 2) hq)
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hxc : (0 : ℝ) ≤ x ^ (3 / 2 - ρ.re) := Real.rpow_nonneg hx0.le _
  have hT1 : 1 ≤ T := by rw [hTdef, Nat.le_floor_iff hx0.le]; exact_mod_cast hx1
  have hT2 : 2 ≤ T := by rw [hTdef, Nat.le_floor_iff hx0.le]; exact_mod_cast hx
  have hTx : (T : ℝ) ≤ x := by rw [hTdef]; exact Nat.floor_le hx0.le
  have hxT : x < (T : ℝ) + 1 := by rw [hTdef]; exact Nat.lt_floor_add_one x
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
  -- ‖L₁‖ ≤ 18M
  have hL1_le : ‖L₁‖ ≤ 18 * M := by
    have hnorm := LFunction_apply_one_norm_le χ hχ hq
    rw [← hL1def] at hnorm
    have hlogq0 : (0 : ℝ) ≤ 1 + Real.log q := by linarith
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1.4 : ℝ) = Real.sqrt (1.4 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsq14 : (1.4 : ℝ) ≤ Real.sqrt q := le_trans hs2 (Real.sqrt_le_sqrt hq2)
    have h5e : 5 * Real.exp 1 ≤ 18 * Real.sqrt q := by nlinarith [Real.exp_one_lt_d9, hsq14]
    rw [hMdef]
    nlinarith [hnorm, mul_le_mul_of_nonneg_right h5e hlogq0]
  -- R6-1@ρ : the complex kernel-Abel identity
  have hAbel : dhD0rho χ ρ x = (1 / (x : ℂ)) * (((x : ℂ) - (T : ℂ))
        * (∑ s ∈ Finset.Icc 1 T, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
        + ∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t,
            (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ)) := by
    rw [dhD0rho, ← hTdef]
    exact kernel_abel_sum_rho (fun s => (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ)) hx1
  set ST : ℂ := ∑ s ∈ Finset.Icc 1 T, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ) with hSTdef
  set SP : ℂ := ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℂ) ^ (1 - ρ) with hSPdef
  set S : ℂ := ((x : ℂ) - (T : ℂ)) * (T : ℂ) ^ (1 - ρ) + SP with hSdef
  set R : ℂ := ((x : ℂ) - (T : ℂ)) * ST
      + ∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t,
          (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ) with hRdef
  -- per-`t` heart bound
  have hR2 : ∀ t : ℕ, 1 ≤ t →
      ‖(∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ)) - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)‖
        ≤ Cwρ * (t : ℝ) ^ (1 / 2 - ρ.re) := by
    intro t ht
    have h := dhAbel_inner_rho χ hχ hsq hq hzero hlo hhi him hZ ht
    rw [← hL1def] at h
    rw [hCwρdef]; simp only [CwRho]
    exact h
  -- the exact main/error split of `R − x·main`
  have hxx : (x : ℂ) * (x : ℂ) ^ (1 - ρ) = (x : ℂ) ^ (2 - ρ) := by
    nth_rewrite 1 [← Complex.cpow_one (x : ℂ)]
    rw [← Complex.cpow_add _ _ hxC0]; congr 1; ring
  have hxmain : (x : ℂ) * main = L₁ * (x : ℂ) ^ (2 - ρ) / ((1 - ρ) * (2 - ρ)) := by
    rw [hmaindef, show (x : ℂ) * (L₁ * (x : ℂ) ^ (1 - ρ) / ((1 - ρ) * (2 - ρ)))
      = L₁ * ((x : ℂ) * (x : ℂ) ^ (1 - ρ)) / ((1 - ρ) * (2 - ρ)) by ring, hxx]
  have hRsplit : R - (x : ℂ) * main
      = (L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))
        + (((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
           + ∑ t ∈ Finset.Icc 1 (T - 1),
               ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                 - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))) := by
    have hEsum : (∑ t ∈ Finset.Icc 1 (T - 1),
          ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
            - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)))
        = (∑ t ∈ Finset.Icc 1 (T - 1), ∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
          - (L₁ / (1 - ρ)) * SP := by
      rw [Finset.sum_sub_distrib]; congr 1
      rw [hSPdef, Finset.mul_sum]; exact Finset.sum_congr rfl (fun t _ => by ring)
    rw [hRdef, hxmain, hEsum, hSdef]; field_simp; ring
  -- bound the main defect via the sandwich
  have hSbound := sum_cpow_sandwich_rho hσ0 hhi hx hT2 hTx hxT
  rw [← hSPdef] at hSbound
  have hSbound' : ‖S - (x : ℂ) ^ (2 - ρ) / (2 - ρ)‖
      ≤ (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re) := by
    rw [hSdef]; exact hSbound
  have hBmain : ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
      ≤ (‖L₁‖ / ‖1 - ρ‖) * ((5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re)) := by
    rw [norm_mul, norm_div]
    exact mul_le_mul_of_nonneg_left hSbound' (by positivity)
  -- bound the error legs `≤ 3·Cwρ·x^{3/2−ρ.re}`
  have hCwρnn : 0 ≤ Cwρ := by
    have := hR2 1 (le_refl 1)
    exact le_trans (norm_nonneg _) (le_trans this (le_of_eq (by
      rw [Nat.cast_one, Real.one_rpow, mul_one])))
  have hBerr : ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
        + ∑ t ∈ Finset.Icc 1 (T - 1),
            ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
              - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖
      ≤ 3 * Cwρ * x ^ (3 / 2 - ρ.re) := by
    have hxTnorm : ‖(x : ℂ) - (T : ℂ)‖ ≤ 1 := by
      rw [show (x : ℂ) - (T : ℂ) = (((x - (T : ℝ)) : ℝ) : ℂ) from by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    have hterm1 : ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))‖
        ≤ Cwρ * x ^ (3 / 2 - ρ.re) := by
      rw [norm_mul]
      have hTle1 : (T : ℝ) ^ (1 / 2 - ρ.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT1) (by linarith)
      have h1x : (1 : ℝ) ≤ x ^ (3 / 2 - ρ.re) := Real.one_le_rpow hx1 (by linarith)
      calc ‖(x : ℂ) - (T : ℂ)‖ * ‖ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ)‖
          ≤ 1 * (Cwρ * (T : ℝ) ^ (1 / 2 - ρ.re)) :=
            mul_le_mul hxTnorm (hR2 T hT1) (norm_nonneg _) (by norm_num)
        _ ≤ Cwρ * x ^ (3 / 2 - ρ.re) := by
            rw [one_mul]
            calc Cwρ * (T : ℝ) ^ (1 / 2 - ρ.re) ≤ Cwρ * 1 :=
                  mul_le_mul_of_nonneg_left hTle1 hCwρnn
              _ ≤ Cwρ * x ^ (3 / 2 - ρ.re) := by rw [mul_one]; nlinarith [hCwρnn, h1x]
    have hterm2 : ‖∑ t ∈ Finset.Icc 1 (T - 1),
          ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
            - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖ ≤ 2 * Cwρ * x ^ (3 / 2 - ρ.re) := by
      calc ‖∑ t ∈ Finset.Icc 1 (T - 1),
              ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖
          ≤ ∑ t ∈ Finset.Icc 1 (T - 1), Cwρ * (t : ℝ) ^ (1 / 2 - ρ.re) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun t ht => ?_))
            rw [Finset.mem_Icc] at ht; exact hR2 t (by omega)
        _ = Cwρ * ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 / 2 - ρ.re) := by rw [Finset.mul_sum]
        _ ≤ Cwρ * (2 * x ^ (3 / 2 - ρ.re)) := by
            apply mul_le_mul_of_nonneg_left _ hCwρnn
            have h := sum_rpow_neg_le (β := ρ.re - 1 / 2) (by linarith)
              (by linarith) (T - 1)
            rw [show -(ρ.re - 1 / 2) = 1 / 2 - ρ.re by ring,
              show 1 - (ρ.re - 1 / 2) = 3 / 2 - ρ.re by ring] at h
            have hym1 : ((T - 1 : ℕ) : ℝ) ≤ x := le_trans (by
              rw [Nat.cast_sub hT1]; push_cast; linarith) hTx
            have hbase : ((T - 1 : ℕ) : ℝ) ^ (3 / 2 - ρ.re) ≤ x ^ (3 / 2 - ρ.re) :=
              Real.rpow_le_rpow (by positivity) hym1 (by linarith)
            have h32 : (0 : ℝ) < 3 / 2 - ρ.re := by linarith
            calc ∑ t ∈ Finset.Icc 1 (T - 1), (t : ℝ) ^ (1 / 2 - ρ.re)
                ≤ ((T - 1 : ℕ) : ℝ) ^ (3 / 2 - ρ.re) / (3 / 2 - ρ.re) := h
              _ ≤ x ^ (3 / 2 - ρ.re) / (3 / 2 - ρ.re) := (div_le_div_iff_of_pos_right h32).mpr hbase
              _ ≤ 2 * x ^ (3 / 2 - ρ.re) := by rw [div_le_iff₀ h32]; nlinarith [hxc]
        _ = 2 * Cwρ * x ^ (3 / 2 - ρ.re) := by ring
    calc ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
            + ∑ t ∈ Finset.Icc 1 (T - 1),
                ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                  - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖
        ≤ ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))‖
          + ‖∑ t ∈ Finset.Icc 1 (T - 1),
              ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖ := norm_add_le _ _
      _ ≤ Cwρ * x ^ (3 / 2 - ρ.re) + 2 * Cwρ * x ^ (3 / 2 - ρ.re) := add_le_add hterm1 hterm2
      _ = 3 * Cwρ * x ^ (3 / 2 - ρ.re) := by ring
  -- combine : ‖R − x·main‖ ≤ C₂ρ·x^{3/2−ρ.re}
  have hBmain' : ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
      ≤ 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re) := by
    have hx13 : x ^ (1 - ρ.re) ≤ x ^ (3 / 2 - ρ.re) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hKnn : (0 : ℝ) ≤ 5 + 4 * ‖1 - ρ‖ / (1 - ρ.re) := by
      have : (0:ℝ) ≤ 4 * ‖1 - ρ‖ / (1 - ρ.re) := by positivity
      linarith
    calc ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
        ≤ (‖L₁‖ / ‖1 - ρ‖) * ((5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (1 - ρ.re)) := hBmain
      _ ≤ (18 * M / ‖1 - ρ‖) * ((5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re)) := by
          apply mul_le_mul
          · exact (div_le_div_iff_of_pos_right hnpos).mpr hL1_le
          · exact mul_le_mul_of_nonneg_left hx13 hKnn
          · positivity
          · positivity
      _ = 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re) := by ring
  have hRbound : ‖R - (x : ℂ) * main‖ ≤ C2Rho q Z₀ ρ * x ^ (3 / 2 - ρ.re) := by
    rw [hRsplit]
    have hcomb : C2Rho q Z₀ ρ * x ^ (3 / 2 - ρ.re)
        = 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re)
          + 3 * Cwρ * x ^ (3 / 2 - ρ.re) := by
      rw [C2Rho, ← hMdef, ← hCwρdef]; ring
    rw [hcomb]
    calc ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))
            + (((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
               + ∑ t ∈ Finset.Icc 1 (T - 1),
                   ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                     - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ)))‖
        ≤ ‖(L₁ / (1 - ρ)) * (S - (x : ℂ) ^ (2 - ρ) / (2 - ρ))‖
          + ‖((x : ℂ) - (T : ℂ)) * (ST - L₁ * (T : ℂ) ^ (1 - ρ) / (1 - ρ))
             + ∑ t ∈ Finset.Icc 1 (T - 1),
                 ((∑ s ∈ Finset.Icc 1 t, (dhA χ s : ℂ) * (s : ℂ) ^ (-ρ))
                   - L₁ * (t : ℂ) ^ (1 - ρ) / (1 - ρ))‖ := norm_add_le _ _
      _ ≤ 18 * M / ‖1 - ρ‖ * (5 + 4 * ‖1 - ρ‖ / (1 - ρ.re)) * x ^ (3 / 2 - ρ.re)
            + 3 * Cwρ * x ^ (3 / 2 - ρ.re) := add_le_add hBmain' hBerr
  -- divide by x
  have heq : (1 / (x : ℂ)) * R - main = (R - (x : ℂ) * main) / (x : ℂ) := by field_simp
  have hfinal : ‖dhD0rho χ ρ x - main‖ = ‖R - (x : ℂ) * main‖ / x := by
    rw [hAbel, heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
  rw [hfinal, div_le_iff₀ hx0]
  have hxpow : x ^ (1 / 2 - ρ.re) * x = x ^ (3 / 2 - ρ.re) := by
    nth_rewrite 2 [← Real.rpow_one x]; rw [← Real.rpow_add hx0]; congr 1; ring
  calc ‖R - (x : ℂ) * main‖ ≤ C2Rho q Z₀ ρ * x ^ (3 / 2 - ρ.re) := hRbound
    _ = C2Rho q Z₀ ρ * x ^ (1 / 2 - ρ.re) * x := by rw [← hxpow]; ring

end Salt.SW

end
