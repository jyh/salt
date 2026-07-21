/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MVCore2
import Salt.MR.MVHilbert
import Salt.LS.Gallagher

/-!
# MR track, P-lane: large-value machinery (Lemmas 7, 8, 9, 11)

Source pins: MR arXiv v4 `1501.04585v4` §2.3–2.4 (large- and mean-value machinery,
Halász for integers/primes); MRT v3 `1503.05121v3` for the ζ-region inputs.

Frozen shapes (S8 MR-CORE freeze v2; `≪` is qualitative, an explicit constant is
carried):

* **L7 `wellspaced_l2`** (Lemma 7, [20, Thm 9.4]): for a well-spaced set `𝒯`
  (pairwise `|t−r| ≥ 1`) inside `[−T,T]`,
  `Σ_{t∈𝒯} ‖A(it)‖² ≪ (T+N)·log(2N)·Σ‖aₙ‖²`.
  Route: `gallagher_pointwise` at each point (δ=1) + a line-disjointness helper +
  the unconditional `dirichlet_poly_l2_mvt_final` on **both** `∫‖F‖²` and `∫‖F′‖²`
  (the derivative folds `log n` into the coefficient).

* **L8 `large_value_count`** (Lemma 8, θ-free): `P(s) = Σ_{P≤p≤2P} a_p/p^s`,
  `|a_p| ≤ 1`, `𝒯` well-spaced with `|P(1+it)| ≥ V⁻¹`. Then
  `|𝒯| ≪ T^{2 log V / log P}·V²·exp(2 (log T/log P) loglog T)`.

* **L9 `halasz_integers`** (Lemma 9, [20, Thm 9.6]):
  `Σ_{t∈𝒯} ‖A(it)‖² ≪ (N + |𝒯|·√T)·log(2T)·Σ‖aₙ‖²`.

* **L11 `halasz_primes_pow`** (Lemma 11, θ=3/4 override): prime-supported
  `P(s) = Σ_{P≤p≤2P} a_p p^{−s}`, `𝒯` well-spaced ⊂ `[−T,T]`.
  `Σ_{t∈𝒯} ‖P(it)‖² ≪ (P + |𝒯|·P·exp(−log P/((log T)^{3/4}(loglog T)⁴))·(log T)²)·
  Σ‖a_p‖²/log P`. Contour at `σ = 1 − c/((log T)^{3/4}(loglog T)⁴)`.

`l2_duality` (MR L10, landed in `MVHilbert.lean`) feeds L9/L11.
-/

namespace Salt.MR

open scoped BigOperators
open MeasureTheory intervalIntegral Complex Set

/-- **Well-spaced set of real ordinates.** A finite `𝒯 ⊆ ℝ` is well-spaced when
distinct points are at least `1` apart. -/
def WellSpaced (𝒯 : Finset ℝ) : Prop :=
  ∀ t ∈ 𝒯, ∀ r ∈ 𝒯, t ≠ r → 1 ≤ |t - r|

/-- The frequency-twisted coefficient sequence `n ↦ aₙ · i · log n`. Differentiating
`dpoly N a` in `t` folds the frequency `log n` into the coefficient, giving
`dpoly N (dtwist a)`. -/
noncomputable def dtwist (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * Complex.I * (Real.log n : ℂ)

/-- Termwise derivative: `d/dt [aₙ · exp(i·t·log n)] = (aₙ·i·log n) · exp(i·t·log n)`. -/
lemma hasDerivAt_dpoly_term (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
      (dtwist a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))) t := by
  have hb : HasDerivAt (fun t : ℝ => ((t : ℂ))) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hg : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ) * (Real.log n : ℂ))
      (Complex.I * 1 * (Real.log n : ℂ)) t := (hb.const_mul Complex.I).mul_const _
  have hexp := hg.cexp
  have hfull := hexp.const_mul (a n)
  have hval : dtwist a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))
      = a n * (Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))
          * (Complex.I * 1 * (Real.log n : ℂ))) := by
    unfold dtwist; ring
  rw [hval]
  exact hfull

/-- **L2.1 (HasDerivAt form).** `dpoly N a` is differentiable in `t` with derivative
the twisted polynomial `dpoly N (dtwist a)`. -/
theorem hasDerivAt_dpoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (dpoly N a) (dpoly N (dtwist a) t) t := by
  have h := HasDerivAt.sum (u := Finset.Icc 1 N)
    (A := fun n => fun t : ℝ => a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
    (A' := fun n => dtwist a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
    (fun n _ => hasDerivAt_dpoly_term a n t)
  have hf : (∑ n ∈ Finset.Icc 1 N,
        fun t : ℝ => a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)))
      = dpoly N a := by
    funext s; rw [Finset.sum_apply]; rfl
  rw [hf] at h
  exact h

/-- **L2.1 (deriv form).** `deriv (dpoly N a) t = dpoly N (dtwist a) t`. -/
theorem deriv_dpoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    deriv (dpoly N a) t = dpoly N (dtwist a) t :=
  (hasDerivAt_dpoly N a t).deriv

/-- Each `dpoly` summand is globally `C¹`. -/
lemma contDiff_dpoly_term (a : ℕ → ℂ) (n : ℕ) :
    ContDiff ℝ 1 (fun t : ℝ => a n * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
  have hof : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have harg : ContDiff ℝ 1 (fun t : ℝ => Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
    exact (contDiff_const.mul hof).mul contDiff_const
  exact contDiff_const.mul (Complex.contDiff_exp.comp harg)

/-- **L2.1 (ContDiff form).** `dpoly N a` is globally `C¹` — the hypothesis
`gallagher_pointwise` consumes. -/
theorem contDiff_dpoly (N : ℕ) (a : ℕ → ℂ) : ContDiff ℝ 1 (dpoly N a) := by
  unfold dpoly
  exact ContDiff.sum (fun n _ => contDiff_dpoly_term a n)

/-- `‖dtwist a n‖² = (log n)²·‖aₙ‖²`. -/
lemma norm_dtwist_sq (a : ℕ → ℂ) (n : ℕ) :
    ‖dtwist a n‖ ^ 2 = (Real.log n) ^ 2 * ‖a n‖ ^ 2 := by
  unfold dtwist
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [mul_pow, sq_abs]
  ring

/-- `deriv (dpoly N a)` is continuous (it is again a `dpoly`). -/
lemma continuous_deriv_dpoly (N : ℕ) (a : ℕ → ℂ) : Continuous (deriv (dpoly N a)) := by
  have h : deriv (dpoly N a) = dpoly N (dtwist a) := funext (fun t => deriv_dpoly N a t)
  rw [h]; exact continuous_dpoly N (dtwist a)

/-- The coefficient sum of the twisted polynomial is controlled by `(log N)²` times
that of the original: `Σ ‖dtwist a n‖² ≤ (log N)²·Σ ‖aₙ‖²` over `[1,N]`. -/
lemma sum_dtwist_sq_le (N : ℕ) (a : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, ‖dtwist a n‖ ^ 2
      ≤ (Real.log N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [norm_dtwist_sq]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hn' := Finset.mem_Icc.mp hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn'.1)
  have hlognN : Real.log n ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hn'.1)
      (by exact_mod_cast hn'.2)
  exact pow_le_pow_left₀ hlogn hlognN 2

/-- **Derivative mean-value bound.** `∫_{-c}^{c} ‖(dpoly N a)′‖² ≤ (2c+20N)·(log N)²·Σ‖aₙ‖²`:
the derivative is `dpoly N (dtwist a)`, and `‖dtwist a n‖ = |log n|·‖aₙ‖ ≤ (log N)‖aₙ‖`. -/
lemma integral_deriv_dpoly_sq_le (N : ℕ) (a : ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ t in (-c)..c, ‖deriv (dpoly N a) t‖ ^ 2)
      ≤ (2 * c + 20 * (N : ℝ)) * ((Real.log N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
  have hrw : (∫ t in (-c)..c, ‖deriv (dpoly N a) t‖ ^ 2)
      = ∫ t in (-c)..c, ‖dpoly N (dtwist a) t‖ ^ 2 := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [deriv_dpoly]
  rw [hrw]
  refine le_trans (dirichlet_poly_l2_mvt_final N (dtwist a) c) ?_
  refine mul_le_mul_of_nonneg_left (sum_dtwist_sq_le N a) ?_
  positivity

/-- Weighted AM–GM: `2xy ≤ L·x² + L⁻¹·y²` for `L > 0` (all real `x, y`). The
`L = log(2N)` balancing is exactly what turns `(log N)²` from the derivative moment
into a single `log(2N)` in Lemma 7. -/
lemma two_mul_le_amgm {x y L : ℝ} (hL : 0 < L) :
    2 * (x * y) ≤ L * x ^ 2 + L⁻¹ * y ^ 2 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hkey : L⁻¹ * (L * x - y) ^ 2 = L * x ^ 2 + L⁻¹ * y ^ 2 - 2 * (x * y) := by
    field_simp; ring
  linarith [mul_nonneg (inv_nonneg.mpr hL.le) (sq_nonneg (L * x - y)), hkey]

/-- **Line-disjointness helper** ([B, in-file], the L7 keystone step). For a
nonnegative continuous `g`, a well-spaced `𝒯`, and unit intervals `(t−½, t+½]`
all contained in `(A, B]`, the sum of the interval integrals is bounded by the
single integral over `[A, B]`: the width-1 windows are pairwise disjoint because
`𝒯` is `1`-separated. -/
lemma sum_intervalIntegral_le (g : ℝ → ℝ) (hg_cont : Continuous g)
    (hg_nonneg : ∀ s, 0 ≤ g s) (𝒯 : Finset ℝ) (A B : ℝ) (hAB : A ≤ B)
    (hws : WellSpaced 𝒯)
    (hsub : ∀ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2) ⊆ Set.Ioc A B) :
    ∑ t ∈ 𝒯, (∫ s in (t - 1 / 2)..(t + 1 / 2), g s) ≤ ∫ s in A..B, g s := by
  classical
  -- disjointness of the width-1 windows indexed by the subtype of `𝒯`
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun x : {t // t ∈ 𝒯} => Set.Ioc (x.val - 1 / 2) (x.val + 1 / 2))) := by
    intro x y hxy
    rw [Function.onFun, Set.disjoint_left]
    intro z hzx hzy
    have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    have hge : (1 : ℝ) ≤ |x.val - y.val| := hws x.val x.property y.val y.property hne
    have hlt : |x.val - y.val| < 1 := by
      rw [abs_lt]
      exact ⟨by have := hzy.1; have := hzx.2; linarith,
             by have := hzx.1; have := hzy.2; linarith⟩
    linarith
  have hsub' : ∀ x : {t // t ∈ 𝒯},
      Set.Ioc (x.val - 1 / 2) (x.val + 1 / 2) ⊆ Set.Ioc A B :=
    fun x => hsub x.val x.property
  have hint_win : IntegrableOn g (Set.Ioc A B) := hg_cont.integrableOn_Ioc
  have hint_union : IntegrableOn g
      (⋃ x : {t // t ∈ 𝒯}, Set.Ioc (x.val - 1 / 2) (x.val + 1 / 2)) :=
    hint_win.mono_set (Set.iUnion_subset hsub')
  rw [← Finset.sum_coe_sort 𝒯 (fun t => ∫ s in (t - 1 / 2)..(t + 1 / 2), g s)]
  calc ∑ x : {t // t ∈ 𝒯}, ∫ s in (x.val - 1 / 2)..(x.val + 1 / 2), g s
      = ∑ x : {t // t ∈ 𝒯}, ∫ s in Set.Ioc (x.val - 1 / 2) (x.val + 1 / 2), g s := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        exact intervalIntegral.integral_of_le (by linarith)
    _ = ∫ s in ⋃ x : {t // t ∈ 𝒯}, Set.Ioc (x.val - 1 / 2) (x.val + 1 / 2), g s := by
        rw [MeasureTheory.integral_iUnion (fun x => measurableSet_Ioc) hdisj hint_union,
          tsum_fintype]
    _ ≤ ∫ s in Set.Ioc A B, g s := by
        refine setIntegral_mono_set hint_win ?_ (Set.iUnion_subset hsub').eventuallyLE
        exact Filter.Eventually.of_forall (fun s => hg_nonneg s)
    _ = ∫ s in A..B, g s := (intervalIntegral.integral_of_le hAB).symm

/-- **Trivial well-spaced count.** A `1`-separated `𝒯 ⊆ [−T, T]` has at most `2T+1`
points: the unit windows `(t−½, t+½]` are pairwise disjoint (each of measure `1`) and
all lie in `(−T−½, T+½]` (of measure `2T+1`). This is the count Lemma 8 amplifies. -/
lemma wellspaced_card_le (𝒯 : Finset ℝ) (T : ℝ) (hT : 0 ≤ T) (hws : WellSpaced 𝒯)
    (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) : (𝒯.card : ℝ) ≤ 2 * T + 1 := by
  classical
  have hdisj : (↑𝒯 : Set ℝ).PairwiseDisjoint
      (fun t => Set.Ioc (t - 1 / 2) (t + 1 / 2)) := by
    intro t ht r hr htr
    simp only [Function.onFun, Set.disjoint_left]
    intro z hzt hzr
    have hge : (1 : ℝ) ≤ |t - r| := hws t ht r hr htr
    have hlt : |t - r| < 1 := by
      rw [abs_lt]
      exact ⟨by have := hzr.1; have := hzt.2; linarith,
             by have := hzt.1; have := hzr.2; linarith⟩
    linarith
  have hmeas : volume (⋃ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2))
      = ∑ t ∈ 𝒯, volume (Set.Ioc (t - 1 / 2) (t + 1 / 2)) :=
    MeasureTheory.measure_biUnion_finset hdisj (fun t _ => measurableSet_Ioc)
  have hval : ∀ t : ℝ, volume (Set.Ioc (t - 1 / 2) (t + 1 / 2)) = 1 := by
    intro t; rw [Real.volume_Ioc]; norm_num
  have hsum : ∑ t ∈ 𝒯, volume (Set.Ioc (t - 1 / 2) (t + 1 / 2)) = (𝒯.card : ENNReal) := by
    simp only [hval, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub_union : (⋃ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2))
      ⊆ Set.Ioc (-T - 1 / 2) (T + 1 / 2) := by
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨t, ht, hzt⟩ := hz
    have h := Set.mem_Icc.mp (hsub t ht)
    exact ⟨by have := hzt.1; linarith [h.1], by have := hzt.2; linarith [h.2]⟩
  have hle : (𝒯.card : ENNReal) ≤ ENNReal.ofReal (2 * T + 1) := by
    rw [← hsum, ← hmeas]
    calc volume (⋃ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2))
        ≤ volume (Set.Ioc (-T - 1 / 2) (T + 1 / 2)) := measure_mono hsub_union
      _ = ENNReal.ofReal (2 * T + 1) := by rw [Real.volume_Ioc]; congr 1; ring
  have hmono := ENNReal.toReal_mono (by simp : ENNReal.ofReal (2 * T + 1) ≠ ⊤) hle
  rwa [ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by linarith)] at hmono

/-- **L7 — well-spaced L² mean value (Lemma 7, [20, Thm 9.4]).** For a well-spaced
`𝒯 ⊆ [−T, T]`,
`Σ_{t∈𝒯} ‖A(it)‖² ≤ 84·(T+N)·log(2N)·Σ ‖aₙ‖²`.
Route: Gallagher pointwise (δ=1) at each `t₀`, sum via line-disjointness of the unit
windows, then the unconditional `(2T+20N)` mean value on `∫‖F‖²` and `∫‖F′‖²`; the
weighted AM–GM with `L = log(2N)` collapses the `(log N)²` derivative moment to a
single `log(2N)`. The constant `84` is inessential (`≪`). -/
theorem wellspaced_l2 (N : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 0 ≤ T) (𝒯 : Finset ℝ)
    (hws : WellSpaced 𝒯) (hsub𝒯 : ∀ t ∈ 𝒯, t ∈ Set.Icc (-T) T) :
    ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ 84 * (T + (N : ℝ)) * Real.log (2 * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have hz : ∀ t : ℝ, dpoly 0 a t = 0 := by
      intro t; rw [dpoly, Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    have hrhs : (∑ n ∈ Finset.Icc 1 0, ‖a n‖ ^ 2) = 0 := by
      rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    rw [hrhs, mul_zero]
    simp [hz]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
  set S := ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun n _ => by positivity)
  set LL := Real.log (2 * (N : ℝ)) with hLLdef
  set LN := Real.log (N : ℝ) with hLNdef
  have hLLpos : 0 < LL := Real.log_pos (by linarith)
  have hLLne : LL ≠ 0 := ne_of_gt hLLpos
  have hLNnn : 0 ≤ LN := Real.log_nonneg hN1
  have hLNLL : LN ≤ LL := Real.log_le_log (by linarith) (by linarith)
  have hLLhalf : (1 : ℝ) / 2 ≤ LL := by
    have hlog2 : Real.log 2 ≤ LL := Real.log_le_log (by norm_num) (by linarith)
    linarith [Real.log_two_gt_d9]
  have hT'0 : (0 : ℝ) ≤ T + 1 / 2 := by linarith
  have hsubwin : ∀ t ∈ 𝒯,
      Set.Ioc (t - 1 / 2) (t + 1 / 2) ⊆ Set.Ioc (-(T + 1 / 2)) (T + 1 / 2) := by
    intro t ht
    have h := Set.mem_Icc.mp (hsub𝒯 t ht)
    exact Set.Ioc_subset_Ioc (by linarith [h.1]) (by linarith [h.2])
  -- Gallagher pointwise (δ = 1) at each point of 𝒯
  have hgal : ∀ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ (∫ s in (t - 1 / 2)..(t + 1 / 2), ‖dpoly N a s‖ ^ 2)
        + 2 * ∫ s in (t - 1 / 2)..(t + 1 / 2), ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖ := by
    intro t _
    have hg := Salt.LS.gallagher_pointwise (contDiff_dpoly N a)
      (show (0 : ℝ) < 1 from one_pos) t
    simpa only [inv_one, one_mul] using hg
  have hsum1 : ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ (∑ t ∈ 𝒯, ∫ s in (t - 1 / 2)..(t + 1 / 2), ‖dpoly N a s‖ ^ 2)
        + 2 * ∑ t ∈ 𝒯, ∫ s in (t - 1 / 2)..(t + 1 / 2),
            ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖ := by
    have hle := Finset.sum_le_sum (fun t ht => hgal t ht)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
    exact hle
  -- line-disjointness on both sums
  have hA : (∑ t ∈ 𝒯, ∫ s in (t - 1 / 2)..(t + 1 / 2), ‖dpoly N a s‖ ^ 2)
      ≤ ∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2 :=
    sum_intervalIntegral_le (fun s => ‖dpoly N a s‖ ^ 2)
      ((continuous_dpoly N a).norm.pow 2) (fun s => sq_nonneg _) 𝒯 _ _ (by linarith) hws hsubwin
  have hB0 : (∑ t ∈ 𝒯, ∫ s in (t - 1 / 2)..(t + 1 / 2),
        ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖)
      ≤ ∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖ :=
    sum_intervalIntegral_le (fun s => ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖)
      ((continuous_dpoly N a).norm.mul (continuous_deriv_dpoly N a).norm)
      (fun s => mul_nonneg (norm_nonneg _) (norm_nonneg _)) 𝒯 _ _ (by linarith) hws hsubwin
  -- integrated AM-GM on the cross term
  have hcF := continuous_dpoly N a
  have hcF' := continuous_deriv_dpoly N a
  have hi_FF' : IntervalIntegrable
      (fun s => 2 * (‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖)) MeasureTheory.volume
      (-(T + 1 / 2)) (T + 1 / 2) :=
    (continuous_const.mul (hcF.norm.mul hcF'.norm)).intervalIntegrable _ _
  have hi_amgm : IntervalIntegrable
      (fun s => LL * ‖dpoly N a s‖ ^ 2 + LL⁻¹ * ‖deriv (dpoly N a) s‖ ^ 2)
      MeasureTheory.volume (-(T + 1 / 2)) (T + 1 / 2) :=
    ((continuous_const.mul (hcF.norm.pow 2)).add
      (continuous_const.mul (hcF'.norm.pow 2))).intervalIntegrable _ _
  have hi_F2 : IntervalIntegrable (fun s => ‖dpoly N a s‖ ^ 2) MeasureTheory.volume
      (-(T + 1 / 2)) (T + 1 / 2) := (hcF.norm.pow 2).intervalIntegrable _ _
  have hi_F'2 : IntervalIntegrable (fun s => ‖deriv (dpoly N a) s‖ ^ 2) MeasureTheory.volume
      (-(T + 1 / 2)) (T + 1 / 2) := (hcF'.norm.pow 2).intervalIntegrable _ _
  have hCross : 2 * (∫ s in (-(T + 1 / 2))..(T + 1 / 2),
        ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖)
      ≤ LL * (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2)
        + LL⁻¹ * ∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpoly N a) s‖ ^ 2 := by
    have heq : (∫ s in (-(T + 1 / 2))..(T + 1 / 2),
          LL * ‖dpoly N a s‖ ^ 2 + LL⁻¹ * ‖deriv (dpoly N a) s‖ ^ 2)
        = LL * (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2)
          + LL⁻¹ * ∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpoly N a) s‖ ^ 2 := by
      rw [intervalIntegral.integral_add (hi_F2.const_mul LL) (hi_F'2.const_mul LL⁻¹),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hL2 : (∫ s in (-(T + 1 / 2))..(T + 1 / 2),
          2 * (‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖))
        = 2 * ∫ s in (-(T + 1 / 2))..(T + 1 / 2),
            ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖ := by
      rw [intervalIntegral.integral_const_mul]
    rw [← heq, ← hL2]
    exact intervalIntegral.integral_mono_on (by linarith) hi_FF' hi_amgm
      (fun s _ => two_mul_le_amgm hLLpos)
  -- mean-value bounds
  set P := 2 * (T + 1 / 2) + 20 * (N : ℝ) with hPdef
  have hP0 : (0 : ℝ) ≤ P := by rw [hPdef]; nlinarith [hT, Nat.cast_nonneg (α := ℝ) N]
  have hI2 : (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2) ≤ P * S :=
    dirichlet_poly_l2_mvt_final N a (T + 1 / 2)
  have hJ2 : (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpoly N a) s‖ ^ 2)
      ≤ P * (LN ^ 2 * S) := integral_deriv_dpoly_sq_le N a hT'0
  have hPS0 : (0 : ℝ) ≤ P * S := mul_nonneg hP0 hS0
  have hLLinvLN : LL⁻¹ * LN ^ 2 ≤ LL := by
    have hsq : LN ^ 2 ≤ LL ^ 2 := by nlinarith [hLNnn, hLNLL]
    have h1 : LL⁻¹ * LN ^ 2 ≤ LL⁻¹ * LL ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hLLpos.le)
    have h2 : LL⁻¹ * LL ^ 2 = LL := by field_simp
    linarith [h1, h2]
  have hLLinvJ : LL⁻¹ * (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpoly N a) s‖ ^ 2)
      ≤ LL * (P * S) := by
    calc LL⁻¹ * (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖deriv (dpoly N a) s‖ ^ 2)
        ≤ LL⁻¹ * (P * (LN ^ 2 * S)) :=
          mul_le_mul_of_nonneg_left hJ2 (inv_nonneg.mpr hLLpos.le)
      _ = (LL⁻¹ * LN ^ 2) * (P * S) := by ring
      _ ≤ LL * (P * S) := mul_le_mul_of_nonneg_right hLLinvLN hPS0
  -- assemble
  calc ∑ t ∈ 𝒯, ‖dpoly N a t‖ ^ 2
      ≤ (∑ t ∈ 𝒯, ∫ s in (t - 1 / 2)..(t + 1 / 2), ‖dpoly N a s‖ ^ 2)
        + 2 * ∑ t ∈ 𝒯, ∫ s in (t - 1 / 2)..(t + 1 / 2),
            ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖ := hsum1
    _ ≤ (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2)
        + 2 * (∫ s in (-(T + 1 / 2))..(T + 1 / 2),
            ‖dpoly N a s‖ * ‖deriv (dpoly N a) s‖) := by
          have hb := mul_le_mul_of_nonneg_left hB0 (by norm_num : (0 : ℝ) ≤ 2)
          linarith [hA, hb]
    _ ≤ (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2)
        + (LL * (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2)
          + LL⁻¹ * ∫ s in (-(T + 1 / 2))..(T + 1 / 2),
              ‖deriv (dpoly N a) s‖ ^ 2) := by linarith [hCross]
    _ ≤ P * S + (LL * (P * S) + LL * (P * S)) := by
          have h2 : LL * (∫ s in (-(T + 1 / 2))..(T + 1 / 2), ‖dpoly N a s‖ ^ 2)
              ≤ LL * (P * S) := mul_le_mul_of_nonneg_left hI2 hLLpos.le
          linarith [hI2, h2, hLLinvJ]
    _ = P * S * (1 + 2 * LL) := by ring
    _ ≤ 84 * (T + (N : ℝ)) * LL * S := by
          rw [hPdef]
          have hbig : (0 : ℝ) ≤ 80 * T + 44 * (N : ℝ) - 2 := by linarith
          have hsmall : (0 : ℝ) ≤ 38 * T + 2 * (N : ℝ) - 2 := by linarith
          nlinarith [mul_nonneg hS0 (mul_nonneg (sub_nonneg.mpr hLLhalf) hbig),
            mul_nonneg hS0 hsmall]

end Salt.MR
