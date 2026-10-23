/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.ThreePrimes.Arcs
import Salt.ThreePrimes.Count
import Salt.ThreePrimes.SingularSeries
import Salt.ThreePrimes.SingularIntegral

/-!
# Three primes: the assembly

These are lemmas L20 and L21 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Steps 7
and 8), and the theorem: **every sufficiently large odd number is a sum of three primes.**

Take `P = ⌊(log N)^{10}⌋` and `δ = P/N`, and write `f(α) = S(α)³ e(−Nα)`.

1. **The count is an integral over one period.** `R(N) = ∫₀¹ f`, and `f` has period `1`, so
   `R(N) = ∫ f` over the window `(δ, 1 + δ]` too (`weightedCount_eq_window`).
2. **Split the window** into the disjoint major arcs and what is left, the minor arcs
   (`integral_window_split`).
3. **The minor arcs contribute `o(N²)`.** There `|S| ≤ K (2N/√P + N^{7/8}) (log N)³`, and
   `∫ |S|² ≤ Σ_{n ≤ N} Λ(n)² ≤ C N log N` by Parseval. So the minor integral is at most
   `K C (2N²(log N)⁴/√P + N^{15/8}(log N)⁴)`, and `√P ≈ (log N)⁵` beats `(log N)⁴`
   (`norm_integral_minorArcs_le`). **This is why three primes and not two.** With three copies of
   `S`, one is bounded pointwise and the other two by Parseval. With two copies there is no spare
   copy to take the supremum of, and `∫ |S|² ≈ N log N` is larger than the main term, which would
   be about `N`. Vinogradov's estimate itself holds equally for two primes.
4. **Each major arc contributes its main term.** On the arc at `a/q`, `S = (μ(q)/φ(q)) v + E`
   with `|E| ≤ K N/(log N)^{34}` (the major-arc approximation, with `B = 10`). The cube's error is
   at most `3|E| (N log N)²`, and the arc has length `2P/N`, so the error is
   `O(P N²/(log N)^{32})`. Over the at most `P²` arcs that totals `O(N²/(log N)²)`
   (`norm_majorArc_integral_sub_le`).
5. **The phases collect into the singular series.** Summing `e(−Na/q)` over the `a` coprime to `q`
   gives `c_q(N)` (`sum_phases_eq_ramanujanSum`), and `μ(q)³ = μ(q)`. So the main terms add up to
   `(Σ_{q ≤ P} μ(q) c_q(N)/φ(q)³) · J_δ` (`sum_arcIndex_main`).
6. **Complete both.** `J_δ = C(N − 1, 2) + O(N²/P²)` (the singular integral), and
   `Σ_{q ≤ P} = 𝔖(N) − (a tail)`. The tail is at most `Σ_{q > P} μ(q)²/φ(q)²`, which tends to `0`
   as `P → ∞`, uniformly in `N` (`tendsto_singular_tail`). **No rate is needed**: the theorem asks
   only for sufficiently large `N`. The convergence of `Σ_q μ(q)²/φ(q)²` (an Euler product) is all
   the tail uses, and that convergence spends only `φ(p) = p − 1 ≥ p/2` at each prime
   (`abs_localFactor_sub_one_le`). No lower bound on `φ(q)` at composite `q`, such as
   `φ(q) ≫ q^{1−ε}`, is needed.
7. **For odd `N`, `𝔖(N) ≥ c₀ > 0`,** so `R(N) ≥ (c₀/8) N²` once `N` is large
   (`weightedCount_lower`). Counting with weights cost at most `C N^{3/2}(log N)³`, far less, so
   `N` is a sum of three primes (`three_primes`).
-/

namespace Salt.ThreePrimes

open ArithmeticFunction Filter Topology
open Salt.ExpSum (eR norm_eR)

/-- **The arc parameter** `P = ⌊(log N)^{10}⌋`. -/
noncomputable def arcParam (N : ℕ) : ℕ := ⌊Real.log N ^ (10 : ℕ)⌋₊

/-- **The circle-method integrand** `f(α) = S(α)³ e(−Nα)`. -/
noncomputable def circleIntegrand (N : ℕ) (α : ℝ) : ℂ :=
  primeExpSum N α ^ 3 * eR (-(N : ℝ) * α)

/-- **The period window** `(P/N, 1 + P/N]`. -/
def arcWindow (N P : ℕ) : Set ℝ := Set.Ioc ((P : ℝ) / N) (1 + (P : ℝ) / N)

/-- **The minor arcs**: the window with the major arcs removed. -/
def minorArcs (N P : ℕ) : Set ℝ :=
  arcWindow N P \ ⋃ x ∈ arcIndex P, majorArc N P x.1 x.2

/-- **`S` has period one:** `S(α + 1) = S(α)`, since each phase `e(nα)` has period one. -/
theorem primeExpSum_add_one (N : ℕ) (α : ℝ) : primeExpSum N (α + 1) = primeExpSum N α := by
  unfold primeExpSum
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℝ) * (α + 1) = n * α + ((n : ℤ) : ℝ) by push_cast; ring,
    Salt.MR.eR_add_intCast]

/-- **The circle-method integrand has period one.** -/
theorem circleIntegrand_periodic (N : ℕ) : Function.Periodic (circleIntegrand N) 1 := by
  intro α
  unfold circleIntegrand
  rw [primeExpSum_add_one, show -(N : ℝ) * (α + 1) = -(N : ℝ) * α + ((-(N : ℤ) : ℤ) : ℝ) by
    push_cast; ring, Salt.MR.eR_add_intCast]

/-- `S` is continuous: a finite sum of continuous phases. -/
theorem continuous_primeExpSum (N : ℕ) : Continuous (primeExpSum N) := by
  unfold primeExpSum
  exact continuous_finsetSum _ fun n _ => continuous_const.mul
    (Salt.LS.continuous_e.comp (continuous_const.mul continuous_id))

/-- The integrand `S(α)³ e(−Nα)` is continuous. -/
theorem continuous_circleIntegrand (N : ℕ) : Continuous (circleIntegrand N) :=
  ((continuous_primeExpSum N).pow 3).mul
    (Salt.LS.continuous_e.comp (continuous_const.mul continuous_id))

/-- **Step 1:** the weighted count is the integral of `f` over the window, by periodicity. -/
theorem weightedCount_eq_window (N P : ℕ) :
    ((weightedCount N : ℝ) : ℂ) = ∫ α in arcWindow N P, circleIntegrand N α := by
  have hle : (P : ℝ) / N ≤ 1 + (P : ℝ) / N := by linarith
  rw [arcWindow, ← intervalIntegral.integral_of_le hle, add_comm (1 : ℝ),
    (circleIntegrand_periodic N).intervalIntegral_add_eq ((P : ℝ) / N) 0, zero_add,
    weightedCount_eq_integral]
  rfl

/-- **Step 2:** the window splits into the disjoint major arcs and the minor arcs. -/
theorem integral_window_split {N P : ℕ} (hP : 1 ≤ P) (hN : 2 * P ^ 3 < N) :
    ∫ α in arcWindow N P, circleIntegrand N α
      = ∑ x ∈ arcIndex P, (∫ α in majorArc N P x.1 x.2, circleIntegrand N α)
        + ∫ α in minorArcs N P, circleIntegrand N α := by
  unfold minorArcs
  have hP2 : 2 * P ^ 2 < N := by
    have : P ^ 2 ≤ P ^ 3 := Nat.pow_le_pow_right hP (by norm_num)
    omega
  have hsub : (⋃ x ∈ arcIndex P, majorArc N P x.1 x.2) ⊆ arcWindow N P :=
    Set.iUnion₂_subset fun x hx => majorArc_subset_window hP hP2 hx
  have hint : ∀ s ⊆ arcWindow N P, MeasureTheory.IntegrableOn (circleIntegrand N) s := by
    intro s hs
    exact ((continuous_circleIntegrand N).integrableOn_Icc
      (a := (P : ℝ) / N) (b := 1 + (P : ℝ) / N)).mono_set (hs.trans Set.Ioc_subset_Icc_self)
  have hmeas : MeasurableSet (⋃ x ∈ arcIndex P, majorArc N P x.1 x.2) :=
    Finset.measurableSet_biUnion _ fun x _ => measurableSet_Icc
  have hmeas2 : MeasurableSet (arcWindow N P \ ⋃ x ∈ arcIndex P, majorArc N P x.1 x.2) :=
    measurableSet_Ioc.diff hmeas
  have hdisj : Disjoint (⋃ x ∈ arcIndex P, majorArc N P x.1 x.2)
      (arcWindow N P \ ⋃ x ∈ arcIndex P, majorArc N P x.1 x.2) := Set.disjoint_sdiff_right
  have h1 := MeasureTheory.setIntegral_union hdisj hmeas2 (hint _ hsub) (hint _ Set.sdiff_subset)
  have h2 := MeasureTheory.integral_biUnion_finset (μ := MeasureTheory.volume)
    (f := circleIntegrand N) (s := fun x => majorArc N P x.1 x.2) (arcIndex P)
    (fun x _ => measurableSet_Icc) (fun x hx y hy hxy => majorArc_disjoint hN hx hy hxy)
    (fun x hx => hint _ (majorArc_subset_window hP hP2 hx))
  have h3 : (⋃ x ∈ arcIndex P, majorArc N P x.1 x.2) ∪
      (arcWindow N P \ ⋃ x ∈ arcIndex P, majorArc N P x.1 x.2) = arcWindow N P :=
    Set.union_sdiff_cancel hsub
  rw [← h2, ← h1, h3]

/-- Reindexing `Σ_{1 ≤ n ≤ N} f(n) = Σ_{0 ≤ n < N} f(n + 1)`. -/
theorem sum_Icc_one_eq_sum_range_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `S(α) = e(α) · Σ_{n<N} Λ(n+1) e(nα)`: a phase times an exponential polynomial of the form
Parseval's identity takes. -/
theorem primeExpSum_eq_mul_expSum (N : ℕ) (α : ℝ) :
    primeExpSum N α = eR α * Salt.LS.expSum N (fun n => (vonMangoldt (n + 1) : ℂ)) α := by
  rw [primeExpSum, sum_Icc_one_eq_sum_range_succ, Salt.LS.expSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LS_e_eq_eR, show ((n + 1 : ℕ) : ℝ) * α = α + n * α by push_cast; ring,
    Salt.ExpSum.eR_add]
  ring

/-- **Parseval for `S`:** `∫₀¹ |S|² = Σ_{1 ≤ n ≤ N} Λ(n)²`. -/
theorem integral_norm_primeExpSum_sq (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖primeExpSum N α‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 := by
  simp_rw [primeExpSum_eq_mul_expSum, norm_mul, norm_eR, one_mul]
  rw [Salt.LS.parseval, sum_Icc_one_eq_sum_range_succ]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]

/-- **Parseval over the window:** `∫_{(δ, 1+δ]} |S|² = Σ_{1 ≤ n ≤ N} Λ(n)²`, by periodicity. -/
theorem setIntegral_window_norm_sq (N P : ℕ) :
    ∫ α in arcWindow N P, ‖primeExpSum N α‖ ^ 2 = ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 := by
  have hper : Function.Periodic (fun α => ‖primeExpSum N α‖ ^ 2) 1 := fun α => by
    simp only [primeExpSum_add_one]
  have hle : (P : ℝ) / N ≤ 1 + (P : ℝ) / N := by linarith
  rw [arcWindow, ← intervalIntegral.integral_of_le hle, add_comm (1 : ℝ),
    hper.intervalIntegral_add_eq ((P : ℝ) / N) 0, zero_add, integral_norm_primeExpSum_sq]

/-- **Step 3, the minor arcs:** `|∫_𝔪 f| ≤ sup_𝔪 |S| · ∫ |S|²`, with Parseval and the off-arc
bound. -/
theorem norm_integral_minorArcs_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N P : ℕ, 2 ≤ N → 1 ≤ P → 2 * P ^ 2 < N →
      ‖∫ α in minorArcs N P, circleIntegrand N α‖
        ≤ K * (2 * (N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((7 : ℝ) / 8)) * Real.log N ^ 3
            * ((N : ℝ) * Real.log N) := by
  obtain ⟨K, hK, hoff⟩ := norm_primeExpSum_le_off_arcs
  refine ⟨K * (Real.log 4 + 4), mul_nonneg hK (by positivity), fun N P hN hP hNP => ?_⟩
  set B := K * (2 * (N : ℝ) / Real.sqrt P + (N : ℝ) ^ ((7 : ℝ) / 8)) * Real.log N ^ 3 with hB
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hK (by positivity)) (by positivity)
  have hmeasm : MeasurableSet (minorArcs N P) :=
    measurableSet_Ioc.diff (Finset.measurableSet_biUnion _ fun x _ => measurableSet_Icc)
  have hcont : Continuous fun α => ‖primeExpSum N α‖ ^ 2 :=
    (continuous_primeExpSum N).norm.pow 2
  have hintW : MeasureTheory.IntegrableOn (fun α => ‖primeExpSum N α‖ ^ 2) (arcWindow N P) :=
    (hcont.integrableOn_Icc (a := (P : ℝ) / N) (b := 1 + (P : ℝ) / N)).mono_set
      Set.Ioc_subset_Icc_self
  have hintm : MeasureTheory.IntegrableOn (fun α => ‖primeExpSum N α‖ ^ 2) (minorArcs N P) :=
    hintW.mono_set Set.sdiff_subset
  have hpt : ∀ α ∈ minorArcs N P, ‖circleIntegrand N α‖ ≤ B * ‖primeExpSum N α‖ ^ 2 := by
    intro α hα
    have hS := hoff N P α hN hP hNP hα.1 (fun x hx hmem => hα.2 (Set.mem_biUnion hx hmem))
    rw [circleIntegrand, norm_mul, norm_eR, mul_one, norm_pow]
    calc ‖primeExpSum N α‖ ^ 3 = ‖primeExpSum N α‖ * ‖primeExpSum N α‖ ^ 2 := by ring
      _ ≤ B * ‖primeExpSum N α‖ ^ 2 := mul_le_mul_of_nonneg_right hS (by positivity)
  calc ‖∫ α in minorArcs N P, circleIntegrand N α‖
      ≤ ∫ α in minorArcs N P, B * ‖primeExpSum N α‖ ^ 2 :=
        MeasureTheory.norm_integral_le_of_norm_le (hintm.const_mul B)
          ((MeasureTheory.ae_restrict_iff' hmeasm).2 (Filter.Eventually.of_forall hpt))
    _ = B * ∫ α in minorArcs N P, ‖primeExpSum N α‖ ^ 2 := MeasureTheory.integral_const_mul _ _
    _ ≤ B * ∫ α in arcWindow N P, ‖primeExpSum N α‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hB0
        exact MeasureTheory.setIntegral_mono_set hintW
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) Set.sdiff_subset.eventuallyLE
    _ = B * ∑ n ∈ Finset.Icc 1 N, vonMangoldt n ^ 2 := by rw [setIntegral_window_norm_sq]
    _ ≤ B * ((Real.log 4 + 4) * N * Real.log N) :=
        mul_le_mul_of_nonneg_left (Salt.LS.sum_vonMangoldt_sq_le N hN) hB0
    _ = _ := by rw [hB]; ring

/-- **Cubes of close numbers are close:** if `|s − m| ≤ E` and `|s|, |m| ≤ R`, then
`|s³ − m³| ≤ 3 E R²`. -/
theorem norm_cube_sub_cube_le {s m : ℂ} {E R : ℝ} (hE : ‖s - m‖ ≤ E) (hs : ‖s‖ ≤ R)
    (hm : ‖m‖ ≤ R) : ‖s ^ 3 - m ^ 3‖ ≤ 3 * E * R ^ 2 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hs
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hfac : s ^ 3 - m ^ 3 = (s - m) * (s ^ 2 + s * m + m ^ 2) := by ring
  have h2 : ‖s ^ 2 + s * m + m ^ 2‖ ≤ 3 * R ^ 2 := by
    calc ‖s ^ 2 + s * m + m ^ 2‖ ≤ ‖s‖ ^ 2 + ‖s‖ * ‖m‖ + ‖m‖ ^ 2 := by
          refine (norm_add₃_le).trans ?_
          rw [norm_pow, norm_pow, norm_mul]
      _ ≤ R ^ 2 + R * R + R ^ 2 := by gcongr
      _ = 3 * R ^ 2 := by ring
  rw [hfac, norm_mul]
  calc ‖s - m‖ * ‖s ^ 2 + s * m + m ^ 2‖ ≤ E * (3 * R ^ 2) :=
        mul_le_mul hE h2 (norm_nonneg _) hE0
    _ = 3 * E * R ^ 2 := by ring

/-- `|μ(q)/φ(q)| ≤ 1`. -/
theorem norm_moebius_div_totient_le (q : ℕ) :
    ‖(moebius q : ℂ) / (q.totient : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_intCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos q.totient with h | h
  · simp [h]
  · have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast h
    rw [div_le_one (by linarith)]
    have hμ : |(moebius q : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    exact hμ.trans hφ

/-- The arc parameter is at most `(log N)^{10}`. So on an arc the denominator `q ≤ P` and the
offset `|β| ≤ P/N` are within the major-arc approximation's range, with `B = 10`. -/
theorem arcParam_le_log_pow (N : ℕ) : (arcParam N : ℝ) ≤ Real.log N ^ 10 :=
  Nat.floor_le (pow_nonneg (Real.log_natCast_nonneg N) _)

/-- If the arc parameter is positive then `log N ≥ 1`. -/
theorem one_le_log_of_one_le_arcParam {N : ℕ} (h : 1 ≤ arcParam N) : 1 ≤ Real.log N := by
  have hL0 := Real.log_natCast_nonneg N
  by_contra hlt
  push Not at hlt
  have h1 : Real.log N ^ 10 < 1 := pow_lt_one₀ hL0 hlt (by norm_num)
  have h2 : (1 : ℝ) ≤ arcParam N := by exact_mod_cast h
  linarith [arcParam_le_log_pow N]

/-- `norm_majorArc_integral_sub_le` with the Siegel–Walfisz statement as the hypothesis `hSWall`,
in place of the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem norm_majorArc_integral_sub_le_of_SW (hSWall : Salt.BV.SiegelWalfisz) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ x ∈ arcIndex (arcParam N),
      ‖(∫ α in majorArc N (arcParam N) x.1 x.2, circleIntegrand N α)
          - ((moebius x.1 : ℂ) / (x.1.totient : ℂ)) ^ 3 * eR (-(N : ℝ) * x.2 / x.1)
            * ∫ β in (-((arcParam N : ℝ) / N))..((arcParam N : ℝ) / N),
                expSumOne N β ^ 3 * eR (-(N : ℝ) * β)‖
        ≤ K * (arcParam N : ℝ) * (N : ℝ) ^ 2 / Real.log N ^ 32 := by
  obtain ⟨K₀, hK₀, happ⟩ :=
    majorArc_approx_of_SW hSWall (A := 34) (B := 10) (by norm_num) (by norm_num)
  refine ⟨6 * K₀, by positivity, ?_⟩
  rintro N hN ⟨q, a⟩ hx
  simp only [arcIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
  obtain ⟨⟨⟨hq1, hqP⟩, ha1, -⟩, haq, hcop⟩ := hx
  dsimp only
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := one_le_log_of_one_le_arcParam (le_trans hq1 hqP)
  have hLpos : 0 < Real.log N := by linarith
  have hPle := arcParam_le_log_pow N
  have hδ0 : 0 ≤ (arcParam N : ℝ) / N := by positivity
  have hqB : (q : ℝ) ≤ Real.log N ^ (10 : ℝ) := by
    rw [Real.rpow_ofNat]
    exact le_trans (by exact_mod_cast hqP) hPle
  set E := K₀ * N / Real.log N ^ 34 with hE
  set M : ℂ := (moebius q : ℂ) / (q.totient : ℂ) with hM
  -- pointwise bound on the integrand's difference
  have hpt : ∀ β ∈ Set.uIoc (-((arcParam N : ℝ) / N)) ((arcParam N : ℝ) / N),
      ‖eR (-(N : ℝ) * a / q) * eR (-(N : ℝ) * β)
          * (primeExpSum N ((a : ℝ) / q + β) ^ 3 - (M * expSumOne N β) ^ 3)‖
        ≤ 3 * E * ((N : ℝ) * Real.log N) ^ 2 := by
    intro β hβ
    rw [Set.uIoc_of_le (by linarith)] at hβ
    have hβ' : |β| ≤ Real.log N ^ (10 : ℝ) / N := by
      rw [Real.rpow_ofNat, abs_le]
      have : (arcParam N : ℝ) / N ≤ Real.log N ^ 10 / N :=
        div_le_div_of_nonneg_right hPle hNpos.le
      constructor <;> linarith [hβ.1, hβ.2]
    have h1 := happ N q a hN hq1 hqB hcop.symm β hβ'
    rw [Real.rpow_ofNat] at h1
    rw [norm_mul, norm_mul, norm_eR, norm_eR, one_mul, one_mul]
    refine norm_cube_sub_cube_le h1 (norm_primeExpSum_le_trivial N _) ?_
    rw [norm_mul]
    calc ‖M‖ * ‖expSumOne N β‖ ≤ 1 * N :=
          mul_le_mul (norm_moebius_div_totient_le q) (norm_expSumOne_le N β) (norm_nonneg _)
            (by norm_num)
      _ ≤ (N : ℝ) * Real.log N := by nlinarith
  have harc : (∫ α in majorArc N (arcParam N) q a, circleIntegrand N α)
      = ∫ β in (-((arcParam N : ℝ) / N))..((arcParam N : ℝ) / N),
          circleIntegrand N ((a : ℝ) / q + β) := by
    rw [majorArc, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_comp_add_left,
      sub_eq_add_neg]
  have hfun : ∀ β, circleIntegrand N ((a : ℝ) / q + β)
      - M ^ 3 * eR (-(N : ℝ) * a / q) * (expSumOne N β ^ 3 * eR (-(N : ℝ) * β))
      = eR (-(N : ℝ) * a / q) * eR (-(N : ℝ) * β)
          * (primeExpSum N ((a : ℝ) / q + β) ^ 3 - (M * expSumOne N β) ^ 3) := by
    intro β
    rw [circleIntegrand, show -(N : ℝ) * ((a : ℝ) / q + β) = -(N : ℝ) * a / q + -(N : ℝ) * β by
      ring, Salt.ExpSum.eR_add]
    ring
  have hc1 : Continuous fun β => circleIntegrand N ((a : ℝ) / q + β) :=
    (continuous_circleIntegrand N).comp (continuous_const.add continuous_id)
  have hc2 : Continuous fun β => M ^ 3 * eR (-(N : ℝ) * a / q)
      * (expSumOne N β ^ 3 * eR (-(N : ℝ) * β)) :=
    continuous_const.mul (((continuous_expSumOne N).pow 3).mul
      (Salt.LS.continuous_e.comp (continuous_const.mul continuous_id)))
  rw [harc, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_congr (fun β _ => hfun β)]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hpt).trans (le_of_eq ?_)
  rw [show (arcParam N : ℝ) / N - -((arcParam N : ℝ) / N) = 2 * ((arcParam N : ℝ) / N) by ring,
    abs_of_nonneg (by positivity), hE]
  field_simp
  ring

/-- **Step 4, one major arc:** the integral over the arc at `a/q` is
`(μ(q)/φ(q))³ e(−Na/q) J_δ` up to `O(P N²/(log N)^{32})`. -/
theorem norm_majorArc_integral_sub_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ x ∈ arcIndex (arcParam N),
      ‖(∫ α in majorArc N (arcParam N) x.1 x.2, circleIntegrand N α)
          - ((moebius x.1 : ℂ) / (x.1.totient : ℂ)) ^ 3 * eR (-(N : ℝ) * x.2 / x.1)
            * ∫ β in (-((arcParam N : ℝ) / N))..((arcParam N : ℝ) / N),
                expSumOne N β ^ 3 * eR (-(N : ℝ) * β)‖
        ≤ K * (arcParam N : ℝ) * (N : ℝ) ^ 2 / Real.log N ^ 32 :=
  norm_majorArc_integral_sub_le_of_SW Salt.SW.siegelWalfisz_holds

/-- **`μ(q)³ = μ(q)`**, since the Möbius function takes only the values `−1`, `0`, `1`. -/
theorem moebius_cube (q : ℕ) : ((moebius q : ℂ)) ^ 3 = moebius q := by
  by_cases h0 : moebius q = 0
  · simp [h0]
  · rcases moebius_ne_zero_iff_eq_or.mp h0 with h | h <;> (simp [h]; try norm_num)

/-- **The majorant** `μ(q)²/φ(q)²` of the singular series' terms. -/
noncomputable def moebiusSqDivTotientSq (q : ℕ) : ℝ :=
  ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2

/-- At `N = 0` the Ramanujan sum is `φ(q)`, so the term's size is exactly `μ(q)²/φ(q)²`. -/
theorem norm_singularTerm_zero (q : ℕ) : ‖singularTerm 0 q‖ = moebiusSqDivTotientSq q := by
  have hc : ramanujanSum q 0 = (Nat.totient q : ℂ) := by
    simp only [ramanujanSum, Nat.cast_zero, zero_mul, zero_div]
    rw [show Salt.ExpSum.eR 0 = 1 by simp [Salt.ExpSum.eR], Finset.sum_const, nsmul_eq_mul,
      mul_one, card_coprime_filter]
  have hμ : ‖(moebius q : ℂ)‖ = (moebius q : ℝ) ^ 2 := by
    rw [Complex.norm_intCast]
    by_cases h0 : moebius q = 0
    · simp [h0]
    · rcases moebius_ne_zero_iff_eq_or.mp h0 with h | h <;> simp [h]
  rw [singularTerm, hc, norm_mul, norm_div, norm_pow, hμ, Complex.norm_natCast,
    moebiusSqDivTotientSq]
  rcases Nat.eq_zero_or_pos (Nat.totient q) with h | h
  · simp [h]
  · have : (0 : ℝ) < Nat.totient q := by exact_mod_cast h
    field_simp

/-- **The majorant series converges:** `Σ_q μ(q)²/φ(q)² < ∞`. -/
theorem summable_moebiusSqDivTotientSq : Summable moebiusSqDivTotientSq :=
  (summable_norm_singularTerm 0).congr norm_singularTerm_zero

/-- The majorant is nonnegative. -/
theorem moebiusSqDivTotientSq_nonneg (q : ℕ) : 0 ≤ moebiusSqDivTotientSq q := by
  unfold moebiusSqDivTotientSq; positivity

/-- The tail `Σ_{q > P}` of the majorant, written as a shifted series `Σ_k g(k + P + 1)`. -/
theorem tsum_tail_eq_tsum_nat_add (P : ℕ) :
    (∑' q : ℕ, if P < q then ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2 else 0)
      = ∑' k : ℕ, moebiusSqDivTotientSq (k + (P + 1)) := by
  have hs : Summable (fun q : ℕ => if P < q then moebiusSqDivTotientSq q else 0) :=
    summable_moebiusSqDivTotientSq.of_nonneg_of_le
      (fun q => by split_ifs <;> simp [moebiusSqDivTotientSq_nonneg])
      (fun q => by split_ifs <;> simp [moebiusSqDivTotientSq_nonneg])
  change (∑' q : ℕ, if P < q then moebiusSqDivTotientSq q else 0) = _
  rw [← hs.sum_add_tsum_nat_add (P + 1)]
  rw [Finset.sum_eq_zero (fun i hi => by
    simp only [Finset.mem_range] at hi; rw [if_neg (by omega)])]
  rw [zero_add]
  refine tsum_congr fun k => ?_
  rw [if_pos (by omega)]

/-- **Step 5, the phases:** `Σ_{1 ≤ a ≤ q, gcd(a, q) = 1} e(−Na/q) = c_q(N)`, through
`a ↦ q − a`. -/
theorem sum_phases_eq_ramanujanSum (N q : ℕ) (hq : 1 ≤ q) :
    ∑ a ∈ (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q), eR (-(N : ℝ) * a / q)
      = ramanujanSum q N := by
  unfold ramanujanSum
  refine Finset.sum_nbij' (fun a => q - a) (fun b => q - b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at ha ⊢
    exact ⟨by omega, (Nat.coprime_self_sub_right ha.1.2).2 ha.2.symm⟩
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hb ⊢
    exact ⟨⟨by omega, by omega⟩, (Nat.coprime_self_sub_left hb.1.le).2 hb.2.symm⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hsub : (((q - a : ℕ) : ℝ)) = (q : ℝ) - a := by
      rw [Nat.cast_sub ha.1.2]
    rw [hsub, ← Salt.MR.eR_add_intCast (-(N : ℝ) * a / q) (N : ℤ)]
    congr 1
    push_cast
    field_simp
    ring

/-- **Step 5, the main terms collect:** summed over the arcs, `(μ(q)/φ(q))³ e(−Na/q)` is the
truncated singular series `Σ_{q ≤ P} μ(q) c_q(N)/φ(q)³`. -/
theorem sum_arcIndex_main (N P : ℕ) :
    ∑ x ∈ arcIndex P, ((moebius x.1 : ℂ) / (x.1.totient : ℂ)) ^ 3 * eR (-(N : ℝ) * x.2 / x.1)
      = ∑ q ∈ Finset.Icc 1 P, singularTerm N q := by
  rw [arcIndex, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' := Finset.mem_Icc.1 hq
  have hset : (Finset.Icc 1 q).filter (fun a => Nat.Coprime a q)
      = (Finset.Icc 1 P).filter (fun a => a ≤ q ∧ Nat.Coprime a q) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [← Finset.sum_filter, ← hset]
  dsimp only
  rw [← Finset.mul_sum, sum_phases_eq_ramanujanSum N q hq'.1,
    singularTerm, div_pow, moebius_cube]

/-- **Step 6, the tail:** `Σ_{q > P} μ(q)²/φ(q)² → 0` as `P → ∞`. -/
theorem tendsto_singular_tail :
    Tendsto (fun P : ℕ => ∑' q : ℕ,
      if P < q then ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2 else 0) atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add moebiusSqDivTotientSq).comp (tendsto_add_atTop_nat 1)
  refine h.congr fun P => ?_
  exact (tsum_tail_eq_tsum_nat_add P).symm

/-- There are at most `P²` arcs. -/
theorem card_arcIndex_le (P : ℕ) : ((arcIndex P).card : ℝ) ≤ (P : ℝ) ^ 2 := by
  have h : (arcIndex P).card ≤ P ^ 2 := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel, sq]
  exact_mod_cast h

/-- **The singular series splits** as its truncation `Σ_{q ≤ P}` plus the shifted tail
`Σ_k (term at k + P + 1)`. -/
theorem singularSeries_eq_sum_add_tail (N P : ℕ) :
    singularSeries N = ∑ q ∈ Finset.Icc 1 P, singularTerm N q
      + ∑' k : ℕ, singularTerm N (k + (P + 1)) := by
  have hs : Summable (singularTerm N) := (summable_norm_singularTerm N).of_norm
  rw [singularSeries, ← hs.sum_add_tsum_nat_add (P + 1), Finset.sum_range_succ',
    sum_Icc_one_eq_sum_range_succ]
  simp [singularTerm]

/-- **The tail is small:** `|Σ_k (term at k + P + 1)| ≤ Σ_{q > P} μ(q)²/φ(q)²`. -/
theorem norm_singularTail_le (N P : ℕ) :
    ‖∑' k : ℕ, singularTerm N (k + (P + 1))‖
      ≤ ∑' q : ℕ, if P < q then ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2 else 0 := by
  rw [tsum_tail_eq_tsum_nat_add]
  have h1 : Summable fun k : ℕ => ‖singularTerm N (k + (P + 1))‖ :=
    (summable_norm_singularTerm N).comp_injective (add_left_injective _)
  have h2 : Summable fun k : ℕ => moebiusSqDivTotientSq (k + (P + 1)) :=
    summable_moebiusSqDivTotientSq.comp_injective (add_left_injective _)
  exact (norm_tsum_le_tsum_norm h1).trans
    (h1.tsum_le_tsum (fun k => norm_singularTerm_le N _) h2)

/-- **The truncated series is bounded** by the majorant's total `Σ_q μ(q)²/φ(q)²`. -/
theorem norm_sum_singularTerm_le (N P : ℕ) :
    ‖∑ q ∈ Finset.Icc 1 P, singularTerm N q‖ ≤ ∑' q, moebiusSqDivTotientSq q :=
  (norm_sum_le _ _).trans ((Finset.sum_le_sum fun q _ => norm_singularTerm_le N q).trans
    (summable_moebiusSqDivTotientSq.sum_le_tsum _
      (fun q _ => moebiusSqDivTotientSq_nonneg q)))

/-- `weightedCount_ge_main_sub_errors` with the Siegel–Walfisz statement as the hypothesis `hSWall`,
in place of the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem weightedCount_ge_main_sub_errors_of_SW (hSWall : Salt.BV.SiegelWalfisz) :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ N : ℕ, 2 ≤ N → 1 ≤ arcParam N →
      2 * arcParam N ^ 3 < N →
      (∏' p : Nat.Primes, localFactor N p) * ((N - 1).choose 2 : ℕ)
        - ((arcParam N : ℝ) ^ 2 * (K₂ * arcParam N * (N : ℝ) ^ 2 / Real.log N ^ 32)
          + K₁ * (2 * (N : ℝ) / Real.sqrt (arcParam N) + (N : ℝ) ^ ((7 : ℝ) / 8))
              * Real.log N ^ 3 * ((N : ℝ) * Real.log N)
          + (∑' q, moebiusSqDivTotientSq q) * (1 / (4 * ((arcParam N : ℝ) / N) ^ 2))
          + (∑' q : ℕ, if arcParam N < q then ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2
              else 0) * ((N - 1).choose 2 : ℕ))
        ≤ weightedCount N := by
  obtain ⟨K₁, hK₁, hmin⟩ := norm_integral_minorArcs_le
  obtain ⟨K₂, hK₂, hmaj⟩ := norm_majorArc_integral_sub_le_of_SW hSWall
  refine ⟨K₁, K₂, hK₁, hK₂, fun N hN hP hP3 => ?_⟩
  have hP2 : 2 * arcParam N ^ 2 < N := by
    have : arcParam N ^ 2 ≤ arcParam N ^ 3 := Nat.pow_le_pow_right hP (by norm_num)
    omega
  have hPN : 2 * arcParam N ≤ N := by
    have : arcParam N ^ 1 ≤ arcParam N ^ 3 := Nat.pow_le_pow_right hP (by norm_num)
    rw [pow_one] at this
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hPpos : (0 : ℝ) < arcParam N := by exact_mod_cast hP
  have hδ0 : 0 < (arcParam N : ℝ) / N := div_pos hPpos hNpos
  have hδ2 : (arcParam N : ℝ) / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]
    have : (2 * arcParam N : ℝ) ≤ N := by exact_mod_cast hPN
    linarith
  have hsplit := (weightedCount_eq_window N (arcParam N)).trans
    (integral_window_split hP hP3)
  have hMa : ‖∑ x ∈ arcIndex (arcParam N),
        (∫ α in majorArc N (arcParam N) x.1 x.2, circleIntegrand N α)
      - (∑ q ∈ Finset.Icc 1 (arcParam N), singularTerm N q)
        * ∫ β in (-((arcParam N : ℝ) / N))..((arcParam N : ℝ) / N),
            expSumOne N β ^ 3 * eR (-(N : ℝ) * β)‖
      ≤ (arcParam N : ℝ) ^ 2 * (K₂ * arcParam N * (N : ℝ) ^ 2 / Real.log N ^ 32) := by
    rw [← sum_arcIndex_main, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x hx => hmaj N hN x hx).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (card_arcIndex_le _)
      (div_nonneg (mul_nonneg (mul_nonneg hK₂ hPpos.le) (by positivity)) (by positivity))
  have hMi := hmin N (arcParam N) hN hP hP2
  have hJ := integral_expSumOne_cube_trunc N hδ0 hδ2
  have hTn := norm_sum_singularTerm_le N (arcParam N)
  have hser := singularSeries_eq_sum_add_tail N (arcParam N)
  have htl := norm_singularTail_le N (arcParam N)
  have hprod := singularSeries_eq_tprod N
  set J := ∫ β in (-((arcParam N : ℝ) / N))..((arcParam N : ℝ) / N),
    expSumOne N β ^ 3 * eR (-(N : ℝ) * β) with hJdef
  set Cn : ℕ := (N - 1).choose 2 with hCn
  set T := ∑ q ∈ Finset.Icc 1 (arcParam N), singularTerm N q with hT
  set tl := ∑' k : ℕ, singularTerm N (k + (arcParam N + 1)) with htldef
  set pr := ∏' p : Nat.Primes, localFactor N p with hpr
  set Ma := ∑ x ∈ arcIndex (arcParam N),
    (∫ α in majorArc N (arcParam N) x.1 x.2, circleIntegrand N α) with hMadef
  set Mi := ∫ α in minorArcs N (arcParam N), circleIntegrand N α with hMidef
  have key : ((weightedCount N : ℝ) : ℂ)
      = ((pr * Cn : ℝ) : ℂ) + ((Ma - T * J) + Mi + T * (J - Cn) - tl * Cn) := by
    rw [hsplit]
    push_cast
    rw [← hprod, hser]
    ring
  have hre := congrArg Complex.re key
  rw [Complex.ofReal_re, Complex.add_re, Complex.ofReal_re] at hre
  set D := (Ma - T * J) + Mi + T * (J - Cn) - tl * Cn with hD
  have hDre : -‖D‖ ≤ D.re := by
    have := Complex.abs_re_le_norm D
    linarith [neg_abs_le D.re]
  have hG0 : 0 ≤ ∑' q, moebiusSqDivTotientSq q :=
    tsum_nonneg moebiusSqDivTotientSq_nonneg
  have hDn : ‖D‖ ≤ ‖Ma - T * J‖ + ‖Mi‖ + ‖T‖ * ‖J - Cn‖ + ‖tl‖ * Cn := by
    have h1 := norm_sub_le ((Ma - T * J) + Mi + T * (J - Cn)) (tl * Cn)
    have h2 := norm_add₃_le (a := Ma - T * J) (b := Mi) (c := T * (J - Cn))
    rw [norm_mul, Complex.norm_natCast] at h1
    rw [norm_mul] at h2
    linarith
  have hTJ : ‖T‖ * ‖J - Cn‖
      ≤ (∑' q, moebiusSqDivTotientSq q) * (1 / (4 * ((arcParam N : ℝ) / N) ^ 2)) :=
    mul_le_mul hTn hJ (norm_nonneg _) hG0
  have htlC := mul_le_mul_of_nonneg_right htl (Nat.cast_nonneg (α := ℝ) Cn)
  linarith

/-- **The count around its main term.** For `N ≥ 2` with `P = arcParam N ≥ 1` and `2P³ < N`,
`R(N)` is at least `𝔖(N) C(N − 1, 2)` minus four errors: the major arcs, the minor arcs, the
singular integral's truncation, and the singular series' tail. -/
theorem weightedCount_ge_main_sub_errors :
    ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ N : ℕ, 2 ≤ N → 1 ≤ arcParam N →
      2 * arcParam N ^ 3 < N →
      (∏' p : Nat.Primes, localFactor N p) * ((N - 1).choose 2 : ℕ)
        - ((arcParam N : ℝ) ^ 2 * (K₂ * arcParam N * (N : ℝ) ^ 2 / Real.log N ^ 32)
          + K₁ * (2 * (N : ℝ) / Real.sqrt (arcParam N) + (N : ℝ) ^ ((7 : ℝ) / 8))
              * Real.log N ^ 3 * ((N : ℝ) * Real.log N)
          + (∑' q, moebiusSqDivTotientSq q) * (1 / (4 * ((arcParam N : ℝ) / N) ^ 2))
          + (∑' q : ℕ, if arcParam N < q then ((moebius q : ℝ)) ^ 2 / (Nat.totient q : ℝ) ^ 2
              else 0) * ((N - 1).choose 2 : ℕ))
        ≤ weightedCount N :=
  weightedCount_ge_main_sub_errors_of_SW Salt.SW.siegelWalfisz_holds

/-- **Powers of `log` are small:** for `s, ε > 0`, eventually `(log N)^r ≤ ε N^s`. -/
theorem eventually_log_pow_le (r : ℕ) {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ r ≤ ε * (N : ℝ) ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop (r : ℝ) hs).def hε
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h] with N hN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg N) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _), Real.rpow_natCast] at hN
  exact hN

/-- **`log N` is eventually large:** eventually `M ≤ log N`. -/
theorem eventually_le_log (M : ℝ) : ∀ᶠ N : ℕ in atTop, M ≤ Real.log N :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop M

/-- **The arc parameter grows:** `P = ⌊(log N)^{10}⌋ → ∞`. -/
theorem tendsto_arcParam : Tendsto arcParam atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_pow_atTop (by norm_num : (10 : ℕ) ≠ 0)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))))

/-- **`√P ≥ (log N)^5/2`** once `log N ≥ 2`, since `P > (log N)^{10} − 1`. -/
theorem log_pow_five_div_two_le_sqrt_arcParam {N : ℕ} (hL : 2 ≤ Real.log N) :
    Real.log N ^ 5 / 2 ≤ Real.sqrt (arcParam N) := by
  have hlt : Real.log N ^ 10 < (arcParam N : ℝ) + 1 :=
    Nat.lt_floor_add_one (Real.log N ^ 10)
  have h10 : (2 : ℝ) ^ 10 ≤ Real.log N ^ 10 := pow_le_pow_left₀ (by norm_num) hL 10
  have hsq : (Real.log N ^ 5 / 2) ^ 2 ≤ (arcParam N : ℝ) := by
    have e : (Real.log N ^ 5 / 2) ^ 2 = Real.log N ^ 10 / 4 := by ring
    rw [e]; linarith
  calc Real.log N ^ 5 / 2 = Real.sqrt ((Real.log N ^ 5 / 2) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (arcParam N) := Real.sqrt_le_sqrt hsq

/-- **The final inequality, in real numbers:** with the main term at least `c₀ C(N−1,2)` and
each error at most `(c₀/16) N²`, the count is at least `(c₀/8) N²`. -/
theorem count_lower_of_bounds {c₀ G K₁ K₂ τ n L P pr Cn W : ℝ}
    (hc₀ : 0 < c₀) (_hK₁ : 0 ≤ K₁) (_hK₂ : 0 ≤ K₂) (hn : 32 ≤ n) (hP1 : 1 ≤ P)
    (hPL : P ≤ L ^ 10) (hL1 : 1 ≤ L) (hpr : c₀ ≤ pr) (hClo : n ^ 2 / 2 - 2 * n ≤ Cn)
    (hChi : Cn ≤ n ^ 2 / 2) (_hτ0 : 0 ≤ τ) (hτ : τ ≤ c₀ / 8) (hG : G ≤ c₀ / 4 * P ^ 2)
    (hK₂L : K₂ ≤ c₀ / 16 * L ^ 2) (hsq : 2 * K₁ * L ^ 4 ≤ c₀ / 16 * Real.sqrt P)
    (hrp : K₁ * L ^ 4 * n ^ ((7 : ℝ) / 8) ≤ c₀ / 16 * n)
    (hW : pr * Cn - (P ^ 2 * (K₂ * P * n ^ 2 / L ^ 32)
          + K₁ * (2 * n / Real.sqrt P + n ^ ((7 : ℝ) / 8)) * L ^ 3 * (n * L)
          + G * (1 / (4 * (P / n) ^ 2)) + τ * Cn) ≤ W) :
    c₀ / 8 * n ^ 2 ≤ W := by
  have hn0 : 0 < n := by linarith
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P := by linarith
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.2 hP0
  have hC0 : 0 ≤ Cn := by nlinarith
  have hc16 : 0 ≤ c₀ / 16 * L ^ 2 := by positivity
  have t1 : P ^ 2 * (K₂ * P * n ^ 2 / L ^ 32) ≤ c₀ / 16 * n ^ 2 := by
    have hP3 : P ^ 3 ≤ L ^ 30 := by
      calc P ^ 3 ≤ (L ^ 10) ^ 3 := pow_le_pow_left₀ hP0.le hPL 3
        _ = L ^ 30 := by ring
    have e : P ^ 2 * (K₂ * P * n ^ 2 / L ^ 32) = K₂ * P ^ 3 * n ^ 2 / L ^ 32 := by ring
    rw [e, div_le_iff₀ (by positivity)]
    calc K₂ * P ^ 3 * n ^ 2 ≤ (c₀ / 16 * L ^ 2) * L ^ 30 * n ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hK₂L hP3 (by positivity) hc16)
            (by positivity)
      _ = c₀ / 16 * n ^ 2 * L ^ 32 := by ring
  have t2 : K₁ * (2 * n / Real.sqrt P) * L ^ 3 * (n * L) ≤ c₀ / 16 * n ^ 2 := by
    have e : K₁ * (2 * n / Real.sqrt P) * L ^ 3 * (n * L)
        = (2 * K₁ * L ^ 4) / Real.sqrt P * n ^ 2 := by
      field_simp
    rw [e]
    have : (2 * K₁ * L ^ 4) / Real.sqrt P ≤ c₀ / 16 := by rw [div_le_iff₀ hsP]; linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have t3 : K₁ * n ^ ((7 : ℝ) / 8) * L ^ 3 * (n * L) ≤ c₀ / 16 * n ^ 2 := by
    have e : K₁ * n ^ ((7 : ℝ) / 8) * L ^ 3 * (n * L)
        = (K₁ * L ^ 4 * n ^ ((7 : ℝ) / 8)) * n := by ring
    rw [e]
    calc _ ≤ c₀ / 16 * n * n := mul_le_mul_of_nonneg_right hrp hn0.le
      _ = _ := by ring
  have t4 : G * (1 / (4 * (P / n) ^ 2)) ≤ c₀ / 16 * n ^ 2 := by
    have e : G * (1 / (4 * (P / n) ^ 2)) = G / (4 * P ^ 2) * n ^ 2 := by
      field_simp
    rw [e]
    have : G / (4 * P ^ 2) ≤ c₀ / 16 := by rw [div_le_iff₀ (by positivity)]; linarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have t5 : τ * Cn ≤ c₀ / 16 * n ^ 2 := by
    calc τ * Cn ≤ c₀ / 8 * (n ^ 2 / 2) := mul_le_mul hτ hChi hC0 (by positivity)
      _ = _ := by ring
  have t0 : c₀ * Cn ≤ pr * Cn := mul_le_mul_of_nonneg_right hpr hC0
  have hmain : c₀ / 2 * n ^ 2 - c₀ / 16 * n ^ 2 ≤ c₀ * Cn := by
    have h2n : 2 * n ≤ n ^ 2 / 16 := by nlinarith
    have := mul_le_mul_of_nonneg_left hClo hc₀.le
    nlinarith
  have esplit : K₁ * (2 * n / Real.sqrt P + n ^ ((7 : ℝ) / 8)) * L ^ 3 * (n * L)
      = K₁ * (2 * n / Real.sqrt P) * L ^ 3 * (n * L)
        + K₁ * n ^ ((7 : ℝ) / 8) * L ^ 3 * (n * L) := by ring
  linarith

/-- `C(N − 1, 2) = (N − 1)(N − 2)/2` lies between `N²/2 − 2N` and `N²/2`. -/
theorem choose_two_bounds {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ 2 / 2 - 2 * N ≤ ((N - 1).choose 2 : ℕ)
      ∧ (((N - 1).choose 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / 2 := by
  rw [Nat.cast_choose_two, Nat.cast_sub hN, Nat.cast_one]
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  constructor <;> nlinarith

/-- `weightedCount_lower` with the Siegel–Walfisz statement as the hypothesis `hSWall`, in place of
the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem weightedCount_lower_of_SW (hSWall : Salt.BV.SiegelWalfisz) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Odd N → c * (N : ℝ) ^ 2 ≤ weightedCount N := by
  obtain ⟨c₀, hc₀, hlow⟩ := singularSeries_lower_bound
  obtain ⟨K₁, K₂, hK₁, hK₂, hdec⟩ := weightedCount_ge_main_sub_errors_of_SW hSWall
  refine ⟨c₀ / 8, by positivity, ?_⟩
  have hτ := (tendsto_singular_tail.comp tendsto_arcParam).eventually
    (Iic_mem_nhds (by positivity : (0 : ℝ) < c₀ / 8))
  have hPM := tendsto_arcParam.eventually_ge_atTop
    (⌈4 * (∑' q, moebiusSqDivTotientSq q) / c₀⌉₊ + 1)
  have hL := eventually_le_log (2 + 64 * K₁ / c₀ + 16 * K₂ / c₀)
  have h30 := eventually_log_pow_le 30 (s := 1) one_pos (by norm_num : (0 : ℝ) < 1 / 4)
  have h4 := eventually_log_pow_le 4 (s := 1 / 8) (by norm_num)
    (ε := c₀ / (16 * (K₁ + 1))) (by positivity)
  filter_upwards [hτ, hPM, hL, h30, h4, eventually_ge_atTop 32] with N hτN hPMN hLN h30N h4N hN
  intro hodd
  have hNR : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hK₁c : 0 ≤ 64 * K₁ / c₀ := by positivity
  have hK₂c : 0 ≤ 16 * K₂ / c₀ := by positivity
  have hL2 : 2 ≤ Real.log N := by linarith
  have hL1 : 1 ≤ Real.log N := by linarith
  have hP1 : 1 ≤ arcParam N := le_trans (Nat.le_add_left 1 _) hPMN
  have hPL := arcParam_le_log_pow N
  have hP1R : (1 : ℝ) ≤ arcParam N := by exact_mod_cast hP1
  have hP3 : 2 * arcParam N ^ 3 < N := by
    have h1 : ((arcParam N : ℝ)) ^ 3 ≤ Real.log N ^ 30 := by
      calc ((arcParam N : ℝ)) ^ 3 ≤ (Real.log N ^ 10) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hPL 3
        _ = Real.log N ^ 30 := by ring
    rw [Real.rpow_one] at h30N
    have : (2 * arcParam N ^ 3 : ℝ) < N := by linarith
    exact_mod_cast this
  have hW := hdec N (by omega) hP1 hP3
  obtain ⟨hClo, hChi⟩ := choose_two_bounds (N := N) (by omega)
  refine count_lower_of_bounds hc₀ hK₁ hK₂ hNR hP1R hPL hL1 (hlow N hodd) hClo hChi
    (tsum_nonneg fun q => by split_ifs <;> positivity) hτN ?_ ?_ ?_ ?_ hW
  · -- `G ≤ (c₀/4) P²`
    have hc : 4 * (∑' q, moebiusSqDivTotientSq q) / c₀ ≤ arcParam N := by
      have := Nat.le_ceil (4 * (∑' q, moebiusSqDivTotientSq q) / c₀)
      have h' : ((⌈4 * (∑' q, moebiusSqDivTotientSq q) / c₀⌉₊ + 1 : ℕ) : ℝ) ≤ arcParam N := by
        exact_mod_cast hPMN
      push_cast at h'
      linarith
    rw [div_le_iff₀ hc₀] at hc
    have hPP : (arcParam N : ℝ) ≤ (arcParam N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hPP (by positivity : (0 : ℝ) ≤ c₀ / 4)
    linarith
  · -- `K₂ ≤ (c₀/16) L²`
    have h1 : 16 * K₂ / c₀ ≤ Real.log N := by linarith
    rw [div_le_iff₀ hc₀] at h1
    nlinarith
  · -- `2 K₁ L⁴ ≤ (c₀/16) √P`
    have hs := log_pow_five_div_two_le_sqrt_arcParam hL2
    have h1 : 64 * K₁ / c₀ ≤ Real.log N := by linarith
    rw [div_le_iff₀ hc₀] at h1
    have hL4 : 0 ≤ Real.log N ^ 4 := by positivity
    calc 2 * K₁ * Real.log N ^ 4 ≤ c₀ / 32 * Real.log N * Real.log N ^ 4 :=
          mul_le_mul_of_nonneg_right (by linarith) hL4
      _ = c₀ / 16 * (Real.log N ^ 5 / 2) := by ring
      _ ≤ c₀ / 16 * Real.sqrt (arcParam N) := mul_le_mul_of_nonneg_left hs (by positivity)
  · -- `K₁ L⁴ N^{7/8} ≤ (c₀/16) N`
    have hN8 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by positivity
    have hN78 : (0 : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) := by positivity
    have hsplit : (N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((7 : ℝ) / 8) = N := by
      rw [← Real.rpow_add hNpos]; norm_num
    have hK : K₁ * (c₀ / (16 * (K₁ + 1))) ≤ c₀ / 16 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    calc K₁ * Real.log N ^ 4 * (N : ℝ) ^ ((7 : ℝ) / 8)
        ≤ K₁ * (c₀ / (16 * (K₁ + 1)) * (N : ℝ) ^ ((1 : ℝ) / 8)) * (N : ℝ) ^ ((7 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4N hK₁) hN78
      _ = K₁ * (c₀ / (16 * (K₁ + 1)))
            * ((N : ℝ) ^ ((1 : ℝ) / 8) * (N : ℝ) ^ ((7 : ℝ) / 8)) := by ring
      _ = K₁ * (c₀ / (16 * (K₁ + 1))) * N := by rw [hsplit]
      _ ≤ c₀ / 16 * N := mul_le_mul_of_nonneg_right hK hNpos.le

/-- **Step 7:** for odd `N`, the weighted count is eventually at least `c N²` for some `c > 0`. -/
theorem weightedCount_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Odd N → c * (N : ℝ) ^ 2 ≤ weightedCount N :=
  weightedCount_lower_of_SW Salt.SW.siegelWalfisz_holds

/-- `three_primes` with the Siegel–Walfisz statement as the hypothesis `hSWall`, in place of
the unconditional gate `Salt.SW.siegelWalfisz_holds`. -/
theorem three_primes_of_SW (hSWall : Salt.BV.SiegelWalfisz) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N := by
  obtain ⟨c, hc, hlow⟩ := weightedCount_lower_of_SW hSWall
  obtain ⟨C, hC, hle⟩ := weightedCount_le
  have h3 := eventually_log_pow_le 3 (s := 1 / 2) (by norm_num)
    (ε := c / (2 * (C + 1))) (by positivity)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlow.and (h3.and (eventually_ge_atTop 2)))
  refine ⟨N₀, fun N hN hodd => ?_⟩
  obtain ⟨hl, hlog, h2⟩ := hN₀ N hN.le
  refine exists_three_primes_of_weightedCount hle h2 (lt_of_lt_of_le ?_ (hl hodd))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsplit : (N : ℝ) ^ ((3 : ℝ) / 2) = (N : ℝ) ^ ((1 : ℝ) / 2) * N := by
    rw [show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
  have hNh : 0 < (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hNpos _
  have hsq : (N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 2) = N := by
    rw [← Real.rpow_add hNpos]; norm_num
  have hK : C * (c / (2 * (C + 1))) < c := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  calc C * (N : ℝ) ^ ((3 : ℝ) / 2) * Real.log N ^ 3
      ≤ C * (N : ℝ) ^ ((3 : ℝ) / 2) * (c / (2 * (C + 1)) * (N : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hlog (mul_nonneg hC (by positivity))
    _ = C * (c / (2 * (C + 1))) * ((N : ℝ) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 2)) * N := by
        rw [hsplit]; ring
    _ = C * (c / (2 * (C + 1))) * N * N := by rw [hsq]
    _ < c * N * N := by
        have := mul_lt_mul_of_pos_right hK (mul_pos hNpos hNpos)
        linarith
    _ = c * (N : ℝ) ^ 2 := by ring

/-- **Vinogradov's three-primes theorem:** every sufficiently large odd number is a sum of three
primes. -/
theorem three_primes :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N → Odd N →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = N :=
  three_primes_of_SW Salt.SW.siegelWalfisz_holds

end Salt.ThreePrimes
