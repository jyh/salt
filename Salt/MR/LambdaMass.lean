/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MultShiu
import Salt.MR.Prop21Uniform
import Salt.Maynard.Mertens

/-!
# LAMBDA-MASS — the σ-damped Λ-window masses (A-5a) and the datum hoist (A-7b)

Two independent stones of the `HCENTER` ladder (`docs/exploration/hsup-design.md`,
amendment V2).

## A-5a — the σ-damped Λ-window masses

The two per-leg mass bounds the honest A-5 target
`S₋·S₊ ≤ C·X^β·y^{−2β}·min(L,1/σ)²` consumes, stated on the corpus's own Λ-window
`Finset.Ioo ⌊y⌋₊ ⌈X/y⌉₊` with the corpus's own summand shape
`‖lambdaLin (restrictAbove y g) n‖ / n^c` (`window_mass_eval`, `GrandComp.lean:67`):

* **the damped (high) leg** `c = 1 + σ`, `σ > 0`:
  `∑ ≤ (log 4 + 4)·y^{−σ}·min(L', 2 + 1/σ)`;
* **the shifted (low) leg** `c = 1 − δ`, `0 < δ ≤ 1`:
  `∑ ≤ (log 4 + 4)·(X/y)^δ·min(L', 1 + 2/δ)`,

with `L' := log⌈X/y⌉₊ + (log 4 + 4)` the corpus's Mertens grade (`window_mass_eval`'s
own `L'`) — and the `log X` restatement `L' ≤ log X + (log 4 + 5)` at `1 ≤ y`, `1 ≤ X`.

**The page.**  Both `min` arms run off ONE engine — `abel_master` against Chebyshev
(`Chebyshev.psi_le_const_mul_self`, constant `log 4 + 4`), exactly as the landed
`lambda_partial_alpha`/`lambda_tail_shift` do.

* the `L`-arm is weight-free: on the window `n > y`, so `n^{−σ} ≤ y^{−σ}` (resp.
  `n^{δ} ≤ (X/y)^δ`), and what is left is `∑_{n≤⌈X/y⌉} Λ n/n ≤ L'`
  (`Salt.Maynard.sum_vonMangoldt_div_le`);
* the `1/σ`-arm is the MAX-WEIGHT trick: run `abel_master` against the *globally*
  decreasing weight `w n = (max n y)^{−(1+σ)}` (which agrees with `n^{−(1+σ)}` on the
  window and is ≥ 0 below it), so the Λ-mass is traded for the bare sum
  `∑_{n≤K} (max n y)^{−(1+σ)} ≤ y^{−σ}·(2 + 1/σ)` — the `n ≤ y` block contributes
  `y·y^{−(1+σ)} = y^{−σ}` and the `n > y` block an integral comparison
  `≤ y^{−σ}/σ`.  The `y^{−σ}` damping is *carried by the weight*, which is why only
  the Chebyshev bound `ψ(u) ≤ (log 4+4)·u` is needed — no Mertens lower bound
  (the A(u)-only route loses a full `log y` here; recorded so it is not re-proposed);
* the `1/δ`-arm of the low leg is the landed `lambda_partial_alpha` at `α = 1 − δ`.

## A-7b — the datum hoist

`prop21_unconditional_uniform` (`Prop21Uniform.lean`) already hoists `(C_E, C_R)`
past `X`, but the pair still sits *after* the datum `(g, t₀)`.  A-9 instantiates the
twist at the `X`-dependent centre `t₀ + t₁(X)`, so a `t₀`-dependent constant is
circular.  This file hoists past `(g, t₀)` as well:

  `∃ X₀ C_E C_R, 0 ≤ C_E ∧ 0 ≤ C_R ∧ ∀ g, (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ t₀, ∀ {X h c₀ y η}, …`

**The gate (refuter's open link, checked):** `ms_b_smooth_factor`'s witness
(`MultShiu.lean:1908`) is `exp(M + Cm/log 8 + (e−1) + (e−1)(log 4+4)/log 8 +
4(1 + 1/(β₀−1)))` with `β₀ = 2 − 2/log 8` and `(M, Cm)` from
`Salt.Mertens.mertens_second_sharp` — numerals and Mertens constants only: **datum-free**.
Same for `mult_shiu_MS_A`'s (`:1434`) and `mult_shiu_MS_B`'s (`:2220`).

**The route taken is cheaper than re-running those proofs**: every `g`-dependence in
the MS-EXIT integrand is a *norm of a linearized carrier*, and each such norm is
majorized termwise by its `g ≡ 1` value (`norm_ellLin_le_of_norm_le`,
`norm_lambdaLin_le_of_norm_le`).  So the hoisted constant is simply the landed
`mult_shiu_MS_EXIT` constant AT `g ≡ 1`, and the general datum is dominated into it.
No landed line is edited.
-/

namespace Salt.MR

open Complex MeasureTheory Set
open ArithmeticFunction
open scoped BigOperators

/-! ## A-7b — the datum hoist -/

/-! ### Termwise majorization of the linearized carriers -/

/-- **Carrier monotonicity (`ellLin`).**  If `‖d p‖ ≤ ‖e p‖` at every prime then
`‖ellLin d n‖ ≤ ‖ellLin e n‖` at every `n`: on squarefree `n` both sides are products
over `n.primeFactors`, elsewhere both vanish. -/
theorem norm_ellLin_le_of_norm_le {d e : ℕ → ℂ} (h : ∀ p, p.Prime → ‖d p‖ ≤ ‖e p‖) (n : ℕ) :
    ‖ellLin d n‖ ≤ ‖ellLin e n‖ := by
  unfold ellLin
  by_cases hn : n = 0
  · simp [hn]
  · by_cases hsq : Squarefree n
    · simp only [if_neg hn, if_pos hsq, norm_prod]
      exact Finset.prod_le_prod (fun p _ => norm_nonneg _)
        (fun p hp => h p (Nat.prime_of_mem_primeFactors hp))
    · simp [hn, hsq]

/-- **Carrier monotonicity (`lambdaLin`).**  If `‖d p‖ ≤ ‖e p‖` at every prime then
`‖lambdaLin d n‖ ≤ ‖lambdaLin e n‖` at every `n`: on a prime power both sides are
`‖·(minFac)‖^k·|log minFac|`, elsewhere both vanish. -/
theorem norm_lambdaLin_le_of_norm_le {d e : ℕ → ℂ} (h : ∀ p, p.Prime → ‖d p‖ ≤ ‖e p‖) (n : ℕ) :
    ‖lambdaLin d n‖ ≤ ‖lambdaLin e n‖ := by
  unfold lambdaLin
  by_cases hn : IsPrimePow n
  · simp only [if_pos hn, norm_mul, norm_pow, norm_neg, norm_one, one_pow]
    have hprime : (n.minFac).Prime := Nat.minFac_prime hn.ne_one
    gcongr
    exact h _ hprime
  · simp [hn]

/-- The below-cutoff datum is dominated by the all-ones below-cutoff datum. -/
theorem norm_restrictBelow_le_one (y : ℝ) {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    ∀ p, p.Prime → ‖restrictBelow y g p‖ ≤ ‖restrictBelow y (fun _ => (1 : ℂ)) p‖ := by
  intro p hp
  unfold restrictBelow
  by_cases hy : (p : ℝ) ≤ y
  · simp only [if_pos hy, norm_one]; exact hg p hp
  · simp [hy]

/-- The above-cutoff datum is dominated by the all-ones above-cutoff datum. -/
theorem norm_restrictAbove_le_one (y : ℝ) {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    ∀ p, p.Prime → ‖restrictAbove y g p‖ ≤ ‖restrictAbove y (fun _ => (1 : ℂ)) p‖ := by
  intro p hp
  unfold restrictAbove
  by_cases hy : y < (p : ℝ)
  · simp only [if_pos hy, norm_one]; exact hg p hp
  · simp [hy]

/-! ### The MS-B integrand is continuous (hence interval-integrable) -/

/-- The MS-B `α`-integrand is continuous: a finite sum of terms
`A·(B/k^α)·C/n^(c+α)` with `k, n ≥ 1`. -/
theorem msB_integrand_continuous (d : ℕ → ℂ) (x y : ℝ) :
    Continuous fun α : ℝ =>
      ∑ q ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter
          (fun q => q.1 * q.2.1 * q.2.2 ≤ ⌊x⌋₊),
        ‖ellLin (restrictBelow y d) q.1‖
          * (‖lambdaLin (restrictAbove y d) q.2.1‖ / (q.2.1 : ℝ) ^ α)
          * ‖ellLin (restrictAbove y d) q.2.2‖
            / (q.2.2 : ℝ) ^ (2 * (1 / Real.log y) + α) := by
  refine continuous_finsetSum _ (fun q hq => ?_)
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
  have hk : (0 : ℝ) < (q.2.1 : ℝ) := by
    have : 1 ≤ q.2.1 := hq.1.2.1.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hn : (0 : ℝ) < (q.2.2 : ℝ) := by
    have : 1 ≤ q.2.2 := hq.1.2.2.1
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have h1 : Continuous fun α : ℝ => (q.2.1 : ℝ) ^ α := by
    simp only [Real.rpow_def_of_pos hk]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun α : ℝ => (q.2.2 : ℝ) ^ (2 * (1 / Real.log y) + α) := by
    simp only [Real.rpow_def_of_pos hn]
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_const.add continuous_id))
  exact ((continuous_const.mul
      (continuous_const.div h1 (fun α => ne_of_gt (Real.rpow_pos_of_pos hk α)))).mul
    continuous_const).div h2 (fun α => ne_of_gt (Real.rpow_pos_of_pos hn _))

/-! ### THE STONE — MS-EXIT with the constant BEFORE the datum -/

/-- **A-7b (i) — `mult_shiu_MS_EXIT_const`.**  The GHS-(2.4) secondary-term discharge
with the constant hoisted past the datum `g`:

  `∃ C_E, ∀ g, (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ x y, 8 ≤ y → y ≤ x → … ≤ C_E·(x/log x)·log y`.

Statement, hypotheses and conclusion are byte-identical to `mult_shiu_MS_EXIT`'s; only
the binder order changes.  The witness is the landed constant AT the all-ones datum;
the general datum is dominated into it termwise (`norm_ellLin_le_of_norm_le`,
`norm_lambdaLin_le_of_norm_le`), the `α`-integral by `integral_mono_on` against the
continuity of both integrands. -/
theorem mult_shiu_MS_EXIT_const :
    ∃ C_E : ℝ, ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (x y : ℝ), 8 ≤ y → y ≤ x →
      (∑ q ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter (fun q => q.1 * q.2 ≤ ⌊x⌋₊),
            ‖ellLin (restrictBelow y g) q.1‖ * ‖ellLin (restrictAbove y g) q.2‖
              / (q.2 : ℝ) ^ (1 / Real.log y))
          + (∫ α in (0 : ℝ)..(1 / Real.log y),
              ∑ q ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter
                  (fun q => q.1 * q.2.1 * q.2.2 ≤ ⌊x⌋₊),
                ‖ellLin (restrictBelow y g) q.1‖
                  * (‖lambdaLin (restrictAbove y g) q.2.1‖ / (q.2.1 : ℝ) ^ α)
                  * ‖ellLin (restrictAbove y g) q.2.2‖
                    / (q.2.2 : ℝ) ^ (2 * (1 / Real.log y) + α))
        ≤ C_E * (x / Real.log x) * Real.log y := by
  classical
  have hone : ∀ p : ℕ, p.Prime → ‖(fun _ => (1 : ℂ)) p‖ ≤ 1 := by intro p _; simp
  obtain ⟨C_E, hC_E⟩ := mult_shiu_MS_EXIT (fun _ => (1 : ℂ)) hone
  refine ⟨C_E, fun g hg x y hy hyx => ?_⟩
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hη0 : (0 : ℝ) ≤ 1 / Real.log y := by positivity
  have hbelow := norm_restrictBelow_le_one y hg
  have habove := norm_restrictAbove_le_one y hg
  refine le_trans (add_le_add ?_ ?_) (hC_E x y hy hyx)
  · -- Term 1: termwise domination
    refine Finset.sum_le_sum (fun q _ => ?_)
    gcongr
    · exact norm_ellLin_le_of_norm_le hbelow q.1
    · exact norm_ellLin_le_of_norm_le habove q.2
  · -- Term 2: termwise domination under the integral
    refine intervalIntegral.integral_mono_on hη0
      ((msB_integrand_continuous g x y).intervalIntegrable _ _)
      ((msB_integrand_continuous (fun _ => (1 : ℂ)) x y).intervalIntegrable _ _)
      (fun α _ => ?_)
    refine Finset.sum_le_sum (fun q _ => ?_)
    gcongr
    · exact norm_ellLin_le_of_norm_le hbelow q.1
    · exact norm_lambdaLin_le_of_norm_le habove q.2.1
    · exact norm_ellLin_le_of_norm_le habove q.2.2

/-! ### THE STONE — the S1′ representation with the constants BEFORE the datum -/

/-- **The `log⁴ = o(√X)` threshold (∃-packaged)** — `Prop21Uniform`'s private helper
`logpow4_le_sqrt_ev`, re-stated verbatim here (a `private` declaration is not visible
across modules).  There is an `X₁` beyond which `(log X)⁴ ≤ √X/2`. -/
private lemma logpow4_le_sqrt_ev' :
    ∃ X₁ : ℝ, ∀ X : ℝ, X₁ ≤ X → (Real.log X) ^ 4 ≤ Real.sqrt X / 2 := by
  have hlo : (fun x : ℝ => Real.log x ^ (4 : ℝ)) =o[Filter.atTop] fun x : ℝ => x ^ (1 / 2 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound := hlo.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Filter.eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max a 1, fun X hX => ?_⟩
  have hXa : a ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hkey := ha X hXa
  have h1nn : (0 : ℝ) ≤ Real.log X ^ (4 : ℝ) := Real.rpow_nonneg hlogXnn 4
  have h2nn : (0 : ℝ) ≤ X ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h1nn, Real.norm_of_nonneg h2nn,
    show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    ← Real.sqrt_eq_rpow] at hkey
  linarith [hkey]

/-- **A-7b (ii) — `prop21_unconditional_uniform_absC`: the S1′ representation with the
E-constants outside the `X`-quantifier AND outside the datum.**  The A-9-ready form of
`prop21_unconditional_uniform`: ONE triple `(X₀, C_E, C_R)` valid for EVERY 1-bounded
datum `g`, EVERY twist centre `t₀`, and every scale `X ≥ X₀` simultaneously.

This is what A-9 needs: it instantiates the twist at the `X`-dependent ball centre
`t₀ + t₁(X)`, so a `t₀`-dependent constant would be circular.

Gates, hypotheses and conclusion are byte-identical to `prop21_unconditional_uniform`'s;
only the binder order changes.  Provenance: `C_E = max C_E' 0` with `C_E'` from
`mult_shiu_MS_EXIT_const` (datum-free by the majorization at `g ≡ 1`), and
`C_R = 32·C_cheb` with `C_cheb` the short-interval Chebyshev constant of
`shortInterval_vonMangoldt_le` (a numeral: `250`, so `C_R = 8000`). -/
theorem prop21_unconditional_uniform_absC :
    ∃ X₀ C_E C_R : ℝ, 0 ≤ C_E ∧ 0 ≤ C_R ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ : ℝ),
      ∀ {X h c₀ y η : ℝ}, X₀ ≤ X →
        h = X / Real.sqrt (Real.log X) → 1 < c₀ → η = 1 / Real.log y →
        0 < c₀ - 2 * η → 10 ≤ y → y ≤ Real.sqrt X → Real.sqrt (Real.log X) ≤ y →
      ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n * (hatK X h n : ℂ))
          - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X h c₀ y η‖
        ≤ C_E * ((X + h) / Real.log (X + h)) * Real.log y
          + C_R * (X / Real.log X) * Real.log y := by
  -- ALL THREE constants are obtained BEFORE the datum and before any scale is named
  obtain ⟨Cc, hCc0, hCbound⟩ := shortInterval_vonMangoldt_le
  obtain ⟨X₁, hX₁⟩ := logpow4_le_sqrt_ev'
  obtain ⟨C_E, hCEall⟩ := mult_shiu_MS_EXIT_const
  refine ⟨max X₁ 17179869184, max C_E 0, 32 * Cc, le_max_right _ _, by linarith, ?_⟩
  intro g hg t₀ X h c₀ y η hXlb hh hc₀ hη hc' hy10 hyX hygate
  have hgtw : ∀ p, p.Prime → ‖(fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀ hp.one_lt.le, mul_one]
    exact hg p hp
  have hCE := hCEall (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) hgtw
  -- outer-regime facts
  have hXbig : (17179869184 : ℝ) ≤ X := le_trans (le_max_right _ _) hXlb
  have hXX₁ : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hX : Real.exp 1 ≤ X :=
    (Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 17179869184)).trans hXbig
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hsqlogX : (0 : ℝ) < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr (by linarith)
  have hsqge1 : (1 : ℝ) ≤ Real.sqrt (Real.log X) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlogX1
  have hh0 : (0 : ℝ) < h := by rw [hh]; exact div_pos hXpos hsqlogX
  have hhX : h ≤ X := by rw [hh, div_le_iff₀ hsqlogX]; nlinarith [hsqge1, hXpos]
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : (0 : ℝ) < Real.log y := Real.log_pos (by linarith)
  have hexp10 : Real.exp 1 ≤ 10 := by linarith [Real.exp_one_lt_three]
  have hylog1 : (1 : ℝ) ≤ Real.log y := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (le_trans hexp10 hy10)
  have hη0 : (0 : ℝ) ≤ η := by rw [hη]; exact le_of_lt (div_pos one_pos hlogy)
  have hη1 : η ≤ 1 := by rw [hη, div_le_one hlogy]; exact hylog1
  -- the per-window regime, then THE GRAIN at the uniform Chebyshev constant
  have hreg := window_regime_of_large hXbig (hX₁ X hXX₁) hh hy10 hyX
  have hgrain : ∀ l ∈ Finset.Ioc ⌊y⌋₊ ⌊y + y * h / X⌋₊,
      (∑ k ∈ Finset.Ioc ⌊X / (l : ℝ)⌋₊ ⌊(X + h) / (l : ℝ)⌋₊, vonMangoldt k)
        ≤ Cc * (h / (l : ℝ)) := by
    intro l hl
    obtain ⟨h1, h2, h3⟩ := hreg l hl
    have hkey := hCbound (X / (l : ℝ)) (h / (l : ℝ)) h1 h2 h3
    rwa [show (X + h) / (l : ℝ) = X / (l : ℝ) + h / (l : ℝ) from add_div X h (l : ℝ)]
  -- the ramp leg at the explicit constant, then the norm bridge
  have hmass := ramp_sliver_bound_const (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) hgtw
    hX hh hy10 hygate hCc0 hgrain
  have hsliver : ‖rampTerm (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) X h y η‖
      ≤ 8 * (4 * Cc * (X / Real.log X) * Real.log y) :=
    le_trans (ramp_norm_le_sliverMass y (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I))
      hy0 hXpos hh0 hhX hη0 hη1) (mul_le_mul_of_nonneg_left hmass (by norm_num))
  -- the S1′ representation at the hoisted E-constant
  have hmain := prop21_unconditional_ofC g hg t₀
    (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) rfl hX1 hh0 hc₀ hη hc' hy10 hyX hCE hsliver
  refine le_trans hmain ?_
  -- bump `C_E` to `max C_E 0` (the head factor is nonnegative) and reassociate `C_R`
  have hXh1 : (1 : ℝ) < X + h := by linarith
  have hlogXh : (0 : ℝ) < Real.log (X + h) := Real.log_pos hXh1
  have hA : (0 : ℝ) ≤ (X + h) / Real.log (X + h) * Real.log y :=
    mul_nonneg (div_nonneg (by linarith) hlogXh.le) hlogy.le
  have hbump : C_E * ((X + h) / Real.log (X + h)) * Real.log y
      ≤ max C_E 0 * ((X + h) / Real.log (X + h)) * Real.log y := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left C_E 0) hA
  linarith [hbump]

/-- **A-7b (iii) — `prop21_uniform_at_scale_absC`.**  The datum-hoisted uniform bound at
the freeze's recommended pin

  `h = X/√(log X)`,  `c₀ = 1 + 1/log X`,  `y = (log X)^4`,  `η = 1/log y`,

with every gate discharged from the single threshold `X₀` (so the consumer supplies only
`X₀ ≤ X`).  Same gate page as `prop21_uniform_at_scale`; the only change is that
`(X₀, C_E, C_R)` now precede `(g, t₀)`. -/
theorem prop21_uniform_at_scale_absC :
    ∃ X₀ C_E C_R : ℝ, 0 ≤ C_E ∧ 0 ≤ C_R ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ : ℝ), ∀ X : ℝ, X₀ ≤ X →
      ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n
            * (hatK X (X / Real.sqrt (Real.log X)) n : ℂ))
          - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X
              (X / Real.sqrt (Real.log X)) (1 + 1 / Real.log X) (Real.log X ^ 4)
              (1 / Real.log (Real.log X ^ 4))‖
        ≤ C_E * ((X + X / Real.sqrt (Real.log X))
              / Real.log (X + X / Real.sqrt (Real.log X))) * Real.log (Real.log X ^ 4)
          + C_R * (X / Real.log X) * Real.log (Real.log X ^ 4) := by
  obtain ⟨X₀, C_E, C_R, hCE0, hCR0, hbound⟩ := prop21_unconditional_uniform_absC
  obtain ⟨X₁, hX₁⟩ := logpow4_le_sqrt_ev'
  refine ⟨max (max X₀ X₁) (Real.exp 2), C_E, C_R, hCE0, hCR0, ?_⟩
  intro g hg t₀ X hXlb
  have hX₀ : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXX₁ : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hXe2 : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXe2
  -- `log X ≥ 2`, hence `log log X ≥ log 2 > 1/2`
  have hL2 : (2 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hXe2
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hLL : Real.log (Real.log X ^ 4) = 4 * Real.log (Real.log X) := by
    rw [Real.log_pow]; norm_num
  have hlogL : Real.log 2 ≤ Real.log (Real.log X) := Real.log_le_log (by norm_num) hL2
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLLpos : (0 : ℝ) < Real.log (Real.log X) := by linarith
  -- the gates
  have hc₀ : (1 : ℝ) < 1 + 1 / Real.log X := by
    have hpos : (0 : ℝ) < 1 / Real.log X := by positivity
    linarith
  have hy10 : (10 : ℝ) ≤ Real.log X ^ 4 := by
    have h2 : (4 : ℝ) ≤ Real.log X * Real.log X := by nlinarith
    nlinarith [h2, sq_nonneg (Real.log X * Real.log X - 4)]
  have hyX : Real.log X ^ 4 ≤ Real.sqrt X := by
    have hkey := hX₁ X hXX₁
    have h0 : (0 : ℝ) ≤ Real.sqrt X := Real.sqrt_nonneg X
    linarith
  have hygate : Real.sqrt (Real.log X) ≤ Real.log X ^ 4 := by
    have hL1 : (1 : ℝ) ≤ Real.log X := by linarith
    have h8 : Real.log X ≤ (Real.log X ^ 4) ^ 2 := by
      rw [show (Real.log X ^ 4) ^ 2 = Real.log X ^ 8 by ring]
      exact le_self_pow₀ hL1 (by norm_num)
    calc Real.sqrt (Real.log X) ≤ Real.sqrt ((Real.log X ^ 4) ^ 2) := Real.sqrt_le_sqrt h8
      _ = Real.log X ^ 4 := Real.sqrt_sq (by positivity)
  have hc' : (0 : ℝ) < 1 + 1 / Real.log X - 2 * (1 / Real.log (Real.log X ^ 4)) := by
    rw [hLL]
    have h1 : 2 * (1 / (4 * Real.log (Real.log X))) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    have h2 : (0 : ℝ) < 1 / Real.log X := by positivity
    linarith
  exact hbound g hg t₀ (X := X) (h := X / Real.sqrt (Real.log X)) (c₀ := 1 + 1 / Real.log X)
    (y := Real.log X ^ 4) (η := 1 / Real.log (Real.log X ^ 4))
    hX₀ rfl hc₀ rfl hc' hy10 hyX hygate

/-! ## A-5a — the σ-damped Λ-window masses -/

/-! ### rpow plumbing -/

/-- Base antitonicity at a nonpositive exponent: `a ≤ b ⟹ b^{−c} ≤ a^{−c}` for `0 < a`,
`0 ≤ c`. -/
theorem rpow_neg_le_rpow_neg_of_le {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) :
    b ^ (-c) ≤ a ^ (-c) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg (by linarith)]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha c) (Real.rpow_le_rpow ha.le hab hc)

/-- `y·y^{−(1+a)} = y^{−a}` for `0 < y`. -/
theorem mul_rpow_neg_one_add {y a : ℝ} (hy : 0 < y) : y * y ^ (-(1 + a)) = y ^ (-a) := by
  rw [show (-a : ℝ) = 1 + -(1 + a) by ring, Real.rpow_add hy, Real.rpow_one]

/-! ### The max-weight bare sum — where the `y^{−σ}` damping is manufactured -/

/-- **The max-weight bare sum.**  For `1 ≤ y` and `0 < σ`,

  `∑_{i<K} (max (i+1) y)^{−(1+σ)} ≤ y^{−σ}·(2 + 1/σ)`.

The two blocks: `i+1 ≤ y` contributes `⌊y⌋·y^{−(1+σ)} ≤ y^{−σ}`, and `i+1 > y`
contributes its first term (`≤ y^{−σ}`) plus an integral comparison
(`AntitoneOn.sum_le_integral_Ico`, `∫_{⌊y⌋+1}^K t^{−(1+σ)} ≤ y^{−σ}/σ`).

This is the whole content of the `1/σ` arm: the weight is globally decreasing, so
`abel_master` trades the Λ-mass for it against Chebyshev alone — no Mertens lower bound
is needed (the `A(u) = ∑Λ/n ≤ log u + C` route loses a full `log y` at this step). -/
theorem sum_range_maxpow_le {y σ : ℝ} (hy : 1 ≤ y) (hσ : 0 < σ) (K : ℕ) :
    (∑ i ∈ Finset.range K, (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)))
      ≤ y ^ (-σ) * (2 + 1 / σ) := by
  have hy0 : (0 : ℝ) < y := by linarith
  set m : ℕ := ⌊y⌋₊ with hmdef
  have hmy : (m : ℝ) ≤ y := Nat.floor_le hy0.le
  have hym : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
  have hypos : (0 : ℝ) < y ^ (-σ) := Real.rpow_pos_of_pos hy0 _
  have hσinv : (0 : ℝ) < 1 / σ := by positivity
  -- the flat-block value
  have hflatval : y ^ (-(1 + σ)) ≤ y ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hflatnn : (0 : ℝ) ≤ y ^ (-(1 + σ)) := Real.rpow_nonneg hy0.le _
  have hblockA : (m : ℝ) * y ^ (-(1 + σ)) ≤ y ^ (-σ) := by
    have h1 : (m : ℝ) * y ^ (-(1 + σ)) ≤ y * y ^ (-(1 + σ)) := by nlinarith
    rw [mul_rpow_neg_one_add hy0] at h1
    exact h1
  rcases le_or_gt K m with hKm | hmK
  · -- every index sits in the flat block
    have hflat : ∀ i ∈ Finset.range K,
        (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)) = y ^ (-(1 + σ)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have hle : ((i + 1 : ℕ) : ℝ) ≤ y := by
        have h1 : i + 1 ≤ m := by omega
        have h2 : ((i + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
        linarith
      rw [max_eq_right hle]
    rw [Finset.sum_congr rfl hflat, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hKle : (K : ℝ) ≤ (m : ℝ) := by exact_mod_cast hKm
    nlinarith
  · -- the flat block, then the decaying block
    have hcons := Finset.sum_Ico_consecutive
      (fun i => (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ))) (Nat.zero_le m) (le_of_lt hmK)
    rw [Finset.range_eq_Ico, ← hcons]
    -- block A: the flat part
    have hA : (∑ i ∈ Finset.Ico 0 m, (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ))) ≤ y ^ (-σ) := by
      have hflat : ∀ i ∈ Finset.Ico 0 m,
          (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)) = y ^ (-(1 + σ)) := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hle : ((i + 1 : ℕ) : ℝ) ≤ y := by
          have h1 : i + 1 ≤ m := by omega
          have h2 : ((i + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
          linarith
        rw [max_eq_right hle]
      rw [Finset.sum_congr rfl hflat, Finset.sum_const, Nat.card_Ico, Nat.sub_zero,
        nsmul_eq_mul]
      exact hblockA
    -- block B: the decaying part, first term split off
    have hbot := Finset.sum_eq_sum_Ico_succ_bot hmK
      (fun i => (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)))
    have hm1 : y ≤ ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hm1pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hfirst : (max ((m + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)) ≤ y ^ (-σ) := by
      rw [max_eq_left hm1]
      exact le_trans (rpow_neg_le_rpow_neg_of_le hy0 hm1 (by linarith)) hflatval
    -- the tail: strip the `max` and compare with the integral
    have htail : (∑ i ∈ Finset.Ico (m + 1) K, (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)))
        ≤ y ^ (-σ) * (1 / σ) := by
      have hstrip : ∀ i ∈ Finset.Ico (m + 1) K,
          (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)) = ((i + 1 : ℕ) : ℝ) ^ (-(1 + σ)) := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hge : ((m + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
          have : m + 1 ≤ i + 1 := by omega
          exact_mod_cast this
        rw [max_eq_left (le_trans hm1 hge)]
      rw [Finset.sum_congr rfl hstrip]
      have hmK1 : m + 1 ≤ K := hmK
      have hanti : AntitoneOn (fun t : ℝ => t ^ (-(1 + σ)))
          (Set.Icc ((m + 1 : ℕ) : ℝ) (K : ℝ)) := by
        intro s hs t _ hst
        exact rpow_neg_le_rpow_neg_of_le (lt_of_lt_of_le hm1pos hs.1) hst (by linarith)
      have hcmp := AntitoneOn.sum_le_integral_Ico hmK1 hanti
      have hKr : ((m + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK1
      have hint : (∫ t in ((m + 1 : ℕ) : ℝ)..(K : ℝ), t ^ (-(1 + σ)))
          = ((K : ℝ) ^ (-σ) - ((m + 1 : ℕ) : ℝ) ^ (-σ)) / (-σ) := by
        rw [integral_rpow (Or.inr ⟨by intro h; linarith, by
            rw [Set.uIcc_of_le hKr]; intro h; rw [Set.mem_Icc] at h; linarith [h.1]⟩),
          show (-(1 + σ) + 1 : ℝ) = -σ from by ring]
      rw [hint] at hcmp
      refine le_trans hcmp ?_
      have hKnn : (0 : ℝ) ≤ (K : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hm1le : ((m + 1 : ℕ) : ℝ) ^ (-σ) ≤ y ^ (-σ) :=
        rpow_neg_le_rpow_neg_of_le hy0 hm1 hσ.le
      rw [div_neg, ← neg_div, neg_sub, div_le_iff₀ hσ]
      have : y ^ (-σ) * (1 / σ) * σ = y ^ (-σ) := by field_simp
      rw [this]
      linarith
    rw [hbot]
    linarith

/-! ### The window facts -/

/-- The corpus's Λ-window (`winCoeff`, `window_mass_eval`) is `⌊y⌋ < n < ⌈X/y⌉`: every
member is `≥ 1`, exceeds `y`, and stays strictly below `X/y`. -/
theorem mem_lambda_window {X y : ℝ} {n : ℕ} (hn : n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊) :
    1 ≤ n ∧ y < (n : ℝ) ∧ (n : ℝ) < X / y := by
  rw [Finset.mem_Ioo] at hn
  refine ⟨by omega, ?_, Nat.lt_ceil.mp hn.2⟩
  have h1 : (⌊y⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn.1
  linarith [Nat.lt_floor_add_one y]

/-- The window sits inside `(0, ⌈X/y⌉]`, where `Salt.Maynard.sum_vonMangoldt_div_le`
lives. -/
theorem lambda_window_subset_Ioc {X y : ℝ} :
    Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ ⊆ Finset.Ioc 0 ⌈X / y⌉₊ := by
  intro n hn; rw [Finset.mem_Ioo] at hn; rw [Finset.mem_Ioc]; omega

/-- The window sits inside `[1, ⌈X/y⌉]`, the `abel_master` range. -/
theorem lambda_window_subset_Icc {X y : ℝ} :
    Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ ⊆ Finset.Icc 1 ⌈X / y⌉₊ := by
  intro n hn; rw [Finset.mem_Ioo] at hn; rw [Finset.mem_Icc]; omega

/-- The window's Mertens grade `L' = log⌈X/y⌉ + (log 4 + 4)` is positive. -/
theorem window_grade_pos {X y : ℝ} :
    (0 : ℝ) < Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rcases Nat.eq_zero_or_pos ⌈X / y⌉₊ with hK | hK
  · rw [hK]; norm_num; linarith
  · have h1 : (1 : ℝ) ≤ (⌈X / y⌉₊ : ℝ) := by exact_mod_cast hK
    have := Real.log_nonneg h1
    linarith

/-- **The `log X` restatement of the window grade.**  At `1 ≤ y ≤ X` the corpus grade
`L' = log⌈X/y⌉ + (log 4 + 4)` is `≤ log X + (log 4 + 5)` — the `min(log X, 1/σ)` shape
of the design block. -/
theorem window_grade_le_logX {X y : ℝ} (hy : 1 ≤ y) (hX : 1 ≤ X) :
    Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4) ≤ Real.log X + (Real.log 4 + 5) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy : X / y ≤ X := by
    rw [div_le_iff₀ hy0]; nlinarith
  have hceil : ((⌈X / y⌉₊ : ℕ) : ℝ) ≤ X + 1 := by
    have h1 : ((⌈X / y⌉₊ : ℕ) : ℝ) < X / y + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hlog : Real.log ((⌈X / y⌉₊ : ℕ) : ℝ) ≤ Real.log (2 * X) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog2X : Real.log (2 * X) = Real.log 2 + Real.log X := by
    rw [Real.log_mul (by norm_num) (by linarith)]
  have hlt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  linarith

/-! ### The damped (high) leg — `c = 1 + σ` -/

/-- **A-5a (a), the `L` arm.**  On the window `n > y`, so the σ-damping is uniform and
what is left is the Mertens grade:

  `∑_{⌊y⌋<n<⌈X/y⌉} Λ(n)·n^{−1−σ} ≤ y^{−σ}·(log⌈X/y⌉ + (log 4 + 4))`. -/
theorem vonMangoldt_window_damped_log {X y σ : ℝ} (hy : 1 ≤ y) (hσ : 0 ≤ σ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 + σ))
      ≤ y ^ (-σ) * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hypow : (0 : ℝ) < y ^ (-σ) := Real.rpow_pos_of_pos hy0 _
  rcases Nat.eq_zero_or_pos ⌈X / y⌉₊ with hK0 | hK1
  · have hempty : Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ = ∅ := by
      rw [hK0]; exact Finset.Ioo_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    nlinarith [window_grade_pos (X := X) (y := y)]
  · have hstep : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        (Λ n : ℝ) / (n : ℝ) ^ (1 + σ) ≤ y ^ (-σ) * ((Λ n : ℝ) / (n : ℝ)) := by
      intro n hn
      obtain ⟨_, hny, _⟩ := mem_lambda_window hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnn : (0 : ℝ) ≤ (Λ n : ℝ) / (n : ℝ) :=
        div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
      rw [Real.rpow_add hnpos, Real.rpow_one, ← div_div,
        show (Λ n : ℝ) / (n : ℝ) / (n : ℝ) ^ σ = ((Λ n : ℝ) / (n : ℝ)) * (n : ℝ) ^ (-σ) from by
          rw [Real.rpow_neg hnpos.le, div_eq_mul_inv],
        mul_comm (y ^ (-σ))]
      exact mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg_of_le hy0 hny.le hσ) hnn
    calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 + σ))
        ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, y ^ (-σ) * ((Λ n : ℝ) / (n : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = y ^ (-σ) * ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ y ^ (-σ) * ∑ n ∈ Finset.Ioc 0 ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            lambda_window_subset_Ioc (fun n _ _ =>
              div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n))) hypow.le
      _ ≤ y ^ (-σ) * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left (Salt.Maynard.sum_vonMangoldt_div_le hK1) hypow.le

/-- **A-5a (a), the `1/σ` arm.**  The max-weight Abel run:

  `∑_{⌊y⌋<n<⌈X/y⌉} Λ(n)·n^{−1−σ} ≤ (log 4 + 4)·y^{−σ}·(2 + 1/σ)`. -/
theorem vonMangoldt_window_damped_inv {X y σ : ℝ} (hy : 1 ≤ y) (hσ : 0 < σ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 + σ))
      ≤ (Real.log 4 + 4) * (y ^ (-σ) * (2 + 1 / σ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hmaxpos : ∀ n : ℕ, (0 : ℝ) < max ((n : ℕ) : ℝ) y :=
    fun n => lt_of_lt_of_le hy0 (le_max_right _ _)
  set f : ℕ → ℝ := fun n => (max ((n : ℕ) : ℝ) y) ^ (-(1 + σ)) * (Λ n : ℝ) with hfdef
  have hfnn : ∀ n, 0 ≤ f n := fun n =>
    mul_nonneg (Real.rpow_nonneg (hmaxpos n).le _) vonMangoldt_nonneg
  have hcong : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 + σ) = f n := by
    intro n hn
    obtain ⟨_, hny, _⟩ := mem_lambda_window hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    rw [hfdef]
    simp only
    rw [max_eq_left hny.le, Real.rpow_neg hnpos.le, div_eq_mul_inv, mul_comm]
  calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 + σ))
      = ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, f n := Finset.sum_congr rfl hcong
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌈X / y⌉₊, f n :=
        Finset.sum_le_sum_of_subset_of_nonneg lambda_window_subset_Icc (fun n _ _ => hfnn n)
    _ = ∑ i ∈ Finset.range ⌈X / y⌉₊, f (i + 1) := sum_Icc_one_eq_sum_range f _
    _ ≤ (Real.log 4 + 4)
          * ∑ i ∈ Finset.range ⌈X / y⌉₊, (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ)) :=
        abel_master (a := fun i => (Λ (i + 1) : ℝ))
          (w := fun i => (max ((i + 1 : ℕ) : ℝ) y) ^ (-(1 + σ))) (c := Real.log 4 + 4) _
          (fun m => by
            rw [sum_range_vonMangoldt_succ]
            exact Chebyshev.psi_le_const_mul_self (by positivity))
          (fun i => rpow_neg_le_rpow_neg_of_le (hmaxpos (i + 1))
            (max_le_max (by exact_mod_cast Nat.le_succ (i + 1)) le_rfl) (by linarith))
          (fun i => Real.rpow_nonneg (hmaxpos (i + 1)).le _)
    _ ≤ (Real.log 4 + 4) * (y ^ (-σ) * (2 + 1 / σ)) := by
        have hc : (0 : ℝ) ≤ Real.log 4 + 4 := by
          have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
        exact mul_le_mul_of_nonneg_left (sum_range_maxpow_le hy hσ _) hc

/-- **A-5a (a) — THE DAMPED LEG.**  For `1 ≤ y`, `0 < σ` and any exponent `c = 1 + σ`,

  `∑_{⌊y⌋<n<⌈X/y⌉} Λ(n)/n^c ≤ (log 4 + 4)·y^{−σ}·min(L', 2 + 1/σ)`,

`L' = log⌈X/y⌉ + (log 4 + 4)`.  This is the honest `min(log X, 1/σ)` of the design
block (use `window_grade_le_logX` for the `log X` face). -/
theorem vonMangoldt_window_damped_min {X y c σ : ℝ} (hy : 1 ≤ y) (hσ : 0 < σ)
    (hc : c = 1 + σ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ c)
      ≤ (Real.log 4 + 4) * y ^ (-σ)
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) := by
  subst hc
  have hy0 : (0 : ℝ) < y := by linarith
  have hypow : (0 : ℝ) < y ^ (-σ) := Real.rpow_pos_of_pos hy0 _
  have hc4 : (1 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  rcases le_total (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) with hmin | hmin
  · rw [min_eq_left hmin]
    have hL := vonMangoldt_window_damped_log (X := X) hy hσ.le
    have hbump : y ^ (-σ) * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4))
        ≤ (Real.log 4 + 4) * y ^ (-σ) * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) := by
      refine mul_le_mul_of_nonneg_right ?_ window_grade_pos.le
      nlinarith
    linarith
  · rw [min_eq_right hmin]
    have hI := vonMangoldt_window_damped_inv (X := X) hy hσ
    nlinarith

/-! ### The shifted (low) leg — `c = 1 − δ` -/

/-- **A-5a (b), the `L` arm.**  On the window `n < X/y`, so the `δ`-shift is uniform:

  `∑_{⌊y⌋<n<⌈X/y⌉} Λ(n)·n^{−1+δ} ≤ (X/y)^δ·(log⌈X/y⌉ + (log 4 + 4))`. -/
theorem vonMangoldt_window_shifted_log {X y δ : ℝ} (hy : 1 ≤ y) (hX : 0 ≤ X) (hδ : 0 ≤ δ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 - δ))
      ≤ (X / y) ^ δ * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy0 : (0 : ℝ) ≤ X / y := by positivity
  have hXypow : (0 : ℝ) ≤ (X / y) ^ δ := Real.rpow_nonneg hXy0 _
  rcases Nat.eq_zero_or_pos ⌈X / y⌉₊ with hK0 | hK1
  · have hempty : Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊ = ∅ := by
      rw [hK0]; exact Finset.Ioo_eq_empty (by omega)
    rw [hempty, Finset.sum_empty]
    nlinarith [window_grade_pos (X := X) (y := y)]
  · have hstep : ∀ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        (Λ n : ℝ) / (n : ℝ) ^ (1 - δ) ≤ (X / y) ^ δ * ((Λ n : ℝ) / (n : ℝ)) := by
      intro n hn
      obtain ⟨_, hny, hnX⟩ := mem_lambda_window hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnn : (0 : ℝ) ≤ (Λ n : ℝ) / (n : ℝ) :=
        div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)
      rw [Real.rpow_sub hnpos, Real.rpow_one, div_div_eq_mul_div,
        show (Λ n : ℝ) * (n : ℝ) ^ δ / (n : ℝ) = ((Λ n : ℝ) / (n : ℝ)) * (n : ℝ) ^ δ from by
          ring, mul_comm ((X / y) ^ δ)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnpos.le hnX.le hδ) hnn
    calc (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 - δ))
        ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (X / y) ^ δ * ((Λ n : ℝ) / (n : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = (X / y) ^ δ * ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (X / y) ^ δ * ∑ n ∈ Finset.Ioc 0 ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            lambda_window_subset_Ioc (fun n _ _ =>
              div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n))) hXypow
      _ ≤ (X / y) ^ δ * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) :=
          mul_le_mul_of_nonneg_left (Salt.Maynard.sum_vonMangoldt_div_le hK1) hXypow

/-- **A-5a (b), the `1/δ` arm** — the landed `lambda_partial_alpha` at `α = 1 − δ`:

  `∑_{⌊y⌋<n<⌈X/y⌉} Λ(n)·n^{−1+δ} ≤ (log 4 + 4)·(X/y)^δ·(1 + 2/δ)`. -/
theorem vonMangoldt_window_shifted_inv {X y δ : ℝ} (hy : 1 ≤ y) (hXy : 1 ≤ X / y)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 - δ))
      ≤ (Real.log 4 + 4) * ((X / y) ^ δ * (1 + 2 / δ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy0 : (0 : ℝ) < X / y := by linarith
  have hc4 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  have hone : (1 : ℝ) ≤ (X / y) ^ δ := by
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hXy hδ0.le
    rwa [Real.one_rpow] at this
  have hceil : ((⌈X / y⌉₊ : ℕ) : ℝ) ≤ 2 * (X / y) := by
    have h1 : ((⌈X / y⌉₊ : ℕ) : ℝ) < X / y + 1 := Nat.ceil_lt_add_one hXy0.le
    linarith
  have hceilpow : ((⌈X / y⌉₊ : ℕ) : ℝ) ^ δ ≤ 2 * (X / y) ^ δ := by
    have h1 : ((⌈X / y⌉₊ : ℕ) : ℝ) ^ δ ≤ (2 * (X / y)) ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hδ0.le
    rw [Real.mul_rpow (by norm_num) hXy0.le] at h1
    have h2 : (2 : ℝ) ^ δ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hδ1
      rwa [Real.rpow_one] at this
    nlinarith [Real.rpow_nonneg hXy0.le δ]
  have hext : (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ (1 - δ))
      ≤ ∑ i ∈ Finset.range ⌈X / y⌉₊, (Λ (i + 1) : ℝ) / ((i + 1 : ℕ) : ℝ) ^ (1 - δ) := by
    rw [← sum_Icc_one_eq_sum_range (fun n => (Λ n : ℝ) / (n : ℝ) ^ (1 - δ))]
    exact Finset.sum_le_sum_of_subset_of_nonneg lambda_window_subset_Icc
      (fun n _ _ => div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  refine le_trans hext (le_trans (lambda_partial_alpha (by linarith) (by linarith) _) ?_)
  rw [show (1 : ℝ) - (1 - δ) = δ from by ring]
  have hstep : 1 + ((⌈X / y⌉₊ : ℕ) : ℝ) ^ δ / δ ≤ (X / y) ^ δ * (1 + 2 / δ) := by
    have h1 : ((⌈X / y⌉₊ : ℕ) : ℝ) ^ δ / δ ≤ 2 * (X / y) ^ δ / δ := by gcongr
    have h2 : (X / y) ^ δ * (1 + 2 / δ) = (X / y) ^ δ + 2 * (X / y) ^ δ / δ := by
      field_simp
    linarith
  exact mul_le_mul_of_nonneg_left hstep hc4

/-- **A-5a (b) — THE SHIFTED LEG.**  For `1 ≤ y`, `1 ≤ X/y`, `0 < δ ≤ 1` and any
exponent `c = 1 − δ`,

  `∑_{⌊y⌋<n<⌈X/y⌉} Λ(n)/n^c ≤ (log 4 + 4)·(X/y)^δ·min(L', 1 + 2/δ)`,

`L' = log⌈X/y⌉ + (log 4 + 4)`.  At `δ = max(β − 1/L, 0)` this is the low-leg factor of
the honest A-5 target `X^β·y^{−2β}·min(L,1/σ)²`. -/
theorem vonMangoldt_window_shifted_min {X y c δ : ℝ} (hy : 1 ≤ y) (hXy : 1 ≤ X / y)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc : c = 1 - δ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊, (Λ n : ℝ) / (n : ℝ) ^ c)
      ≤ (Real.log 4 + 4) * (X / y) ^ δ
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ) := by
  subst hc
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy0 : (0 : ℝ) < X / y := by linarith
  have hX0 : (0 : ℝ) ≤ X := by
    have h1 : (1 : ℝ) * y ≤ X := (le_div_iff₀ hy0).mp hXy
    linarith
  have hpow : (0 : ℝ) < (X / y) ^ δ := Real.rpow_pos_of_pos hXy0 _
  have hc4 : (1 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  rcases le_total (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ) with hmin | hmin
  · rw [min_eq_left hmin]
    have hL := vonMangoldt_window_shifted_log (X := X) hy hX0 hδ0.le
    have hbump : (X / y) ^ δ * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4))
        ≤ (Real.log 4 + 4) * (X / y) ^ δ * (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) := by
      refine mul_le_mul_of_nonneg_right ?_ window_grade_pos.le
      nlinarith
    linarith
  · rw [min_eq_right hmin]
    have hI := vonMangoldt_window_shifted_inv (X := X) hy hXy hδ0 hδ1
    nlinarith

/-! ### The consumer face — the corpus's `lambdaLin` window masses -/

/-- **A-5a — the damped leg at the corpus's window summand.**  `window_mass_eval`'s own
shape (`‖lambdaLin (restrictAbove y g) n‖ / n^c`) at the high leg `c = 1 + σ`. -/
theorem lambdaLin_window_damped_min (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y c σ : ℝ} (hy : 1 ≤ y) (hσ : 0 < σ) (hc : c = 1 + σ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c)
      ≤ (Real.log 4 + 4) * y ^ (-σ)
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / σ) := by
  refine le_trans (Finset.sum_le_sum (fun n _ => ?_))
    (vonMangoldt_window_damped_min (X := X) hy hσ hc)
  gcongr
  exact lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) n

/-- **A-5a — the shifted leg at the corpus's window summand.**  `window_mass_eval`'s own
shape at the low leg `c = 1 − δ`. -/
theorem lambdaLin_window_shifted_min (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {X y c δ : ℝ} (hy : 1 ≤ y) (hXy : 1 ≤ X / y) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hc : c = 1 - δ) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ c)
      ≤ (Real.log 4 + 4) * (X / y) ^ δ
          * min (Real.log (⌈X / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / δ) := by
  refine le_trans (Finset.sum_le_sum (fun n _ => ?_))
    (vonMangoldt_window_shifted_min (X := X) hy hXy hδ0 hδ1 hc)
  gcongr
  exact lambdaLin_norm_le (restrictAbove y g) (restrictAbove_norm_le hg) n

end Salt.MR

