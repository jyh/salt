/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Mertens.PrimePower

/-!
# The ζ-side asymptotic of the prime zeta function (MERTENS arc, node MERT-3a)

This file proves the third leg of the identification `M = γ − B`: the behaviour of the
prime zeta function `P(s) = ∑' p, p^{-s}` as `s → 1⁺`.  Concretely,

`P(s) + log(s - 1) → -B`  (where `B = mertensB` is the prime-power constant),

both as a `Tendsto` in the filter `𝓝[>] 1` (`primeZeta_tendsto`) and in explicit
`ε`-`δ` form (`primeZeta_asymp`).

## Route

For real `s > 1`, take `Real.log` of the Euler product `ζ(s) = ∏_p (1 - p^{-s})⁻¹`:

`log ζ(s) = ∑' p, -log(1 - p^{-s}) = P(s) + R(s)`,

where `R(s) = ∑' p, ppInnerS p s` is the `s`-deformed prime-power residual (the Mercator
tail `∑_{k ≥ 2} p^{-ks}/k`).  As `s → 1⁺`:

* `log((s-1) ζ(s)) → log 1 = 0` — the residue `riemannZeta_residue_one` restricted to real `s`
  through the Euler-product identity `ζ(s) = exp(logZetaReal s)`;
* `R(s) → B` — Tannery's theorem (`tendsto_tsum_of_dominated_convergence`), dominated by
  `2/p²`, with per-prime limits `ppInnerS p s → ppInner p` (Tannery again over the inner index).

Hence `P(s) + log(s-1) = log((s-1) ζ(s)) - R(s) → 0 - B = -B`.
-/

namespace Salt.Mertens

open scoped BigOperators
open Filter Topology Complex

/-! ## The `s`-deformed inner prime-power sum -/

/-- `ppInnerS p s = ∑_{k ≥ 0} 1/((k+2) · p^{(k+2)s})`, the `s`-deformation of `ppInner p`
(recovered at `s = 1`). -/
noncomputable def ppInnerS (p : ℕ) (s : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s))

/-- Bridge between the real-exponent and natural-exponent powers used in the two sums. -/
lemma rpow_natAdd_two (p : ℝ) (k : ℕ) : p ^ ((k : ℝ) + 2) = p ^ (k + 2) := by
  rw [← Real.rpow_natCast p (k + 2)]; congr 1; push_cast; ring

/-- Each deformed term is nonnegative. -/
lemma ppInnerS_nonneg (p : ℕ) (s : ℝ) : 0 ≤ ppInnerS p s :=
  tsum_nonneg (fun _ => by positivity)

/-- Termwise geometric domination for `s ≥ 1`: the deformed term is `≤` the `s = 1` term,
which is bounded by `(1/p)²·(1/2)^k`. -/
lemma ppInnerS_term_le (p : ℕ) (hp : 2 ≤ p) (s : ℝ) (hs : 1 ≤ s) (k : ℕ) :
    1 / (((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s))
      ≤ (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hc : (0 : ℝ) ≤ (k : ℝ) + 2 := by positivity
  have hexp : (p : ℝ) ^ (k + 2) ≤ (p : ℝ) ^ (((k : ℝ) + 2) * s) := by
    rw [← rpow_natAdd_two p k]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (le_mul_of_one_le_right hc hs)
  have hApos : (0 : ℝ) < ((k : ℝ) + 2) * (p : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
    positivity
  have hAB : ((k : ℝ) + 2) * (p : ℝ) ^ (k + 2)
      ≤ ((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s) :=
    mul_le_mul_of_nonneg_left hexp hc
  calc 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s))
      ≤ 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2)) := one_div_le_one_div_of_le hApos hAB
    _ ≤ (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k := ppInner_term_le p hp k

/-- The deformed inner sum converges for `s ≥ 1`. -/
lemma ppInnerS_summable (p : ℕ) (hp : 2 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun k : ℕ => 1 / (((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s))) := by
  have hmaj : Summable (fun k : ℕ => (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun k => ppInnerS_term_le p hp s hs k) hmaj

/-- Uniform bound `ppInnerS p s ≤ 2/p²` for `s ≥ 1`. -/
lemma ppInnerS_le (p : ℕ) (hp : 2 ≤ p) (s : ℝ) (hs : 1 ≤ s) :
    ppInnerS p s ≤ 2 / (p : ℝ) ^ 2 := by
  have hmaj : Summable (fun k : ℕ => (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  calc ppInnerS p s
      ≤ ∑' k : ℕ, (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_le_tsum (fun k => ppInnerS_term_le p hp s hs k)
          (ppInnerS_summable p hp s hs) hmaj
    _ = (1 / (p : ℝ)) ^ 2 * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := tsum_mul_left
    _ = (1 / (p : ℝ)) ^ 2 * 2 := by rw [tsum_geometric_two]
    _ = 2 / (p : ℝ) ^ 2 := by rw [one_div_pow]; ring

/-- The deformed Mercator peel: `ppInnerS p s = -log(1 - p^{-s}) - p^{-s}`. -/
lemma ppInnerS_eq (p : ℕ) (hp : 2 ≤ p) (s : ℝ) (hs : 0 < s) :
    ppInnerS p s = -Real.log (1 - (p : ℝ) ^ (-s)) - (p : ℝ) ^ (-s) := by
  have hp0' : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hx0 : (0 : ℝ) < (p : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
  have hx1 : (p : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hxabs : |(p : ℝ) ^ (-s)| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hHS := Real.hasSum_pow_div_log_of_abs_lt_one hxabs
  have key : -Real.log (1 - (p : ℝ) ^ (-s)) = (p : ℝ) ^ (-s) + ppInnerS p s := by
    rw [← hHS.tsum_eq, hHS.summable.tsum_eq_zero_add]
    congr 1
    · simp
    · rw [ppInnerS]
      apply tsum_congr
      intro n
      have hpe : (p : ℝ) ^ (((n : ℝ) + 2) * s) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
      have hpow : ((p : ℝ) ^ (-s)) ^ (n + 1 + 1) = ((p : ℝ) ^ (((n : ℝ) + 2) * s))⁻¹ := by
        rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1 + 1), ← Real.rpow_mul hp0',
          show (-s) * ((n + 1 + 1 : ℕ) : ℝ) = -(((n : ℝ) + 2) * s) by push_cast; ring,
          Real.rpow_neg hp0']
      rw [hpow, show ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 by push_cast; ring]
      rw [eq_div_iff (by positivity)]
      field_simp
  linarith

/-- Per-prime limit: `ppInnerS p s → ppInner p` as `s → 1⁺` (Tannery over the inner index). -/
lemma ppInnerS_tendsto (p : ℕ) (hp : 2 ≤ p) :
    Tendsto (fun s => ppInnerS p s) (𝓝[>] 1) (𝓝 (ppInner p)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp0' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hgoal :
      Tendsto (fun s => ∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s)))
        (𝓝[>] 1) (𝓝 (∑' k : ℕ, (1 : ℝ) / (((k : ℝ) + 2) * (p : ℝ) ^ (k + 2)))) := by
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun k : ℕ => (1 / (p : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ k)
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    · intro k
      have hbr : (p : ℝ) ^ ((k : ℝ) + 2) = (p : ℝ) ^ (k + 2) := rpow_natAdd_two p k
      have hcont : Continuous
          (fun s : ℝ => (1 : ℝ) / (((k : ℝ) + 2) * (p : ℝ) ^ (((k : ℝ) + 2) * s))) := by
        refine Continuous.div continuous_const
          (continuous_const.mul ((Real.continuous_const_rpow hp0).comp
            (continuous_const.mul continuous_id))) (fun s => ?_)
        positivity
      simpa only [mul_one, hbr] using (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall (fun s hs => ?_)
      intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact ppInnerS_term_le p hp s (le_of_lt hs) k
  simpa only [ppInnerS, ppInner] using hgoal

/-! ## The prime zeta function, the residual, and the log-Euler sum -/

/-- The prime zeta function `P(s) = ∑' p, p^{-s}` (real `s`). -/
noncomputable def primeZeta (s : ℝ) : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)

/-- The `s`-deformed prime-power residual `R(s) = ∑' p, ppInnerS p s`. -/
noncomputable def ppResidual (s : ℝ) : ℝ := ∑' p : Nat.Primes, ppInnerS (p : ℕ) s

/-- The real log-Euler sum `∑' p, -log(1 - p^{-s})`, equal to `log ζ(s)` for `s > 1`. -/
noncomputable def logZetaReal (s : ℝ) : ℝ :=
  ∑' p : Nat.Primes, -Real.log (1 - ((p : ℕ) : ℝ) ^ (-s))

/-- `P(s)` converges for `s > 1` (a sub-`p`-series of `∑ n^{-s}`). -/
lemma primeZeta_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s)) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
    (Real.summable_nat_rpow_inv.mpr hs).congr (fun n => (Real.rpow_neg (Nat.cast_nonneg n) s).symm)
  exact h.subtype _

/-- `R(s)` converges for `s ≥ 1` (dominated by `2/p²`). -/
lemma ppResidual_summable {s : ℝ} (hs : 1 ≤ s) :
    Summable (fun p : Nat.Primes => ppInnerS (p : ℕ) s) :=
  Summable.of_nonneg_of_le (fun _ => ppInnerS_nonneg _ _)
    (fun p => ppInnerS_le _ p.2.two_le s hs) (summable_two_div_sq.subtype _)

/-- The split `log ζ(s) = P(s) + R(s)` at the level of the real sums, for `s > 1`. -/
lemma logZetaReal_eq {s : ℝ} (hs : 1 < s) :
    logZetaReal s = primeZeta s + ppResidual s := by
  rw [logZetaReal, primeZeta, ppResidual,
    ← Summable.tsum_add (primeZeta_summable hs) (ppResidual_summable hs.le)]
  apply tsum_congr
  intro p
  rw [ppInnerS_eq (p : ℕ) p.2.two_le s (by linarith)]
  ring

/-! ## The residual limit `R(s) → B` -/

/-- `R(s) → B` as `s → 1⁺` (Tannery over the primes, dominated by `2/p²`). -/
lemma ppResidual_tendsto : Tendsto ppResidual (𝓝[>] 1) (𝓝 mertensB) := by
  have hgoal :
      Tendsto (fun s => ∑' p : Nat.Primes, ppInnerS (p : ℕ) s) (𝓝[>] 1)
        (𝓝 (∑' p : Nat.Primes, ppInner (p : ℕ))) := by
    apply tendsto_tsum_of_dominated_convergence
      (bound := fun p : Nat.Primes => 2 / ((p : ℕ) : ℝ) ^ 2)
    · exact summable_two_div_sq.subtype _
    · intro p
      exact ppInnerS_tendsto (p : ℕ) p.2.two_le
    · refine eventually_nhdsWithin_of_forall (fun s hs => ?_)
      intro p
      rw [Real.norm_eq_abs, abs_of_nonneg (ppInnerS_nonneg _ _)]
      exact ppInnerS_le (p : ℕ) p.2.two_le s (le_of_lt hs)
  exact hgoal

/-! ## The Euler-product identity and the `log ζ(s) + log(s-1) → 0` limit -/

/-- The real Euler-product identity: `ζ(s) = exp(logZetaReal s)` for `s > 1`. -/
lemma zeta_eq_exp {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) = ((Real.exp (logZetaReal s) : ℝ) : ℂ) := by
  have hs' : 1 < ((s : ℂ)).re := by rw [Complex.ofReal_re]; exact hs
  have hEuler := riemannZeta_eulerProduct_exp_log hs'
  rw [← hEuler, Complex.ofReal_exp]
  congr 1
  rw [logZetaReal, Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  have hpR : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := by positivity
  have hp1 : (1 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt
  have hx1 : ((p : ℕ) : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hx0 : (0 : ℝ) < ((p : ℕ) : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by linarith) _
  have harg : (0 : ℝ) ≤ 1 - ((p : ℕ) : ℝ) ^ (-s) := by linarith
  have hcast : ((p : ℕ) : ℂ) ^ (-(s : ℂ)) = ((((p : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpR, Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hcast, ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log harg,
    ← Complex.ofReal_neg]

/-- `log ζ(s) + log(s - 1) → 0` as `s → 1⁺`. -/
lemma logZeta_add_log_tendsto :
    Tendsto (fun s : ℝ => logZetaReal s + Real.log (s - 1)) (𝓝[>] 1) (𝓝 0) := by
  -- `s ↦ ↑s` maps `𝓝[>] 1` into `𝓝[≠] (1:ℂ)`
  have hcomp : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] 1) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 1) (𝓝 ((1 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 1
      rw [Complex.ofReal_one] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall (fun s hs => ?_)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hcontra
      rw [← Complex.ofReal_one, Complex.ofReal_inj] at hcontra
      exact (Set.mem_Ioi.mp hs).ne' hcontra
  -- residue restricted to real `s`
  have hres : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ)) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hcomp
  -- `w s := (s - 1) · exp(logZetaReal s) → 1`
  have hw : Tendsto (fun s : ℝ => (s - 1) * Real.exp (logZetaReal s)) (𝓝[>] 1) (𝓝 1) := by
    rw [← Filter.tendsto_ofReal_iff]
    simp only [Complex.ofReal_one]
    refine hres.congr' (eventually_nhdsWithin_of_forall (fun s hs => ?_))
    change ((s : ℂ) - 1) * riemannZeta (s : ℂ) = (((s - 1) * Real.exp (logZetaReal s) : ℝ) : ℂ)
    rw [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
      zeta_eq_exp (Set.mem_Ioi.mp hs)]
  -- compose with continuity of `log` at `1`
  have hlogw : Tendsto (fun s : ℝ => Real.log ((s - 1) * Real.exp (logZetaReal s)))
      (𝓝[>] 1) (𝓝 0) := by
    have h := (Real.continuousAt_log (one_ne_zero)).tendsto.comp hw
    rwa [Real.log_one] at h
  refine hlogw.congr' (eventually_nhdsWithin_of_forall (fun s hs => ?_))
  have hs1 : 1 < s := Set.mem_Ioi.mp hs
  rw [Real.log_mul (by linarith : s - 1 ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
  ring

/-! ## The main asymptotic -/

/-- **Prime zeta asymptotic (filter form).** `P(s) + log(s - 1) → -B` as `s → 1⁺`. -/
theorem primeZeta_tendsto :
    Tendsto (fun s : ℝ => primeZeta s + Real.log (s - 1)) (𝓝[>] 1) (𝓝 (-mertensB)) := by
  have h := logZeta_add_log_tendsto.sub ppResidual_tendsto
  rw [zero_sub] at h
  refine h.congr' (eventually_nhdsWithin_of_forall (fun s hs => ?_))
  rw [logZetaReal_eq (Set.mem_Ioi.mp hs)]
  ring

/-- **Prime zeta asymptotic (`ε`-`δ` form).** For every `ε > 0` there is `δ > 0` with
`|P(s) + log(s - 1) + B| ≤ ε` whenever `1 < s < 1 + δ`. -/
theorem primeZeta_asymp :
    ∀ ε > 0, ∃ δ > 0, ∀ s : ℝ, 1 < s → s < 1 + δ →
      |primeZeta s + Real.log (s - 1) + mertensB| ≤ ε := by
  intro ε hε
  have h := primeZeta_tendsto
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ0, hδ⟩ := h ε hε
  refine ⟨δ, hδ0, fun s hs1 hsδ => ?_⟩
  have hmem : s ∈ Set.Ioi (1 : ℝ) := Set.mem_Ioi.mpr hs1
  have hdist : dist s 1 < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < s - 1)]; linarith
  have hlt := hδ hmem hdist
  rw [Real.dist_eq, show primeZeta s + Real.log (s - 1) - -mertensB
    = primeZeta s + Real.log (s - 1) + mertensB by ring] at hlt
  exact le_of_lt hlt

end Salt.Mertens
