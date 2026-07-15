/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WeightedCount

/-!
# The abstract prime-sum Abel pass (BJS Lemma 20) and its Lemma-52 applications

Design: `docs/blueprints/flags.md`, the CNT2 entries ("THE SW-FIBER DESIGN BLOCK
RESOLVED", catch #53) and node **AB1**.  This is the analytic core that carries the
c̄-weighted double sum `weightedPairSum` (landed input `tripleSum_le_weighted_pairSum`,
`Salt.Chen.WeightedCount`) to the switch constant `c̄` (landed target
`cbar_eq_double_integral`).

## The abstract enabler — BJS Lemma 20

For a positive monotone differentiable `f` on `[w, z]` (`2 ≤ w ≤ z`), Abel/Riemann–
Stieltjes partial summation against the prime-reciprocal coefficient `c(n) = 1/n·[n prime]`
and `g(t) = log log t` gives

  `Σ_{p ∈ [w,z) prime} f(p)/p ≤ ∫_w^z f(t)/(t log t) dt + E·max(f w, f z)`,

with `E = 21/log w` the honest windowed-Mertens error (the corpus window bound
`Salt.BrunLower.sum_inv_le_of_prime_window` supplies the incremental
`Σ_{x≤p<y} 1/p ≤ log log y − log log x + 19/log x` in place of BJS's sharper
`1/log²x`; the extra `+2/log w` absorbs the `⌊·⌋+1` running-window rounding and the
one boundary prime at `w`).  Two versions:

* `prime_sum_abel_antitone` — `f` decreasing (`f' ≤ 0`), error `E·f(w)` (left reference).
* `prime_sum_abel_monotone` — `f` increasing (`f' ≥ 0`), error `E·f(z)` (right reference).

The proof mirrors `Salt.BrunLower.window_core`'s Abel structure but keeps `f` abstract:
the discrete Abel identity (`sum_mul_eq_sub_sub_integral_mul`) plus the FTC cancellation of
the base sum `C(w)` yields `Σ = f(z)·P(z) − ∫_w^z f'(t)·P(t) dt` with `P(t)` the window
prime count, then one `integral_mono_on` against the windowed-Mertens reference and one
integration by parts (`integral_mul_deriv_eq_deriv_mul`) convert `f'` to the target `f·g'`.

No `sorry`, no `native_decide`, no new axioms.
-/

open MeasureTheory intervalIntegral Set
open scoped BigOperators

namespace Salt.Chen

/-! ## Section 1 — the prime-reciprocal coefficient and the windowed-Mertens reference -/

/-- The prime-reciprocal arithmetic coefficient `c(n) = 1/n` on primes, `0` otherwise.
This is BJS Lemma 20's `c(n)` for `f = h_{p₁}`, `I`. -/
noncomputable def cprime : ℕ → ℝ := fun n => if n.Prime then (1 : ℝ) / n else 0

lemma cprime_zero : cprime 0 = 0 := by simp [cprime, Nat.not_prime_zero]

lemma cprime_one : cprime 1 = 0 := by simp [cprime, Nat.not_prime_one]

/-- `f k · c(k) = f k / k` on primes, `0` otherwise — the Abel LHS summand. -/
lemma mul_cprime_eq (f : ℝ → ℝ) (k : ℕ) :
    f k * cprime k = if k.Prime then f k / k else 0 := by
  unfold cprime
  by_cases hk : k.Prime
  · simp only [hk, if_true]; rw [mul_one_div]
  · simp only [hk, if_false, mul_zero]

/-- **The `⌊·⌋+1` running-window log correction.**  For `2 ≤ a ≤ b`,
`log log(⌊b⌋+1) ≤ log log b + 1/log a`.  (The discrete window count runs up to `⌊t⌋`,
whose continuous surrogate `⌊t⌋+1` overshoots `t` by `< 1`; the `log log` overshoot is
`≤ 1/(t log t) ≤ 1/log a`.) -/
lemma loglog_floor_succ_le {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    Real.log (Real.log ((⌊b⌋₊ : ℝ) + 1)) ≤ Real.log (Real.log b) + 1 / Real.log a := by
  have hb : (2 : ℝ) ≤ b := le_trans ha hab
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlogb1 : 0 < Real.log (b + 1) := Real.log_pos (by linarith)
  have hfb : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hfloor2 : (2 : ℝ) ≤ (⌊b⌋₊ : ℝ) := by
    have : (2 : ℕ) ≤ ⌊b⌋₊ := Nat.le_floor (by exact_mod_cast hb)
    exact_mod_cast this
  -- monotone step: loglog(⌊b⌋+1) ≤ loglog(b+1)
  have hbf1pos : (0 : ℝ) < (⌊b⌋₊ : ℝ) + 1 := by linarith
  have hbf1gt1 : (1 : ℝ) < (⌊b⌋₊ : ℝ) + 1 := by linarith
  have hmono : Real.log (Real.log ((⌊b⌋₊ : ℝ) + 1)) ≤ Real.log (Real.log (b + 1)) :=
    Real.log_le_log (Real.log_pos hbf1gt1)
      (Real.log_le_log hbf1pos (by linarith))
  -- the increment step: loglog(b+1) ≤ loglog b + 1/log a
  have h1 : Real.log (b + 1) - Real.log b ≤ 1 / b := by
    rw [← Real.log_div (by linarith) (by linarith)]
    have hbb : (b + 1) / b = 1 + 1 / b := by field_simp
    rw [hbb]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / b by positivity)
    linarith [this]
  have hstep : Real.log (Real.log (b + 1)) ≤ Real.log (Real.log b) + 1 / Real.log a := by
    have e1 : Real.log (Real.log (b + 1)) - Real.log (Real.log b)
        = Real.log (Real.log (b + 1) / Real.log b) :=
      (Real.log_div (ne_of_gt hlogb1) (ne_of_gt hlogb)).symm
    have e2 : Real.log (b + 1) / Real.log b ≤ 1 + 1 / (b * Real.log b) := by
      rw [div_le_iff₀ hlogb]
      have hbne : b ≠ 0 := by positivity
      have hlbne : Real.log b ≠ 0 := ne_of_gt hlogb
      have hexp : (1 + 1 / (b * Real.log b)) * Real.log b = Real.log b + 1 / b := by
        field_simp
      rw [hexp]; linarith [h1]
    have e3 : Real.log (Real.log (b + 1) / Real.log b) ≤ 1 / (b * Real.log b) := by
      calc Real.log (Real.log (b + 1) / Real.log b)
          ≤ Real.log (1 + 1 / (b * Real.log b)) := Real.log_le_log (by positivity) e2
        _ ≤ (1 + 1 / (b * Real.log b)) - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
        _ = 1 / (b * Real.log b) := by ring
    have e4 : 1 / (b * Real.log b) ≤ 1 / Real.log a := by
      apply one_div_le_one_div_of_le hloga
      calc Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
        _ ≤ b * Real.log b := by nlinarith [hlogb.le, (show (1 : ℝ) ≤ b by linarith)]
    linarith [e1, e3, e4]
  linarith [hmono, hstep]

/-- **The windowed prime-reciprocal bound (the reference function's pointwise majorant).**
For `2 ≤ a ≤ b`, `Σ_{p ∈ (⌊a⌋, ⌊b⌋] prime} 1/p ≤ log log b − log log a + 20/log a`.
The corpus incremental window bound (`sum_inv_le_of_prime_window`, constant `19/log a`) plus
the `⌊·⌋+1` correction (`loglog_floor_succ_le`, `+1/log a`). -/
lemma window_prime_sum_le {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p
      ≤ Real.log (Real.log b) - Real.log (Real.log a) + 20 / Real.log a := by
  have hb : (2 : ℝ) ≤ b := le_trans ha hab
  have hloga : 0 < Real.log a := Real.log_pos (by linarith)
  have hbf1 : (b : ℝ) < (⌊b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one b
  have hlogbf1 : 0 < Real.log ((⌊b⌋₊ : ℝ) + 1) :=
    Real.log_pos (by linarith)
  -- corpus incremental window bound with upper endpoint `⌊b⌋+1`
  have hcorp := Salt.BrunLower.sum_inv_le_of_prime_window (w := a) (z := (⌊b⌋₊ : ℝ) + 1) ha
    (by linarith) (S := (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime) ?_
  · -- rewrite `log(log z/log a) = loglog z − loglog a`, apply the correction
    rw [Real.log_div (ne_of_gt hlogbf1) (ne_of_gt hloga)] at hcorp
    have hcorr := loglog_floor_succ_le ha hab
    have hsum : (20 : ℝ) / Real.log a = 19 / Real.log a + 1 / Real.log a := by
      rw [← add_div]; norm_num
    linarith [hcorp, hcorr]
  · -- membership: each prime `p ∈ (⌊a⌋, ⌊b⌋]` satisfies `a ≤ p < ⌊b⌋+1`
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hlo, hhi⟩, hpp⟩ := hp
    refine ⟨hpp, ?_, ?_⟩
    · have hple : (⌊a⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (by omega : ⌊a⌋₊ + 1 ≤ p)
      have := Nat.lt_floor_add_one a
      linarith
    · have : (p : ℝ) ≤ (⌊b⌋₊ : ℝ) := by exact_mod_cast hhi
      linarith

/-- The base sum `C(t) = Σ_{k ≤ ⌊t⌋} c(k)`; its increment over `[⌊a⌋, ⌊b⌋]` is the
window prime-reciprocal sum. -/
lemma cprime_sum_sub {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc 0 b, cprime k) - ∑ k ∈ Finset.Icc 0 a, cprime k
      = ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 : ℝ) / p := by
  have hdisj : Disjoint (Finset.Icc 0 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'
    omega
  have hunion : Finset.Icc 0 a ∪ Finset.Ioc a b = Finset.Icc 0 b := by
    ext x
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hsplit : ∑ k ∈ Finset.Icc 0 b, cprime k
      = (∑ k ∈ Finset.Icc 0 a, cprime k) + ∑ k ∈ Finset.Ioc a b, cprime k := by
    rw [← hunion, Finset.sum_union hdisj]
  have hfilter : ∑ k ∈ Finset.Ioc a b, cprime k
      = ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, (1 : ℝ) / p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _; rfl
  rw [hsplit, hfilter]; ring

/-- **Boundary reconciliation.**  The BJS half-open window `[w, z)` prime sum is bounded by
the Abel index window `(⌊w⌋, ⌊z⌋]` prime sum plus the single boundary term at `w` (present
only when `w` is an integer prime, where `f w ≥ 0`). -/
lemma primesInWindow_sum_le {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) {f : ℝ → ℝ}
    (hf_pos : ∀ t ∈ Set.Icc w z, 0 ≤ f t) :
    ∑ p ∈ Salt.BrunLower.primesInWindow w z, f p / p
      ≤ (∑ p ∈ (Finset.Ioc ⌊w⌋₊ ⌊z⌋₊).filter Nat.Prime, f p / p) + f w / w := by
  have hwpos : (0 : ℝ) < w := by linarith
  have hz : (2 : ℝ) ≤ z := le_trans hw hwz
  set T := Salt.BrunLower.primesInWindow w z with hT
  set A := (Finset.Ioc ⌊w⌋₊ ⌊z⌋₊).filter Nat.Prime with hA
  -- membership facts about `T` and `A`
  have hTmem : ∀ p ∈ T, Nat.Prime p ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
    intro p hp
    rw [hT, Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hp
    exact ⟨hp.2.1, hp.2.2, Nat.lt_ceil.mp hp.1⟩
  have hAnonneg : ∀ q ∈ A, 0 ≤ f q / q := by
    intro q hq
    rw [hA, Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨hlo, hhi⟩, _⟩ := hq
    have hwq : w ≤ (q : ℝ) := by
      have h1 : (⌊w⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : ⌊w⌋₊ + 1 ≤ q)
      have := Nat.lt_floor_add_one w
      linarith
    have hqz : (q : ℝ) ≤ z := by
      have : (q : ℝ) ≤ (⌊z⌋₊ : ℝ) := by exact_mod_cast hhi
      have := Nat.floor_le (show (0:ℝ) ≤ z by linarith)
      linarith
    have := hf_pos q ⟨hwq, hqz⟩
    positivity
  -- `T \ A ⊆ {⌊w⌋}` with the sole element equal to `w`
  have hTdiff : ∀ p ∈ T \ A, (p : ℝ) = w ∧ f p / p = f w / w := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpT, hpA⟩ := hp
    obtain ⟨hpp, hwp, hpz⟩ := hTmem p hpT
    have hple : p ≤ ⌊z⌋₊ := Nat.le_floor hpz.le
    have hnotlo : ¬ ⌊w⌋₊ < p := by
      intro hlt
      exact hpA (by rw [hA, Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hlt, hple⟩, hpp⟩)
    have hpfw : p ≤ ⌊w⌋₊ := Nat.not_lt.mp hnotlo
    have hfloorw : (⌊w⌋₊ : ℝ) ≤ w := Nat.floor_le (by linarith)
    have hpeq : (p : ℝ) = w := by
      have : (p : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hpfw
      linarith
    exact ⟨hpeq, by rw [hpeq]⟩
  -- `T ⊆ A ∪ (T \ A)`, disjoint
  have hsub : T ⊆ A ∪ (T \ A) := by
    intro p hp
    by_cases hpA : p ∈ A
    · exact Finset.mem_union_left _ hpA
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, hpA⟩)
  have hdisj : Disjoint A (T \ A) := Finset.disjoint_sdiff
  have hcompl : ∀ q ∈ A ∪ (T \ A), q ∉ T → 0 ≤ f q / q := by
    intro q hq _
    rcases Finset.mem_union.mp hq with hqA | hqTA
    · exact hAnonneg q hqA
    · exact absurd (Finset.mem_sdiff.mp hqTA).1 (by intro h; exact ‹q ∉ T› h)
  calc ∑ p ∈ T, f p / p
      ≤ ∑ p ∈ A ∪ (T \ A), f p / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hcompl
    _ = (∑ p ∈ A, f p / p) + ∑ p ∈ T \ A, f p / p := Finset.sum_union hdisj
    _ ≤ (∑ p ∈ A, f p / p) + f w / w := by
        have hbd : ∑ p ∈ T \ A, f p / p ≤ f w / w := by
          calc ∑ p ∈ T \ A, f p / p
              = ∑ _p ∈ T \ A, f w / w :=
                Finset.sum_congr rfl (fun p hp => (hTdiff p hp).2)
            _ = (T \ A).card • (f w / w) := by rw [Finset.sum_const]
            _ ≤ 1 • (f w / w) := by
                apply nsmul_le_nsmul_left ?_ ?_
                · have := hf_pos w ⟨le_refl w, hwz⟩; positivity
                · -- card (T \ A) ≤ 1 since T \ A ⊆ {⌊w⌋₊}
                  apply Finset.card_le_one.mpr
                  intro x hx y hy
                  have hxeq := (hTdiff x hx).1
                  have hyeq := (hTdiff y hy).1
                  have : (x : ℝ) = (y : ℝ) := by rw [hxeq, hyeq]
                  exact_mod_cast this
            _ = f w / w := by rw [one_smul]
        linarith

/-! ## Section 2 — the abstract Abel pass (BJS Lemma 20) -/

/-- **BJS Lemma 20, decreasing carrier.**  For `2 ≤ w ≤ z` and a positive, differentiable,
decreasing `f` on `[w, z]`,
`Σ_{p ∈ [w,z) prime} f(p)/p ≤ ∫_w^z f(t)/(t log t) dt + (21/log w)·f(w)`.
Left-reference (`log log t − log log w + 20/log w`) Abel pass: the discrete summation
identity, one `integral_mono_on` against the windowed-Mertens reference, one integration by
parts converting `f'` to `f·(log log)'`, and the boundary reconciliation. -/
theorem prime_sum_abel_antitone {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc w z, HasDerivAt f (f' t) t)
    (hf'_int : IntervalIntegrable f' MeasureTheory.volume w z)
    (hf_pos : ∀ t ∈ Set.Icc w z, 0 ≤ f t)
    (hf'_nonpos : ∀ t ∈ Set.Icc w z, f' t ≤ 0) :
    ∑ p ∈ Salt.BrunLower.primesInWindow w z, f p / p
      ≤ (∫ t in w..z, f t / (t * Real.log t)) + (21 / Real.log w) * f w := by
  have hz : (2 : ℝ) ≤ z := le_trans hw hwz
  have hwpos : (0 : ℝ) < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hwnn : (0 : ℝ) ≤ w := le_of_lt hwpos
  have hfzpos : 0 ≤ f z := hf_pos z ⟨hwz, le_refl z⟩
  have hfwpos : 0 ≤ f w := hf_pos w ⟨le_refl w, hwz⟩
  -- deriv f = f' and differentiability on the interval
  have hderiv_eq : ∀ t ∈ Set.Icc w z, deriv f t = f' t := fun t ht => (hderiv t ht).deriv
  have hdiff : ∀ t ∈ Set.Icc w z, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hderiv' : ∀ t ∈ Set.uIcc w z, HasDerivAt f (f' t) t :=
    fun t ht => hderiv t (by rwa [Set.uIcc_of_le hwz] at ht)
  -- integrability of `f'` on `[w,z]`, transported to `deriv f`
  have hint_f' : IntegrableOn f' (Set.Icc w z) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mp hf'_int
  have hint_deriv : IntegrableOn (deriv f) (Set.Icc w z) :=
    hint_f'.congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  -- Abel summation
  have habel := sum_mul_eq_sub_sub_integral_mul cprime hwnn hwz hdiff hint_deriv
  set Cz : ℝ := ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, cprime k with hCz
  set Cw : ℝ := ∑ k ∈ Finset.Icc 0 ⌊w⌋₊, cprime k with hCw
  -- interval-integral form and swap `deriv f → f'` in the integrand
  rw [← intervalIntegral.integral_of_le hwz,
    intervalIntegral.integral_congr (g := fun t => f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k)
      (fun t ht => by rw [hderiv_eq t (by rwa [Set.uIcc_of_le hwz] at ht)])] at habel
  -- convert the Abel LHS to the prime sum over the `(⌊w⌋, ⌊z⌋]` window
  have hSfin_eq : (∑ k ∈ Finset.Ioc ⌊w⌋₊ ⌊z⌋₊, f ↑k * cprime k)
      = ∑ p ∈ (Finset.Ioc ⌊w⌋₊ ⌊z⌋₊).filter Nat.Prime, f p / p := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun k _ => mul_cprime_eq f k)
  rw [hSfin_eq] at habel
  -- integrability of the Abel integrand `f' · C`
  have hCint : IntervalIntegrable
      (fun t => f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k) MeasureTheory.volume w z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mpr
      (integrableOn_mul_sum_Icc cprime (m := 0) hwnn hint_f')
  -- FTC for `f'`
  have hFTC : (∫ t in w..z, f' t) = f z - f w :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hf'_int
  -- the windowed-Mertens reference `G`
  set G : ℝ → ℝ := fun t => Real.log (Real.log t) - Real.log (Real.log w) + 20 / Real.log w
    with hGdef
  have hGw : G w = 20 / Real.log w := by
    have hGwe : G w = Real.log (Real.log w) - Real.log (Real.log w) + 20 / Real.log w := rfl
    rw [hGwe]; ring
  have hGderiv : ∀ t ∈ Set.uIcc w z, HasDerivAt G ((t * Real.log t)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hwz, Set.mem_Icc] at ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hinner : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have houter : HasDerivAt Real.log (Real.log t)⁻¹ (Real.log t) :=
      Real.hasDerivAt_log (ne_of_gt hlogtpos)
    have hcomp : HasDerivAt (fun s => Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t :=
      houter.comp t hinner
    have hval : (Real.log t)⁻¹ * t⁻¹ = (t * Real.log t)⁻¹ := by rw [mul_inv]; ring
    rw [hval] at hcomp
    exact (hcomp.sub_const _).add_const _
  have hGcont : ContinuousOn G (Set.uIcc w z) := by
    rw [Set.uIcc_of_le hwz]
    have ht_ne : ∀ t ∈ Set.Icc w z, t ≠ 0 :=
      fun t ht => ne_of_gt (by rw [Set.mem_Icc] at ht; linarith [ht.1])
    have hlogt_ne : ∀ t ∈ Set.Icc w z, Real.log t ≠ 0 :=
      fun t ht => ne_of_gt (Real.log_pos (by rw [Set.mem_Icc] at ht; linarith [ht.1]))
    have hll : ContinuousOn (fun t => Real.log (Real.log t)) (Set.Icc w z) :=
      (continuousOn_id.log ht_ne).log hlogt_ne
    exact (hll.sub continuousOn_const).add continuousOn_const
  have hGderiv_int : IntervalIntegrable (fun t => (t * Real.log t)⁻¹) MeasureTheory.volume w z :=
    (Salt.BrunLower.continuousOn_inv_tlog_real hw hwz).intervalIntegrable
  -- pointwise `C t ≤ Cw + G t`
  have hCbound : ∀ t ∈ Set.Icc w z,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k) ≤ Cw + G t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have hsub := cprime_sum_sub (a := ⌊w⌋₊) (b := ⌊t⌋₊) (Nat.floor_le_floor ht.1)
    rw [← hCw] at hsub
    have hwin := window_prime_sum_le hw ht.1
    have hGt : G t = Real.log (Real.log t) - Real.log (Real.log w) + 20 / Real.log w := rfl
    linarith [hsub, hwin, hGt]
  -- window bound at the top endpoint: `Cz − Cw ≤ G z`
  have hCzbound : Cz - Cw ≤ G z := by
    have hsub := cprime_sum_sub (a := ⌊w⌋₊) (b := ⌊z⌋₊) (Nat.floor_le_floor hwz)
    rw [← hCz, ← hCw] at hsub
    have hwin := window_prime_sum_le hw hwz
    have hGz : G z = Real.log (Real.log z) - Real.log (Real.log w) + 20 / Real.log w := rfl
    linarith [hsub, hwin, hGz]
  -- comparison: `∫ f'·(Cw+G) ≤ ∫ f'·C`
  have hmono : (∫ t in w..z, f' t * (Cw + G t))
      ≤ ∫ t in w..z, f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k := by
    apply intervalIntegral.integral_mono_on hwz
      (hf'_int.mul_continuousOn (continuousOn_const.add hGcont)) hCint
    intro t ht
    exact mul_le_mul_of_nonpos_left (hCbound t ht) (hf'_nonpos t ht)
  -- split the reference integral
  have hsplit_int : (∫ t in w..z, f' t * (Cw + G t))
      = Cw * (f z - f w) + ∫ t in w..z, f' t * G t := by
    rw [intervalIntegral.integral_congr (g := fun t => Cw * f' t + f' t * G t)
        (fun t _ => by ring),
      intervalIntegral.integral_add (hf'_int.const_mul Cw) (hf'_int.mul_continuousOn hGcont),
      intervalIntegral.integral_const_mul, hFTC]
  -- integration by parts: `∫ f'·G = G z·f z − G w·f w − ∫ f·(log log)'`
  have hInteq : (∫ t in w..z, (t * Real.log t)⁻¹ * f t)
      = ∫ t in w..z, f t / (t * Real.log t) :=
    intervalIntegral.integral_congr (fun t _ => by rw [mul_comm, ← div_eq_mul_inv])
  have hIBP : (∫ t in w..z, f' t * G t)
      = G z * f z - G w * f w - ∫ t in w..z, f t / (t * Real.log t) := by
    rw [intervalIntegral.integral_congr (g := fun t => G t * f' t) (fun t _ => mul_comm _ _),
      intervalIntegral.integral_mul_deriv_eq_deriv_mul hGderiv hderiv' hGderiv_int hf'_int,
      hInteq]
  -- assemble the Ioc-window bound
  have hfzterm : f z * (Cz - Cw - G z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfzpos (by linarith [hCzbound])
  have hAset : (∑ p ∈ (Finset.Ioc ⌊w⌋₊ ⌊z⌋₊).filter Nat.Prime, f p / p)
      ≤ (∫ t in w..z, f t / (t * Real.log t)) + (20 / Real.log w) * f w := by
    have e20 : (20 / Real.log w) * f w = 20 * (f w / Real.log w) := by ring
    rw [hGw] at hIBP
    nlinarith [habel, hmono, hsplit_int, hIBP, hfzterm, e20]
  -- boundary reconciliation `primesInWindow → Ioc`, fold the extra `f w / w`
  have hbdry := primesInWindow_sum_le hw hwz hf_pos
  have hlw : Real.log w ≤ w := le_trans (Real.log_le_sub_one_of_pos hwpos) (by linarith)
  have hfw_ww : f w / w ≤ f w / Real.log w := by
    apply div_le_div_of_nonneg_left hfwpos hlogw hlw
  have e20' : (20 / Real.log w) * f w = 20 * (f w / Real.log w) := by ring
  have e21' : (21 / Real.log w) * f w = 21 * (f w / Real.log w) := by ring
  linarith [hbdry, hAset, hfw_ww, e20', e21']

/-- **BJS Lemma 20, increasing carrier.**  For `2 ≤ w ≤ z` and a positive, differentiable,
increasing `f` on `[w, z]`,
`Σ_{p ∈ [w,z) prime} f(p)/p ≤ ∫_w^z f(t)/(t log t) dt + (21/log w)·f(z)`.
Right-reference (`log log z − log log t + 20/log w`) Abel pass, mirror of the decreasing
carrier with every sign flipped and the error attached to the top endpoint `f(z)`. -/
theorem prime_sum_abel_monotone {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z)
    {f f' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc w z, HasDerivAt f (f' t) t)
    (hf'_int : IntervalIntegrable f' MeasureTheory.volume w z)
    (hf_pos : ∀ t ∈ Set.Icc w z, 0 ≤ f t)
    (hf'_nonneg : ∀ t ∈ Set.Icc w z, 0 ≤ f' t) :
    ∑ p ∈ Salt.BrunLower.primesInWindow w z, f p / p
      ≤ (∫ t in w..z, f t / (t * Real.log t)) + (21 / Real.log w) * f z := by
  have hz : (2 : ℝ) ≤ z := le_trans hw hwz
  have hwpos : (0 : ℝ) < w := by linarith
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hwnn : (0 : ℝ) ≤ w := le_of_lt hwpos
  have hfzpos : 0 ≤ f z := hf_pos z ⟨hwz, le_refl z⟩
  have hfwpos : 0 ≤ f w := hf_pos w ⟨le_refl w, hwz⟩
  have hderiv_eq : ∀ t ∈ Set.Icc w z, deriv f t = f' t := fun t ht => (hderiv t ht).deriv
  have hdiff : ∀ t ∈ Set.Icc w z, DifferentiableAt ℝ f t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hderiv' : ∀ t ∈ Set.uIcc w z, HasDerivAt f (f' t) t :=
    fun t ht => hderiv t (by rwa [Set.uIcc_of_le hwz] at ht)
  have hint_f' : IntegrableOn f' (Set.Icc w z) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mp hf'_int
  have hint_deriv : IntegrableOn (deriv f) (Set.Icc w z) :=
    hint_f'.congr_fun (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul cprime hwnn hwz hdiff hint_deriv
  set Cz : ℝ := ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, cprime k with hCz
  set Cw : ℝ := ∑ k ∈ Finset.Icc 0 ⌊w⌋₊, cprime k with hCw
  rw [← intervalIntegral.integral_of_le hwz,
    intervalIntegral.integral_congr (g := fun t => f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k)
      (fun t ht => by rw [hderiv_eq t (by rwa [Set.uIcc_of_le hwz] at ht)])] at habel
  have hSfin_eq : (∑ k ∈ Finset.Ioc ⌊w⌋₊ ⌊z⌋₊, f ↑k * cprime k)
      = ∑ p ∈ (Finset.Ioc ⌊w⌋₊ ⌊z⌋₊).filter Nat.Prime, f p / p := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun k _ => mul_cprime_eq f k)
  rw [hSfin_eq] at habel
  have hCint : IntervalIntegrable
      (fun t => f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k) MeasureTheory.volume w z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hwz).mpr
      (integrableOn_mul_sum_Icc cprime (m := 0) hwnn hint_f')
  have hFTC : (∫ t in w..z, f' t) = f z - f w :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv' hf'_int
  have hfwz_le : f w ≤ f z := by
    have hnn : 0 ≤ ∫ t in w..z, f' t :=
      intervalIntegral.integral_nonneg hwz (fun t ht => hf'_nonneg t ht)
    rw [hFTC] at hnn; linarith
  -- the right reference `Ĝ`
  set Ghat : ℝ → ℝ := fun t => Real.log (Real.log z) - Real.log (Real.log t) + 20 / Real.log w
    with hGhatdef
  have hGhatz : Ghat z = 20 / Real.log w := by
    have hGhatze : Ghat z = Real.log (Real.log z) - Real.log (Real.log z) + 20 / Real.log w := rfl
    rw [hGhatze]; ring
  have hGhatderiv : ∀ t ∈ Set.uIcc w z, HasDerivAt Ghat (-(t * Real.log t)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hwz, Set.mem_Icc] at ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hinner : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have houter : HasDerivAt Real.log (Real.log t)⁻¹ (Real.log t) :=
      Real.hasDerivAt_log (ne_of_gt hlogtpos)
    have hcomp : HasDerivAt (fun s => Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t :=
      houter.comp t hinner
    have hval : (Real.log t)⁻¹ * t⁻¹ = (t * Real.log t)⁻¹ := by rw [mul_inv]; ring
    rw [hval] at hcomp
    exact (hcomp.const_sub _).add_const _
  have hGhatcont : ContinuousOn Ghat (Set.uIcc w z) := by
    rw [Set.uIcc_of_le hwz]
    have ht_ne : ∀ t ∈ Set.Icc w z, t ≠ 0 :=
      fun t ht => ne_of_gt (by rw [Set.mem_Icc] at ht; linarith [ht.1])
    have hlogt_ne : ∀ t ∈ Set.Icc w z, Real.log t ≠ 0 :=
      fun t ht => ne_of_gt (Real.log_pos (by rw [Set.mem_Icc] at ht; linarith [ht.1]))
    have hll : ContinuousOn (fun t => Real.log (Real.log t)) (Set.Icc w z) :=
      (continuousOn_id.log ht_ne).log hlogt_ne
    exact (continuousOn_const.sub hll).add continuousOn_const
  have hGhatderiv_int :
      IntervalIntegrable (fun t => -(t * Real.log t)⁻¹) MeasureTheory.volume w z :=
    ((Salt.BrunLower.continuousOn_inv_tlog_real hw hwz).intervalIntegrable).neg
  -- pointwise lower bound `Cz − Ĝ t ≤ C t`
  have hClow : ∀ t ∈ Set.Icc w z,
      Cz - Ghat t ≤ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have ht2 : (2 : ℝ) ≤ t := le_trans hw ht.1
    have hsub := cprime_sum_sub (a := ⌊t⌋₊) (b := ⌊z⌋₊) (Nat.floor_le_floor ht.2)
    rw [← hCz] at hsub
    have hwin := window_prime_sum_le ht2 ht.2
    have hlogtw : Real.log w ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    have h20 : (20 : ℝ) / Real.log t ≤ 20 / Real.log w :=
      div_le_div_of_nonneg_left (by norm_num) hlogw hlogtw
    have hGht : Ghat t = Real.log (Real.log z) - Real.log (Real.log t) + 20 / Real.log w := rfl
    linarith [hsub, hwin, h20, hGht]
  -- window bound at the bottom endpoint: `Cz − Cw ≤ Ĝ w`
  have hCzbound : Cz - Cw ≤ Ghat w := by
    have hsub := cprime_sum_sub (a := ⌊w⌋₊) (b := ⌊z⌋₊) (Nat.floor_le_floor hwz)
    rw [← hCz, ← hCw] at hsub
    have hwin := window_prime_sum_le hw hwz
    have hGhw : Ghat w = Real.log (Real.log z) - Real.log (Real.log w) + 20 / Real.log w := rfl
    linarith [hsub, hwin, hGhw]
  -- comparison: `∫ f'·(Cz−Ĝ) ≤ ∫ f'·C`
  have hmono : (∫ t in w..z, f' t * (Cz - Ghat t))
      ≤ ∫ t in w..z, f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, cprime k := by
    apply intervalIntegral.integral_mono_on hwz
      (hf'_int.mul_continuousOn (continuousOn_const.sub hGhatcont)) hCint
    intro t ht
    exact mul_le_mul_of_nonneg_left (hClow t ht) (hf'_nonneg t ht)
  -- split the reference integral
  have hsplit_int : (∫ t in w..z, f' t * (Cz - Ghat t))
      = Cz * (f z - f w) - ∫ t in w..z, f' t * Ghat t := by
    rw [intervalIntegral.integral_congr (g := fun t => Cz * f' t - f' t * Ghat t)
        (fun t _ => by ring),
      intervalIntegral.integral_sub (hf'_int.const_mul Cz) (hf'_int.mul_continuousOn hGhatcont),
      intervalIntegral.integral_const_mul, hFTC]
  -- integration by parts: `∫ f'·Ĝ = Ĝz·f z − Ĝw·f w + ∫ f·(log log)'`
  have hInteq2 : (∫ t in w..z, -(t * Real.log t)⁻¹ * f t)
      = -∫ t in w..z, f t / (t * Real.log t) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [neg_mul, mul_comm ((t * Real.log t)⁻¹) (f t), ← div_eq_mul_inv])
  have hIBP : (∫ t in w..z, f' t * Ghat t)
      = Ghat z * f z - Ghat w * f w + ∫ t in w..z, f t / (t * Real.log t) := by
    rw [intervalIntegral.integral_congr (g := fun t => Ghat t * f' t) (fun t _ => mul_comm _ _),
      intervalIntegral.integral_mul_deriv_eq_deriv_mul hGhatderiv hderiv' hGhatderiv_int hf'_int,
      hInteq2]
    ring
  -- assemble the Ioc-window bound
  have hfwterm : f w * (Cz - Cw - Ghat w) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfwpos (by linarith [hCzbound])
  have hAset : (∑ p ∈ (Finset.Ioc ⌊w⌋₊ ⌊z⌋₊).filter Nat.Prime, f p / p)
      ≤ (∫ t in w..z, f t / (t * Real.log t)) + (20 / Real.log w) * f z := by
    have e20 : (20 / Real.log w) * f z = 20 * (f z / Real.log w) := by ring
    rw [hGhatz] at hIBP
    nlinarith [habel, hmono, hsplit_int, hIBP, hfwterm, e20]
  -- boundary reconciliation, fold `f w / w ≤ f z / log w`
  have hbdry := primesInWindow_sum_le hw hwz hf_pos
  have hlw : Real.log w ≤ w := le_trans (Real.log_le_sub_one_of_pos hwpos) (by linarith)
  have hfw_ww : f w / w ≤ f z / Real.log w := by
    calc f w / w ≤ f z / w := (div_le_div_iff_of_pos_right hwpos).mpr hfwz_le
      _ ≤ f z / Real.log w := div_le_div_of_nonneg_left hfzpos hlogw hlw
  have e20' : (20 / Real.log w) * f z = 20 * (f z / Real.log w) := by ring
  have e21' : (21 / Real.log w) * f z = 21 * (f z / Real.log w) := by ring
  linarith [hbdry, hAset, hfw_ww, e20', e21']

/-! ## Section 3 — Application A: the `p₂`-sum (BJS Lemma 52, eq. (186)→(187))

The inner `p₂`-carrier `h_p(t) = 1/log(N/(p t))` is positive and increasing on `[y, w]`
(as long as `p·w < N`); `prime_sum_abel_monotone` gives the sharp `∫ h_p d(loglog)` bound. -/

/-- The BJS inner weight `h_p(t) = 1/log(N/(p t))` (Lemma 52). -/
noncomputable def hbjs (N p t : ℝ) : ℝ := (Real.log (N / (p * t)))⁻¹

/-- **Application A — the `p₂`-Abel pass on the concrete carrier.**  For `2 ≤ y ≤ w`,
`0 < p`, and `p·w < N` (so `h_p > 0` throughout `[y, w]`),
`Σ_{p₂ ∈ [y,w) prime} h_p(p₂)/p₂ ≤ ∫_y^w h_p(t)/(t log t) dt + (21/log y)·h_p(w)`.
Direct instantiation of `prime_sum_abel_monotone` with `f = h_p`, whose derivative is
`h_p'(t) = 1/(t·log²(N/pt)) ≥ 0` (increasing). -/
theorem applicationA {N p y w : ℝ} (hy : 2 ≤ y) (hyw : y ≤ w) (hp : 0 < p) (hpwN : p * w < N) :
    ∑ p₂ ∈ Salt.BrunLower.primesInWindow y w, hbjs N p p₂ / p₂
      ≤ (∫ t in y..w, hbjs N p t / (t * Real.log t)) + (21 / Real.log y) * hbjs N p w := by
  have hNpos : 0 < N := by have : 0 < p * w := mul_pos hp (by linarith); linarith
  -- log(N/(p t)) > 0 on [y,w]
  have hlogpos_all : ∀ t ∈ Set.Icc y w, 0 < Real.log (N / (p * t)) := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have htpos : 0 < t := by linarith [ht.1]
    have hpt : 0 < p * t := mul_pos hp htpos
    have hptw : p * t ≤ p * w := by nlinarith [hp.le, ht.2]
    have hptN : p * t < N := lt_of_le_of_lt hptw hpwN
    have hNptgt1 : 1 < N / (p * t) := by rw [lt_div_iff₀ hpt]; linarith
    exact Real.log_pos hNptgt1
  -- the derivative function
  set h' : ℝ → ℝ := fun t => (t * (Real.log (N / (p * t))) ^ 2)⁻¹ with hh'
  refine prime_sum_abel_monotone hy hyw (f' := h') ?_ ?_ ?_ ?_
  · -- HasDerivAt (hbjs N p) (h' t) t
    intro t ht
    rw [Set.mem_Icc] at ht
    have htpos : 0 < t := by linarith [ht.1]
    have hpt : 0 < p * t := mul_pos hp htpos
    have hptw : p * t ≤ p * w := by nlinarith [hp.le, ht.2]
    have hptN : p * t < N := lt_of_le_of_lt hptw hpwN
    have hNptpos : 0 < N / (p * t) := div_pos hNpos hpt
    have hlogpos : 0 < Real.log (N / (p * t)) := hlogpos_all t ⟨ht.1, ht.2⟩
    have hNne : N ≠ 0 := ne_of_gt hNpos
    have htne : t ≠ 0 := ne_of_gt htpos
    have hpne : p ≠ 0 := ne_of_gt hp
    have hd_pt : HasDerivAt (fun s => p * s) p t := by
      simpa using (hasDerivAt_id t).const_mul p
    have hd_frac : HasDerivAt (fun s => N / (p * s)) ((0 * (p * t) - N * p) / (p * t) ^ 2) t :=
      (hasDerivAt_const t N).div hd_pt (ne_of_gt hpt)
    have hd_log : HasDerivAt (fun s => Real.log (N / (p * s)))
        (((0 * (p * t) - N * p) / (p * t) ^ 2) / (N / (p * t))) t :=
      hd_frac.log (ne_of_gt hNptpos)
    have hd_h := hd_log.inv (ne_of_gt hlogpos)
    have hgoal : (hbjs N p) = fun s => (Real.log (N / (p * s)))⁻¹ := rfl
    have hlogne : Real.log (N / (p * t)) ≠ 0 := ne_of_gt hlogpos
    have hNptne : N / (p * t) ≠ 0 := ne_of_gt hNptpos
    have heq : h' t
        = -(((0 * (p * t) - N * p) / (p * t) ^ 2) / (N / (p * t)))
            / (Real.log (N / (p * t))) ^ 2 := by
      simp only [hh']
      field_simp
      ring
    rw [hgoal, heq]
    exact hd_h
  · -- IntervalIntegrable h'
    have hne_pt : ∀ t ∈ Set.Icc y w, (p * t) ≠ 0 := by
      intro t ht; rw [Set.mem_Icc] at ht
      exact ne_of_gt (mul_pos hp (by linarith [ht.1]))
    have hNpt_ne : ∀ t ∈ Set.Icc y w, N / (p * t) ≠ 0 := by
      intro t ht
      exact ne_of_gt (div_pos hNpos (mul_pos hp (by rw [Set.mem_Icc] at ht; linarith [ht.1])))
    have hcont_frac : ContinuousOn (fun t => N / (p * t)) (Set.Icc y w) :=
      continuousOn_const.div (by fun_prop) hne_pt
    have hcont_log : ContinuousOn (fun t => Real.log (N / (p * t))) (Set.Icc y w) :=
      hcont_frac.log hNpt_ne
    have hcont_den : ContinuousOn (fun t => t * (Real.log (N / (p * t))) ^ 2) (Set.Icc y w) :=
      continuousOn_id.mul (hcont_log.pow 2)
    have hden_ne : ∀ t ∈ Set.Icc y w, t * (Real.log (N / (p * t))) ^ 2 ≠ 0 := by
      intro t ht
      have htpos : 0 < t := by rw [Set.mem_Icc] at ht; linarith [ht.1]
      have hlog := hlogpos_all t ht
      positivity
    have hcont : ContinuousOn h' (Set.uIcc y w) := by
      rw [hh', Set.uIcc_of_le hyw]
      exact hcont_den.inv₀ hden_ne
    exact hcont.intervalIntegrable
  · -- positivity of hbjs
    intro t ht
    exact le_of_lt (inv_pos.mpr (hlogpos_all t ht))
  · -- 0 ≤ h' t
    intro t ht
    rw [hh']
    have htpos : 0 < t := by rw [Set.mem_Icc] at ht; linarith [ht.1]
    have hlog := hlogpos_all t ht
    positivity

end Salt.Chen
