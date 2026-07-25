/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.MR.MultShiu
import Salt.MR.HalaszIntegers
import Salt.SW.CrushE

/-!
# RENORMALISE — Granville–Soundararajan Lemma 7.1 (the frequency shift)

Source: A. Granville & K. Soundararajan, *Decay of mean-values of multiplicative
functions*, `math/9911246`, p. 22 (§7).  Transcribed from the rendered page.

**GS Lemma 7.1.**  Suppose `f` is a multiplicative function with `|f n| ≤ 1` for all
`n`.  Then for any real `α`

  `∑_{n≤x} f(n) n^{iα} = x^{iα}/(1+iα) · ∑_{n≤x} f(n)
      + O( x/log x · log(e+|α|) · exp(∑_{p≤x} |1−f(p)|/p) )`.

## STEP 0 — the sign re-derivation (the MRT (A.8) conjugate defect)

MRT (A.8) prints the *conjugate* factor.  Re-derived here from GS 7.1 itself.
Put `F n := f n · n^{−it₁}` (multiplicative, `‖F n‖ ≤ 1`) and `α := t₁ − t`.  Then

* `F(n) · n^{iα} = f(n) n^{−it₁} n^{i(t₁−t)} = f(n) n^{−it}`, so
  `∑_{n≤x} F(n) n^{iα} = ∑_{n≤x} f(n) n^{−it}`;
* `∑_{n≤x} F(n) = ∑_{n≤x} f(n) n^{−it₁}`.

Feeding these into GS 7.1 (applied to `F` at `α = t₁ − t`) gives

  `∑_{n≤x} f(n) n^{−it} = x^{i(t₁−t)}/(1 + i(t₁−t)) · ∑_{n≤x} f(n) n^{−it₁} + O(…)`,

so **the factor multiplying the `t₁`-sum is `x^{i(t₁−t)}/(1+i(t₁−t))`** — NOT its
conjugate.  Independent confirmation on GS p. 23 (the Corollary-3 deduction), which
reads `(1/x)∑_{n≤x} f(n) = x^{iy₀}/(1+iy₀) · ∑_{n≤x} f(n)n^{−iy₀} + O(…)`: that is
exactly the display above at `t = 0`, `t₁ = y₀`.  The Lean statements below carry
THIS sign (`renormalise`, `renormalise_shifted`).

Modulus page: `‖x^{iu}/(1+iu)‖ = (1+u²)^{−1/2} ≤ √2/(1+|u|)`, since
`(1+|u|)² ≤ 2(1+u²) ⟺ (1−|u|)² ≥ 0`.  (`renormalise_factor_norm`,
`renormalise_factor_norm_le`.)

## STEP 0.5 — the `κ = 1 → κ = 2` relaxation (the day-1 fail-fast)

VERDICT: **constant-tracking, not structural.**  In `Salt/MR/MultShiu.lean`,

* `hall_tenenbaum_core` (`:783`) uses its `hF1 : ∀ n, F n ≤ 1` at *exactly one* leaf
  step (`:822`), bounding `k · F(p^k) · F(m) ≤ k · F(m)` after
  `ht_valuation_partition`.  All of `ht_first_term`, `ht_second_term_swap`,
  `ht_valuation_partition`, `ht_UA_bound`, `ht_UB_bound` are κ-free.
* `euler_exp_bound` (`:925`) uses `hF1` at *exactly one* leaf step (`:1008`),
  bounding `F(p^{i+2})/p^{i+2} ≤ p^{−(i+2)}`.  `mult_divisor_sum_prod`,
  `geom_tail_sq`, `sum_inv_sq_le` are κ-free.

Both usages are at **prime powers only**, so the κ = 2 versions below take the honest
hypothesis `∀ p k, p.Prime → 1 ≤ k → F (p^k) ≤ 2` (GS's own "`h(p^k) ≤ 2` for all
prime powers"), which is what `h = ‖g‖` actually satisfies — the global `∀ n, F n ≤ 2`
is FALSE for `‖g‖` (e.g. `‖g 6‖ ≤ 4`).  Constants: HT-1's `1 + log 4 + 36` becomes
`1 + 2(log 4 + 36)`; HT-2's `B₂ = 4` becomes `8`.

## Stones

* R1 `hall_tenenbaum_core_two` — Halberstam–Richert / Hall–Tenenbaum at κ = 2 (GS (7.1)).
* R2 `euler_exp_bound_two` — the truncated Euler bound at κ = 2.
* R3 `ht_tail_ratio` — GS (7.2), via `abel_master` with a two-piece weight.
* R4 `sum_conv_unfold` — GS (7.3), the double-sum exchange.
* R5 `geom_sum_crude` — `∑_{m≤z} m^{iα} = z^{1+iα}/(1+iα) + O(1 + |α| log z)`.
  **CRUDE**, not GS's sharp `O(1+α²)`: see the R5 section for the exact defect.
* R6 `renormalise` — GS Lemma 7.1 itself, plus `renormalise_shifted` (the MRT-shaped
  `t/t₁` corollary) and the modulus page `renormalise_factor_norm(_le)`.

Supporting: `eIu` (the `exp (I·u·log y)` power), `mobDatum` (`g = μ ∗ f`, so `f = 1 ∗ g`),
`mobNorm` (`h = ‖g‖`, the κ = 2 sieve datum), `renormaliseConst`.
-/

namespace Salt.MR

open scoped BigOperators
open Finset

/-! ## R1 — the Hall–Tenenbaum core at `κ = 2` (GS (7.1)) -/

/-- **GS (7.1) — Halberstam–Richert at `κ = 2`.**  For non-negative multiplicative `F`
with `F (p^k) ≤ 2` at every prime power and `x ≥ 2`,

  `(∑_{n≤x} F n) · log x ≤ (1 + 2(log 4 + 36)) · x · ∑_{n≤x} F n / n`.

The κ = 1 proof (`hall_tenenbaum_core`) is reused verbatim except at its single
`F(p^k) ≤ 1` leaf, which becomes `F(p^k) ≤ 2`; the whole `∑ F(n) log n` half therefore
picks up the factor `2`. -/
theorem hall_tenenbaum_core_two {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n)
    (hmul : ∀ a b, Nat.Coprime a b → F (a * b) = F a * F b)
    (hFpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → F (p ^ k) ≤ 2) {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n) * Real.log x
      ≤ (1 + 2 * (Real.log 4 + 36)) * x * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n / n) := by
  set N := ⌊x⌋₊ with hNdef
  have hxpos : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hxpos.le
  set W := ∑ n ∈ Finset.Icc 1 N, F n / n with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun n _ => div_nonneg (hF0 n) (by positivity))
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hdecomp : (∑ n ∈ Finset.Icc 1 N, F n) * Real.log x
      = (∑ n ∈ Finset.Icc 1 N, F n * Real.log (x / n))
        + ∑ n ∈ Finset.Icc 1 N, F n * Real.log n := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Real.log_div hxpos.ne' hnpos.ne']; ring
  rw [hdecomp]
  have hfirst : (∑ n ∈ Finset.Icc 1 N, F n * Real.log (x / n)) ≤ x * W :=
    ht_first_term hF0 hxpos N
  have hsecond : (∑ n ∈ Finset.Icc 1 N, F n * Real.log n)
      ≤ 2 * (Real.log 4 + 36) * (N : ℝ) * W := by
    rw [ht_second_term_swap]
    have hstep1 : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), F n * (n.factorization p : ℝ))
        ≤ 2 * ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
          ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), (q.1 : ℝ) * F q.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro p hp
      have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      rw [ht_valuation_partition hmul hpp]
      calc Real.log p * ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), (q.1 : ℝ) * F (p ^ q.1) * F q.2
          ≤ Real.log p * ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), 2 * ((q.1 : ℝ) * F q.2) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) hlogp
            intro q hq
            rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
            obtain ⟨⟨⟨hk1, _⟩, _, _⟩, _⟩ := hq
            have hk : F (p ^ q.1) ≤ 2 := hFpp p q.1 hpp hk1
            have hbase : (0 : ℝ) ≤ (q.1 : ℝ) * F q.2 :=
              mul_nonneg (by positivity) (hF0 q.2)
            nlinarith [hbase, hk]
        _ = 2 * (Real.log p * ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), (q.1 : ℝ) * F q.2) := by
            rw [← Finset.mul_sum]; ring
    refine hstep1.trans ?_
    have hUsplit : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
          ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
            (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)), (q.1 : ℝ) * F q.2)
        = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
            ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => q.1 = 1),
              (q.1 : ℝ) * F q.2)
          + (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log p *
            ∑ q ∈ (((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
              (fun q => ¬ p ∣ q.2 ∧ p ^ q.1 * q.2 ≤ N)).filter (fun q => ¬ q.1 = 1),
              (q.1 : ℝ) * F q.2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro p _
      rw [← mul_add, Finset.sum_filter_add_sum_filter_not]
    rw [hUsplit]
    have hUA := ht_UA_bound hF0 hN1 (F := F)
    have hUB := ht_UB_bound hF0 hN1 (F := F)
    have hexp : 2 * (Real.log 4 + 36) * (N : ℝ) * W
        = 2 * (Real.log 4 * (N : ℝ) * W + 36 * (N : ℝ) * W) := by ring
    rw [hexp]; linarith [hUA, hUB]
  have hcomb : 2 * (Real.log 4 + 36) * (N : ℝ) * W ≤ 2 * (Real.log 4 + 36) * x * W := by
    apply mul_le_mul_of_nonneg_right _ hW0
    exact mul_le_mul_of_nonneg_left hNx (by linarith)
  have hid : (1 + 2 * (Real.log 4 + 36)) * x * W = x * W + 2 * (Real.log 4 + 36) * x * W := by
    ring
  linarith [hfirst, hsecond, hcomb, hid]

/-! ## R2 — the truncated Euler exponential bound at `κ = 2` -/

/-- **The truncated Euler bound at `κ = 2`.**  For non-negative multiplicative `F` with
`F 1 = 1` and `F (p^k) ≤ 2` at every prime power,

  `∑_{n≤N} F n / n ≤ exp((∑_{p≤N} F p / p) + 8)`.

Same route as `euler_exp_bound`; the `ν ≥ 2` geometric tail doubles (`2 r² ↦ 4 r²`),
so the absolute prime-power constant `B₂ = 4` becomes `8`. -/
theorem euler_exp_bound_two {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n)
    (hmul : ∀ a b, Nat.Coprime a b → F (a * b) = F a * F b)
    (hFpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → F (p ^ k) ≤ 2) (hFone : F 1 = 1) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, F n / n)
      ≤ Real.exp ((∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, F p / p) + 8) := by
  set ĝ : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else F n / n, by simp⟩ with hĝdef
  have hĝ_apply : ∀ n, ĝ n = if n = 0 then 0 else F n / n := fun n => by rw [hĝdef]; rfl
  have hĝ_val : ∀ n, n ≠ 0 → ĝ n = F n / (n : ℝ) := fun n hn => by rw [hĝ_apply, if_neg hn]
  have hĝnn : ∀ n, 0 ≤ ĝ n := by
    intro n; rw [hĝ_apply]; split
    · exact le_refl 0
    · exact div_nonneg (hF0 n) (by positivity)
  have hĝmult : ĝ.IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
    · rw [hĝ_apply, if_neg (one_ne_zero), hFone]; norm_num
    · intro m n hm hn hmn
      rw [hĝ_val _ (mul_ne_zero hm hn), hĝ_val _ hm, hĝ_val _ hn, hmul m n hmn]
      push_cast; rw [mul_div_mul_comm]
  set N' := Nat.factorial N with hN'def
  have hN'0 : N' ≠ 0 := Nat.factorial_ne_zero N
  set P := (Finset.Icc 1 N).filter Nat.Prime with hPdef
  have hPF : N'.primeFactors = P := by
    ext p
    rw [Nat.mem_primeFactors, hPdef, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpp, hpdvd, _⟩
      exact ⟨⟨hpp.one_lt.le, hpp.dvd_factorial.mp hpdvd⟩, hpp⟩
    · rintro ⟨⟨_, hpN⟩, hpp⟩
      exact ⟨hpp, hpp.dvd_factorial.mpr hpN, hN'0⟩
  have hstep1 : (∑ n ∈ Finset.Icc 1 N, F n / (n : ℝ)) ≤ ∑ d ∈ N'.divisors, ĝ d := by
    have hsub : Finset.Icc 1 N ⊆ N'.divisors := by
      intro n hn; rw [Finset.mem_Icc] at hn; rw [Nat.mem_divisors]
      exact ⟨Nat.dvd_factorial (by omega) hn.2, hN'0⟩
    have hL : (∑ n ∈ Finset.Icc 1 N, F n / (n : ℝ)) = ∑ n ∈ Finset.Icc 1 N, ĝ n := by
      apply Finset.sum_congr rfl; intro n hn; rw [Finset.mem_Icc] at hn
      rw [hĝ_val n (by omega)]
    rw [hL]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => hĝnn d)
  rw [mult_divisor_sum_prod ĝ hĝmult hN'0, hPF] at hstep1
  refine hstep1.trans ?_
  have hfactor_eq : ∀ p ∈ P, (∑ j ∈ Finset.range (N'.factorization p + 1), ĝ (p ^ j))
      = 1 + ∑ i ∈ Finset.range (N'.factorization p), ĝ (p ^ (i + 1)) := by
    intro p _
    rw [Finset.sum_range_succ', pow_zero, hĝmult.map_one, add_comm]
  rw [Finset.prod_congr rfl hfactor_eq]
  refine (Real.prod_one_add_le_exp_sum P
    (fun _ => Finset.sum_nonneg (fun _ _ => hĝnn _))).trans ?_
  apply Real.exp_le_exp.mpr
  have hper : ∀ p ∈ P, (∑ i ∈ Finset.range (N'.factorization p), ĝ (p ^ (i + 1)))
      ≤ F p / (p : ℝ) + 4 / (p : ℝ) ^ 2 := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp2 : 2 ≤ p := hpp.two_le
    have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hr : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hppos (by norm_num)]; norm_num; exact_mod_cast hp2
    have hpdvd : p ∣ N' := Nat.dvd_of_mem_primeFactors (hPF ▸ hp)
    have hvp : 1 ≤ N'.factorization p := hpp.factorization_pos_of_dvd hN'0 hpdvd
    obtain ⟨w, hw⟩ : ∃ w, N'.factorization p = w + 1 := ⟨N'.factorization p - 1, by omega⟩
    rw [hw, Finset.sum_range_succ']
    have hg1 : ĝ (p ^ (0 + 1)) = F p / (p : ℝ) := by
      rw [zero_add, pow_one, hĝ_val p hpp.pos.ne']
    rw [hg1]
    have htail : (∑ i ∈ Finset.range w, ĝ (p ^ (i + 1 + 1))) ≤ 4 / (p : ℝ) ^ 2 := by
      have hbnd : (∑ i ∈ Finset.range w, ĝ (p ^ (i + 1 + 1)))
          ≤ ∑ i ∈ Finset.range w, 2 * (1 / (p : ℝ)) ^ (i + 2) := by
        apply Finset.sum_le_sum; intro i _
        rw [hĝ_val _ (pow_ne_zero _ hpp.pos.ne'), show i + 1 + 1 = i + 2 from rfl,
          div_pow, one_pow, Nat.cast_pow, mul_one_div]
        gcongr
        exact hFpp p (i + 2) hpp (by omega)
      refine hbnd.trans ?_
      rw [← Finset.mul_sum]
      have hgt := geom_tail_sq hr0 hr w
      have : (2 : ℝ) * ∑ i ∈ Finset.range w, (1 / (p : ℝ)) ^ (i + 2)
          ≤ 2 * (2 * (1 / (p : ℝ)) ^ 2) := by linarith
      refine this.trans (le_of_eq ?_)
      rw [div_pow, one_pow]; ring
    linarith
  refine (Finset.sum_le_sum hper).trans ?_
  rw [Finset.sum_add_distrib]
  have htail2 : (∑ p ∈ P, 4 / (p : ℝ) ^ 2) ≤ 8 := by
    have heq : (∑ p ∈ P, 4 / (p : ℝ) ^ 2) = 4 * ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [heq]
    have hsub : (∑ p ∈ P, 1 / (p : ℝ) ^ 2) ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => by positivity)
    nlinarith [hsub, sum_inv_sq_le N]
  linarith [htail2]

/-! ## R3 — the tail ratio (GS (7.2))

GS deduces (7.2) from (7.1) by *partial summation against `∫ dt/(t log t)`*, giving the
bracket `1/log x − log(1 − log y/log x)`.  Mechanised here in the **honest constant form**
`(2 + log y)/log x` (the freeze does not need GS's exact `2 + O(1/log x)`), by the landed
discrete Abel engine `abel_master` (`MultShiu:65`) run against the TWO-PIECE weight
`w i = min(1/(i+1), y/x)`: the `min` flattens the weight below `x/y` (so `∑_{i<N} w i ≤
1 + (harmonic N − harmonic ⌊x/y⌋) ≤ 2 + log y`, the `log y` saving), while the linear
partial-sum hypothesis is supplied by `hall_tenenbaum_core_two` at the *shifted* scale —
every nonzero term has `n > x/y`, so `log n > log(x/y) ≥ (log x)/2`. -/

/-- **GS (7.2) — the tail ratio.**  For non-negative multiplicative `F` with
`F (p^k) ≤ 2`, and `1 ≤ y ≤ √x` (`y² ≤ x`), `2 ≤ x`:

  `∑_{x/y < n ≤ x} F n / n ≤ 2·C₁·(2 + log y)/log x · ∑_{n≤x} F n / n`,  `C₁ = 1+2(log4+36)`.

The `(1 + log y)/log x` shape is exactly GS's `1/log x − log(1 − log y/log x)` up to
absolute constants on the range `y ≤ √x`. -/
theorem ht_tail_ratio {F : ℕ → ℝ} (hF0 : ∀ n, 0 ≤ F n)
    (hmul : ∀ a b, Nat.Coprime a b → F (a * b) = F a * F b)
    (hFpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → F (p ^ k) ≤ 2)
    {x y : ℝ} (hx : 2 ≤ x) (hy : 1 ≤ y) (hyx : y ^ 2 ≤ x) :
    (∑ n ∈ Finset.Ioc ⌊x / y⌋₊ ⌊x⌋₊, F n / n)
      ≤ 2 * (1 + 2 * (Real.log 4 + 36)) * (2 + Real.log y) / Real.log x
        * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n / n := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  set N := ⌊x⌋₊ with hNdef
  set K := ⌊x / y⌋₊ with hKdef
  set W := ∑ n ∈ Finset.Icc 1 N, F n / n with hWdef
  set C₁ : ℝ := 1 + 2 * (Real.log 4 + 36) with hC₁def
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC₁pos : (0 : ℝ) < C₁ := by rw [hC₁def]; linarith
  have hW0 : 0 ≤ W := Finset.sum_nonneg (fun n _ => div_nonneg (hF0 n) (by positivity))
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  -- `y ≤ √x` in logarithmic form, and the shifted scale `L = log (x/y) ≥ (log x)/2`.
  have hlogy2 : 2 * Real.log y ≤ Real.log x := by
    have h1 : Real.log (y ^ 2) ≤ Real.log x := Real.log_le_log (by positivity) hyx
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hxy1 : (1 : ℝ) ≤ x / y := by rw [le_div_iff₀ hy0]; nlinarith
  have hxy0 : (0 : ℝ) < x / y := by linarith
  set L := Real.log (x / y) with hLdef
  have hLhalf : Real.log x / 2 ≤ L := by
    rw [hLdef, Real.log_div hx0.ne' hy0.ne']; linarith
  have hLpos : 0 < L := by linarith
  -- Basic `K`, `N` facts.
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hxy1)
  have hKN : K ≤ N := Nat.floor_le_floor (div_le_self hx0.le hy)
  have hKgt : x / y < (K : ℝ) + 1 := Nat.lt_floor_add_one (x / y)
  have hKle : (K : ℝ) ≤ x / y := Nat.floor_le hxy0.le
  -- The Abel data: the restricted sequence `a` and the TWO-PIECE weight `w`.
  set a : ℕ → ℝ := fun i => if K < i + 1 ∧ i + 1 ≤ N then F (i + 1) else 0 with hadef
  have ha_val : ∀ i : ℕ, a i = if K < i + 1 ∧ i + 1 ≤ N then F (i + 1) else 0 := fun _ => rfl
  set w : ℕ → ℝ := fun i => min (1 / ((i : ℝ) + 1)) (y / x) with hwdef
  have hw_val : ∀ i : ℕ, w i = min (1 / ((i : ℝ) + 1)) (y / x) := fun _ => rfl
  set c : ℝ := C₁ * W / L with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hw_nn : ∀ i, 0 ≤ w i := by
    intro i; rw [hw_val i]; exact le_min (by positivity) (by positivity)
  have hw_dec : ∀ i, w (i + 1) ≤ w i := by
    intro i
    rw [hw_val (i + 1), hw_val i]
    refine min_le_min ?_ le_rfl
    refine one_div_le_one_div_of_le (by positivity) ?_
    push_cast; linarith
  -- Above `x/y` the `min` is the harmonic weight.
  have hw_eq : ∀ i : ℕ, K < i + 1 → w i = 1 / ((i : ℝ) + 1) := by
    intro i hi
    have hiR : x / y < (i : ℝ) + 1 := by
      have h : ((K : ℝ) + 1) ≤ (i : ℝ) + 1 := by exact_mod_cast (by omega : K + 1 ≤ i + 1)
      linarith
    rw [hw_val i]
    refine min_eq_left ?_
    rw [div_le_div_iff₀ (by positivity) hx0]
    rw [div_lt_iff₀ hy0] at hiR
    nlinarith
  -- The `abel_master` hypothesis: the SHIFTED linear partial-sum bound.
  have hA : ∀ m, (∑ i ∈ Finset.range m, a i) ≤ c * m := by
    intro m
    set M := min m N with hMdef
    rcases le_or_gt M K with hMK | hMK
    · have hzero : (∑ i ∈ Finset.range m, a i) = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        rw [ha_val i]
        refine if_neg ?_
        rintro ⟨h1, h2⟩
        omega
      rw [hzero]
      exact mul_nonneg hc0 (Nat.cast_nonneg m)
    have hM2 : 2 ≤ M := by omega
    have hMm : M ≤ m := by rw [hMdef]; exact min_le_left _ _
    have hMN : M ≤ N := by rw [hMdef]; exact min_le_right _ _
    have htrunc : (∑ i ∈ Finset.range M, a i) = ∑ i ∈ Finset.range m, a i := by
      refine Finset.sum_subset
        (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hMm))
        (fun i hi hni => ?_)
      rw [Finset.mem_range] at hi
      simp only [Finset.mem_range, not_lt] at hni
      rw [ha_val i]
      refine if_neg ?_
      rintro ⟨_, h2⟩
      omega
    have hstep : (∑ i ∈ Finset.range M, a i) ≤ ∑ n ∈ Finset.Icc 1 M, F n := by
      rw [sum_Icc_one_eq_sum_range (fun n => F n) M]
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [ha_val i]
      split
      · exact le_rfl
      · exact hF0 _
    have hMR2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    have hHT := hall_tenenbaum_core_two hF0 hmul hFpp hMR2
    rw [Nat.floor_natCast] at hHT
    have hWM : (∑ n ∈ Finset.Icc 1 M, F n / n) ≤ W := by
      rw [hWdef]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hMN)
        (fun n _ _ => div_nonneg (hF0 n) (by positivity))
    have hSM0 : 0 ≤ ∑ n ∈ Finset.Icc 1 M, F n := Finset.sum_nonneg (fun n _ => hF0 n)
    have hlogM : L ≤ Real.log M := by
      rw [hLdef]
      refine Real.log_le_log hxy0 ?_
      have h : ((K : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast (by omega : K + 1 ≤ M)
      linarith
    have hfinal : (∑ n ∈ Finset.Icc 1 M, F n) * L ≤ C₁ * (M : ℝ) * W := by
      calc (∑ n ∈ Finset.Icc 1 M, F n) * L
          ≤ (∑ n ∈ Finset.Icc 1 M, F n) * Real.log M :=
            mul_le_mul_of_nonneg_left hlogM hSM0
        _ ≤ C₁ * (M : ℝ) * (∑ n ∈ Finset.Icc 1 M, F n / n) := hHT
        _ ≤ C₁ * (M : ℝ) * W := by
            refine mul_le_mul_of_nonneg_left hWM ?_
            positivity
    have hMm' : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hMm
    have hcm : c * (m : ℝ) = C₁ * W * (m : ℝ) / L := by rw [hcdef]; ring
    rw [hcm, le_div_iff₀ hLpos, ← htrunc]
    calc (∑ i ∈ Finset.range M, a i) * L
        ≤ (∑ n ∈ Finset.Icc 1 M, F n) * L := mul_le_mul_of_nonneg_right hstep hLpos.le
      _ ≤ C₁ * (M : ℝ) * W := hfinal
      _ ≤ C₁ * W * (m : ℝ) := by nlinarith [mul_nonneg hC₁pos.le hW0]
  -- Run the discrete Abel engine.
  have habel := abel_master (a := a) (w := w) (c := c) N hA hw_dec hw_nn
  -- Identify the left side.
  have hLHS : (∑ i ∈ Finset.range N, w i * a i) = ∑ n ∈ Finset.Ioc K N, F n / n := by
    have h1 : (∑ i ∈ Finset.range N, w i * a i)
        = ∑ i ∈ Finset.range N, (if K < i + 1 then F (i + 1) / ((i + 1 : ℕ) : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      by_cases hK : K < i + 1
      · rw [ha_val i, if_pos ⟨hK, by omega⟩, hw_eq i hK, if_pos hK]
        push_cast; ring
      · rw [ha_val i, if_neg (fun h => hK h.1), if_neg hK, mul_zero]
    rw [h1, ← sum_Icc_one_eq_sum_range (fun n => if K < n then F n / (n : ℝ) else 0) N,
      ← Finset.sum_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  -- The weight sum: the `min` gives `≤ 1 + (harmonic N − harmonic K) ≤ 2 + log y`.
  have hfilt : (Finset.range N).filter (fun i => i + 1 ≤ K) = Finset.range K := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have hwsum : (∑ i ∈ Finset.range N, w i) ≤ 2 + Real.log y := by
    have hlow : (∑ i ∈ Finset.range K, w i) ≤ 1 := by
      have hb : (∑ i ∈ Finset.range K, w i) ≤ ∑ _i ∈ Finset.range K, y / x :=
        Finset.sum_le_sum (fun i _ => by rw [hw_val i]; exact min_le_right _ _)
      refine hb.trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h1 : (K : ℝ) * (y / x) ≤ (x / y) * (y / x) :=
        mul_le_mul_of_nonneg_right hKle (by positivity)
      have h2 : (x / y) * (y / x) = 1 := by field_simp
      linarith
    have hhigh : (∑ i ∈ (Finset.range N).filter (fun i => ¬ (i + 1 ≤ K)), w i)
        ≤ 1 + Real.log y := by
      have hb : (∑ i ∈ (Finset.range N).filter (fun i => ¬ (i + 1 ≤ K)), w i)
          ≤ ∑ i ∈ (Finset.range N).filter (fun i => ¬ (i + 1 ≤ K)), (1 : ℝ) / ((i : ℝ) + 1) :=
        Finset.sum_le_sum (fun i _ => by rw [hw_val i]; exact min_le_left _ _)
      refine hb.trans ?_
      have hpair := Finset.sum_filter_add_sum_filter_not (Finset.range N)
        (fun i => i + 1 ≤ K) (fun i => (1 : ℝ) / ((i : ℝ) + 1))
      rw [hfilt] at hpair
      rw [sum_range_one_div_succ_eq_harmonic] at hpair
      have h1 : (harmonic N : ℝ) ≤ 1 + Real.log N := by
        have := harmonic_le_one_add_log N
        rw [← sum_range_one_div_succ_eq_harmonic] at hpair ⊢
        exact (sum_range_one_div_succ_eq_harmonic N) ▸ this
      have h2 : Real.log ((K : ℝ) + 1) ≤ (harmonic K : ℝ) := by
        have h := log_add_one_le_harmonic K
        rwa [Nat.cast_add, Nat.cast_one] at h
      have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
      have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have h3 : Real.log (N : ℝ) ≤ Real.log x :=
        Real.log_le_log (by linarith) (Nat.floor_le hx0.le)
      have h4 : Real.log (x / y) ≤ Real.log ((K : ℝ) + 1) := Real.log_le_log hxy0 hKgt.le
      rw [Real.log_div hx0.ne' hy0.ne'] at h4
      have hsum : (∑ i ∈ Finset.range N, (1 : ℝ) / ((i : ℝ) + 1)) = (harmonic N : ℝ) :=
        sum_range_one_div_succ_eq_harmonic N
      rw [hsum] at hpair
      linarith
    have hpair2 := Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun i => i + 1 ≤ K) w
    rw [hfilt] at hpair2
    linarith
  -- Assemble.
  rw [hLHS] at habel
  refine habel.trans ?_
  have hmul2 : c * (∑ i ∈ Finset.range N, w i) ≤ c * (2 + Real.log y) :=
    mul_le_mul_of_nonneg_left hwsum hc0
  refine hmul2.trans ?_
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have hbase : 0 ≤ C₁ * W * (2 + Real.log y) := by positivity
  have hL' : c * (2 + Real.log y) = C₁ * W * (2 + Real.log y) / L := by rw [hcdef]; ring
  have hR' : 2 * C₁ * (2 + Real.log y) / Real.log x * W
      = 2 * (C₁ * W * (2 + Real.log y)) / Real.log x := by ring
  rw [hL', hR', div_le_div_iff₀ hLpos hlogx]
  nlinarith [hbase, hLhalf]

/-! ## The unimodular power `y ↦ y^{iu}`

The corpus writes `y^{iu}` as `Complex.exp (I·u·log y)` (`Salt/MR/HalaszIntegers.lean`),
never as a `cpow` — `cpow`'s norm lemmas are gated off `Re s = 0`.  `eIu` names that form
so the long displays below stay readable; it is *definitionally* the corpus form, so the
`HalaszIntegers` stones transfer by `exact`. -/

/-- `eIu u y = y^{iu}` (real base, purely imaginary exponent), in the corpus's
`exp (I·u·log y)` form. -/
noncomputable def eIu (u y : ℝ) : ℂ := Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ))

theorem eIu_eq (u y : ℝ) :
    eIu u y = Complex.exp (Complex.I * (u : ℂ) * (Real.log y : ℂ)) := rfl

@[simp] theorem norm_eIu (u y : ℝ) : ‖eIu u y‖ = 1 := norm_exp_Iu_log u y

@[simp] theorem eIu_one (u : ℝ) : eIu u 1 = 1 := by
  rw [eIu_eq, Real.log_one]; simp

/-- `y ↦ y^{iu}` is completely multiplicative on the positive reals. -/
theorem eIu_mul (u : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    eIu u (a * b) = eIu u a * eIu u b := by
  rw [eIu_eq, eIu_eq, eIu_eq, Real.log_mul ha.ne' hb.ne', Complex.ofReal_add, mul_add,
    Complex.exp_add]

/-- Additivity in the frequency: `z^{i(u+v)} = z^{iu} · z^{iv}` (no positivity needed). -/
theorem eIu_add (u v z : ℝ) : eIu (u + v) z = eIu u z * eIu v z := by
  rw [eIu_eq, eIu_eq, eIu_eq, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `‖1 + iu‖ ≥ 1`. -/
theorem one_le_norm_one_add_Iu (u : ℝ) : (1 : ℝ) ≤ ‖(1 + Complex.I * (u : ℂ))‖ := by
  rw [norm_one_add_Iu]
  have : (1 : ℝ) = Real.sqrt 1 := by simp
  rw [this]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])

/-- `‖w / (1+iu)‖ ≤ ‖w‖`. -/
theorem norm_div_one_add_Iu_le (u : ℝ) (w : ℂ) :
    ‖w / (1 + Complex.I * (u : ℂ))‖ ≤ ‖w‖ := by
  rw [norm_div]
  rcases eq_or_lt_of_le (one_le_norm_one_add_Iu u) with h | h
  · rw [← h, div_one]
  · rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg w]

/-! ### Bridges: the `HalaszIntegers` stones restated in `eIu` form -/

theorem eIu_intervalIntegrable (u : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t => eIu u t) MeasureTheory.volume a b :=
  (continuousOn_expILog u a b ha hb).intervalIntegrable

/-- `∫₁^b t^{iu} dt = (b^{1+iu} − 1)/(1+iu)` (`exp_int_eval`). -/
theorem eIu_int_eval (u b : ℝ) (hb : 1 ≤ b) :
    (∫ t in (1 : ℝ)..b, eIu u t) = ((b : ℂ) * eIu u b - 1) / (1 + Complex.I * (u : ℂ)) :=
  exp_int_eval u b hb

/-- The sum–integral (Euler–Maclaurin) comparison (`sum_int_comparison`). -/
theorem eIu_sum_int_comparison (u : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖(∑ n ∈ Finset.Icc 1 N, eIu u n) - ∫ t in (1 : ℝ)..(N : ℝ), eIu u t‖
      ≤ 1 + |u| * ∑ k ∈ Finset.range (N - 1), (1 : ℝ) / ((k : ℝ) + 1) :=
  sum_int_comparison u N hN

/-! ## R5 — the geometric-sum estimate (CRUDE form)

GS p. 22 uses the SHARP `∑_{m≤z} m^{iα} = z^{1+iα}/(1+iα) + O(1+α²)`, which needs the
*second-order* Euler–Maclaurin term (the `ψ₁ = ({t}²−{t})/2` antiderivative).  Neither
mathlib nor the corpus has `ψ₁`; the corpus's `expILog_sub_unitIntegral_le`
(`HalaszIntegers:161`) is the first-order MVT bound, whose harmonic sum costs `log z`.
This file therefore lands the **freeze-sanctioned CRUDE form**

  `∑_{m≤z} m^{iα} = z^{1+iα}/(1+iα) + O(1 + |α| log z)`,

and pays for it in `renormalise` by moving the `d`-split from GS's `x/(1+α²)` to
`x/(3+|α|(1+log x))`; the exit factor `log(e+|α|)` becomes `1 + log(3+|α|(1+log x))`
(see the `renormalise` docstring for the exact accounting). -/

/-- **R5 (crude).**  For `z ≥ 1` and real `u`,

  `‖∑_{m≤z} m^{iu} − z^{1+iu}/(1+iu)‖ ≤ 3 + |u|(1 + log z)`.

Three pieces: the sum–integral defect on `[1,⌊z⌋]` (`≤ 1 + |u|(1+log z)`, the harmonic
sum), the sliver `∫_{⌊z⌋}^z` (`≤ 1`, unimodular integrand on a length-`<1` interval), and
the constant `1/(1+iu)` left over by `∫₁^z = (z^{1+iu}−1)/(1+iu)` (`≤ 1`). -/
theorem geom_sum_crude (u : ℝ) {z : ℝ} (hz : 1 ≤ z) :
    ‖(∑ m ∈ Finset.Icc 1 ⌊z⌋₊, eIu u m) - (z : ℂ) * eIu u z / (1 + Complex.I * (u : ℂ))‖
      ≤ 3 + |u| * (1 + Real.log z) := by
  have hz0 : (0 : ℝ) < z := by linarith
  set N := ⌊z⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hz)
  have hNz : (N : ℝ) ≤ z := Nat.floor_le hz0.le
  have hzN : z < (N : ℝ) + 1 := Nat.lt_floor_add_one z
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  have hi1N : IntervalIntegrable (fun t => eIu u t) MeasureTheory.volume 1 (N : ℝ) :=
    eIu_intervalIntegrable u one_pos hN0R
  have hiNz : IntervalIntegrable (fun t => eIu u t) MeasureTheory.volume (N : ℝ) z :=
    eIu_intervalIntegrable u hN0R hz0
  have hsplit : (∫ t in (1 : ℝ)..(N : ℝ), eIu u t) + (∫ t in (N : ℝ)..z, eIu u t)
      = ∫ t in (1 : ℝ)..z, eIu u t :=
    intervalIntegral.integral_add_adjacent_intervals hi1N hiNz
  -- Piece A: the sum–integral defect, with the harmonic sum bounded by `1 + log N`.
  have hA : ‖(∑ m ∈ Finset.Icc 1 N, eIu u m) - ∫ t in (1 : ℝ)..(N : ℝ), eIu u t‖
      ≤ 1 + |u| * (1 + Real.log z) := by
    refine (eIu_sum_int_comparison u N hN1).trans ?_
    have hmono : (∑ k ∈ Finset.range (N - 1), (1 : ℝ) / ((k : ℝ) + 1))
        ≤ ∑ k ∈ Finset.range N, (1 : ℝ) / ((k : ℝ) + 1) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)
      intro i hi; simp only [Finset.mem_range] at *; omega
    have hharm : (∑ k ∈ Finset.range (N - 1), (1 : ℝ) / ((k : ℝ) + 1)) ≤ 1 + Real.log N :=
      le_trans (hmono.trans_eq (sum_range_one_div_succ_eq_harmonic N))
        (harmonic_le_one_add_log N)
    have hlog : Real.log (N : ℝ) ≤ Real.log z := Real.log_le_log hN0R hNz
    nlinarith [abs_nonneg u, hharm, hlog]
  -- Piece B: the sliver `∫_{N}^{z}`, unimodular integrand, length `< 1`.
  have hB : ‖∫ t in (N : ℝ)..z, eIu u t‖ ≤ 1 := by
    have hconst : ‖∫ t in (N : ℝ)..z, eIu u t‖ ≤ 1 * |z - (N : ℝ)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => le_of_eq (norm_eIu u t))
    have : |z - (N : ℝ)| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    linarith
  -- Piece C: the leftover constant `1/(1+iu)`.
  have hC : ‖(1 : ℂ) / (1 + Complex.I * (u : ℂ))‖ ≤ 1 := by
    have := norm_div_one_add_Iu_le u 1
    simpa using this
  -- Assemble.
  have hkey : (∑ m ∈ Finset.Icc 1 N, eIu u m) - (z : ℂ) * eIu u z / (1 + Complex.I * (u : ℂ))
      = ((∑ m ∈ Finset.Icc 1 N, eIu u m) - ∫ t in (1 : ℝ)..(N : ℝ), eIu u t)
        - (∫ t in (N : ℝ)..z, eIu u t) - (1 : ℂ) / (1 + Complex.I * (u : ℂ)) := by
    have h1 : (∫ t in (1 : ℝ)..(N : ℝ), eIu u t) + (∫ t in (N : ℝ)..z, eIu u t)
        = (z : ℂ) * eIu u z / (1 + Complex.I * (u : ℂ))
          - 1 / (1 + Complex.I * (u : ℂ)) := by
      rw [hsplit, eIu_int_eval u z hz, sub_div]
    linear_combination h1
  rw [hkey]
  calc ‖((∑ m ∈ Finset.Icc 1 N, eIu u m) - ∫ t in (1 : ℝ)..(N : ℝ), eIu u t)
          - (∫ t in (N : ℝ)..z, eIu u t) - (1 : ℂ) / (1 + Complex.I * (u : ℂ))‖
      ≤ ‖((∑ m ∈ Finset.Icc 1 N, eIu u m) - ∫ t in (1 : ℝ)..(N : ℝ), eIu u t)
          - (∫ t in (N : ℝ)..z, eIu u t)‖ + ‖(1 : ℂ) / (1 + Complex.I * (u : ℂ))‖ :=
        norm_sub_le _ _
    _ ≤ (‖(∑ m ∈ Finset.Icc 1 N, eIu u m) - ∫ t in (1 : ℝ)..(N : ℝ), eIu u t‖
          + ‖∫ t in (N : ℝ)..z, eIu u t‖) + ‖(1 : ℂ) / (1 + Complex.I * (u : ℂ))‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ 3 + |u| * (1 + Real.log z) := by linarith

/-! ## R4 — the convolution unfolding (GS (7.3)) -/

/-- **GS (7.3) — the double-sum exchange.**  For any `g : ℕ → ℂ` and any real `u`,

  `∑_{n≤N} (∑_{d∣n} g d) n^{iu} = ∑_{d≤N} g(d) d^{iu} ∑_{m≤N/d} m^{iu}`.

Route: `Salt.SW.sum_divisors_eq_hyperbola_asymm` at the degenerate cut `D = N`, `C = 0`
(the `e`-leg and the corner block vanish), applied to `a d = g d · d^{iu}`, `b e = e^{iu}`;
the pointwise identity `d^{iu}·(n/d)^{iu} = n^{iu}` is `eIu_mul`. -/
theorem sum_conv_unfold (u : ℝ) (g : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, g d) * eIu u n)
      = ∑ d ∈ Finset.Icc 1 N, (g d * eIu u d) * ∑ m ∈ Finset.Icc 1 (N / d), eIu u m := by
  have key := Salt.SW.sum_divisors_eq_hyperbola_asymm
    (fun d => g d * eIu u (d : ℝ)) (fun e => eIu u (e : ℝ)) N N 0 le_rfl (Nat.zero_le _)
    (by simp) (by omega)
  rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)] at key
  simp only [Finset.sum_empty, mul_zero, add_zero, sub_zero] at key
  rw [← key]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mem_divisors] at hd
  obtain ⟨hdvd, _⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hq0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd0
  have hcast : ((d : ℝ)) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  have hprod : eIu u (d : ℝ) * eIu u ((n / d : ℕ) : ℝ) = eIu u (n : ℝ) := by
    rw [← eIu_mul u (by exact_mod_cast hd0) (by exact_mod_cast hq0), hcast]
  rw [← hprod]; ring


/-! ## The GS datum `g` with `f = 1 ∗ g` -/

/-- `f` bundled as an `ArithmeticFunction ℂ` (the `n = 0` guard). -/
noncomputable def afOf (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else f n, by simp⟩

theorem afOf_apply (f : ℕ → ℂ) (n : ℕ) : afOf f n = if n = 0 then 0 else f n := rfl

/-- **GS's datum `g`** (p. 22): the multiplicative function with
`g(p^k) = f(p^k) − f(p^{k−1})`, realised as `g = μ ∗ f` so that `f = 1 ∗ g` is free. -/
noncomputable def mobDatum (f : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) * afOf f

/-- `f = 1 ∗ g`: `f n = ∑_{d ∣ n} g d`. -/
theorem mobDatum_conv (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    f n = ∑ d ∈ n.divisors, mobDatum f d := by
  have h : ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
      * mobDatum f = afOf f := by
    rw [mobDatum, ← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  have h2 : (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)
      * mobDatum f) n = afOf f n := by rw [h]
  rw [ArithmeticFunction.coe_zeta_mul_apply, afOf_apply, if_neg hn] at h2
  exact h2.symm

theorem mobDatum_mult {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) :
    (mobDatum f).IsMultiplicative := by
  have hafm : (afOf f).IsMultiplicative := by
    refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
    · rw [afOf_apply, if_neg one_ne_zero, hf1]
    · intro m n hm hn hmn
      rw [afOf_apply, afOf_apply, afOf_apply, if_neg (mul_ne_zero hm hn), if_neg hm,
        if_neg hn, hfmul m n hmn]
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul hafm

/-- **`g(p^k) = f(p^k) − f(p^{k−1})`** — GS's defining relation, obtained by telescoping
`f(p^j) = ∑_{i≤j} g(p^i)` (no Möbius computation needed). -/
theorem mobDatum_prime_pow (f : ℕ → ℂ) {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    mobDatum f (p ^ k) = f (p ^ k) - f (p ^ (k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hS : ∀ j : ℕ, (∑ i ∈ Finset.range (j + 1), mobDatum f (p ^ i)) = f (p ^ j) := by
    intro j
    rw [mobDatum_conv f (pow_ne_zero j hp.pos.ne'), Nat.sum_divisors_prime_pow hp]
  have h2 := hS (m + 1)
  have h3 := hS m
  rw [Finset.sum_range_succ] at h2
  simp only [Nat.add_sub_cancel]
  linear_combination h2 - h3

/-- `h = ‖g‖` — the non-negative multiplicative datum fed to the κ = 2 sieve stones. -/
noncomputable def mobNorm (f : ℕ → ℂ) (n : ℕ) : ℝ := ‖mobDatum f n‖

theorem mobNorm_nonneg (f : ℕ → ℂ) (n : ℕ) : 0 ≤ mobNorm f n := norm_nonneg _

theorem mobNorm_mul {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) (a b : ℕ)
    (hab : Nat.Coprime a b) : mobNorm f (a * b) = mobNorm f a * mobNorm f b := by
  rw [mobNorm, mobNorm, mobNorm, (mobDatum_mult hf1 hfmul).map_mul_of_coprime hab, norm_mul]

theorem mobNorm_one {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) : mobNorm f 1 = 1 := by
  rw [mobNorm, (mobDatum_mult hf1 hfmul).map_one, norm_one]

/-- The κ = 2 datum bound: `‖g(p^k)‖ = ‖f(p^k) − f(p^{k−1})‖ ≤ 2`. -/
theorem mobNorm_prime_pow_le_two {f : ℕ → ℂ} (hfle : ∀ n, ‖f n‖ ≤ 1) (p k : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) : mobNorm f (p ^ k) ≤ 2 := by
  rw [mobNorm, mobDatum_prime_pow f hp hk]
  exact (norm_sub_le _ _).trans (by linarith [hfle (p ^ k), hfle (p ^ (k - 1))])

/-- The exponent datum: `‖g(p)‖ = ‖1 − f(p)‖`. -/
theorem mobNorm_prime {f : ℕ → ℂ} (hf1 : f 1 = 1) {p : ℕ} (hp : p.Prime) :
    mobNorm f p = ‖1 - f p‖ := by
  have h := mobDatum_prime_pow f hp (le_refl 1)
  rw [pow_one] at h
  norm_num [hf1] at h
  rw [mobNorm, h, norm_sub_rev]

/-! ## R6 — the exit (GS Lemma 7.1) -/

/-- The honest-explicit exit constant `28·(1 + 2(log 4 + 36))·e^8`. -/
noncomputable def renormaliseConst : ℝ := 28 * (1 + 2 * (Real.log 4 + 36)) * Real.exp 8

/-- **The general-`u` estimate (the `d`-split).**  With `y = 3 + |u|(1 + log x)` the split
point (GS uses `1 + α²`, which the crude R5 cannot afford), for `y² ≤ x`:

  `‖∑_{n≤x} f(n) n^{iu} − x^{1+iu}/(1+iu) · ∑_{d≤x} g(d)/d‖
      ≤ 2C₁ (5 + 2 log y) (x/log x) ∑_{d≤x} ‖g(d)‖/d`.

`d ≤ x/y` uses R5 (`≤ y` each, times GS (7.1) at scale `x/y`, giving `2C₁ x/log x`);
`x/y < d ≤ x` bounds both the sum and its main term trivially by `x/d`, times GS (7.2)
(`ht_tail_ratio`), giving `4C₁(2 + log y) x/log x`. -/
theorem renormalise_aux {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) (u : ℝ) {x : ℝ} (hx : 2 ≤ x)
    (hyx : (3 + |u| * (1 + Real.log x)) ^ 2 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu u n)
        - (x : ℂ) * eIu u x / (1 + Complex.I * (u : ℂ))
            * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, mobDatum f d / (d : ℂ)‖
      ≤ 2 * (1 + 2 * (Real.log 4 + 36))
          * (5 + 2 * Real.log (3 + |u| * (1 + Real.log x)))
          * (x / Real.log x) * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, mobNorm f d / d := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set y := 3 + |u| * (1 + Real.log x) with hydef
  have hlogx1 : (0 : ℝ) ≤ 1 + Real.log x := by linarith
  have hy3 : (3 : ℝ) ≤ y := by
    rw [hydef]; nlinarith [abs_nonneg u]
  have hy0 : (0 : ℝ) < y := by linarith
  have hx9 : (9 : ℝ) ≤ x := by nlinarith
  set N := ⌊x⌋₊ with hNdef
  set D := ⌊x / y⌋₊ with hDdef
  set Wh := ∑ d ∈ Finset.Icc 1 N, mobNorm f d / d with hWhdef
  set C₁ : ℝ := 1 + 2 * (Real.log 4 + 36) with hC₁def
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC₁1 : (1 : ℝ) ≤ C₁ := by rw [hC₁def]; linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hWh0 : 0 ≤ Wh :=
    Finset.sum_nonneg (fun n _ => div_nonneg (mobNorm_nonneg f n) (by positivity))
  -- the datum's sieve hypotheses
  have hF0 : ∀ n, 0 ≤ mobNorm f n := mobNorm_nonneg f
  have hFm : ∀ a b, Nat.Coprime a b → mobNorm f (a * b) = mobNorm f a * mobNorm f b :=
    mobNorm_mul hf1 hfmul
  have hFpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → mobNorm f (p ^ k) ≤ 2 :=
    fun p k hp hk => mobNorm_prime_pow_le_two hfle p k hp hk
  -- STEP 1: the convolution unfolding (R4).
  have hstep1 : (∑ n ∈ Finset.Icc 1 N, f n * eIu u n)
      = ∑ d ∈ Finset.Icc 1 N, (mobDatum f d * eIu u d)
          * ∑ m ∈ Finset.Icc 1 (N / d), eIu u m := by
    rw [← sum_conv_unfold u ((mobDatum f : ℕ → ℂ)) N]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mem_Icc] at hn
    rw [← mobDatum_conv f (by omega : n ≠ 0)]
  -- STEP 2/3: peel off the main term.
  set Rt : ℕ → ℂ := fun d => (∑ m ∈ Finset.Icc 1 (N / d), eIu u m)
      - ((x / (d : ℝ) : ℝ) : ℂ) * eIu u (x / (d : ℝ)) / (1 + Complex.I * (u : ℂ)) with hRtdef
  have hRt_val : ∀ d : ℕ, Rt d = (∑ m ∈ Finset.Icc 1 (N / d), eIu u m)
      - ((x / (d : ℝ) : ℝ) : ℂ) * eIu u (x / (d : ℝ)) / (1 + Complex.I * (u : ℂ)) :=
    fun _ => rfl
  have hmain : (∑ n ∈ Finset.Icc 1 N, f n * eIu u n)
      - (x : ℂ) * eIu u x / (1 + Complex.I * (u : ℂ))
          * (∑ d ∈ Finset.Icc 1 N, mobDatum f d / (d : ℂ))
      = ∑ d ∈ Finset.Icc 1 N, (mobDatum f d * eIu u d) * Rt d := by
    rw [hstep1, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hxd : (0 : ℝ) < x / (d : ℝ) := by positivity
    have hee : eIu u (d : ℝ) * eIu u (x / (d : ℝ)) = eIu u x := by
      rw [← eIu_mul u hd0 hxd, mul_div_cancel₀ _ hd0.ne']
    have hcast : ((x / (d : ℝ) : ℝ) : ℂ) = (x : ℂ) / (d : ℂ) := by push_cast; ring
    rw [hRt_val d, mul_sub, hcast]
    have hdC : (d : ℂ) ≠ 0 := by
      simpa using (by exact_mod_cast (by omega : d ≠ 0) : (d : ℂ) ≠ 0)
    field_simp
    rw [← hee]
    ring
  rw [hmain]
  -- STEP 4: pass to norms.
  have hnorm : ‖∑ d ∈ Finset.Icc 1 N, (mobDatum f d * eIu u d) * Rt d‖
      ≤ ∑ d ∈ Finset.Icc 1 N, mobNorm f d * ‖Rt d‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl (fun d _ => ?_)))
    rw [norm_mul, norm_mul, norm_eIu, mul_one, mobNorm]
  refine hnorm.trans ?_
  -- STEP 5: the `d`-split at `D = ⌊x/y⌋`.
  have hIccIoc : ∀ k : ℕ, Finset.Icc 1 k = Finset.Ioc 0 k := by
    intro k; ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hDN : D ≤ N := Nat.floor_le_floor (div_le_self hx0.le (by linarith))
  have hsplit : (∑ d ∈ Finset.Icc 1 D, mobNorm f d * ‖Rt d‖)
      + (∑ d ∈ Finset.Ioc D N, mobNorm f d * ‖Rt d‖)
      = ∑ d ∈ Finset.Icc 1 N, mobNorm f d * ‖Rt d‖ := by
    rw [hIccIoc D, hIccIoc N]
    exact Finset.sum_Ioc_consecutive _ (Nat.zero_le D) hDN
  rw [← hsplit]
  -- STEP 6: the small-`d` leg.
  have hxy1 : (1 : ℝ) ≤ x / y := by rw [le_div_iff₀ hy0]; nlinarith
  have hxy2 : (2 : ℝ) ≤ x / y := by rw [le_div_iff₀ hy0]; nlinarith
  have hxy0 : (0 : ℝ) < x / y := by linarith
  have hlogy2 : 2 * Real.log y ≤ Real.log x := by
    have h1 : Real.log (y ^ 2) ≤ Real.log x := Real.log_le_log (by positivity) hyx
    rwa [Real.log_pow, Nat.cast_ofNat] at h1
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hLhalf : Real.log x / 2 ≤ Real.log (x / y) := by
    rw [Real.log_div hx0.ne' hy0.ne']; linarith
  have hLpos : 0 < Real.log (x / y) := by linarith
  have hsmall : (∑ d ∈ Finset.Icc 1 D, mobNorm f d * ‖Rt d‖)
      ≤ 2 * C₁ * (x / Real.log x) * Wh := by
    have hper : ∀ d ∈ Finset.Icc 1 D, mobNorm f d * ‖Rt d‖ ≤ y * mobNorm f d := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hdN : d ≤ N := le_trans hd.2 hDN
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
      have hdx : (d : ℝ) ≤ x := le_trans (by exact_mod_cast hdN) hNx
      have hz1 : (1 : ℝ) ≤ x / (d : ℝ) := by rw [le_div_iff₀ hd0]; linarith
      have hfl : ⌊x / (d : ℝ)⌋₊ = N / d := by
        rw [hNdef, ← Nat.floor_div_natCast x d]
      have hR := geom_sum_crude u hz1
      rw [hfl] at hR
      have hlogxd : Real.log (x / (d : ℝ)) ≤ Real.log x := by
        refine Real.log_le_log (by linarith) ?_
        rw [div_le_iff₀ hd0]; nlinarith
      have hRy : ‖Rt d‖ ≤ y := by
        rw [hRt_val d]
        refine hR.trans ?_
        rw [hydef]
        nlinarith [abs_nonneg u]
      calc mobNorm f d * ‖Rt d‖ ≤ mobNorm f d * y :=
            mul_le_mul_of_nonneg_left hRy (hF0 d)
        _ = y * mobNorm f d := by ring
    refine (Finset.sum_le_sum hper).trans ?_
    rw [← Finset.mul_sum]
    -- GS (7.1) at scale `x/y`.
    have hHT := hall_tenenbaum_core_two hF0 hFm hFpp hxy2
    rw [← hDdef] at hHT
    have hWD : (∑ d ∈ Finset.Icc 1 D, mobNorm f d / d) ≤ Wh := by
      rw [hWhdef]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hDN)
        (fun n _ _ => div_nonneg (hF0 n) (by positivity))
    have hSD0 : 0 ≤ ∑ d ∈ Finset.Icc 1 D, mobNorm f d :=
      Finset.sum_nonneg (fun n _ => hF0 n)
    have hbnd : (∑ d ∈ Finset.Icc 1 D, mobNorm f d) * (Real.log x / 2) ≤ C₁ * (x / y) * Wh := by
      calc (∑ d ∈ Finset.Icc 1 D, mobNorm f d) * (Real.log x / 2)
          ≤ (∑ d ∈ Finset.Icc 1 D, mobNorm f d) * Real.log (x / y) :=
            mul_le_mul_of_nonneg_left hLhalf hSD0
        _ ≤ C₁ * (x / y) * (∑ d ∈ Finset.Icc 1 D, mobNorm f d / d) := hHT
        _ ≤ C₁ * (x / y) * Wh := by
            refine mul_le_mul_of_nonneg_left hWD ?_
            have : (0 : ℝ) ≤ x / y := by positivity
            nlinarith
    have h4 : 2 * y * (C₁ * (x / y) * Wh) = 2 * C₁ * x * Wh := by field_simp
    have h3 := mul_le_mul_of_nonneg_left hbnd (by linarith : (0 : ℝ) ≤ 2 * y)
    rw [h4] at h3
    have hexp : y * (∑ d ∈ Finset.Icc 1 D, mobNorm f d) * Real.log x
        = 2 * y * ((∑ d ∈ Finset.Icc 1 D, mobNorm f d) * (Real.log x / 2)) := by ring
    have hA : y * (∑ d ∈ Finset.Icc 1 D, mobNorm f d) * Real.log x ≤ 2 * C₁ * x * Wh := by
      rw [hexp]; exact h3
    have hP : 2 * C₁ * (x / Real.log x) * Wh * Real.log x = 2 * C₁ * x * Wh := by
      field_simp
    refine le_of_mul_le_mul_right ?_ hlogx
    rw [hP]; exact hA
  -- STEP 7: the large-`d` leg.
  have hlarge : (∑ d ∈ Finset.Ioc D N, mobNorm f d * ‖Rt d‖)
      ≤ 4 * C₁ * (2 + Real.log y) * (x / Real.log x) * Wh := by
    have hper : ∀ d ∈ Finset.Ioc D N,
        mobNorm f d * ‖Rt d‖ ≤ 2 * x * (mobNorm f d / d) := by
      intro d hd
      rw [Finset.mem_Ioc] at hd
      have hd0 : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (by omega : 0 < d)
      have hRb : ‖Rt d‖ ≤ 2 * x / (d : ℝ) := by
        rw [hRt_val d]
        refine (norm_sub_le _ _).trans ?_
        have h1 : ‖∑ m ∈ Finset.Icc 1 (N / d), eIu u m‖ ≤ x / (d : ℝ) := by
          have hb : ‖∑ m ∈ Finset.Icc 1 (N / d), eIu u (m : ℝ)‖ ≤ ((N / d : ℕ) : ℝ) := by
            refine (norm_sum_le _ _).trans ?_
            have hle : ∀ m ∈ Finset.Icc 1 (N / d), ‖eIu u (m : ℝ)‖ ≤ (1 : ℝ) :=
              fun m _ => le_of_eq (norm_eIu u (m : ℝ))
            refine (Finset.sum_le_sum hle).trans ?_
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            simp [Nat.card_Icc]
          refine hb.trans ?_
          have hstep : ((N : ℝ)) / (d : ℝ) ≤ x / (d : ℝ) := by gcongr
          exact le_trans Nat.cast_div_le hstep
        have h2 : ‖((x / (d : ℝ) : ℝ) : ℂ) * eIu u (x / (d : ℝ))
            / (1 + Complex.I * (u : ℂ))‖ ≤ x / (d : ℝ) := by
          refine (norm_div_one_add_Iu_le u _).trans ?_
          rw [norm_mul, norm_eIu, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
        rw [show 2 * x / (d : ℝ) = x / (d : ℝ) + x / (d : ℝ) by ring]
        linarith
      calc mobNorm f d * ‖Rt d‖ ≤ mobNorm f d * (2 * x / (d : ℝ)) :=
            mul_le_mul_of_nonneg_left hRb (hF0 d)
        _ = 2 * x * (mobNorm f d / d) := by ring
    refine (Finset.sum_le_sum hper).trans ?_
    rw [← Finset.mul_sum]
    have htail := ht_tail_ratio hF0 hFm hFpp hx (by linarith : (1 : ℝ) ≤ y) hyx
    rw [← hNdef, ← hDdef, ← hC₁def, ← hWhdef] at htail
    have h2x : (0 : ℝ) ≤ 2 * x := by linarith
    refine (mul_le_mul_of_nonneg_left htail h2x).trans (le_of_eq ?_)
    field_simp
    ring
  -- STEP 8: assemble.
  have hfinal : 2 * C₁ * (x / Real.log x) * Wh
      + 4 * C₁ * (2 + Real.log y) * (x / Real.log x) * Wh
      = 2 * C₁ * (5 + 2 * Real.log y) * (x / Real.log x) * Wh := by ring
  linarith [hsmall, hlarge, hfinal]

theorem renormaliseConst_eq :
    renormaliseConst = 28 * (1 + 2 * (Real.log 4 + 36)) * Real.exp 8 := rfl

theorem one_le_exp_eight : (1 : ℝ) ≤ Real.exp 8 := by
  rw [show (1 : ℝ) = Real.exp 0 by simp]
  exact Real.exp_le_exp.mpr (by norm_num)

@[simp] theorem eIu_zero (v : ℝ) : eIu 0 v = 1 := by
  rw [eIu_eq]; norm_num

/-- The `α = 0` instance of `renormalise_aux` (the "use twice" step): it is what
eliminates `∑_{d≤x} g(d)/d` from the final statement. -/
theorem renormalise_aux_zero {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 2 ≤ x) (hx9 : (9 : ℝ) ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n)
        - (x : ℂ) * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, mobDatum f d / (d : ℂ)‖
      ≤ 2 * (1 + 2 * (Real.log 4 + 36)) * (5 + 2 * Real.log 3) * (x / Real.log x)
          * ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, mobNorm f d / d := by
  have h := renormalise_aux hf1 hfmul hfle 0 hx (by norm_num; linarith)
  simp only [abs_zero, zero_mul, add_zero, eIu_zero, Complex.ofReal_zero, mul_zero,
    mul_one, div_one] at h
  exact h

/-- **GS Lemma 7.1 (R6, the exit).**  For multiplicative `f` with `‖f n‖ ≤ 1`, any real
`α` and `x ≥ 2`:

  `‖∑_{n≤x} f(n) n^{iα} − x^{iα}/(1+iα) · ∑_{n≤x} f(n)‖
      ≤ C · (x/log x) · (1 + log(3 + |α|(1 + log x))) · exp(∑_{p≤x} ‖1 − f(p)‖/p)`

with `C = 28·(1 + 2(log 4 + 36))·e⁸` (`renormaliseConst`).

**Sign (STEP 0):** the factor is `x^{iα}/(1+iα)`, NOT its conjugate — see the module
docstring for the re-derivation and the GS p. 23 cross-check.

**Honest deviation from GS.**  GS's factor is `log(e+|α|)`; here it is
`1 + log(3 + |α|(1 + log x))`.  The extra `log log x` is the exact price of the CRUDE
R5 (`geom_sum_crude`): GS's `∑_{m≤z} m^{iα} = z^{1+iα}/(1+iα) + O(1+α²)` needs the
second-order Euler–Maclaurin term (`ψ₁`), which neither mathlib nor the corpus has.  The
`d`-split therefore moves from `x/(1+α²)` to `x/(3+|α|(1+log x))`.  Landing the sharp R5
would restore GS's factor verbatim with no other change to this proof.

Proof: `renormalise_aux` twice — once at `α`, once at `0` — the second instance turning
`x·∑_{d≤x} g(d)/d` into `∑_{n≤x} f(n)`; then `euler_exp_bound_two` on `∑ ‖g(d)‖/d`, whose
`ν = 1` Euler factor is exactly `∑_{p≤x} ‖g(p)‖/p = ∑_{p≤x} ‖1 − f(p)‖/p`.  Beyond
`(3+|α|(1+log x))² > x` the statement is discharged by the trivial bound. -/
theorem renormalise {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) (α : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu α n)
        - eIu α x / (1 + Complex.I * (α : ℂ)) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n‖
      ≤ renormaliseConst * (x / Real.log x)
          * (1 + Real.log (3 + |α| * (1 + Real.log x)))
          * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, ‖1 - f p‖ / p) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  set N := ⌊x⌋₊ with hNdef
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  set y := 3 + |α| * (1 + Real.log x) with hydef
  have hy3 : (3 : ℝ) ≤ y := by rw [hydef]; nlinarith [abs_nonneg α]
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  set C₁ : ℝ := 1 + 2 * (Real.log 4 + 36) with hC₁def
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC₁1 : (1 : ℝ) ≤ C₁ := by rw [hC₁def]; linarith
  set Esum := ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ‖1 - f p‖ / p with hEdef
  have hEsum0 : 0 ≤ Esum :=
    Finset.sum_nonneg (fun p _ => div_nonneg (norm_nonneg _) (by positivity))
  have hE1 : (1 : ℝ) ≤ Real.exp Esum := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]; exact Real.exp_le_exp.mpr hEsum0
  have hP0 : (0 : ℝ) ≤ x / Real.log x := by positivity
  have hb1 : ‖eIu α x / (1 + Complex.I * (α : ℂ))‖ ≤ 1 := by
    refine (norm_div_one_add_Iu_le α _).trans ?_
    rw [norm_eIu]
  have hRC : (28 : ℝ) ≤ renormaliseConst := by
    rw [renormaliseConst_eq]
    nlinarith [one_le_exp_eight, hlog4]
  rcases le_or_gt (y ^ 2) x with hyx | hyx
  · -- MAIN BRANCH
    have hx9 : (9 : ℝ) ≤ x := by nlinarith
    set Wh := ∑ d ∈ Finset.Icc 1 N, mobNorm f d / d with hWhdef
    have hWh0 : 0 ≤ Wh :=
      Finset.sum_nonneg (fun n _ => div_nonneg (mobNorm_nonneg f n) (by positivity))
    have haux := renormalise_aux hf1 hfmul hfle α hx (by rw [← hydef]; exact hyx)
    have haux0 := renormalise_aux_zero hf1 hfmul hfle hx hx9
    rw [← hNdef, ← hydef, ← hC₁def, ← hWhdef] at haux
    rw [← hNdef, ← hC₁def, ← hWhdef] at haux0
    set Gsum := ∑ d ∈ Finset.Icc 1 N, mobDatum f d / (d : ℂ) with hGdef
    have hcomb : (∑ n ∈ Finset.Icc 1 N, f n * eIu α n)
        - eIu α x / (1 + Complex.I * (α : ℂ)) * (∑ n ∈ Finset.Icc 1 N, f n)
        = ((∑ n ∈ Finset.Icc 1 N, f n * eIu α n)
            - (x : ℂ) * eIu α x / (1 + Complex.I * (α : ℂ)) * Gsum)
          - eIu α x / (1 + Complex.I * (α : ℂ))
              * ((∑ n ∈ Finset.Icc 1 N, f n) - (x : ℂ) * Gsum) := by ring
    rw [hcomb]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    have hmulb : ‖eIu α x / (1 + Complex.I * (α : ℂ))‖
        * ‖(∑ n ∈ Finset.Icc 1 N, f n) - (x : ℂ) * Gsum‖
        ≤ 1 * (2 * C₁ * (5 + 2 * Real.log 3) * (x / Real.log x) * Wh) := by
      refine mul_le_mul hb1 haux0 (norm_nonneg _) zero_le_one
    -- the two errors, combined
    have hsum : 2 * C₁ * (5 + 2 * Real.log y) * (x / Real.log x) * Wh
        + 1 * (2 * C₁ * (5 + 2 * Real.log 3) * (x / Real.log x) * Wh)
        ≤ 28 * C₁ * (1 + Real.log y) * (x / Real.log x) * Wh := by
      have hL3y : Real.log 3 ≤ Real.log y := Real.log_le_log (by norm_num) hy3
      have hbase : (0 : ℝ) ≤ C₁ * (x / Real.log x) * Wh := by
        have : (0 : ℝ) ≤ C₁ := by linarith
        positivity
      nlinarith [hbase, hL3y, hlogy0]
    -- the Euler bound on `Wh`
    have hWhbnd : Wh ≤ Real.exp Esum * Real.exp 8 := by
      have hF0 : ∀ n, 0 ≤ mobNorm f n := mobNorm_nonneg f
      have hFm : ∀ a b, Nat.Coprime a b → mobNorm f (a * b) = mobNorm f a * mobNorm f b :=
        mobNorm_mul hf1 hfmul
      have hFpp : ∀ p k : ℕ, p.Prime → 1 ≤ k → mobNorm f (p ^ k) ≤ 2 :=
        fun p k hp hk => mobNorm_prime_pow_le_two hfle p k hp hk
      have h := euler_exp_bound_two hF0 hFm hFpp (mobNorm_one hf1 hfmul) N
      have hcongr : (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, mobNorm f p / p) = Esum :=
        Finset.sum_congr rfl (fun p hp => by
          rw [mobNorm_prime hf1 (Finset.mem_filter.mp hp).2])
      rw [hcongr, Real.exp_add] at h
      exact h
    have hfin : 28 * C₁ * (1 + Real.log y) * (x / Real.log x) * Wh
        ≤ renormaliseConst * (x / Real.log x) * (1 + Real.log y) * Real.exp Esum := by
      have hc : (0 : ℝ) ≤ 28 * C₁ * (1 + Real.log y) * (x / Real.log x) := by
        have : (0 : ℝ) ≤ C₁ := by linarith
        positivity
      have h1 : 28 * C₁ * (1 + Real.log y) * (x / Real.log x) * Wh
          ≤ 28 * C₁ * (1 + Real.log y) * (x / Real.log x) * (Real.exp Esum * Real.exp 8) :=
        mul_le_mul_of_nonneg_left hWhbnd hc
      refine h1.trans (le_of_eq ?_)
      rw [renormaliseConst_eq, ← hC₁def]; ring
    linarith [haux, hmulb, hsum, hfin]
  · -- TRIVIAL BRANCH: `y > √x`, so `1 + log y > (log x)/2` and `28·(x/log x)·(log x/2) = 14x`.
    have hlogxy : Real.log x < 2 * Real.log y := by
      have h1 : Real.log x < Real.log (y ^ 2) := Real.log_lt_log hx0 hyx
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hQ : Real.log x / 2 ≤ 1 + Real.log y := by linarith
    have htriv : ‖(∑ n ∈ Finset.Icc 1 N, f n * eIu α n)
        - eIu α x / (1 + Complex.I * (α : ℂ)) * (∑ n ∈ Finset.Icc 1 N, f n)‖ ≤ 2 * x := by
      have hs1 : ‖∑ n ∈ Finset.Icc 1 N, f n * eIu α n‖ ≤ (N : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        have hle : ∀ n ∈ Finset.Icc 1 N, ‖f n * eIu α n‖ ≤ (1 : ℝ) := by
          intro n _; rw [norm_mul, norm_eIu, mul_one]; exact hfle n
        refine (Finset.sum_le_sum hle).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        simp [Nat.card_Icc]
      have hs2 : ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ (N : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum (fun n (_ : n ∈ Finset.Icc 1 N) => hfle n)).trans ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        simp [Nat.card_Icc]
      have hs3 : ‖eIu α x / (1 + Complex.I * (α : ℂ)) * (∑ n ∈ Finset.Icc 1 N, f n)‖
          ≤ (N : ℝ) := by
        rw [norm_mul]
        calc ‖eIu α x / (1 + Complex.I * (α : ℂ))‖ * ‖∑ n ∈ Finset.Icc 1 N, f n‖
            ≤ 1 * (N : ℝ) := mul_le_mul hb1 hs2 (norm_nonneg _) zero_le_one
          _ = (N : ℝ) := one_mul _
      refine (norm_sub_le _ _).trans ?_
      linarith
    refine htriv.trans ?_
    have hA : (28 : ℝ) * (x / Real.log x) * (Real.log x / 2) * 1 = 14 * x := by
      field_simp; ring
    have hstep : (28 : ℝ) * (x / Real.log x) * (Real.log x / 2) * 1
        ≤ renormaliseConst * (x / Real.log x) * (1 + Real.log y) * Real.exp Esum := by
      have hQ0 : (0 : ℝ) ≤ Real.log x / 2 := by linarith
      gcongr
    linarith [hA, hstep]

/-! ## The modulus page (`(1+u²)^{−1/2} ≤ √2/(1+|u|)`) and the MRT-shaped corollary -/

theorem renormalise_factor_norm (v z : ℝ) :
    ‖eIu v z / (1 + Complex.I * (v : ℂ))‖ = 1 / Real.sqrt (1 + v ^ 2) := by
  rw [norm_div, norm_eIu, norm_one_add_Iu]

theorem renormalise_factor_norm_le (v : ℝ) :
    (1 : ℝ) / Real.sqrt (1 + v ^ 2) ≤ Real.sqrt 2 / (1 + |v|) := by
  have h1 : (0 : ℝ) < Real.sqrt (1 + v ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h2 : (0 : ℝ) < 1 + |v| := by positivity
  rw [div_le_div_iff₀ h1 h2, one_mul]
  have h3 : Real.sqrt 2 * Real.sqrt (1 + v ^ 2) = Real.sqrt (2 * (1 + v ^ 2)) :=
    (Real.sqrt_mul (by norm_num) _).symm
  rw [h3]
  have h4 : (1 + |v|) ^ 2 ≤ 2 * (1 + v ^ 2) := by
    nlinarith [sq_abs v, abs_nonneg v, sq_nonneg (1 - |v|)]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq h2.le] at h5

/-- `n ↦ n^{iv}` twists a multiplicative `f` into a multiplicative function. -/
theorem eIu_twist_mult {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b) (v : ℝ) :
    ∀ a b : ℕ, Nat.Coprime a b →
      f (a * b) * eIu v ((a * b : ℕ) : ℝ) = (f a * eIu v a) * (f b * eIu v b) := by
  intro a b hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have hb1 : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb1; simp [hf1]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1; simp [hf1]
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hcast : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by push_cast; ring
  rw [hfmul a b hab, hcast, eIu_mul v ha0 hb0]
  ring

/-- **The MRT-shaped corollary (correct sign).**  Applying `renormalise` to
`F n = f n · n^{−it₁}` at `α = t₁ − t` (STEP 0) gives

  `∑_{n≤x} f(n) n^{−it} = x^{i(t₁−t)}/(1+i(t₁−t)) · ∑_{n≤x} f(n) n^{−it₁} + O(…)`,

i.e. the factor multiplying the `t₁`-sum is `x^{i(t₁−t)}/(1+i(t₁−t))`, NOT the conjugate
printed by MRT (A.8).  Its modulus is `(1+(t₁−t)²)^{−1/2} ≤ √2/(1+|t₁−t|)`
(`renormalise_factor_norm`, `renormalise_factor_norm_le`). -/
theorem renormalise_shifted {f : ℕ → ℂ} (hf1 : f 1 = 1)
    (hfmul : ∀ a b, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfle : ∀ n, ‖f n‖ ≤ 1) (t t₁ : ℝ) {x : ℝ} (hx : 2 ≤ x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t) n)
        - eIu (t₁ - t) x / (1 + Complex.I * ((t₁ - t : ℝ) : ℂ))
            * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t₁) n‖
      ≤ renormaliseConst * (x / Real.log x)
          * (1 + Real.log (3 + |t₁ - t| * (1 + Real.log x)))
          * Real.exp (∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime,
              ‖1 - f p * eIu (-t₁) p‖ / p) := by
  set F : ℕ → ℂ := fun n => f n * eIu (-t₁) n with hFdef
  have hF1 : F 1 = 1 := by rw [hFdef]; simp [hf1]
  have hFmul : ∀ a b, Nat.Coprime a b → F (a * b) = F a * F b := by
    intro a b hab; rw [hFdef]; exact eIu_twist_mult hf1 hfmul (-t₁) a b hab
  have hFle : ∀ n, ‖F n‖ ≤ 1 := by
    intro n; rw [hFdef]; simp only; rw [norm_mul, norm_eIu, mul_one]; exact hfle n
  have hkey : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, F n * eIu (t₁ - t) n := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hFdef, mul_assoc, ← eIu_add, show -t₁ + (t₁ - t) = -t from by ring]
  rw [hkey]
  exact renormalise hF1 hFmul hFle (t₁ - t) hx

end Salt.MR
