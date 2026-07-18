/-
Copyright (c) 2026 Salt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Salt.Chen.TripleCount
import Salt.Chen.BetaSW
import Salt.SW.SiegelClose

/-!
# The interval prime-count lower bound (Chebyshev grade)

`primes_in_Ioc_ge` : there is `c > 0` and `y₀` with
`c·y / log y ≤ #{p prime : y < p ≤ 2y}` for all `y ≥ y₀`.

This is R2's first named gap (VMVT resume map, `Salt/Vmvt/MeanValue.lean`): the
consumer (R2 prime selection) needs `≥ ½k(k²−1) = Θ(k³)` primes in `(y, 2y]`
with `y = x^{1/k}`, which follows once `c·y/log y ≥ Θ(k³)` — absorbed by the
induction's thresholds in the large-`x` regime.

## Route (the corpus supplies the analytic input)

* `Salt.Chen.psiTot_pnt` : `|ψ(x) − x| ≤ K·x/log x` (unconditional, SW gate).
* `Salt.Chen.stripMass_le` : `∑_{n≤x, ¬prime} Λ(n) ≤ √x·(1 + log x)`
  (the ψ−θ proper-prime-power strip).

Chain: `ψ(2y) − ψ(y) ≥ y − 3Ky/log y ≥ y/2` once `log y ≥ 6K`.  Splitting the
interval mass into primes + the strip,
`ψ(2y) − ψ(y) ≤ (#primes)·log(2y) + stripMass(2y)`, so
`(#primes)·log(2y) ≥ y/2 − √(2y)(1+log(2y)) ≥ y/4` once the strip is `≤ y/4`,
whence `#primes ≥ y/(4 log(2y)) ≥ (1/8)·y/log y` (since `log(2y) ≤ 2 log y`).

No `sorry`, no `native_decide`, no new axioms.
-/

open Salt.LS Salt.Chen Salt.SW ArithmeticFunction
open scoped BigOperators

namespace Salt.Vmvt

/-! ## The strip-absorption estimate -/

/-- **`√t·(1 + log t) ≤ t/8` for `t ≥ 2560000`.**  The proper-prime-power strip
`√x·(1+log x)` is `o(x)`; this is the explicit crossover the count needs.  Proof
via nested square roots: with `s₁ = √t`, `s₂ = √s₁`, one has `log t = 2 log s₁ ≤
4 s₂` (`log_le_two_sqrt`), while `t = s₂⁴`, reducing the goal to `40 ≤ s₂`, i.e.
`t ≥ 40⁴ = 2560000`. -/
lemma sqrt_one_add_log_le {t : ℝ} (ht : 2560000 ≤ t) :
    Real.sqrt t * (1 + Real.log t) ≤ t / 8 := by
  have ht0 : (0 : ℝ) < t := by linarith
  set s1 := Real.sqrt t with hs1def
  set s2 := Real.sqrt s1 with hs2def
  have hs1nn : 0 ≤ s1 := Real.sqrt_nonneg t
  have hs2nn : 0 ≤ s2 := Real.sqrt_nonneg s1
  have hs1sq : s1 * s1 = t := Real.mul_self_sqrt ht0.le
  have hs2sq : s2 * s2 = s1 := Real.mul_self_sqrt hs1nn
  -- `s₁ ≥ 1600`
  have hs1ge : (1600 : ℝ) ≤ s1 := by
    have h2 : Real.sqrt (2560000 : ℝ) = 1600 := by
      rw [show (2560000 : ℝ) = 1600 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc (1600 : ℝ) = Real.sqrt 2560000 := h2.symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
      _ = s1 := hs1def.symm
  -- `s₂ ≥ 40`
  have hs2ge : (40 : ℝ) ≤ s2 := by
    have h2 : Real.sqrt (1600 : ℝ) = 40 := by
      rw [show (1600 : ℝ) = 40 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
    calc (40 : ℝ) = Real.sqrt 1600 := h2.symm
      _ ≤ Real.sqrt s1 := Real.sqrt_le_sqrt hs1ge
      _ = s2 := hs2def.symm
  have hs1pos : 0 < s1 := by linarith
  -- `log t ≤ 4 s₂`
  have hlogs1 : Real.log s1 ≤ 2 * s2 := by
    have h := Salt.SW.log_le_two_sqrt hs1pos
    rw [← hs2def] at h; linarith
  have hlogt : Real.log t ≤ 4 * s2 := by
    have hlt : Real.log t = 2 * Real.log s1 := by
      rw [← hs1sq, Real.log_mul (ne_of_gt hs1pos) (ne_of_gt hs1pos)]; ring
    rw [hlt]; linarith
  have h1add : 1 + Real.log t ≤ 5 * s2 := by
    have hs2one : (1 : ℝ) ≤ s2 := by linarith
    linarith
  calc s1 * (1 + Real.log t)
      ≤ s1 * (5 * s2) := mul_le_mul_of_nonneg_left h1add hs1nn
    _ = 5 * (s2 * s2) * s2 := by rw [← hs2sq]; ring
    _ ≤ (s2 * s2) * (s2 * s2) / 8 := by
        nlinarith [hs2ge, hs2nn, mul_nonneg (mul_nonneg hs2nn hs2nn) hs2nn]
    _ = t / 8 := by rw [hs2sq, hs1sq]

/-! ## The interval mass splits as count·log + strip -/

/-- **The interval mass is dominated by the count times `log(2y)` plus the strip.**
`ψ(2y) − ψ(y) = ∑_{y<n≤2y} Λ(n)` splits into the prime part
(`∑_{y<p≤2y} log p ≤ #primes · log(2y)`, each `log p ≤ log(2y)`) and the
proper-prime-power part (`≤ stripMass(2y)`, the strip over `[1,2y]` dominating
the subinterval). -/
lemma psi_diff_le (y : ℕ) :
    psiTot (2 * y) - psiTot y
      ≤ (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ) * Real.log ((2 * y : ℕ) : ℝ)
        + stripMass (2 * y) := by
  set U := 2 * y with hU
  have hyU : y ≤ U := by omega
  have hunion : Finset.Icc 1 U = Finset.Icc 1 y ∪ Finset.Ioc y U := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 y) (Finset.Ioc y U) := by
    simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdiff : psiTot U - psiTot y = ∑ n ∈ Finset.Ioc y U, vonMangoldt n := by
    have : psiTot U = psiTot y + ∑ n ∈ Finset.Ioc y U, vonMangoldt n := by
      unfold psiTot; rw [hunion, Finset.sum_union hdisj]
    linarith
  rw [hdiff]
  -- split each Λ(n) into prime / non-prime parts
  have hsplit : ∑ n ∈ Finset.Ioc y U, vonMangoldt n
      = (∑ n ∈ Finset.Ioc y U, if n.Prime then vonMangoldt n else 0)
        + ∑ n ∈ Finset.Ioc y U, if n.Prime then (0 : ℝ) else vonMangoldt n := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h : n.Prime <;> simp [h]
  rw [hsplit]
  refine add_le_add ?_ ?_
  · -- prime part ≤ count · log U
    have hstep : (∑ n ∈ Finset.Ioc y U, if n.Prime then vonMangoldt n else 0)
        ≤ ∑ n ∈ Finset.Ioc y U, if n.Prime then Real.log (U : ℝ) else 0 := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      by_cases h : n.Prime
      · simp only [if_pos h]
        rw [Finset.mem_Ioc] at hn
        rw [ArithmeticFunction.vonMangoldt_apply_prime h]
        exact Real.log_le_log (by exact_mod_cast h.pos) (by exact_mod_cast hn.2)
      · simp [h]
    calc (∑ n ∈ Finset.Ioc y U, if n.Prime then vonMangoldt n else 0)
        ≤ ∑ n ∈ Finset.Ioc y U, if n.Prime then Real.log (U : ℝ) else 0 := hstep
      _ = (((Finset.Ioc y U).filter Nat.Prime).card : ℝ) * Real.log (U : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  · -- non-prime part ≤ stripMass U
    unfold stripMass
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]; omega
    · intro n _ _
      split_ifs
      · exact le_refl 0
      · exact vonMangoldt_nonneg

/-! ## The Chebyshev-grade interval prime-count lower bound -/

/-- **`π(2y) − π(y) ≥ c·y/log y` for large `y`** (`c = 1/8`).  Chains the
unconditional PNT bound `psiTot_pnt` (giving `ψ(2y) − ψ(y) ≥ y/2` once
`log y ≥ 6K`) through the prime/strip split `psi_diff_le` and the strip estimate
`stripMass_le`+`sqrt_one_add_log_le` (giving the strip `≤ y/4` once
`y ≥ 1280000`).  The threshold `y₀ = max(⌈e^{6K}⌉, 1280000)` folds both. -/
theorem primes_in_Ioc_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
      (c * y / Real.log y) ≤ (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := Salt.Chen.psiTot_pnt
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Real.exp (6 * K))
  refine ⟨1 / 8, by norm_num, max N₀ 1280000, fun y hy => ?_⟩
  -- thresholds
  have hy1 : 1280000 ≤ y := le_trans (le_max_right N₀ 1280000) hy
  have hyN : N₀ ≤ y := le_trans (le_max_left N₀ 1280000) hy
  have hy3 : 3 ≤ y := by omega
  have hy2U : 3 ≤ 2 * y := by omega
  set Y : ℝ := (y : ℝ) with hYdef
  have hYpos : 0 < Y := by rw [hYdef]; exact_mod_cast (by omega : 0 < y)
  have hY1 : (1 : ℝ) < Y := by rw [hYdef]; exact_mod_cast (by omega : 1 < y)
  have hYnn : 0 ≤ Y := le_of_lt hYpos
  have hLy : 0 < Real.log Y := Real.log_pos hY1
  -- `log y ≥ 6K`
  have hylog : 6 * K ≤ Real.log Y := by
    have hexp : Real.exp (6 * K) ≤ Y := by
      rw [hYdef]
      calc Real.exp (6 * K) ≤ (N₀ : ℝ) := hN₀
        _ ≤ (y : ℝ) := by exact_mod_cast hyN
    calc 6 * K = Real.log (Real.exp (6 * K)) := (Real.log_exp _).symm
      _ ≤ Real.log Y := Real.log_le_log (Real.exp_pos _) hexp
  -- `log(2y)` facts
  have hcast : ((2 * y : ℕ) : ℝ) = 2 * Y := by rw [hYdef]; push_cast; ring
  set L2 : ℝ := Real.log ((2 * y : ℕ) : ℝ) with hL2def
  have hL2eq : L2 = Real.log 2 + Real.log Y := by
    rw [hL2def, hcast, Real.log_mul (by norm_num) (ne_of_gt hYpos)]
  have hLy_le_L2 : Real.log Y ≤ L2 := by
    rw [hL2eq]; linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hL2pos : 0 < L2 := lt_of_lt_of_le hLy hLy_le_L2
  have hL2_le : L2 ≤ 2 * Real.log Y := by
    have : Real.log 2 ≤ Real.log Y :=
      Real.log_le_log (by norm_num) (by rw [hYdef]; exact_mod_cast (by omega : 2 ≤ y))
    rw [hL2eq]; linarith
  -- ψ lower bound: `ψ(2y) − ψ(y) ≥ y/2`
  have hb2 := abs_le.mp (hK (2 * y) hy2U)
  have hby := abs_le.mp (hK y hy3)
  rw [← hL2def, hcast] at hb2
  rw [← hYdef] at hby
  set r : ℝ := K * Y / Real.log Y with hrdef
  have hswap : K * (2 * Y) / L2 ≤ K * (2 * Y) / Real.log Y :=
    div_le_div_of_nonneg_left (by nlinarith [hK0, hYnn]) hLy hLy_le_L2
  have hswap2 : K * (2 * Y) / L2 ≤ 2 * r := by
    have h : K * (2 * Y) / Real.log Y = 2 * r := by rw [hrdef]; ring
    linarith
  have h3r : 3 * r ≤ Y / 2 := by
    have hrr : 3 * r = 3 * K * Y / Real.log Y := by rw [hrdef]; ring
    rw [hrr, div_le_iff₀ hLy]
    nlinarith [mul_le_mul_of_nonneg_left hylog hYnn]
  have hpsi2y : 2 * Y - K * (2 * Y) / L2 ≤ psiTot (2 * y) := by linarith [hb2.1]
  have hpsiy : psiTot y ≤ Y + r := by rw [hrdef]; linarith [hby.2]
  have hpsidiff_lb : Y / 2 ≤ psiTot (2 * y) - psiTot y := by
    linarith [hpsi2y, hpsiy, hswap2, h3r]
  -- strip bound: `stripMass(2y) ≤ y/4`
  have hstripU : stripMass (2 * y) ≤ Y / 4 := by
    have h1 := Salt.Chen.stripMass_le (2 * y) (by omega)
    have hge : (2560000 : ℝ) ≤ ((2 * y : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2560000 ≤ 2 * y)
    have h2 := sqrt_one_add_log_le hge
    rw [hcast] at h1 h2
    have h3 : (2 * Y) / 8 = Y / 4 := by ring
    linarith
  -- assemble: `count · log(2y) ≥ y/4`
  have hpd := psi_diff_le y
  rw [← hL2def] at hpd
  set cnt : ℝ := (((Finset.Ioc y (2 * y)).filter Nat.Prime).card : ℝ) with hcntdef
  have hcountlb : Y / 4 ≤ cnt * L2 := by linarith [hpd, hpsidiff_lb, hstripU]
  -- convert to the count lower bound
  have h18 : (0 : ℝ) ≤ 1 / 8 * Y := mul_nonneg (by norm_num) hYnn
  have hfin : (1 / 8 : ℝ) * Y / Real.log Y * L2 ≤ Y / 4 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hLy]
    nlinarith [mul_le_mul_of_nonneg_left hL2_le h18]
  have hmul : (1 / 8 : ℝ) * Y / Real.log Y * L2 ≤ cnt * L2 := le_trans hfin hcountlb
  exact le_of_mul_le_mul_right hmul hL2pos

end Salt.Vmvt
