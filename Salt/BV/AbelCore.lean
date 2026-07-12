/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.BV.Abel
import Salt.BV.SWChar
import Salt.BV.Headline

/-!
# V4-core-2 — discharging the discretized-Abel core `PsiToPiCore`

Design: `docs/blueprints/bv.md`, node `V4` and `docs/blueprints/flags.md`
(the V4-core entry). This module discharges the genuine analytic heart of the
ψ→π transfer that `Salt/BV/Abel.lean` isolated as the single hypothesis
`PsiToPiCore`.
-/

namespace Salt.BV

open Finset Filter Salt.LS Salt.Maynard ArithmeticFunction
open scoped BigOperators

/-! ## The prime-power correction weight and its freight bound

The Abel identity below expresses `π(x;q,a)` through ψ-partial-sums plus a
*prime-power correction* `∑ ppTerm n`, where `ppTerm n = Λ(n)/log n − 1_{n prime}`
is `0` on primes and non-prime-powers and `1/k` on a proper prime power `p^k`.
The total correction is controlled by `ψ − θ` (mathlib's `psi_sub_theta_le`),
which lands the `√x·log x` freight the budget needs. -/

/-- The per-`n` prime-power correction weight `Λ(n)/log n − 1_{n prime}`. -/
noncomputable def ppTerm (n : ℕ) : ℝ :=
  vonMangoldt n / Real.log n - (if n.Prime then 1 else 0)

/-- On a prime, the correction vanishes: `Λ(p)/log p = 1`. -/
lemma ppTerm_prime {p : ℕ} (hp : p.Prime) : ppTerm p = 0 := by
  have hpos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  unfold ppTerm
  rw [if_pos hp, vonMangoldt_apply_prime hp, div_self hpos.ne', sub_self]

/-- The correction is nonnegative (`Λ ≥ 0`, `log n ≥ 0`; `= 1` on primes). -/
lemma ppTerm_nonneg (n : ℕ) : 0 ≤ ppTerm n := by
  unfold ppTerm
  by_cases hp : n.Prime
  · have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hp.one_lt)
    rw [if_pos hp, vonMangoldt_apply_prime hp, div_self hpos.ne', sub_self]
  · rw [if_neg hp, sub_zero]
    exact div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- Log-weighted, the correction is `Λ(n) − 1_{n prime}·log n` (for `n ≥ 2`). -/
lemma ppTerm_mul_log {n : ℕ} (hn : 2 ≤ n) :
    ppTerm n * Real.log n = vonMangoldt n - (if n.Prime then Real.log n else 0) := by
  have hpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  unfold ppTerm
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
  · rw [if_neg hp, if_neg hp, sub_zero, sub_zero, div_mul_cancel₀ _ hpos.ne']

/-- **Prime-power freight (log-weighted).** `∑_{1<n≤x} (ppTerm n)·log n = ψ(x) − θ(x)`,
the von Mangoldt mass on the non-primes, which mathlib bounds by `2√x·log x`. -/
lemma sum_ppTerm_mul_log_eq (x : ℕ) :
    ∑ n ∈ Finset.Ioc 1 x, ppTerm n * Real.log n
      = Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
  have hfloor : ⌊(x : ℝ)⌋₊ = x := Nat.floor_natCast x
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, hfloor]
  -- rewrite each term as `if ¬n.Prime then Λ n else 0`
  have hterm : ∀ n ∈ Finset.Ioc 1 x, ppTerm n * Real.log n
      = (if ¬ n.Prime then vonMangoldt n else (0 : ℝ)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [ppTerm_mul_log hn.1]
    by_cases hp : n.Prime
    · rw [if_neg (not_not.mpr hp), if_pos hp, vonMangoldt_apply_prime hp, sub_self]
    · rw [if_pos hp, if_neg hp, sub_zero]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  -- bridge `Ioc 1 x` to `Ioc 0 x` (the `n = 1` term is a non-prime with `Λ 1 = 0`)
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  · intro n hn hn'
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    have hn1 : n = 1 := by
      by_contra hne
      exact hn' (by rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩)
    subst hn1
    exact vonMangoldt_apply_one

/-- **Prime-power freight bound.** The unweighted correction sum is `≤ (ψ−θ)/log 4`,
hence `≤ (2√x·log x)/log 4`. Each positive `ppTerm n` sits on a proper prime power
`n ≥ 4`, where `log n ≥ log 4`, so `ppTerm n ≤ ppTerm n · log n / log 4`. -/
lemma sum_ppTerm_le (x : ℕ) :
    ∑ n ∈ Finset.Ioc 1 x, ppTerm n
      ≤ Real.sqrt x * Real.log x / Real.log 2 := by
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  -- Step 1: pointwise `ppTerm n ≤ ppTerm n · log n / log 4`
  have hstep : ∀ n ∈ Finset.Ioc 1 x, ppTerm n ≤ ppTerm n * Real.log n / Real.log 4 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn2 : 2 ≤ n := hn.1
    rw [le_div_iff₀ hlog4]
    by_cases h4 : 4 ≤ n
    · have hle : Real.log 4 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast h4)
      exact mul_le_mul_of_nonneg_left hle (ppTerm_nonneg n)
    · have hn4 : n ≤ 3 := by omega
      interval_cases n
      · rw [ppTerm_prime Nat.prime_two]; simp
      · rw [ppTerm_prime Nat.prime_three]; simp
  refine (Finset.sum_le_sum hstep).trans ?_
  -- Step 2: factor out `1/log 4` and identify the weighted sum with `ψ − θ`
  rw [← Finset.sum_div, sum_ppTerm_mul_log_eq]
  -- Step 3: `ψ − θ ≤ 2√x·log x`, and `2/log 4 = 1/log 2`
  have hpsi : Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) ≤ 2 * Real.sqrt x * Real.log x := by
    rcases Nat.lt_or_ge x 2 with hx | hx
    · have hxr : (x : ℝ) < 2 := by exact_mod_cast hx
      rw [Chebyshev.psi_eq_zero_of_lt_two hxr, Chebyshev.theta_eq_zero_of_lt_two hxr, sub_zero]
      interval_cases x <;> simp
    · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast le_trans one_le_two hx
      exact Chebyshev.psi_sub_theta_le hx1
  have hlog42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [hlog42]
  calc (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) / (2 * Real.log 2)
      ≤ (2 * Real.sqrt x * Real.log x) / (2 * Real.log 2) := by gcongr
    _ = Real.sqrt x * Real.log x / Real.log 2 := by
        rw [mul_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-! ## The log-weighted Abel identity for `primesCount` -/

/-- The residue-restricted von Mangoldt partial sum equals `psiAP`: for the sequence
`g i = 1_{i ≡ a}·Λ(i)`, `∑_{i < k+1} g i = ψ(k; q, a)`. -/
lemma psiAP_eq_sum_range (k q a : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (if i % q = a % q then vonMangoldt i else 0) = psiAP k q a := by
  classical
  rw [← Finset.sum_filter]
  unfold psiAP
  symm
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hn.2⟩
  · intro n hn hn'
    rw [Finset.mem_filter, Finset.mem_range] at hn
    have hn0 : n = 0 := by
      by_contra h0
      exact hn' (by rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, by omega⟩, hn.2⟩)
    subst hn0
    exact ArithmeticFunction.map_zero

/-- `primesCount` as an indicator sum over the residue class. Uses `a < q` so that the
class condition `n % q = a` of `primesCount` matches `psiAP`'s `n % q = a % q`. -/
lemma primesCount_eq_indicator_sum {x q a : ℕ} (haq : a < q) :
    (primesCount x q a : ℝ)
      = ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q),
          (if n.Prime then (1 : ℝ) else 0) := by
  classical
  have hset : (Finset.range (x + 1)).filter (fun p => p.Prime ∧ p % q = a)
      = ((Finset.Ioc 1 x).filter (fun n => n % q = a % q)).filter (fun n => n.Prime) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    rw [Nat.mod_eq_of_lt haq]
    constructor
    · rintro ⟨hlt, hp, hres⟩
      exact ⟨⟨⟨hp.one_lt, by omega⟩, hres⟩, hp⟩
    · rintro ⟨⟨⟨h1, hx⟩, hres⟩, hp⟩
      exact ⟨by omega, hp, hres⟩
  unfold primesCount
  rw [Nat.count_eq_card_filter_range, hset, Finset.card_filter]
  push_cast
  rfl

/-- **Log-weighted Abel identity for `primesCount`** (node V4, obstruction 1). For
`2 ≤ x` and `a < q`, the prime count in the class `a mod q` is the Abel transform of
the ψ-partial-sums `ψ(·; q, a)` against the weight `1/log`, minus the prime-power
correction `∑ ppTerm`. -/
lemma primesCount_abel {x q a : ℕ} (hx : 2 ≤ x) (haq : a < q) :
    (primesCount x q a : ℝ)
      = (Real.log x)⁻¹ * psiAP x q a
        + ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiAP i q a
        - ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n := by
  classical
  set g : ℕ → ℝ := fun n => if n % q = a % q then vonMangoldt n else 0 with hg
  set f : ℕ → ℝ := fun n => (Real.log n)⁻¹ with hf
  have hbp := Finset.sum_Ioc_by_parts f g (show 1 < x from hx)
  simp only [smul_eq_mul] at hbp
  have hG : ∀ k : ℕ, ∑ i ∈ Finset.range (k + 1), g i = psiAP k q a := by
    intro k; rw [hg]; exact psiAP_eq_sum_range k q a
  -- LHS of by-parts: split `(1/log i)·Λ(i) = ppTerm i + 1_{prime}` on the class
  have hLHS : ∑ i ∈ Finset.Ioc 1 x, f i * g i
      = (primesCount x q a : ℝ)
        + ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n := by
    rw [primesCount_eq_indicator_sum haq, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ioc] at hi
    rw [hf, hg]
    by_cases hres : i % q = a % q
    · simp only [if_pos hres]
      -- `(log i)⁻¹ Λ i = ppTerm i + 1_{prime}`
      have hpp : (Real.log i)⁻¹ * vonMangoldt i = ppTerm i + (if i.Prime then (1 : ℝ) else 0) := by
        unfold ppTerm; ring
      rw [hpp]; ring
    · simp only [if_neg hres, mul_zero, add_zero]
  have hpsi1 : psiAP 1 q a = 0 := by
    unfold psiAP
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    have : n = 1 := by omega
    subst this; exact vonMangoldt_apply_one
  -- rewrite the inner partial sums `G(i+1) = psiAP i q a`
  have hinner : ∑ i ∈ Finset.Ioc 1 (x - 1), (f (i + 1) - f i) * (∑ j ∈ Finset.range (i + 1), g j)
      = ∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ - (Real.log i)⁻¹) * psiAP i q a := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hG i, hf]
  rw [hLHS, hG x, hG 1, hpsi1, mul_zero, sub_zero, hinner] at hbp
  simp only [hf] at hbp
  -- assemble: negate the telescoping sum to match the goal's orientation
  have hneg : ∑ i ∈ Finset.Ioc 1 (x - 1),
        ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiAP i q a
      = - ∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log ((i + 1 : ℕ) : ℝ))⁻¹ - (Real.log i)⁻¹) * psiAP i q a := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_); ring
  rw [eq_sub_of_add_eq hbp, hneg]; ring

/-! ## Assembly helpers -/

/-- `ψ(t; 1, 0) = ψ(t)`: the class `0 mod 1` is everything. -/
lemma psiAP_one_zero (t : ℕ) : psiAP t 1 0 = psiTot t := by
  unfold psiAP psiTot
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext n
  simp [Nat.mod_one]

/-- The Abel kernel weights telescope: `∑_{1<i≤x-1} (1/log i − 1/log(i+1)) = 1/log 2 − 1/log x`. -/
lemma sum_w_telescope {x : ℕ} (hx : 2 ≤ x) :
    ∑ i ∈ Finset.Ioc 1 (x - 1), ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
      = (Real.log 2)⁻¹ - (Real.log x)⁻¹ := by
  have hIco : Finset.Ioc 1 (x - 1) = Finset.Ico 2 x := by
    ext n; rw [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [hIco, Finset.sum_Ico_eq_sum_range]
  have hcongr : ∑ k ∈ Finset.range (x - 2),
        ((Real.log ((2 + k : ℕ) : ℝ))⁻¹ - (Real.log ((2 + k + 1 : ℕ) : ℝ))⁻¹)
      = ∑ k ∈ Finset.range (x - 2),
          ((fun j : ℕ => (Real.log ((2 + j : ℕ) : ℝ))⁻¹) k
            - (fun j : ℕ => (Real.log ((2 + j : ℕ) : ℝ))⁻¹) (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    have hk : (2 + k + 1 : ℕ) = 2 + (k + 1) := by omega
    simp only [hk]
  rw [hcongr, Finset.sum_range_sub']
  have h2 : 2 + (x - 2) = x := by omega
  simp only [Nat.add_zero, h2]
  norm_num

/-- **ψ-mean conversion.** For `a` reduced mod `q`, the AP-discrepancy against the
*unrestricted* mean `ψ(t)/φq` is controlled by `dispDisc t q` (the χ₀-mean form) plus
the mean-reconciliation gap `ω(q)·log t/φq` (`norm_psiChi_one_sub_psiTot_le`). -/
lemma abs_Epsi_le {t q a : ℕ} [NeZero q] (ht : 1 ≤ t)
    (ha : a ∈ (Finset.range q).filter (Nat.Coprime q)) :
    |psiAP t q a - psiTot t / (q.totient : ℝ)|
      ≤ dispDisc t q + (q.primeFactors.card : ℝ) * Real.log t / (q.totient : ℝ) := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
  have hφc : (q.totient : ℂ) ≠ 0 := by exact_mod_cast hφpos.ne'
  have hne : ((Finset.range q).filter (Nat.Coprime q)).Nonempty := ⟨a, ha⟩
  have hsup : ‖(psiAP t q a : ℂ) - psiChi t (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖
      ≤ dispDisc t q := by
    rw [dispDisc, dif_pos hne]
    exact Finset.le_sup' (fun a => ‖(psiAP t q a : ℂ) -
      psiChi t (1 : DirichletCharacter ℂ q) / (q.totient : ℂ)‖) ha
  have hgap : ‖psiChi t (1 : DirichletCharacter ℂ q) - (psiTot t : ℂ)‖
      ≤ (q.primeFactors.card : ℝ) * Real.log t := norm_psiChi_one_sub_psiTot_le ht
  have habs : |psiAP t q a - psiTot t / (q.totient : ℝ)|
      = ‖(psiAP t q a : ℂ) - (psiTot t : ℂ) / (q.totient : ℂ)‖ := by
    rw [show ((psiTot t : ℂ) / (q.totient : ℂ)) = ((psiTot t / q.totient : ℝ) : ℂ) by
        push_cast; ring, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hrw : (psiAP t q a : ℂ) - (psiTot t : ℂ) / (q.totient : ℂ)
      = ((psiAP t q a : ℂ) - psiChi t (1 : DirichletCharacter ℂ q) / (q.totient : ℂ))
        + (psiChi t (1 : DirichletCharacter ℂ q) - (psiTot t : ℂ)) / (q.totient : ℂ) := by
    field_simp
    ring
  rw [habs, hrw]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, Complex.norm_natCast]
  refine add_le_add hsup ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hgap (inv_nonneg.mpr hφpos.le)

/-- The Abel identity specialised to the full count `π(x) = π(x; 1, 0)`, with the
`ψ(·; 1, 0)` partial sums rewritten as `ψ(·)` (the class `0 mod 1` is everything). -/
lemma primesCount_one_zero_abel {x : ℕ} (hx : 2 ≤ x) :
    (primesCount x 1 0 : ℝ)
      = (Real.log x)⁻¹ * psiTot x
        + ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiTot i
        - ∑ n ∈ Finset.Ioc 1 x, ppTerm n := by
  rw [primesCount_abel hx (by norm_num : (0 : ℕ) < 1), psiAP_one_zero]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [psiAP_one_zero])
  · exact Finset.sum_congr (Finset.filter_true_of_mem (fun n _ => by simp [Nat.mod_one]))
      (fun _ _ => rfl)

/-! ## The per-`q` maximal discrepancy bound -/

/-- **Per-`q` discrepancy bound.** Combining the Abel identity for `π(x;q,a)` and
`π(x;1,0)`, differencing (which cancels all main terms), the ψ-mean conversion, and the
crude prime-power freight `|P_qa − P_10/φq| ≤ 2·P_10`, the maximal π-discrepancy is
controlled by the Abel transform of `dispDisc` (with the `ω·log/φq` conversion folded
in) plus twice the total prime-power correction. -/
lemma maxDiscrepancy_le_core {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    maxDiscrepancy x q
      ≤ (Real.log x)⁻¹
          * (dispDisc x q + (q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ))
        + ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * (dispDisc i q + (q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
        + 2 * ∑ n ∈ Finset.Ioc 1 x, ppTerm n := by
  haveI : NeZero q := ⟨by omega⟩
  have hq0 : q ≠ 0 := by omega
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ1 : (1 : ℝ) ≤ (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have hLxpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  have hP0 : 0 ≤ ∑ n ∈ Finset.Ioc 1 x, ppTerm n := Finset.sum_nonneg (fun n _ => ppTerm_nonneg n)
  -- weight nonnegativity
  have hw : ∀ i ∈ Finset.Ioc 1 (x - 1),
      0 ≤ (Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    have h1 : 0 < Real.log i := Real.log_pos (by exact_mod_cast hi.1)
    have hmono : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
        (by exact_mod_cast (by omega : i ≤ i + 1))
    have hinv : (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log i)⁻¹ := by gcongr
    linarith
  rw [maxDiscrepancy, dif_neg hq0]
  refine Finset.sup'_le _ _ (fun a ha => ?_)
  rw [Finset.mem_filter, Finset.mem_range] at ha
  have haq : a < q := ha.1
  have hacop : a ∈ (Finset.range q).filter (Nat.Coprime q) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨haq, ha.2.symm⟩
  rw [primesCount_abel hx haq, primesCount_one_zero_abel hx]
  -- combine the two telescoping sums against `1/φq` into `E_ψ`
  have key : ∑ i ∈ Finset.Ioc 1 (x - 1),
        ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiAP i q a
        - (∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiTot i) / (q.totient : ℝ)
      = ∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
            * (psiAP i q a - psiTot i / (q.totient : ℝ)) := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hinner_eq :
      (Real.log x)⁻¹ * psiAP x q a
          + ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiAP i q a
          - ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n
        - ((Real.log x)⁻¹ * psiTot x
            + ∑ i ∈ Finset.Ioc 1 (x - 1),
                ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * psiTot i
            - ∑ n ∈ Finset.Ioc 1 x, ppTerm n) / (q.totient : ℝ)
      = (Real.log x)⁻¹ * (psiAP x q a - psiTot x / (q.totient : ℝ))
          + ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                * (psiAP i q a - psiTot i / (q.totient : ℝ))
          - (∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n
              - (∑ n ∈ Finset.Ioc 1 x, ppTerm n) / (q.totient : ℝ)) := by
    rw [← key]; ring
  rw [hinner_eq]
  -- triangle inequality across the three groups
  set S1 : ℝ := (Real.log x)⁻¹ * (psiAP x q a - psiTot x / (q.totient : ℝ)) with hS1
  set S2 : ℝ := ∑ i ∈ Finset.Ioc 1 (x - 1),
      ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
        * (psiAP i q a - psiTot i / (q.totient : ℝ)) with hS2
  set S3 : ℝ := ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n
      - (∑ n ∈ Finset.Ioc 1 x, ppTerm n) / (q.totient : ℝ) with hS3
  have htri : |S1 + S2 - S3| ≤ |S1| + |S2| + |S3| := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    have := abs_add_le S1 S2
    linarith
  refine htri.trans ?_
  -- bound |S1|
  have hb1 : |S1| ≤ (Real.log x)⁻¹
      * (dispDisc x q + (q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ)) := by
    rw [hS1, abs_mul, abs_of_nonneg (inv_nonneg.mpr hLxpos.le)]
    exact mul_le_mul_of_nonneg_left (abs_Epsi_le (by omega) hacop) (inv_nonneg.mpr hLxpos.le)
  -- bound |S2|
  have hb2 : |S2| ≤ ∑ i ∈ Finset.Ioc 1 (x - 1),
      ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
        * (dispDisc i q + (q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ)) := by
    rw [hS2]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Finset.mem_Ioc] at hi
    rw [abs_mul, abs_of_nonneg (hw i (Finset.mem_Ioc.mpr hi))]
    exact mul_le_mul_of_nonneg_left (abs_Epsi_le (by omega) hacop)
      (hw i (Finset.mem_Ioc.mpr hi))
  -- bound |S3|
  have hb3 : |S3| ≤ 2 * ∑ n ∈ Finset.Ioc 1 x, ppTerm n := by
    rw [hS3]
    have hPqa : ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n
        ≤ ∑ n ∈ Finset.Ioc 1 x, ppTerm n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => ppTerm_nonneg n)
    have hPqa0 : 0 ≤ ∑ n ∈ (Finset.Ioc 1 x).filter (fun n => n % q = a % q), ppTerm n :=
      Finset.sum_nonneg (fun n _ => ppTerm_nonneg n)
    have hmean : (∑ n ∈ Finset.Ioc 1 x, ppTerm n) / (q.totient : ℝ)
        ≤ ∑ n ∈ Finset.Ioc 1 x, ppTerm n := div_le_self hP0 hφ1
    have hmean0 : 0 ≤ (∑ n ∈ Finset.Ioc 1 x, ppTerm n) / (q.totient : ℝ) :=
      div_nonneg hP0 hφpos.le
    rw [abs_le]
    constructor <;> nlinarith [hPqa, hPqa0, hmean, hmean0]
  linarith [hb1, hb2, hb3]

/-! ## The discretized-Abel core (shadowed slots)

The freight route via mathlib's `ψ − θ ≤ 2√x·log x` costs one extra `log`, so the
`4x/L^B` slot of `Salt.BV.PsiToPiCore` becomes `4x(1+log x)/L^B`, and the polylog
conversion lands in a pure-polylog `5(1+log x)³` slot; the hypothesis is taken at
`3 ≤ x` (which is all the reduction ever needs — its eventual regime is `x ≥ 3`). This
is the permitted statement-adjustment, discharged unconditionally below and fed to a
re-proven reduction. -/

/-- **The discretized-Abel core with adjusted slots (`x ≥ 3`).** -/
def PsiToPiCore' : Prop :=
  ∀ (x : ℕ) (B M : ℝ), 3 ≤ x → 0 ≤ B → 0 ≤ M →
    (∀ y : ℕ, y ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, dispDisc y q ≤ M) →
    ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊, maxDiscrepancy x q
      ≤ 5 * (1 + Real.log x) ^ 3 + 2 * M + 4 * x * (1 + Real.log x) / (Real.log x) ^ B

/-- **Discharge of the discretized-Abel core.** The genuine analytic content of node V4,
proven unconditionally: sum the per-`q` bound `maxDiscrepancy_le_core`, swap `∑_q` inside
the Abel kernel (telescoping weights `= 1/log 2`, giving `2M`), fold the `ω/φ` conversion
via `sum_omega_mul_le` into `5(1+log x)³`, and bound the prime-power freight
`2·Q·P₁₀ ≤ 4x(1+log x)/L^B` via `sum_ppTerm_le` and `Q ≤ √x/L^B`. -/
theorem psiToPiCore'_holds : PsiToPiCore' := by
  intro x B M hx3 hB hM hyp
  set Q := ⌊Real.sqrt x / (Real.log x) ^ B⌋₊ with hQdef
  have hx2 : 2 ≤ x := by omega
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hLxpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLxnn : 0 ≤ Real.log x := hLxpos.le
  have hLx1 : 1 ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1logx : (0 : ℝ) ≤ 1 + Real.log x := by linarith
  have hLBpos : 0 < (Real.log x) ^ B := Real.rpow_pos_of_pos hLxpos B
  have hLBge1 : (1 : ℝ) ≤ (Real.log x) ^ B := by
    calc (1 : ℝ) = (Real.log x) ^ (0 : ℝ) := (Real.rpow_zero _).symm
      _ ≤ (Real.log x) ^ B := Real.rpow_le_rpow_of_exponent_le hLx1 hB
  have hsqrtnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hQle_val : (Q : ℝ) ≤ Real.sqrt x / (Real.log x) ^ B := Nat.floor_le (by positivity)
  have hQle_sqrt : (Q : ℝ) ≤ Real.sqrt x := by
    refine hQle_val.trans ?_
    rw [div_le_iff₀ hLBpos]; nlinarith [hsqrtnn, hLBge1]
  have hP10nn : 0 ≤ ∑ n ∈ Finset.Ioc 1 x, ppTerm n :=
    Finset.sum_nonneg (fun n _ => ppTerm_nonneg n)
  have hP10le : ∑ n ∈ Finset.Ioc 1 x, ppTerm n ≤ Real.sqrt x * Real.log x / Real.log 2 :=
    sum_ppTerm_le x
  have htele := sum_w_telescope hx2
  have hwnn : ∀ i ∈ Finset.Ioc 1 (x - 1),
      0 ≤ (Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ := by
    intro i hi
    rw [Finset.mem_Ioc] at hi
    have h1 : 0 < Real.log i := Real.log_pos (by exact_mod_cast hi.1)
    have hmono : Real.log i ≤ Real.log ((i + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
        (by exact_mod_cast (by omega : i ≤ i + 1))
    have hinv : (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ ≤ (Real.log i)⁻¹ := by gcongr
    linarith
  have hwsumnn : 0 ≤ ∑ i ∈ Finset.Ioc 1 (x - 1),
      ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) :=
    Finset.sum_nonneg hwnn
  -- RHS nonnegativity (used in the `Q = 0` branch)
  have hRHSnn : 0 ≤ 5 * (1 + Real.log x) ^ 3 + 2 * M
      + 4 * x * (1 + Real.log x) / (Real.log x) ^ B := by
    have : 0 ≤ 4 * (x : ℝ) * (1 + Real.log x) / (Real.log x) ^ B := by positivity
    have h1 : 0 ≤ 5 * (1 + Real.log x) ^ 3 := by positivity
    linarith
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · rw [hQ0, show Finset.Icc 1 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty]
    exact hRHSnn
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQpos
  -- Sum the per-`q` bound.
  refine (Finset.sum_le_sum (fun q hq =>
    maxDiscrepancy_le_core hx2 (Finset.mem_Icc.mp hq).1)).trans ?_
  -- Per-`q`: `coreRHS q ≤ dispPart q + (ω/φ)(log x/log 2) + 2·P₁₀`.
  have hperq : ∀ q ∈ Finset.Icc 1 Q,
      (Real.log x)⁻¹ * (dispDisc x q + (q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ))
        + ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * (dispDisc i q + (q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
        + 2 * ∑ n ∈ Finset.Ioc 1 x, ppTerm n
      ≤ ((Real.log x)⁻¹ * dispDisc x q
          + ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * dispDisc i q)
        + (q.primeFactors.card : ℝ) / (q.totient : ℝ) * (Real.log x / Real.log 2)
        + 2 * ∑ n ∈ Finset.Ioc 1 x, ppTerm n := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hφpos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hωnn : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := by positivity
    have hωφnn : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) / (q.totient : ℝ) := by positivity
    -- split the mixed core RHS into dispPart + omegaPart
    have hsplit :
        (Real.log x)⁻¹ * (dispDisc x q + (q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ))
          + ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                * (dispDisc i q + (q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
        = ((Real.log x)⁻¹ * dispDisc x q
            + ∑ i ∈ Finset.Ioc 1 (x - 1),
                ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * dispDisc i q)
          + ((Real.log x)⁻¹ * ((q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ))
            + ∑ i ∈ Finset.Ioc 1 (x - 1),
                ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                  * ((q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))) := by
      have hdist : ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * (dispDisc i q + (q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
          = (∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * dispDisc i q)
            + ∑ i ∈ Finset.Ioc 1 (x - 1),
                ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                  * ((q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [mul_add, hdist]; ring
    -- bound the omega part
    have hop : (Real.log x)⁻¹ * ((q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ))
          + ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
                * ((q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
        ≤ (q.primeFactors.card : ℝ) / (q.totient : ℝ) * (Real.log x / Real.log 2) := by
      have e0 : (Real.log x)⁻¹ * ((q.primeFactors.card : ℝ) * Real.log x / (q.totient : ℝ))
          = (q.primeFactors.card : ℝ) / (q.totient : ℝ) := by
        field_simp
      have e1 : ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * ((q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
          ≤ (q.primeFactors.card : ℝ) / (q.totient : ℝ)
              * (Real.log x * ((Real.log 2)⁻¹ - (Real.log x)⁻¹)) := by
        rw [← htele, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum (fun i hi => ?_)
        rw [Finset.mem_Ioc] at hi
        have hlogi : Real.log i ≤ Real.log x :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < i))
            (by exact_mod_cast (by omega : i ≤ x))
        have hlogi0 : 0 ≤ Real.log i := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ i))
        have hwi : 0 ≤ (Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹ :=
          hwnn i (Finset.mem_Ioc.mpr hi)
        -- w_i·(ω·log i/φ) ≤ (ω/φ)·(log x · w_i)
        have : ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)
              * ((q.primeFactors.card : ℝ) * Real.log i / (q.totient : ℝ))
            = (q.primeFactors.card : ℝ) / (q.totient : ℝ)
                * (Real.log i * ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)) := by
          ring
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ hωφnn
        exact mul_le_mul_of_nonneg_right hlogi hwi
      have ecomp : (q.primeFactors.card : ℝ) / (q.totient : ℝ)
            + (q.primeFactors.card : ℝ) / (q.totient : ℝ)
                * (Real.log x * ((Real.log 2)⁻¹ - (Real.log x)⁻¹))
          = (q.primeFactors.card : ℝ) / (q.totient : ℝ) * (Real.log x / Real.log 2) := by
        field_simp
        ring
      rw [e0]
      linarith [e1, ecomp]
    rw [hsplit]
    linarith [hop]
  refine (Finset.sum_le_sum hperq).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Three totals.
  have hdispTot : ∑ q ∈ Finset.Icc 1 Q,
        ((Real.log x)⁻¹ * dispDisc x q
          + ∑ i ∈ Finset.Ioc 1 (x - 1),
              ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * dispDisc i q)
      ≤ 2 * M := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hbnd : ∑ q ∈ Finset.Icc 1 Q,
          ∑ i ∈ Finset.Ioc 1 (x - 1),
            ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹) * dispDisc i q
        ≤ (∑ i ∈ Finset.Ioc 1 (x - 1), ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)) * M := by
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_le_sum (fun i hi => ?_)
      rw [Finset.mem_Ioc] at hi
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (hyp i (by omega)) (hwnn i (Finset.mem_Ioc.mpr hi))
    have hb0 : (Real.log x)⁻¹ * ∑ q ∈ Finset.Icc 1 Q, dispDisc x q ≤ (Real.log x)⁻¹ * M :=
      mul_le_mul_of_nonneg_left (hyp x le_rfl) (inv_nonneg.mpr hLxnn)
    have hle2 : (Real.log 2)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hlog2]; nlinarith [Real.log_two_gt_d9]
    have hcomb : (Real.log x)⁻¹ * M + (∑ i ∈ Finset.Ioc 1 (x - 1),
          ((Real.log i)⁻¹ - (Real.log ((i + 1 : ℕ) : ℝ))⁻¹)) * M ≤ 2 * M := by
      rw [← add_mul, htele]
      have : (Real.log x)⁻¹ + ((Real.log 2)⁻¹ - (Real.log x)⁻¹) = (Real.log 2)⁻¹ := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hle2 hM
    linarith [hb0, hbnd, hcomb]
  have homegaTot : ∑ q ∈ Finset.Icc 1 Q,
        (q.primeFactors.card : ℝ) / (q.totient : ℝ) * (Real.log x / Real.log 2)
      ≤ 5 * (1 + Real.log x) ^ 3 := by
    -- rewrite as the `sum_omega_mul_le` shape with `L = log x / log 2`
    have hrw : ∑ q ∈ Finset.Icc 1 Q,
          (q.primeFactors.card : ℝ) / (q.totient : ℝ) * (Real.log x / Real.log 2)
        = ∑ q ∈ Finset.Icc 1 Q,
            (q.primeFactors.card : ℝ) * (Real.log x / Real.log 2) / (q.totient : ℝ) := by
      refine Finset.sum_congr rfl (fun q _ => by ring)
    rw [hrw]
    refine (sum_omega_mul_le hQpos (by positivity)).trans ?_
    -- polylog budget: logb 2 Q · (log x/log 2) · 4(1+log Q) ≤ 5(1+log x)³
    have hlogQ : Real.log Q ≤ Real.log x / 2 := by
      have := Real.log_le_log (show (0 : ℝ) < Q by exact_mod_cast hQpos) hQle_sqrt
      rwa [Real.log_sqrt hxpos.le] at this
    have hlogbQ : Real.logb 2 Q ≤ Real.log x / (2 * Real.log 2) := by
      rw [Real.logb, div_le_div_iff₀ hlog2 (by positivity)]
      nlinarith [hlogQ, hlog2]
    have hlogQx : Real.log Q ≤ Real.log x := by linarith [hlogQ]
    have hLL2nn : 0 ≤ Real.log x / Real.log 2 := div_nonneg hLxnn hlog2.le
    have hlogQnn : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQpos)
    have hmidnn : 0 ≤ Real.log x / (2 * Real.log 2) * (Real.log x / Real.log 2) :=
      mul_nonneg (div_nonneg hLxnn (by positivity)) hLL2nn
    have hsqnn : 0 ≤ (Real.log x) ^ 2 * (1 + Real.log x) := mul_nonneg (sq_nonneg _) h1logx
    calc Real.logb 2 Q * (Real.log x / Real.log 2) * (4 * (1 + Real.log Q))
        ≤ (Real.log x / (2 * Real.log 2)) * (Real.log x / Real.log 2) * (4 * (1 + Real.log x)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_right hlogbQ hLL2nn
          · linarith [hlogQx]
          · linarith [hlogQnn]
          · exact hmidnn
      _ = (2 / (Real.log 2) ^ 2) * ((Real.log x) ^ 2 * (1 + Real.log x)) := by
          field_simp; ring
      _ ≤ 5 * ((Real.log x) ^ 2 * (1 + Real.log x)) := by
          refine mul_le_mul_of_nonneg_right ?_ hsqnn
          rw [div_le_iff₀ (by positivity)]; nlinarith [Real.log_two_gt_d9]
      _ ≤ 5 * ((1 + Real.log x) ^ 2 * (1 + Real.log x)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine mul_le_mul_of_nonneg_right ?_ h1logx
          nlinarith [hLxnn]
      _ = 5 * (1 + Real.log x) ^ 3 := by ring
  have hfreightTot : ∑ q ∈ Finset.Icc 1 Q, (2 * ∑ n ∈ Finset.Ioc 1 x, ppTerm n)
      ≤ 4 * x * (1 + Real.log x) / (Real.log x) ^ B := by
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
    have hsqrtsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hxpos.le
    have hb : (Q : ℝ) * (2 * ∑ n ∈ Finset.Ioc 1 x, ppTerm n)
        ≤ (Real.sqrt x / (Real.log x) ^ B) * (2 * (Real.sqrt x * Real.log x / Real.log 2)) := by
      apply mul_le_mul hQle_val _ (by positivity) (by positivity)
      linarith [hP10le]
    refine hb.trans ?_
    have hnum : Real.sqrt x * (2 * (Real.sqrt x * Real.log x / Real.log 2))
        ≤ 4 * x * (1 + Real.log x) := by
      have heq : Real.sqrt x * (2 * (Real.sqrt x * Real.log x / Real.log 2))
          = 2 * (Real.sqrt x * Real.sqrt x) * Real.log x / Real.log 2 := by ring
      rw [heq, hsqrtsq, div_le_iff₀ hlog2]
      nlinarith [Real.log_two_gt_d9, mul_nonneg hxpos.le hLxnn, mul_nonneg hxpos.le hlog2.le,
        mul_nonneg (mul_nonneg hxpos.le hLxnn) hlog2.le]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hLBpos hLBpos]
    exact mul_le_mul_of_nonneg_right hnum hLBpos.le
  linarith [hdispTot, homegaTot, hfreightTot]

/-! ## The reduction, re-proven for the adjusted slots -/

/-- **`PsiToPiTransfer` from the adjusted Abel core (complete).** Mirrors
`Salt.BV.psiToPiTransfer_of_core` with the shadowed slots: extract the ψ-family at
saving `A+1`, inflate the haircut to `B := B'+A+1` (the extra `+1` absorbs the
`(1+log x)` factor of the freight slot), apply `PsiToPiCore'` (its `x ≥ 3` regime is
exactly the reduction's eventual regime), and absorb the pure-polylog `5(1+log x)³` via
`absorb_nat` at `θ = 0`. Constant `C := 9 + 2C'`. -/
theorem psiToPiTransfer_of_core' (hCore : PsiToPiCore') : PsiToPiTransfer := by
  intro hψ A hA
  obtain ⟨B', C', hB', hC', hψb⟩ := hψ (A + 1) (by linarith)
  refine ⟨B' + A + 1, 9 + 2 * C', by linarith, by linarith, ?_⟩
  filter_upwards [absorb_nat (θ := (0 : ℝ)) (k := (3 : ℝ)) (A := A) (M := (5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num),
      eventually_ge_atTop 3] with x habs hx3
  have hx2 : 2 ≤ x := by omega
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
      _ ≤ (x : ℝ) := hx3R
  have hLpos : (0 : ℝ) < Real.log x := by linarith
  have hLApos : (0 : ℝ) < (Real.log x) ^ A := Real.rpow_pos_of_pos hLpos A
  have hLA1pos : (0 : ℝ) < (Real.log x) ^ (A + 1) := Real.rpow_pos_of_pos hLpos (A + 1)
  have hM0 : 0 ≤ C' * (x : ℝ) / (Real.log x) ^ (A + 1) :=
    div_nonneg (mul_nonneg hC' hxpos.le) hLA1pos.le
  have hBmono : Real.sqrt x / (Real.log x) ^ (B' + A + 1) ≤ Real.sqrt x / (Real.log x) ^ B' :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hLpos B')
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hsub : Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (B' + A + 1)⌋₊
      ⊆ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B'⌋₊ :=
    Finset.Icc_subset_Icc_right (Nat.floor_le_floor hBmono)
  have hyp : ∀ y : ℕ, y ≤ x →
      ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (B' + A + 1)⌋₊, dispDisc y q
        ≤ C' * (x : ℝ) / (Real.log x) ^ (A + 1) := by
    intro y hyx
    calc ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ (B' + A + 1)⌋₊, dispDisc y q
        ≤ ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B'⌋₊, dispDisc y q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => dispDisc_nonneg y q)
      _ ≤ C' * (x : ℝ) / (Real.log x) ^ (A + 1) := hψb x y hx2 hyx
  have hcore := hCore x (B' + A + 1) (C' * (x : ℝ) / (Real.log x) ^ (A + 1))
    hx3 (by positivity) hM0 hyp
  refine le_trans hcore ?_
  rw [Real.rpow_zero, mul_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] at habs
  -- `habs : 5 * (1 + log x)^3 ≤ x / (log x)^A`
  -- bound the three slots by multiples of `x / (log x)^A`
  have hLexp1 : (Real.log x) ^ A ≤ (Real.log x) ^ (A + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h2M : 2 * (C' * (x : ℝ) / (Real.log x) ^ (A + 1))
      ≤ 2 * (C' * (x : ℝ) / (Real.log x) ^ A) :=
    mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (mul_nonneg hC' hxpos.le) hLApos hLexp1) (by norm_num)
  have hLA1eq : (Real.log x) ^ (A + 1) = (Real.log x) ^ A * Real.log x := by
    rw [Real.rpow_add hLpos, Real.rpow_one]
  have h4 : 4 * (x : ℝ) * (1 + Real.log x) / (Real.log x) ^ (B' + A + 1)
      ≤ 8 * (x : ℝ) / (Real.log x) ^ A := by
    have hstepA : 4 * (x : ℝ) * (1 + Real.log x) / (Real.log x) ^ (B' + A + 1)
        ≤ 4 * (x : ℝ) * (1 + Real.log x) / (Real.log x) ^ (A + 1) :=
      div_le_div_of_nonneg_left (by positivity) hLA1pos
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
    refine hstepA.trans ?_
    rw [hLA1eq, div_le_div_iff₀ (by positivity) hLApos]
    nlinarith [mul_nonneg (mul_nonneg hxpos.le hLApos.le) (by linarith : (0 : ℝ) ≤ Real.log x - 1),
      hLApos.le, hxpos.le]
  calc 5 * (1 + Real.log x) ^ 3 + 2 * (C' * (x : ℝ) / (Real.log x) ^ (A + 1))
          + 4 * (x : ℝ) * (1 + Real.log x) / (Real.log x) ^ (B' + A + 1)
      ≤ (x : ℝ) / (Real.log x) ^ A + 2 * (C' * (x : ℝ) / (Real.log x) ^ A)
          + 8 * (x : ℝ) / (Real.log x) ^ A := add_le_add (add_le_add habs h2M) h4
    _ = (9 + 2 * C') * (x : ℝ) / (Real.log x) ^ A := by ring

/-! ## The unconditional headliners -/

/-- `PsiToPiTransfer`, unconditionally. -/
theorem psiToPiTransfer_holds : PsiToPiTransfer := psiToPiTransfer_of_core' psiToPiCore'_holds

/-- **`HasLevel (1/2)` from Siegel–Walfisz, unconditionally** (node V5.1). -/
theorem hasLevel_half_of_siegelWalfisz (hSW : SiegelWalfisz) : HasLevel (1 / 2) :=
  hasLevel_half_of_siegelWalfisz_of_bridge hSW psiToPiTransfer_holds

/-- **Bounded prime gaps from Siegel–Walfisz, unconditionally** (node V6). -/
theorem bounded_gaps_of_siegelWalfisz (hSW : SiegelWalfisz) :
    ∃ C : ℕ, ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ p ≠ q ∧ p.Prime ∧ q.Prime ∧
      (q : ℤ) - (p : ℤ) ∈ Set.Icc (-(C : ℤ)) (C : ℤ) :=
  bounded_gaps_of_siegelWalfisz_of_bridge hSW psiToPiTransfer_holds

end Salt.BV
