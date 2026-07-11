/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.LS.Defs

/-!
# Large sieve track, nodes L1.1 + L1.2: orthogonality and finite Parseval

Blueprint: `docs/blueprints/largesieve.md`.

* **L1.1** (`integral_e_int`): orthogonality of the characters,
  `∫₀¹ e(kα) dα = [k = 0]` for `k : ℤ`, with the `(n,m)`-form corollary
  `integral_e_mul_conj` used by Parseval.
* **L1.2** (`parseval`): the frozen finite Parseval identity
  `∫₀¹ ‖expSum N a α‖² dα = ∑_{n<N} ‖a n‖²`.

Integrability throughout is `Continuous.intervalIntegrable` on the smooth
carriers (`continuous_e`, `continuous_expSum`); no measurability nodes.
-/

namespace Salt.LS

open scoped BigOperators
open intervalIntegral MeasureTheory

/-- **L1.1 — orthogonality.** `∫₀¹ e(kα) dα = 1` if `k = 0`, else `0`
(exponent cast from `ℤ`). -/
theorem integral_e_int (k : ℤ) :
    (∫ α in (0:ℝ)..1, e ((k : ℝ) * α)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk; simp
  · rw [if_neg hk]
    have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) Complex.I_ne_zero) h2
    have hrw : (∫ α in (0:ℝ)..1, e ((k : ℝ) * α))
        = ∫ α in (0:ℝ)..1, Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * α) := by
      apply intervalIntegral.integral_congr
      intro α _
      unfold e
      exact congrArg Complex.exp (by push_cast; ring)
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ))
            = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hrw, integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, hexp,
      sub_self, zero_div]

/-- **L1.1 corollary — the `(n,m)` form.** For `n m : ℕ`,
`∫₀¹ e(nα) · conj (e(mα)) dα = [n = m]`. This is the shape Parseval consumes. -/
theorem integral_e_mul_conj (n m : ℕ) :
    (∫ α in (0:ℝ)..1, e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))
      = if n = m then 1 else 0 := by
  have step : ∀ α : ℝ,
      e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))
        = e ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    rw [conj_e, ← e_add]
    congr 1
    push_cast; ring
  have hcongr : (∫ α in (0:ℝ)..1, e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))
      = ∫ α in (0:ℝ)..1, e ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * α) :=
    intervalIntegral.integral_congr (fun α _ => step α)
  rw [hcongr, integral_e_int]
  by_cases hnm : n = m
  · subst hnm; simp
  · have hne : ((n : ℤ) - (m : ℤ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
    rw [if_neg hne, if_neg hnm]

/-- **L1.2 — finite Parseval (FROZEN).**
`∫₀¹ ‖expSum N a α‖² dα = ∑_{n<N} ‖a n‖²`. -/
theorem parseval (N : ℕ) (a : ℕ → ℂ) :
    (∫ α in (0:ℝ)..1, ‖expSum N a α‖ ^ 2) = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  -- Pointwise: ‖z‖² (as a complex) is `z * conj z`.
  have pt : ∀ α : ℝ, ((‖expSum N a α‖ ^ 2 : ℝ) : ℂ)
      = expSum N a α * (starRingEnd ℂ) (expSum N a α) := by
    intro α
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- Pointwise: expand the square of the sum into the double sum.
  have expand : ∀ α : ℝ, expSum N a α * (starRingEnd ℂ) (expSum N a α)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (a n * (starRingEnd ℂ) (a m))
            * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
    intro α
    unfold expSum
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro m _
    rw [map_mul]; ring
  -- Continuity of the individual and inner-summed terms (for integrability).
  have cont2 : ∀ n ∈ Finset.range N, ∀ m ∈ Finset.range N,
      Continuous (fun α : ℝ => (a n * (starRingEnd ℂ) (a m))
        * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))) := by
    intro n _ m _; fun_prop
  have cont1 : ∀ n ∈ Finset.range N,
      Continuous (fun α : ℝ => ∑ m ∈ Finset.range N,
        (a n * (starRingEnd ℂ) (a m))
          * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α)))) := by
    intro n hn
    apply continuous_finsetSum
    intro m hm
    exact cont2 n hn m hm
  -- Prove the ℂ-cast identity, then descend to ℝ.
  have key : ((∫ α in (0:ℝ)..1, ‖expSum N a α‖ ^ 2 : ℝ) : ℂ)
      = ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    calc (∫ α in (0:ℝ)..1, ((‖expSum N a α‖ ^ 2 : ℝ) : ℂ))
        = ∫ α in (0:ℝ)..1, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (a n * (starRingEnd ℂ) (a m))
              * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
          simp_rw [pt, expand]
      _ = ∑ n ∈ Finset.range N, ∫ α in (0:ℝ)..1, ∑ m ∈ Finset.range N,
            (a n * (starRingEnd ℂ) (a m))
              * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
          rw [intervalIntegral.integral_finsetSum]
          intro n hn; exact (cont1 n hn).intervalIntegrable 0 1
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∫ α in (0:ℝ)..1,
            (a n * (starRingEnd ℂ) (a m))
              * (e ((n : ℝ) * α) * (starRingEnd ℂ) (e ((m : ℝ) * α))) := by
          apply Finset.sum_congr rfl; intro n _
          rw [intervalIntegral.integral_finsetSum]
          intro m hm; exact (cont2 n (by assumption) m hm).intervalIntegrable 0 1
      _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
            (a n * (starRingEnd ℂ) (a m)) * (if n = m then 1 else 0) := by
          apply Finset.sum_congr rfl; intro n _
          apply Finset.sum_congr rfl; intro m _
          rw [intervalIntegral.integral_const_mul, integral_e_mul_conj]
      _ = ∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n) := by
          apply Finset.sum_congr rfl; intro n hn
          rw [Finset.sum_eq_single n]
          · rw [if_pos rfl, mul_one]
          · intro m _ hmn; rw [if_neg (fun h => hmn h.symm), mul_zero]
          · intro hn'; exact absurd hn hn'
      _ = ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.ofReal_sum]
          apply Finset.sum_congr rfl; intro n _
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast key

end Salt.LS
