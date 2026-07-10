/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.Lemma53Tight

/-!
# The Maynard capstone — `bounded_gaps_from_eh_complete`

The landed `Lemma53Tight.lean` fixes the sixth-fragility MATH (the lemma-5.3 error
constant is now `O(k)`), but the constant `lemma53Const = rankinC·(2 + 4·exp 4)`
still hides `rankinC = (rankin_bound 1).choose` and `mertensC =
(sum_inv_prime_sub_one_le).choose` behind `∃`-opacity, so the item-6 regime
`32·(lemma53Const·k)·log R ≤ B₁·D₀` cannot be numerically discharged.

This file removes the opacity by re-deriving the whole contraction cascade with an
EXPLICIT Rankin constant `rankinK = exp 20`, obtained from an explicit Mertens
bound (`mertensC ≤ 20`).  It then discharges the item-6 regime for `k` past the
`300 ≤ log k` floor and assembles the unconditional

  `bounded_gaps_from_eh_complete : BoundedGapsFromEH`.

No new mathematics: explicit-constant extraction + numerics + eventually-plumbing.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## Part A — explicit Mertens second theorem (sub-one form) -/

/-- **Explicit Mertens sub-one bound.** `∑_{p ≤ n} 1/(p−1) ≤ log log n + 20`.
The constant is explicit (not `∃`-hidden): from `sum_inv_prime_le_aux`'s explicit
`C₀ = 1 + 2(log4+4)/log2 − log(log2) ≤ 19`, plus the telescoping tail `≤ 1`. -/
theorem sum_inv_prime_sub_one_le_explicit (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
      ≤ Real.log (Real.log n) + 20 := by
  have hmain := sum_inv_prime_le_aux hn
  have hsplit : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / (p - 1)
      = (∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 : ℝ) / p)
        + ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
            ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  rw [hsplit]
  -- tail `≤ 1` via telescoping (mirrors `sum_inv_prime_sub_one_le`)
  have htail : ∑ p ∈ (Finset.range (n + 1)).filter Nat.Prime,
      ((1 : ℝ) / ((p : ℝ) - 1) - 1 / p) ≤ 1 := by
    have hsub : (Finset.range (n + 1)).filter Nat.Prime ⊆ Finset.Icc 2 n := by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.2.two_le, by omega⟩
    have hnn : ∀ k ∈ Finset.Icc 2 n, 0 ≤ (1 : ℝ) / ((k : ℝ) - 1) - 1 / k := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
      have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
      have hkk : (k : ℝ) - 1 ≤ k := by linarith
      have := one_div_le_one_div_of_le hk1 hkk
      linarith
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ => hnn k hk)).trans ?_
    rw [sum_Icc_telescope hn]
    have hnpos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  -- numeric: `C₀ + 1 ≤ 20`
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hlog2half : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hfrac : 2 * (Real.log 4 + 4) / Real.log 2 ≤ 16 := by
    rw [div_le_iff₀ hlog2pos, hlog4]; nlinarith [hlog2gt]
  have hloglog : -Real.log 2 ≤ Real.log (Real.log 2) := by
    have h1 : Real.log (1 / 2 : ℝ) ≤ Real.log (Real.log 2) :=
      Real.log_le_log (by norm_num) hlog2half
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at h1
    linarith
  have hlog2le1 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have haux : (1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)) + 1 ≤ 20 := by
    linarith [hfrac, hloglog, hlog2le1]
  linarith [hmain, htail, haux]

/-! ## Part B — explicit `W/φ(W)` bound -/

/-- **Explicit Mertens `W/φ(W)` bound.** `W k/φ(W k) ≤ exp 20·log(D₀ k)`
(copy of `W_div_totient_le` with the explicit Mertens constant `20`). -/
theorem W_div_totient_le_explicit (k : ℕ) (hD : 2 ≤ D₀ k) :
    (W k : ℝ) / (Nat.totient (W k) : ℝ) ≤ Real.exp 20 * Real.log (D₀ k) := by
  have hWsq : Squarefree (W k) := W_squarefree k
  have hWfac : (W k).primeFactors = (Finset.range (D₀ k + 1)).filter Nat.Prime := by
    change (primorial (D₀ k)).primeFactors = _
    rw [primorial, Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)]
  have hlogD : 0 < Real.log (D₀ k) := Real.log_pos (by exact_mod_cast (by omega : 1 < D₀ k))
  have ratio_eq : (W k : ℝ) / (Nat.totient (W k) : ℝ)
      = ∏ p ∈ (W k).primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
    have hnum : (W k : ℝ) = ∏ p ∈ (W k).primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hWsq]
    rw [hnum, totient_squarefree_cast hWsq, ← Finset.prod_div_distrib]
  have hStepB : ∏ p ∈ (W k).primeFactors, (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∏ p ∈ (W k).primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := by
    apply Finset.prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      apply div_nonneg <;> linarith
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hsplit : (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
        field_simp; ring
      rw [hsplit]; linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
  have hStepC : ∏ p ∈ (W k).primeFactors, Real.exp (1 / ((p : ℝ) - 1))
      = Real.exp (∑ p ∈ (W k).primeFactors, 1 / ((p : ℝ) - 1)) :=
    (Real.exp_sum _ _).symm
  have hMert : ∑ p ∈ (W k).primeFactors, 1 / ((p : ℝ) - 1)
      ≤ Real.log (Real.log (D₀ k)) + 20 := by
    rw [hWfac]
    exact sum_inv_prime_sub_one_le_explicit (D₀ k) hD
  calc (W k : ℝ) / (Nat.totient (W k) : ℝ)
      = ∏ p ∈ (W k).primeFactors, (p : ℝ) / ((p : ℝ) - 1) := ratio_eq
    _ ≤ ∏ p ∈ (W k).primeFactors, Real.exp (1 / ((p : ℝ) - 1)) := hStepB
    _ = Real.exp (∑ p ∈ (W k).primeFactors, 1 / ((p : ℝ) - 1)) := hStepC
    _ ≤ Real.exp (Real.log (Real.log (D₀ k)) + 20) := Real.exp_le_exp.mpr hMert
    _ = Real.log (D₀ k) * Real.exp 20 := by rw [Real.exp_add, Real.exp_log hlogD]
    _ = Real.exp 20 * Real.log (D₀ k) := mul_comm _ _

/-! ## Part C — explicit Rankin constant (`L = 1`) -/

/-- The explicit Rankin `L = 1` constant `exp 20` (replacing the opaque `rankinC`). -/
noncomputable def rankinK : ℝ := Real.exp 20

lemma rankinK_ge_one : 1 ≤ rankinK := by
  rw [rankinK]; calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp 20 := Real.exp_le_exp.mpr (by norm_num)

lemma rankinK_nonneg : 0 ≤ rankinK := le_trans zero_le_one rankinK_ge_one

/-- **Explicit Rankin bound (`L = 1`).** `∑_{q<Q,sf} 1/φ(q) ≤ rankinK·log Q`
with `rankinK = exp 20` explicit (copy of `rankin_bound 1` with the explicit
Mertens bound). -/
theorem rankinK_bound (Q : ℕ) (hQ : 2 ≤ Q) :
    ∑ q ∈ (Finset.range Q).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ rankinK * Real.log Q := by
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) < (Q : ℝ) := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ1
  set SF := (Finset.range Q).filter Squarefree with hSF
  set P := (Finset.range Q).filter Nat.Prime with hP
  -- Step 1: rewrite each `1/φ(q)` as a product of Euler factors `∏ rFac 1 p`.
  have hstep1 : ∑ q ∈ SF, (1 / (Nat.totient q : ℝ))
      = ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac 1 p := by
    refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [hSF, Finset.mem_filter] at hq
    have h := rankin_term_eq 1 hq.2
    rw [Nat.cast_one, one_pow] at h
    exact h
  rw [hstep1]
  have hinj : Set.InjOn Nat.primeFactors ↑SF := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hSF, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2]
  have hsub : SF.image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨q, hq, rfl⟩ := ht
    rw [hSF, Finset.mem_filter] at hq
    rw [Finset.mem_powerset]
    intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_range]
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ q := Nat.dvd_of_mem_primeFactors hp
    have hqr : q < Q := by have := hq.1; rwa [Finset.mem_range] at this
    have hq0 : 0 < q := Nat.pos_of_ne_zero hq.2.ne_zero
    have hpq : p ≤ q := Nat.le_of_dvd hq0 hpd
    exact ⟨by omega, hpp⟩
  have hprodadd : ∏ p ∈ P, (1 + rFac 1 p)
      = ∑ t ∈ P.powerset, ∏ p ∈ t, rFac 1 p := by
    have h := Finset.prod_add (fun p => rFac 1 p) (fun _ => (1 : ℝ)) P
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl (fun p _ => by ring)
  have hnonneg : ∀ t ∈ P.powerset, t ∉ SF.image Nat.primeFactors →
      0 ≤ ∏ p ∈ t, rFac 1 p := by
    intro t ht _
    rw [Finset.mem_powerset] at ht
    refine Finset.prod_nonneg (fun p hp => rFac_nonneg 1 ?_)
    have := ht hp
    rw [hP, Finset.mem_filter] at this
    exact this.2
  have himg : ∑ t ∈ SF.image Nat.primeFactors, (∏ p ∈ t, rFac 1 p)
      = ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac 1 p := Finset.sum_image hinj
  have hstep2 : ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac 1 p
      ≤ ∏ p ∈ P, (1 + rFac 1 p) := by
    rw [hprodadd, ← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  have hfacpos : ∀ p ∈ P, 0 < 1 + rFac 1 p := by
    intro p hp
    have hpp : p.Prime := by rw [hP, Finset.mem_filter] at hp; exact hp.2
    have := rFac_nonneg 1 hpp
    linarith
  have hprodpos : 0 < ∏ p ∈ P, (1 + rFac 1 p) := Finset.prod_pos hfacpos
  have hlogprod : Real.log (∏ p ∈ P, (1 + rFac 1 p))
      ≤ Real.log (Real.log Q) + 20 := by
    rw [Real.log_prod (fun p hp => (hfacpos p hp).ne')]
    have h1 : ∑ p ∈ P, Real.log (1 + rFac 1 p) ≤ ∑ p ∈ P, rFac 1 p := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      linarith [Real.log_le_sub_one_of_pos (hfacpos p hp)]
    have h2 : ∑ p ∈ P, rFac 1 p = ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := by
      refine Finset.sum_congr rfl (fun p _ => ?_); simp only [rFac]; push_cast; ring
    have h3 : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) ≤ Real.log (Real.log Q) + 20 := by
      have hrange : Finset.range Q ⊆ Finset.range (Q + 1) := by
        intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      have hsubP : P ⊆ (Finset.range (Q + 1)).filter Nat.Prime := by
        rw [hP]; exact Finset.filter_subset_filter _ hrange
      have hnn : ∀ p ∈ (Finset.range (Q + 1)).filter Nat.Prime, p ∉ P →
          0 ≤ (1 : ℝ) / ((p : ℝ) - 1) := by
        intro p hp _
        rw [Finset.mem_filter] at hp
        have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
        exact div_nonneg (by norm_num) (by linarith)
      calc ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1)
          ≤ ∑ p ∈ (Finset.range (Q + 1)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) - 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubP hnn
        _ ≤ Real.log (Real.log Q) + 20 := sum_inv_prime_sub_one_le_explicit Q hQ
    calc ∑ p ∈ P, Real.log (1 + rFac 1 p)
        ≤ ∑ p ∈ P, rFac 1 p := h1
      _ = ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) := h2
      _ ≤ Real.log (Real.log Q) + 20 := h3
  have hRHSeq : Real.exp (Real.log (Real.log Q) + 20)
      = rankinK * Real.log Q := by
    rw [Real.exp_add, Real.exp_log hlogQ, rankinK]; ring
  calc ∑ q ∈ SF, ∏ p ∈ q.primeFactors, rFac 1 p
      ≤ ∏ p ∈ P, (1 + rFac 1 p) := hstep2
    _ = Real.exp (Real.log (∏ p ∈ P, (1 + rFac 1 p))) := (Real.exp_log hprodpos).symm
    _ ≤ Real.exp (Real.log (Real.log Q) + 20) := Real.exp_le_exp.mpr hlogprod
    _ = rankinK * Real.log Q := hRHSeq

/-! ## Part D — the explicit contraction cascade (`rankinK` in place of `rankinC`)

Re-derivation of the `Lemma53Tight` cascade with the EXPLICIT constant `rankinK`.
The `rankinC`-free private helpers are re-copied here (they are `private` in
`Lemma53Tight`); the constant-carrying lemmas are the tight proofs verbatim with
`rankinC → rankinK` and `lemma53Const → lemma53KConst`. -/

/-- Local copy of the private `g_factor_prod'` (no constant). -/
private theorem g_factor_prod'' {r : ℕ} (hr : Squarefree r)
    (hodd : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    (gMult r : ℝ) * (r : ℝ) / (Nat.totient r : ℝ) ^ 2
      = ∏ p ∈ r.primeFactors, (1 - (((p : ℝ) - 1)⁻¹) ^ 2) := by
  have hrprod : (r : ℝ) = ∏ p ∈ r.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  rw [gMult_cast hodd, hrprod, totient_squarefree_cast hr,
    ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- Local copy of the private `gr_ratio_mem'` (no constant). -/
private theorem gr_ratio_mem'' {ρ : ℕ} (hρ : Squarefree ρ)
    (hodd : ∀ p ∈ ρ.primeFactors, 3 ≤ p) :
    0 ≤ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2
      ∧ (gMult ρ : ℝ) * (ρ : ℝ) / (Nat.totient ρ : ℝ) ^ 2 ≤ 1 := by
  rw [g_factor_prod'' hρ hodd]
  refine ⟨Finset.prod_nonneg (fun p hp => ?_),
    Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)⟩
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hodd p hp
    have h0 : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : ((p : ℝ) - 1)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith
    nlinarith [h0, h1]
  · nlinarith [sq_nonneg (((p : ℝ) - 1)⁻¹)]

/-- Local copy of the private `tail_factor_le'` (no constant). -/
private theorem tail_factor_le'' (k R : ℕ) (j : Fin k) (r : Fin k → ℕ)
    (H : Fin k → ℕ → ℝ) (hH : ∀ i x, 0 ≤ H i x) :
    ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
        ∏ i, H i (a i)
      ≤ ∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x := by
  classical
  rw [Finset.prod_univ_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haK, hguard, hdev⟩ := ha
    have hK := (mem_kSieveIndex_iff a).mp haK
    rw [Fintype.mem_piFinset]
    intro i
    simp only [tailCoordSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨kSieveIndex_coord_lt haK i, hK.1 i, ?_, hguard i, ?_⟩
    · intro p hp
      exact D₀_lt_of_prime_dvd_coord haK (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
    · intro hij; subst hij; exact hdev
  · intro a _ _
    exact Finset.prod_nonneg (fun i _ => hH i (a i))

/-- **`abs_mainSum_le`, explicit constant.** Copy of `abs_mainSum_le_tight` with
`rankinC → rankinK`. -/
theorem abs_mainSum_le_K (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hR : 2 ≤ R) :
    |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ rankinK * Real.log R := by
  classical
  have hRankin := rankinK_bound R hR
  have hterm : ∀ am ∈ Finset.range R,
      |y (Function.update r m am) / (Nat.totient am : ℝ)|
        ≤ if Squarefree am then 1 / (Nat.totient am : ℝ) else 0 := by
    intro am _
    by_cases hsf : Squarefree am
    · have hampos : 0 < am := Nat.pos_of_ne_zero hsf.ne_zero
      have hφpos : (0 : ℝ) < (Nat.totient am : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hampos
      rw [if_pos hsf, abs_div, abs_of_nonneg hφpos.le]
      gcongr
      exact hy1 _
    · rw [if_neg hsf]
      have hnotmem : Function.update r m am ∉ kSieveIndex k R (W k) := fun hmem =>
        hsf (by
          have := ((mem_kSieveIndex_iff _).mp hmem).1 m
          rwa [Function.update_self] at this)
      rw [hysupp _ hnotmem, zero_div, abs_zero]
  calc |∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ ∑ am ∈ Finset.range R, |y (Function.update r m am) / (Nat.totient am : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ am ∈ Finset.range R, (if Squarefree am then 1 / (Nat.totient am : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ am ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient am : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ ≤ rankinK * Real.log R := hRankin

/-- The explicit linear-in-`k` Lemma-5.3 constant `rankinK·(2 + 4·exp 4)`. -/
noncomputable def lemma53KConst : ℝ := rankinK * (2 + 4 * Real.exp 4)

lemma lemma53KConst_nonneg : 0 ≤ lemma53KConst := by
  rw [lemma53KConst]
  have := rankinK_nonneg
  have : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  positivity

/-- **`htail`, explicit constant.** Copy of `htail_tight` with `rankinC → rankinK`. -/
theorem htail_K (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (_hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |(∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
        * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R (W k)).filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))|
      ≤ (4 * Real.exp 4 * rankinK * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
  classical
  obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff r).mp hrsupp
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD4 : 4 ≤ D₀ k := by omega
  have hkD : k ≤ D₀ k := by nlinarith [hD]
  have hD0 : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0
  have hD0ne : (D₀ k : ℝ) ≠ 0 := hD0R.ne'
  have hkD0R : (k : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hkD
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ rankinK := rankinK_nonneg
  have hexp4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  have hodd : ∀ i, ∀ p ∈ (r i).primeFactors, 3 ≤ p := by
    intro i p hp
    have := D₀_lt_of_prime_dvd_coord hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
    omega
  have hrp : ∀ i, ∀ p ∈ (r i).primeFactors, D₀ k < p := fun i p hp =>
    D₀_lt_of_prime_dvd_coord hrsupp (Nat.prime_of_mem_primeFactors hp)
      (Nat.dvd_of_mem_primeFactors hp)
  have hRankin : ∑ q ∈ (Finset.range R).filter Squarefree, 1 / (Nat.totient q : ℝ)
      ≤ rankinK * Real.log R := rankinK_bound R hR
  set H : Fin k → ℕ → ℝ := fun i x =>
    if i = m then 1 / (Nat.totient x : ℝ) else (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 with hHdef
  have hHnn : ∀ i x, 0 ≤ H i x := by
    intro i x; simp only [hHdef]; split_ifs <;> positivity
  set P : ℝ := ∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ) with hPdef
  set INNER : (Fin k → ℕ) → ℝ := fun a =>
    (y a / ∏ i, (Nat.totient (a i) : ℝ))
      * ∏ i ∈ Finset.univ.erase m,
          (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))) with hINNERdef
  set FG := (kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i) with hFGdef
  set Df := (kSieveIndex k R (W k)).filter
      (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i) with hDfdef
  -- per-`a` pointwise bound `|INNER a| ≤ ∏ᵢ Hᵢ(aᵢ)`
  have hbound : ∀ a ∈ kSieveIndex k R (W k), |INNER a| ≤ ∏ i, H i (a i) := by
    intro a haK
    have hφa : ∀ i, (0 : ℝ) < (Nat.totient (a i) : ℝ) := fun i => by
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos haK i)
    have hΦsplit : (∏ i, (Nat.totient (a i) : ℝ))
        = (Nat.totient (a m) : ℝ) * ∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ) :=
      (Finset.mul_prod_erase Finset.univ (fun i => (Nat.totient (a i) : ℝ))
        (Finset.mem_univ m)).symm
    have hprodH : (∏ i, H i (a i))
        = (1 / (Nat.totient (a m) : ℝ))
          * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => H i (a i)) (Finset.mem_univ m)]
      congr 1
      · simp only [hHdef]; rw [if_true]
      · exact Finset.prod_congr rfl (fun i hi => by
          simp only [hHdef]; rw [if_neg (Finset.ne_of_mem_erase hi)])
    rw [hprodH]
    simp only [hINNERdef]
    rw [abs_mul, abs_div, abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hφa i).le)),
      Finset.abs_prod]
    have hstep2 : ∀ i ∈ Finset.univ.erase m,
        |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
          ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by
      intro i _
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ))]
      have h1 := abs_moebius_real_le_one (a i)
      have h2 : (0 : ℝ) ≤ (r i : ℝ) / (Nat.totient (a i) : ℝ) := by positivity
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - |((μ (a i) : ℤ) : ℝ)|) h2]
    calc |y a| / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                |((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))|
        ≤ 1 / (∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ)) := by
          apply mul_le_mul
          · rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
            calc |y a| * (∏ i, (Nat.totient (a i) : ℝ))⁻¹
                ≤ 1 * (∏ i, (Nat.totient (a i) : ℝ))⁻¹ :=
                  mul_le_mul_of_nonneg_right (hy1 a) (by positivity)
              _ = (∏ i, (Nat.totient (a i) : ℝ))⁻¹ := one_mul _
          · exact Finset.prod_le_prod (fun i _ => abs_nonneg _) hstep2
          · exact Finset.prod_nonneg (fun i _ => abs_nonneg _)
          · positivity
      _ = (1 / (Nat.totient (a m) : ℝ))
            * ∏ i ∈ Finset.univ.erase m, ((r i : ℝ) / (Nat.totient (a i) : ℝ) ^ 2) := by
          rw [hΦsplit, Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_pow]
          have hPFne : (∏ i ∈ Finset.univ.erase m, (Nat.totient (a i) : ℝ)) ≠ 0 :=
            (Finset.prod_pos (fun i _ => hφa i)).ne'
          have hφamne : (Nat.totient (a m) : ℝ) ≠ 0 := (hφa m).ne'
          field_simp
  -- per-`j` product bound (all `R`-free except the single `log R`)
  have hjbound : ∀ j ∈ Finset.univ.erase m,
      |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ rankinK * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 := by
    intro j hj
    have hfact := tail_factor_le'' k R j r H hHnn
    set U : Fin k → ℝ := fun i =>
      (r i : ℝ) * (if i = j then (1 / (Nat.totient (r i) : ℝ) ^ 2) * (4 / (D₀ k : ℝ))
        else (1 / (Nat.totient (r i) : ℝ) ^ 2) * (1 + 4 / (D₀ k : ℝ))) with hUdef
    -- factor bound per coordinate `i ≠ m`
    have hUbound : ∀ i ∈ Finset.univ.erase m, (∑ x ∈ tailCoordSet k R r j i, H i x) ≤ U i := by
      intro i hi
      have him : i ≠ m := Finset.ne_of_mem_erase hi
      have hHi : ∀ x, H i x = (r i : ℝ) / (Nat.totient x : ℝ) ^ 2 := by
        intro x; simp only [hHdef]; rw [if_neg him]
      rw [Finset.sum_congr rfl (fun x _ => hHi x)]
      rw [show (∑ x ∈ tailCoordSet k R r j i, (r i : ℝ) / (Nat.totient x : ℝ) ^ 2)
            = (r i : ℝ) * ∑ x ∈ tailCoordSet k R r j i, 1 / (Nat.totient x : ℝ) ^ 2 from by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun x _ => by rw [mul_one_div])]
      simp only [hUdef]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      by_cases hij : i = j
      · rw [if_pos hij]
        have hset : tailCoordSet k R r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x ∧ x ≠ r i) := by
          simp only [tailCoordSet]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_ne_tight k R hD4 (r i) (hsq i)
      · rw [if_neg hij]
        have hset : tailCoordSet k R r j i = (Finset.range R).filter
            (fun x => Squarefree x ∧ (∀ p ∈ x.primeFactors, D₀ k < p) ∧ r i ∣ x) := by
          simp only [tailCoordSet]; apply Finset.filter_congr; intro x _; simp [hij]
        rw [hset]
        exact phiSq_dvd_tight k R hD4 (r i) (hsq i) (hrp i) (kSieveIndex_coord_lt hrsupp i)
    -- the `m`-coordinate factor `≤ rankinK log R`
    have hmfac : (∑ x ∈ tailCoordSet k R r j m, H m x) ≤ rankinK * Real.log R := by
      have hHm : ∀ x, H m x = 1 / (Nat.totient x : ℝ) := by
        intro x; simp only [hHdef]; rw [if_true]
      rw [Finset.sum_congr rfl (fun x _ => hHm x)]
      refine le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => by positivity)) hRankin
      intro x hx
      simp only [tailCoordSet, Finset.mem_filter, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hx.1, hx.2.1⟩
    -- `|P| ≤ ∏_{i≠m} g(rᵢ)`
    have hPabs : |P| ≤ ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
      rw [hPdef]
      calc |∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)|
          = ∏ i, |((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ)| := Finset.abs_prod _ _
        _ ≤ ∏ i, (gMult (r i) : ℝ) := by
            refine Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => ?_)
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gMult (r i) : ℝ))]
            calc |((μ (r i) : ℤ) : ℝ)| * (gMult (r i) : ℝ)
                ≤ 1 * (gMult (r i) : ℝ) := by
                  apply mul_le_mul_of_nonneg_right (abs_moebius_real_le_one _) (by positivity)
              _ = (gMult (r i) : ℝ) := one_mul _
        _ = ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ) := by
            rw [← Finset.mul_prod_erase Finset.univ (fun i => (gMult (r i) : ℝ))
              (Finset.mem_univ m), hrm]
            simp [gMult, Nat.primeFactors_one]
    -- combine per-coordinate factors
    have hprodU : (∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x)
        ≤ (∑ x ∈ tailCoordSet k R r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => ∑ x ∈ tailCoordSet k R r j i, H i x)
        (Finset.mem_univ m)]
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun x _ => hHnn m x))
      exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg (fun x _ => hHnn i x)) hUbound
    -- `(g·U) j ≤ 4/D₀`
    have hjfac : (gMult (r j) : ℝ) * U j ≤ 4 / (D₀ k : ℝ) := by
      simp only [hUdef]; rw [if_true]
      rw [show (gMult (r j) : ℝ) * ((r j : ℝ)
              * ((1 / (Nat.totient (r j) : ℝ) ^ 2) * (4 / (D₀ k : ℝ))))
            = ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (4 / (D₀ k : ℝ)) from by ring]
      calc ((gMult (r j) : ℝ) * (r j : ℝ) / (Nat.totient (r j) : ℝ) ^ 2)
              * (4 / (D₀ k : ℝ))
          ≤ 1 * (4 / (D₀ k : ℝ)) :=
            mul_le_mul_of_nonneg_right (gr_ratio_mem'' (hsq j) (hodd j)).2 (by positivity)
        _ = 4 / (D₀ k : ℝ) := one_mul _
    -- the rest of the coordinates `≤ exp 4`
    have hrestfac : ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
        ≤ Real.exp 4 := by
      have hcard : ((Finset.univ.erase m).erase j).card ≤ k := by
        calc ((Finset.univ.erase m).erase j).card
            ≤ (Finset.univ : Finset (Fin k)).card :=
              Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
          _ = k := by rw [Finset.card_univ, Fintype.card_fin]
      have hfac_le : (1 : ℝ) + 4 / (D₀ k : ℝ) ≤ Real.exp (4 / (D₀ k : ℝ)) := by
        have h := Real.add_one_le_exp (4 / (D₀ k : ℝ)); linarith
      have hcard_le : (((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D₀ k : ℝ)) ≤ 4 := by
        have h1 : (((Finset.univ.erase m).erase j).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
        calc (((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D₀ k : ℝ))
            ≤ (k : ℝ) * (4 / (D₀ k : ℝ)) := by gcongr
          _ ≤ (D₀ k : ℝ) * (4 / (D₀ k : ℝ)) := by gcongr
          _ = 4 := by field_simp
      calc ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i)
          ≤ ∏ _i ∈ (Finset.univ.erase m).erase j, (1 + 4 / (D₀ k : ℝ)) := by
            refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]; positivity
            · have hijne : i ≠ j := Finset.ne_of_mem_erase hi
              simp only [hUdef]; rw [if_neg hijne]
              rw [show (gMult (r i) : ℝ) * ((r i : ℝ)
                    * ((1 / (Nat.totient (r i) : ℝ) ^ 2) * (1 + 4 / (D₀ k : ℝ))))
                    = ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)
                      * (1 + 4 / (D₀ k : ℝ)) from by ring]
              have hge := (gr_ratio_mem'' (hsq i) (hodd i)).2
              nlinarith [hge, (by positivity : (0:ℝ) ≤ 1 + 4 / (D₀ k : ℝ))]
        _ = (1 + 4 / (D₀ k : ℝ)) ^ ((Finset.univ.erase m).erase j).card := by
            rw [Finset.prod_const]
        _ ≤ (Real.exp (4 / (D₀ k : ℝ))) ^ ((Finset.univ.erase m).erase j).card :=
            pow_le_pow_left₀ (by positivity) hfac_le _
        _ = Real.exp ((((Finset.univ.erase m).erase j).card : ℝ) * (4 / (D₀ k : ℝ))) :=
            (Real.exp_nat_mul (4 / (D₀ k : ℝ)) _).symm
        _ ≤ Real.exp 4 := Real.exp_le_exp.mpr hcard_le
    have hrestnn : (0 : ℝ) ≤ ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) := by
      refine Finset.prod_nonneg (fun i hi => ?_)
      have hijne : i ≠ j := Finset.ne_of_mem_erase hi
      simp only [hUdef]; rw [if_neg hijne]; positivity
    -- assemble
    calc |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
              ∏ i, H i (a i)
        ≤ |P| * ∏ i, ∑ x ∈ tailCoordSet k R r j i, H i x :=
          mul_le_mul_of_nonneg_left hfact (abs_nonneg _)
      _ ≤ |P| * ((∑ x ∈ tailCoordSet k R r j m, H m x) * ∏ i ∈ Finset.univ.erase m, U i) :=
          mul_le_mul_of_nonneg_left hprodU (abs_nonneg _)
      _ = (∑ x ∈ tailCoordSet k R r j m, H m x) * (|P| * ∏ i ∈ Finset.univ.erase m, U i) := by ring
      _ ≤ (rankinK * Real.log R) * ((4 / (D₀ k : ℝ)) * Real.exp 4) := by
          refine mul_le_mul hmfac ?_ ?_ (mul_nonneg hC₁0 hlogR)
          · calc |P| * ∏ i ∈ Finset.univ.erase m, U i
                ≤ (∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
                    * ∏ i ∈ Finset.univ.erase m, U i := by
                  refine mul_le_mul_of_nonneg_right hPabs (Finset.prod_nonneg (fun i _ => ?_))
                  simp only [hUdef]; split_ifs <;> positivity
              _ = ∏ i ∈ Finset.univ.erase m, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.prod_mul_distrib).symm
              _ = ((gMult (r j) : ℝ) * U j)
                    * ∏ i ∈ (Finset.univ.erase m).erase j, ((gMult (r i) : ℝ) * U i) :=
                  (Finset.mul_prod_erase (Finset.univ.erase m)
                    (fun i => (gMult (r i) : ℝ) * U i) hj).symm
              _ ≤ (4 / (D₀ k : ℝ)) * Real.exp 4 :=
                  mul_le_mul hjfac hrestfac hrestnn (by positivity)
          · exact mul_nonneg (abs_nonneg _)
              (Finset.prod_nonneg (fun i _ => by simp only [hUdef]; split_ifs <;> positivity))
      _ = rankinK * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 := by ring
  -- main bound
  rw [abs_mul]
  calc |P| * |∑ a ∈ FG \ Df, INNER a|
      ≤ |P| * ∑ a ∈ FG \ Df, |INNER a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
    _ ≤ |P| * ∑ a ∈ FG \ Df, ∏ i, H i (a i) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a ha => ?_)) (abs_nonneg _)
        rw [Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
        exact hbound a ha.1.1
    _ ≤ |P| * ∑ j ∈ Finset.univ.erase m,
          ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
            ∏ i, H i (a i) := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hunion : ∀ a ∈ FG \ Df, (∏ i, H i (a i))
            ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
          intro a ha
          rw [Finset.mem_sdiff] at ha
          obtain ⟨haFG, haDf⟩ := ha
          rw [hFGdef, Finset.mem_filter] at haFG
          obtain ⟨j, hjmem, hjne⟩ : ∃ j ∈ Finset.univ.erase m, a j ≠ r j := by
            by_contra hcon
            apply haDf
            rw [hDfdef, Finset.mem_filter]
            refine ⟨haFG.1, haFG.2, fun i hi => ?_⟩
            by_contra hne
            exact hcon ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hne⟩
          calc (∏ i, H i (a i)) = if a j ≠ r j then ∏ i, H i (a i) else 0 := by rw [if_pos hjne]
            _ ≤ ∑ j ∈ Finset.univ.erase m, (if a j ≠ r j then ∏ i, H i (a i) else 0) := by
                refine Finset.single_le_sum
                  (f := fun j => if a j ≠ r j then ∏ i, H i (a i) else 0) (fun j _ => ?_) hjmem
                split_ifs
                · exact Finset.prod_nonneg (fun i _ => hHnn i (a i))
                · exact le_refl 0
        calc ∑ a ∈ FG \ Df, ∏ i, H i (a i)
            ≤ ∑ a ∈ FG \ Df, ∑ j ∈ Finset.univ.erase m,
                (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_le_sum hunion
          _ = ∑ j ∈ Finset.univ.erase m, ∑ a ∈ FG \ Df,
                (if a j ≠ r j then ∏ i, H i (a i) else 0) := Finset.sum_comm
          _ ≤ ∑ j ∈ Finset.univ.erase m,
                ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
                  ∏ i, H i (a i) := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              rw [← Finset.sum_filter]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_
                (fun a _ _ => Finset.prod_nonneg (fun i _ => hHnn i (a i)))
              intro a ha
              rw [Finset.mem_filter, Finset.mem_sdiff, hFGdef, Finset.mem_filter] at ha
              rw [Finset.mem_filter]
              exact ⟨ha.1.1.1, ha.1.1.2, ha.2⟩
    _ = ∑ j ∈ Finset.univ.erase m,
          |P| * ∑ a ∈ (kSieveIndex k R (W k)).filter (fun a => (∀ i, r i ∣ a i) ∧ a j ≠ r j),
            ∏ i, H i (a i) := Finset.mul_sum _ _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase m, rankinK * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 :=
        Finset.sum_le_sum hjbound
    _ = ((Finset.univ.erase m).card : ℝ)
          * (rankinK * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * Real.exp 4 * rankinK * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
        have hcardle : ((Finset.univ.erase m).card : ℝ) ≤ (k : ℝ) := by
          have : (Finset.univ.erase m).card ≤ k := by
            calc (Finset.univ.erase m).card ≤ (Finset.univ : Finset (Fin k)).card :=
                  Finset.card_le_card (Finset.erase_subset _ _)
              _ = k := by rw [Finset.card_univ, Fintype.card_fin]
          exact_mod_cast this
        have hXnn : (0 : ℝ) ≤ rankinK * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4 :=
          mul_nonneg (mul_nonneg (mul_nonneg hC₁0 hlogR) (by positivity)) hexp4
        have heq : (k : ℝ) * (rankinK * Real.log R * (4 / (D₀ k : ℝ)) * Real.exp 4)
            = (4 * Real.exp 4 * rankinK * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
          field_simp
        exact le_trans (mul_le_mul_of_nonneg_right hcardle hXnn) (le_of_eq heq)

/-- **Lemma 5.3, explicit constant.** Copy of `lemma53_tight` with
`rankinC → rankinK`, `lemma53Const → lemma53KConst`. -/
theorem lemma53_K (k R : ℕ) (m : Fin k) (y : (Fin k → ℕ) → ℝ)
    (hy1 : ∀ s, |y s| ≤ 1) (hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → y s = 0)
    (r : Fin k → ℕ) (hrm : r m = 1) (hR : 2 ≤ R) (hrsupp : r ∈ kSieveIndex k R (W k))
    (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |yM k R (W k) m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)|
      ≤ (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
  classical
  have hSb := abs_mainSum_le_K k R m y hy1 hysupp r hR
  have hTb := htail_K k R m y hy1 hysupp r hrm hR hrsupp hk hD
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by have : 1 ≤ k^2 := Nat.one_le_pow 2 k (by omega); omega
    exact_mod_cast this
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hC₁0 : (0 : ℝ) ≤ rankinK := rankinK_nonneg
  have hexp4 : (0 : ℝ) ≤ Real.exp 4 := (Real.exp_pos 4).le
  have hsub : (kSieveIndex k R (W k)).filter
        (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)
      ⊆ (kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1⟩
  have hlpc : lamPhiContractM k R (W k) m y r
      = (∑ a ∈ (kSieveIndex k R (W k)).filter
            (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ))))
        + (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
              ((kSieveIndex k R (W k)).filter
                (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
            (y a / ∏ i, (Nat.totient (a i) : ℝ))
              * ∏ i ∈ Finset.univ.erase m,
                  (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [lamPhiContractM_collapse k R (W k) m y r hrm, ← Finset.sum_filter, add_comm]
    exact (Finset.sum_sdiff hsub).symm
  have hdiff : yM k R (W k) m y r
        - ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ)
      = ((∏ i ∈ Finset.univ.erase m,
            ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2)) - 1)
          * (∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ))
        + (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
          * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
                ((kSieveIndex k R (W k)).filter
                  (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
              (y a / ∏ i, (Nat.totient (a i) : ℝ))
                * ∏ i ∈ Finset.univ.erase m,
                    (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) := by
    rw [show yM k R (W k) m y r
          = (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
            * lamPhiContractM k R (W k) m y r from rfl,
      hlpc, mul_add, stepB_identity k R m y hysupp r hrsupp hrm]
    ring
  rw [hdiff]
  set G := ∏ i ∈ Finset.univ.erase m,
    ((gMult (r i) : ℝ) * (r i : ℝ) / (Nat.totient (r i) : ℝ) ^ 2) with hGdef
  set S := ∑ am ∈ Finset.range R, y (Function.update r m am) / (Nat.totient am : ℝ) with hSdef
  set PT := (∏ i, ((μ (r i) : ℤ) : ℝ) * (gMult (r i) : ℝ))
      * (∑ a ∈ ((kSieveIndex k R (W k)).filter (fun a => ∀ i, r i ∣ a i)) \
            ((kSieveIndex k R (W k)).filter
              (fun a => (∀ i, r i ∣ a i) ∧ ∀ i, i ≠ m → a i = r i)),
          (y a / ∏ i, (Nat.totient (a i) : ℝ))
            * ∏ i ∈ Finset.univ.erase m,
                (((μ (a i) : ℤ) : ℝ) * ((r i : ℝ) / (Nat.totient (a i) : ℝ)))) with hPTdef
  have hG : |G - 1| ≤ 2 / (D₀ k : ℝ) := gProd_bound k R hk hD r hrsupp m
  have e2 : |G - 1| * |S| ≤ (2 / (D₀ k : ℝ)) * (rankinK * Real.log R) :=
    mul_le_mul hG hSb (abs_nonneg _) (by positivity)
  have hfinal : (2 / (D₀ k : ℝ)) * (rankinK * Real.log R)
        + (4 * Real.exp 4 * rankinK * (k : ℝ)) * Real.log R / (D₀ k : ℝ)
      ≤ (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := by
    have hnum : 2 * (rankinK * Real.log R)
          + 4 * Real.exp 4 * rankinK * (k : ℝ) * Real.log R
        ≤ (lemma53KConst * (k : ℝ)) * Real.log R := by
      rw [lemma53KConst]
      nlinarith [hC₁0, hlogR, hexp4, hkR, mul_nonneg hC₁0 hlogR,
        mul_nonneg (mul_nonneg hexp4 hC₁0) hlogR]
    have hLHSeq : (2 / (D₀ k : ℝ)) * (rankinK * Real.log R)
          + (4 * Real.exp 4 * rankinK * (k : ℝ)) * Real.log R / (D₀ k : ℝ)
        = (2 * (rankinK * Real.log R)
            + 4 * Real.exp 4 * rankinK * (k : ℝ) * Real.log R) / (D₀ k : ℝ) := by
      field_simp
    rw [hLHSeq]
    gcongr
  calc |(G - 1) * S + PT|
      ≤ |(G - 1) * S| + |PT| := abs_add_le _ _
    _ = |G - 1| * |S| + |PT| := by rw [abs_mul]
    _ ≤ (2 / (D₀ k : ℝ)) * (rankinK * Real.log R)
          + (4 * Real.exp 4 * rankinK * (k : ℝ)) * Real.log R / (D₀ k : ℝ) :=
        add_le_add e2 hTb
    _ ≤ (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ) := hfinal

/-- **Lemma 5.3, relative form, explicit constant.** Copy of `lemma53_rel_tight`
with `lemma53_tight → lemma53_K`, `lemma53Const → lemma53KConst`. -/
theorem lemma53_rel_K (k R : ℕ) (T : ℝ) (m : Fin k)
    (v : Fin k → ℕ) (hvm : v m = 1) (hR : 2 ≤ R)
    (hvsupp : v ∈ kSieveIndex k R (W k)) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |yM k R (W k) m (yTensor k R T) v
        - ∑ am ∈ Finset.range R,
            yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)|
      ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (v i))
          * ((lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) := by
  classical
  set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (v i) with hPdef
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  by_cases hP0 : P = 0
  · obtain ⟨i₀, hi₀mem, hi₀0⟩ := Finset.prod_eq_zero_iff.mp hP0
    have hi₀ne : i₀ ≠ m := Finset.ne_of_mem_erase hi₀mem
    have hyM0 : yM k R (W k) m (yTensor k R T) v = 0 := by
      have hV0 : lamPhiContractM k R (W k) m (yTensor k R T) v = 0 := by
        rw [lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm]
        apply Finset.sum_eq_zero
        intro a ha
        by_cases hcond : ∀ i, v i ∣ a i
        · rw [if_pos hcond]
          have hya : yTensor k R T a = 0 := by
            simp only [yTensor, if_pos ha]
            refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
            have hpos : 0 < a i₀ :=
              Nat.pos_of_ne_zero (((mem_kSieveIndex_iff a).mp ha).1 i₀).ne_zero
            have hle : fTilde k R T (a i₀) ≤ fTilde k R T (v i₀) :=
              fTilde_anti k R T hR (v i₀) (a i₀) hpos (hcond i₀)
            rw [hi₀0] at hle
            exact le_antisymm hle (fTilde_nonneg k R T _ hR)
          rw [hya]; ring
        · rw [if_neg hcond]
      simp only [yM, hV0, mul_zero]
    have hC0sum : (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro am _
      have hya : yTensor k R T (Function.update v m am) = 0 := by
        simp only [yTensor]
        split_ifs with hmem
        · refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
          rw [Function.update_of_ne hi₀ne]; exact hi₀0
        · rfl
      rw [hya, zero_div]
    rw [hyM0, hC0sum, hP0]; simp
  · have hP : 0 < P := lt_of_le_of_ne hPnn (Ne.symm hP0)
    set z : (Fin k → ℕ) → ℝ :=
      fun a => if (∀ i, v i ∣ a i) then yTensor k R T a / P else 0 with hzdef
    have hza : ∀ a, z a = if (∀ i, v i ∣ a i) then yTensor k R T a / P else 0 :=
      fun a => rfl
    have hy1 : ∀ s, |z s| ≤ 1 := by
      intro s
      rw [hza s]
      split_ifs with hcond
      · rw [abs_div, abs_of_pos hP, div_le_one hP,
          abs_of_nonneg (yTensor_nonneg k R T hR s)]
        simp only [yTensor]
        split_ifs with hmem
        · have hsq : ∀ i, Squarefree (s i) := fun i => ((mem_kSieveIndex_iff s).mp hmem).1 i
          calc ∏ i, fTilde k R T (s i)
              = fTilde k R T (s m) * ∏ i ∈ Finset.univ.erase m, fTilde k R T (s i) :=
                (Finset.mul_prod_erase Finset.univ (fun i => fTilde k R T (s i))
                  (Finset.mem_univ m)).symm
            _ ≤ 1 * ∏ i ∈ Finset.univ.erase m, fTilde k R T (v i) := by
                refine mul_le_mul (fTilde_le_one k R T hR (s m)) ?_
                  (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)) zero_le_one
                refine Finset.prod_le_prod (fun i _ => fTilde_nonneg k R T _ hR) ?_
                intro i _
                exact fTilde_anti k R T hR (v i) (s i)
                  (Nat.pos_of_ne_zero (hsq i).ne_zero) (hcond i)
            _ = P := by rw [one_mul, hPdef]
        · exact hPnn
      · simp
    have hysupp : ∀ s, s ∉ kSieveIndex k R (W k) → z s = 0 := by
      intro s hs
      rw [hza s]
      split_ifs with hcond
      · rw [show yTensor k R T s = 0 by simp only [yTensor]; rw [if_neg hs], zero_div]
      · rfl
    have hV : lamPhiContractM k R (W k) m z v
        = lamPhiContractM k R (W k) m (yTensor k R T) v / P := by
      rw [lamPhiContractM_collapse k R (W k) m z v hvm,
          lamPhiContractM_collapse k R (W k) m (yTensor k R T) v hvm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hcond : ∀ i, v i ∣ a i
      · rw [if_pos hcond, if_pos hcond, hza a, if_pos hcond]; ring
      · rw [if_neg hcond, if_neg hcond, zero_div]
    have hyM : yM k R (W k) m z v = yM k R (W k) m (yTensor k R T) v / P := by
      simp only [yM]; rw [hV]; ring
    have hContr : (∑ am ∈ Finset.range R, z (Function.update v m am) / (Nat.totient am : ℝ))
        = (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)) / P := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro am _
      have hcond : ∀ i, v i ∣ (Function.update v m am) i := by
        intro i
        by_cases hi : i = m
        · subst hi; rw [Function.update_self, hvm]; exact one_dvd _
        · rw [Function.update_of_ne hi]
      rw [hza (Function.update v m am), if_pos hcond]; ring
    have hbound := lemma53_K k R m z hy1 hysupp v hvm hR hvsupp hk hD
    rw [hyM, hContr, ← sub_div, abs_div, abs_of_pos hP, div_le_iff₀ hP] at hbound
    calc |yM k R (W k) m (yTensor k R T) v
            - ∑ am ∈ Finset.range R,
                yTensor k R T (Function.update v m am) / (Nat.totient am : ℝ)|
        ≤ (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ) * P := hbound
      _ = P * ((lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) := by ring

/-! ### S₂ main lower bound helpers (verbatim copies of the private helpers) -/

private lemma sumFTilde_le_B1'' (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) :
    (∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ)) ≤ B1 k R (W k) T := by
  classical
  have hfe : ∀ am : ℕ, fTilde k R T am / (Nat.totient am : ℝ)
      = if am ∈ sqfCop (R0 k R T) (W k) then fWt k R am / (Nat.totient am : ℝ) else 0 := by
    intro am
    simp only [fTilde]
    split_ifs <;> simp
  have hrewrite : (∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ))
      = ∑ am ∈ Finset.range R,
          if am ∈ sqfCop (R0 k R T) (W k) then fWt k R am / (Nat.totient am : ℝ) else 0 :=
    Finset.sum_congr rfl (fun am _ => hfe am)
  rw [hrewrite, ← Finset.sum_filter]
  unfold B1
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro am ham
    rw [Finset.mem_filter] at ham
    exact ham.2
  · intro am ham _
    have hr : 1 ≤ am := by
      rw [sqfCop, Finset.mem_filter] at ham
      exact Nat.one_le_iff_ne_zero.mpr ham.2.1.ne_zero
    exact div_nonneg (fWt_nonneg hr hR) (Nat.cast_nonneg _)

private lemma yTensor_update_le'' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) (am : ℕ) :
    yTensor k R T (Function.update u m am)
      ≤ fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
  have hprodeq : (∏ i, fTilde k R T ((Function.update u m am) i))
      = fTilde k R T am * ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => fTilde k R T ((Function.update u m am) i)) (Finset.mem_univ m)]
    rw [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [yTensor]
  split_ifs with hmem
  · exact le_of_eq hprodeq
  · exact mul_nonneg (fTilde_nonneg k R T am hR)
      (Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR))

private lemma contraction_nonneg'' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) :
    0 ≤ ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) := by
  apply Finset.sum_nonneg
  intro am _
  exact div_nonneg (yTensor_nonneg k R T hR _) (Nat.cast_nonneg _)

private lemma contraction_le'' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (u : Fin k → ℕ) :
    (∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i)) * B1 k R (W k) T := by
  set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hP
  have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
  calc (∑ am ∈ Finset.range R,
          yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ))
      ≤ ∑ am ∈ Finset.range R, (fTilde k R T am * P) / (Nat.totient am : ℝ) := by
        apply Finset.sum_le_sum
        intro am _
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (yTensor_update_le'' k R T m hR u am)
          (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = P * ∑ am ∈ Finset.range R, fTilde k R T am / (Nat.totient am : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro am _
        rw [mul_comm (fTilde k R T am) P, mul_div_assoc]
    _ ≤ P * B1 k R (W k) T :=
        mul_le_mul_of_nonneg_left (sumFTilde_le_B1'' k R T hR) hPnn

private lemma errbox_le'' (k R : ℕ) (T : ℝ) (m : Fin k) (hR : 2 ≤ R)
    (hD : 12 * k ^ 2 ≤ D₀ k) :
    (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
          * |∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≤ B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1)) := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k m.pos
  have hD12 : 12 ≤ D₀ k := by omega
  have hB1nn : 0 ≤ B1 k R (W k) T := B1_nonneg k R (W k) T hR
  have hclaimA : ∀ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
      (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
        * |∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
        / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ B1 k R (W k) T
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    have hsq : ∀ i, Squarefree (u i) := fun i => ((mem_kSieveIndex_iff u).mp husupp).1 i
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    have hgpos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφpos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφpos i)
    have hbnn := contraction_nonneg'' k R T m hR u
    have hble := contraction_le'' k R T m hR u
    set b := ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    rw [abs_of_nonneg hbnn]
    have hΦerase : Φ = ∏ i ∈ Finset.univ.erase m, (Nat.totient (u i) : ℝ) := by
      rw [hΦdef, ← Finset.mul_prod_erase Finset.univ
        (fun i => (Nat.totient (u i) : ℝ)) (Finset.mem_univ m), hum]
      simp
    have hP2Φ : P ^ 2 / Φ
        = ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
      rw [hPdef, hΦerase, ← Finset.prod_pow, ← Finset.prod_div_distrib]
    calc P * b / Φ
        = (P / Φ) * b := by ring
      _ ≤ (P / Φ) * (P * B1 k R (W k) T) :=
          mul_le_mul_of_nonneg_left hble (div_nonneg hPnn hΦpos.le)
      _ = B1 k R (W k) T * (P ^ 2 / Φ) := by ring
      _ = B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
          rw [hP2Φ]
      _ ≤ B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hB1nn
          apply Finset.prod_le_prod
          · intro i _; exact div_nonneg (sq_nonneg _) (hφpos i).le
          · intro i _
            exact div_le_div_of_nonneg_left (sq_nonneg _) (hgpos i)
              (gMult_le_totient (hsq i) (hodd i))
  calc (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * |∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
            / ∏ i, (Nat.totient (u i) : ℝ))
      ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          B1 k R (W k) T
            * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) :=
        Finset.sum_le_sum hclaimA
    _ = B1 k R (W k) T
          * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
              ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (gMult (u i) : ℝ) := by
        rw [← Finset.mul_sum]
    _ = B1 k R (W k) T * Gdiag k R T m := by simp only [Gdiag]
    _ ≤ B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left (Gdiag_le k R T m hR hD) hB1nn

/-- **S₂ main lower bound, relative, explicit constant.** Copy of
`s2main_lower_rel_tight` with `lemma53_rel_tight → lemma53_rel_K`,
`lemma53Const → lemma53KConst`. -/
theorem s2main_lower_rel_K (k R : ℕ) (m : Fin k) (T : ℝ)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    Qdiag_m k R m (yTensor k R T)
      ≥ (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
           (∑ am ∈ Finset.range R,
               yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
             / ∏ i, (Nat.totient (u i) : ℝ))
        - (2 * (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) * (B1 k R (W k) T)
            * (2 * (A1 k R (W k) T) ^ (k - 1)) := by
  classical
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k (by omega)
  have hD12 : 12 ≤ D₀ k := by omega
  have hD0pos : 0 < D₀ k := by omega
  have hD0R : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hD0pos
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ R)
  have hlognn : 0 ≤ Real.log R := Real.log_nonneg hR1
  set C := lemma53KConst * (k : ℝ) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]; exact mul_nonneg lemma53KConst_nonneg (Nat.cast_nonneg k)
  have hspec : ∀ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
      |yM k R (W k) m (yTensor k R T) u
          - ∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
        ≤ (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * (C * Real.log R / (D₀ k : ℝ)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    exact lemma53_rel_K k R T m u hu.2 hR hu.1 hk hD
  set K := 2 * C * Real.log R / (D₀ k : ℝ) with hKdef
  have hmain_rel :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * ((∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
                    * |∑ am ∈ Finset.range R,
                        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))))
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    apply Finset.sum_le_sum
    intro u hu
    have hmem := hu
    rw [Finset.mem_filter] at hu
    obtain ⟨husupp, hum⟩ := hu
    obtain ⟨hsq, hcop, hcopW, hprodR⟩ := (mem_kSieveIndex_iff u).mp husupp
    have hodd : ∀ i, ∀ p ∈ (u i).primeFactors, 3 ≤ p := by
      intro i p hp
      have := D₀_lt_of_prime_dvd_coord husupp (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp)
      omega
    have hgcoord_pos : ∀ i, 0 < (gMult (u i) : ℝ) := by
      intro i
      have hpos : 0 < gMult (u i) := by
        rw [gMult]; apply Finset.prod_pos; intro p hp; have := hodd i p hp; omega
      exact_mod_cast hpos
    have hφcoord_pos : ∀ i, 0 < (Nat.totient (u i) : ℝ) := by
      intro i; exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos husupp i)
    set V := lamPhiContractM k R (W k) m (yTensor k R T) u with hVdef
    set G := ∏ i, (gMult (u i) : ℝ) with hGdef
    set Φ := ∏ i, (Nat.totient (u i) : ℝ) with hΦdef
    set a := yM k R (W k) m (yTensor k R T) u with hadef
    set b := ∑ am ∈ Finset.range R,
        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ) with hbdef
    set P := ∏ i ∈ Finset.univ.erase m, fTilde k R T (u i) with hPdef
    have hPnn : 0 ≤ P := Finset.prod_nonneg (fun i _ => fTilde_nonneg k R T _ hR)
    have hGpos : 0 < G := Finset.prod_pos (fun i _ => hgcoord_pos i)
    have hΦpos : 0 < Φ := Finset.prod_pos (fun i _ => hφcoord_pos i)
    have hGleΦ : G ≤ Φ := by
      apply Finset.prod_le_prod
      · intro i _; exact (hgcoord_pos i).le
      · intro i _; exact gMult_le_totient (hsq i) (hodd i)
    have hμsq : (∏ i, ((μ (u i) : ℤ) : ℝ)) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro i _
      have h := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (hsq i)
      have hc : ((μ (u i) : ℤ) : ℝ) ^ 2 = (((μ (u i)) ^ 2 : ℤ) : ℝ) := by push_cast; ring
      rw [hc, h]; norm_num
    have hyMsq : a ^ 2 = G ^ 2 * V ^ 2 := by
      have hdef : a = (∏ i, ((μ (u i) : ℤ) : ℝ) * (gMult (u i) : ℝ)) * V := rfl
      rw [hdef, mul_pow, Finset.prod_mul_distrib, mul_pow, hμsq, one_mul]
    have herr : |a - b| ≤ P * (C * Real.log R / (D₀ k : ℝ)) := hspec u hmem
    have hsqb : b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ))) ≤ a ^ 2 := by
      have h1b : -(|b| * |a - b|) ≤ b * (a - b) := by
        have := neg_abs_le (b * (a - b)); rwa [abs_mul] at this
      have hstep : b ^ 2 - 2 * |b| * |a - b| ≤ a ^ 2 := by
        nlinarith [sq_nonneg (a - b), h1b]
      have h2b0 : (0 : ℝ) ≤ 2 * |b| := by positivity
      have hmul := mul_le_mul_of_nonneg_left herr h2b0
      linarith [hstep, hmul]
    have heq : b ^ 2 / Φ - K * ((P * |b|) / Φ)
        = (b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ)))) / Φ := by
      rw [sub_div, hKdef]; ring
    have hle1 : (b ^ 2 - 2 * |b| * (P * (C * Real.log R / (D₀ k : ℝ)))) / Φ ≤ a ^ 2 / Φ :=
      (div_le_div_iff_of_pos_right hΦpos).mpr hsqb
    have hle2 : a ^ 2 / Φ ≤ G * V ^ 2 := by
      rw [hyMsq, div_le_iff₀ hΦpos]
      nlinarith [mul_nonneg (mul_nonneg hGpos.le (sq_nonneg V)) (sub_nonneg.mpr hGleΦ)]
    rw [heq]; exact le_trans hle1 hle2
  have hrw' :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * |∑ am ∈ Finset.range R,
                  yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          ((∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
              / ∏ i, (Nat.totient (u i) : ℝ)
            - K * ((∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
                    * |∑ am ∈ Finset.range R,
                        yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
                    / ∏ i, (Nat.totient (u i) : ℝ))) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hQ : Qdiag_m k R m (yTensor k R T)
      = ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    unfold Qdiag_m
    exact s2_diag_lam_restricted k R (W k) m (yTensor k R T)
  have hE := errbox_le'' k R T m hR hD
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC0) hlognn) hD0R.le
  have hcombine :
      (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∑ am ∈ Finset.range R,
              yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
            / ∏ i, (Nat.totient (u i) : ℝ))
        - K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
              * |∑ am ∈ Finset.range R,
                  yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
              / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
            (∏ i, (gMult (u i) : ℝ)) * (lamPhiContractM k R (W k) m (yTensor k R T) u) ^ 2 := by
    rw [hrw']; exact hmain_rel
  rw [ge_iff_le, hQ]
  have hKE :
      K * ∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
          (∏ i ∈ Finset.univ.erase m, fTilde k R T (u i))
            * |∑ am ∈ Finset.range R,
                yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)|
            / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ K * (B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))) :=
    mul_le_mul_of_nonneg_left hE hK0
  have hassoc : K * B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))
      = K * (B1 k R (W k) T * (2 * (A1 k R (W k) T) ^ (k - 1))) := by ring
  rw [hassoc]
  linarith [hcombine, hKE]

/-- **C4 item 6 (assembled), explicit constant.** Copy of `s2CompatFormM_ge_cheb_tight`. -/
theorem s2CompatFormM_ge_cheb_K (k R : ℕ) (T : ℝ) (m : Fin k)
    (hR : 2 ≤ R) (hk : 1 ≤ k) (hD : 24 * k ^ 2 ≤ D₀ k)
    (hcheb : (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) :
    s2CompatFormM k R (W k) m (yTensor k R T)
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
        - (4 * (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ))
            * ((B1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1))
        - 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
            * ((B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)) := by
  have hP2 := s2main_lower_rel_K k R m T hR hk (by omega)
  have h6a := s2CompatFormM_ge_Qdiag k R T m hR hD
  have heq : (2 * (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ)) * (B1 k R (W k) T)
        * (2 * (A1 k R (W k) T) ^ (k - 1))
      = (4 * (lemma53KConst * (k : ℝ)) * Real.log R / (D₀ k : ℝ))
          * ((B1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 1)) := by ring
  rw [heq] at hP2
  linarith [h6a, hP2, hcheb]

/-- **Item 6 discharged to `(1/16)`, explicit constant.** Copy of
`s2CompatFormM_ge_sixteenth_tight` with `lemma53Const → lemma53KConst`; the regime
`hreg` is now numerically dischargeable because `lemma53KConst` is explicit. -/
theorem s2CompatFormM_ge_sixteenth_K (k R : ℕ) (T : ℝ) (m : Fin k)
    (hR : 2 ≤ R) (hk : 3072 ≤ k) (hD : k ^ 3 ≤ D₀ k)
    (hB1pos : 0 < B1 k R (W k) T) (hA1nn : 0 ≤ A1 k R (W k) T)
    (hcheb : (∑ u ∈ (kSieveIndex k R (W k)).filter (fun u => u m = 1),
        (∑ am ∈ Finset.range R,
            yTensor k R T (Function.update u m am) / (Nat.totient am : ℝ)) ^ 2
          / ∏ i, (Nat.totient (u i) : ℝ))
      ≥ (1 / 4 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1))
    (hreg : 32 * (lemma53KConst * (k : ℝ)) * Real.log R ≤ B1 k R (W k) T * (D₀ k : ℝ)) :
    (1 / 16 : ℝ) * (B1 k R (W k) T) ^ 2 * (A1 k R (W k) T) ^ (k - 1)
      ≤ s2CompatFormM k R (W k) m (yTensor k R T) := by
  have h24 : 24 * k ^ 2 ≤ D₀ k := by
    refine le_trans ?_ hD
    calc 24 * k ^ 2 ≤ k * k ^ 2 := by gcongr; omega
      _ = k ^ 3 := by ring
  have hbound := s2CompatFormM_ge_cheb_K k R T m hR (by omega) h24 hcheb
  have hkpos : 0 < k := by omega
  have hD0pos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := lt_of_lt_of_le (pow_pos hkpos 3) hD
    exact_mod_cast this
  set C := lemma53KConst * (k : ℝ) with hCdef
  set M := (A1 k R (W k) T) ^ (k - 1) with hMdef
  have hM : 0 ≤ M := pow_nonneg hA1nn _
  have hB1M : 0 ≤ B1 k R (W k) T * M := mul_nonneg hB1pos.le hM
  have hB2M : 0 ≤ (B1 k R (W k) T) ^ 2 * M := mul_nonneg (sq_nonneg _) hM
  have h1 : 4 * C * Real.log R / (D₀ k : ℝ) ≤ B1 k R (W k) T / 8 := by
    rw [div_le_iff₀ hD0pos] at *
    nlinarith [hreg]
  have he1 : 4 * C * Real.log R / (D₀ k : ℝ) * (B1 k R (W k) T * M)
      ≤ 1 / 8 * ((B1 k R (W k) T) ^ 2 * M) := by
    have := mul_le_mul_of_nonneg_right h1 hB1M
    nlinarith [this]
  have h2 : 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ) ≤ 1 / 16 := by
    rw [div_le_iff₀ hD0pos]
    have hk3 : (k : ℝ) ^ 3 ≤ (D₀ k : ℝ) := by exact_mod_cast hD
    have hkR : (3072 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [hk3, hkR, sq_nonneg (k : ℝ)]
  have he2 : 192 * (k : ℝ) ^ 2 / (D₀ k : ℝ) * ((B1 k R (W k) T) ^ 2 * M)
      ≤ 1 / 16 * ((B1 k R (W k) T) ^ 2 * M) :=
    mul_le_mul_of_nonneg_right h2 hB2M
  nlinarith [hbound, he1, he2]

/-! ## Part E — the `k`-largeness numeric fact -/

/-- `exp 2 > 7` (crude explicit bound). -/
private lemma exp2_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have hpos := Real.exp_pos 1
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [he2]; nlinarith [h, hpos]

/-- `exp 4 < 55` (crude explicit bound). -/
private lemma exp4_lt_55 : Real.exp 4 < 55 := by
  have h := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have he4 : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hexp2ub : Real.exp 2 < 7.4 := by rw [he2]; nlinarith [h, hpos]
  have hpos2 := Real.exp_pos 2
  rw [he4]; nlinarith [hexp2ub, hpos2]

/-- The explicit constant `A = 1728·lemma53KConst·exp 20` is `≤ exp 60`. -/
private lemma A_le_exp60 : 1728 * lemma53KConst * Real.exp 20 ≤ Real.exp 60 := by
  have hexp4 := exp4_lt_55
  have hexp2 := exp2_gt_seven
  have hpos20 := Real.exp_pos 20
  have hexp20 : (383616 : ℝ) ≤ Real.exp 20 := by
    have h : Real.exp 20 = (Real.exp 2) ^ 10 := by
      rw [show (20 : ℝ) = (10 : ℕ) * 2 by norm_num, Real.exp_nat_mul]
    rw [h]
    have h7 : (7 : ℝ) ^ 10 ≤ (Real.exp 2) ^ 10 :=
      pow_le_pow_left₀ (by norm_num) hexp2.le 10
    nlinarith [h7]
  have hlk : lemma53KConst = Real.exp 20 * (2 + 4 * Real.exp 4) := by rw [lemma53KConst, rankinK]
  have hexp40 : Real.exp 40 = Real.exp 20 * Real.exp 20 := by rw [← Real.exp_add]; norm_num
  have hexp60 : Real.exp 60 = Real.exp 20 * Real.exp 40 := by rw [← Real.exp_add]; norm_num
  rw [hlk, hexp60, hexp40]
  have h222 : 1728 * (2 + 4 * Real.exp 4) ≤ Real.exp 20 := by nlinarith [hexp4, hexp20]
  nlinarith [h222, hpos20, mul_pos hpos20 hpos20]

/-- **`k`-largeness.** For `log k ≥ 300`, `1728·lemma53KConst·exp 20·log k ≤ k`.
This closes the item-6 regime because `1728·lemma53KConst·exp 20 ≤ exp 60` and
`exp 60·L ≤ exp L = k` for `L = log k ≥ 300` (via `exp(L−60) ≥ (1+(L−60)/2)² ≥ L`). -/
theorem k_largeness (k : ℕ) (hk : 0 < k) (hlogk : 300 ≤ Real.log k) :
    1728 * lemma53KConst * Real.exp 20 * Real.log k ≤ (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set L := Real.log k with hL
  have hLge : (300 : ℝ) ≤ L := hlogk
  have hkexp : (k : ℝ) = Real.exp L := (Real.exp_log hkR).symm
  have hAle : 1728 * lemma53KConst * Real.exp 20 ≤ Real.exp 60 := A_le_exp60
  set u := (L - 60) / 2 with hu
  have hu120 : (120 : ℝ) ≤ u := by rw [hu]; linarith
  have hunn : (0 : ℝ) ≤ 1 + u := by linarith
  have huexp : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hsq : (Real.exp u) ^ 2 = Real.exp (L - 60) := by
    rw [sq, ← Real.exp_add, hu]; congr 1; ring
  have hexpLm60 : L ≤ Real.exp (L - 60) := by
    have h1 : (1 + u) ^ 2 ≤ (Real.exp u) ^ 2 := pow_le_pow_left₀ hunn huexp 2
    have h2 : L ≤ (1 + u) ^ 2 := by rw [hu]; nlinarith [hu120]
    rw [← hsq]; linarith [h1, h2]
  have hsplit : Real.exp L = Real.exp 60 * Real.exp (L - 60) := by
    rw [← Real.exp_add]; congr 1; ring
  have hLnn : (0 : ℝ) ≤ L := by linarith
  calc 1728 * lemma53KConst * Real.exp 20 * L
      ≤ Real.exp 60 * Real.exp (L - 60) :=
        mul_le_mul hAle hexpLm60 hLnn (Real.exp_pos 60).le
    _ = Real.exp L := hsplit.symm
    _ = (k : ℝ) := hkexp.symm

/-! ## Part F — the item-6 regime discharge -/

/-- **The item-6 regime, discharged.** `32·(lemma53KConst·k₀)·log R ≤ B₁·D₀`.
Combines `B1_ratio_lower` (`B₁ ≥ (φW/W)·log R/(18k₀)`), `D₀ k₀ = k₀³`, the explicit
Mertens `W/φW ≤ exp 20·log D₀ = exp 20·3 log k₀`, and the `k`-largeness fact. -/
theorem regime_discharge (k₀ R : ℕ) (T : ℝ)
    (hk3072 : 3072 ≤ k₀) (hlogk : 300 ≤ Real.log k₀) (hR : 2 ≤ R)
    (hT1 : 1 ≤ T) (hX : 4 ≤ R0 k₀ R T)
    (hbLo : (k₀ : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1))
    (hEB : errB1 k₀ (W k₀)
      ≤ (Nat.totient (W k₀) / W k₀ : ℝ) * (bParam k₀ R)⁻¹ * Real.log k₀ / 18) :
    32 * (lemma53KConst * (k₀ : ℝ)) * Real.log R ≤ B1 k₀ R (W k₀) T * (D₀ k₀ : ℝ) := by
  have hWne : W k₀ ≠ 0 := (W_squarefree k₀).ne_zero
  have hk0R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast (by omega : 0 < k₀)
  have hk0ne : (k₀ : ℝ) ≠ 0 := ne_of_gt hk0R
  have hLkpos : 0 < Real.log k₀ := by linarith
  have hLkne : Real.log k₀ ≠ 0 := ne_of_gt hLkpos
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (by omega : 1 ≤ R)
  have hLRnn : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hWpos : 0 < W k₀ := Nat.pos_of_ne_zero hWne
  have hφWWpos : (0 : ℝ) < (Nat.totient (W k₀) / W k₀ : ℝ) :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
  have hlemnn : 0 ≤ lemma53KConst := lemma53KConst_nonneg
  have hB1nn : 0 ≤ B1 k₀ R (W k₀) T := B1_nonneg k₀ R (W k₀) T hR
  have hD0cube : D₀ k₀ = k₀ ^ 3 := D0_eq_cube k₀ (by omega)
  have hD0_2 : 2 ≤ D₀ k₀ := by
    rw [hD0cube]; exact le_trans (by omega) (Nat.le_self_pow (by norm_num) k₀)
  have hklarge := k_largeness k₀ (by omega) hlogk
  set φWW := (Nat.totient (W k₀) / W k₀ : ℝ) with hφWWdef
  -- B1_ratio_lower, cleared to `φWW·log R ≤ 18·k₀·B₁`
  have hBlo := B1_ratio_lower k₀ R (W k₀) T hWne (by omega) hR hT1 hX hbLo hEB
  rw [bParam_inv] at hBlo
  have hXeq : φWW * (Real.log R / ((k₀ : ℝ) * Real.log k₀)) * Real.log k₀ / 18
      = φWW * Real.log R / (18 * (k₀ : ℝ)) := by
    field_simp
  rw [hXeq] at hBlo
  have f1 : φWW * Real.log R ≤ 18 * (k₀ : ℝ) * B1 k₀ R (W k₀) T := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 18 * (k₀ : ℝ))] at hBlo
    linarith [hBlo]
  -- explicit Mertens, cleared to `1 ≤ 3·exp20·log k₀·φWW`
  have hWφ := W_div_totient_le_explicit k₀ hD0_2
  have hlogD0 : Real.log (D₀ k₀) = 3 * Real.log k₀ := by
    rw [hD0cube, Nat.cast_pow, Real.log_pow]; push_cast; ring
  rw [hlogD0, show (W k₀ : ℝ) / (Nat.totient (W k₀) : ℝ) = φWW⁻¹ from by
    rw [hφWWdef, inv_div]] at hWφ
  have f2 : (1 : ℝ) ≤ 3 * Real.exp 20 * Real.log k₀ * φWW := by
    have hh := mul_le_mul_of_nonneg_left hWφ hφWWpos.le
    rw [mul_inv_cancel₀ hφWWpos.ne'] at hh
    nlinarith [hh]
  -- `log R ≤ 54·exp20·log k₀·k₀·B₁`
  have hLRle : Real.log R
      ≤ 54 * Real.exp 20 * Real.log k₀ * (k₀ : ℝ) * B1 k₀ R (W k₀) T := by
    have hstep1 : Real.log R ≤ Real.log R * (3 * Real.exp 20 * Real.log k₀ * φWW) := by
      nlinarith [f2, hLRnn]
    have hstep3 : Real.log R * (3 * Real.exp 20 * Real.log k₀ * φWW)
        = 3 * Real.exp 20 * Real.log k₀ * (φWW * Real.log R) := by ring
    have hstep4 : 3 * Real.exp 20 * Real.log k₀ * (φWW * Real.log R)
        ≤ 3 * Real.exp 20 * Real.log k₀ * (18 * (k₀ : ℝ) * B1 k₀ R (W k₀) T) :=
      mul_le_mul_of_nonneg_left f1 (by positivity)
    have hstep5 : 3 * Real.exp 20 * Real.log k₀ * (18 * (k₀ : ℝ) * B1 k₀ R (W k₀) T)
        = 54 * Real.exp 20 * Real.log k₀ * (k₀ : ℝ) * B1 k₀ R (W k₀) T := by ring
    linarith [hstep1, hstep3.le, hstep3.ge, hstep4, hstep5.le, hstep5.ge]
  -- assemble
  rw [hD0cube, Nat.cast_pow]
  calc 32 * (lemma53KConst * (k₀ : ℝ)) * Real.log R
      ≤ 32 * (lemma53KConst * (k₀ : ℝ))
          * (54 * Real.exp 20 * Real.log k₀ * (k₀ : ℝ) * B1 k₀ R (W k₀) T) :=
        mul_le_mul_of_nonneg_left hLRle
          (mul_nonneg (by norm_num) (mul_nonneg hlemnn hk0R.le))
    _ = (1728 * lemma53KConst * Real.exp 20 * Real.log k₀)
          * ((k₀ : ℝ) ^ 2 * B1 k₀ R (W k₀) T) := by ring
    _ ≤ (k₀ : ℝ) * ((k₀ : ℝ) ^ 2 * B1 k₀ R (W k₀) T) :=
        mul_le_mul_of_nonneg_right hklarge (mul_nonneg (sq_nonneg _) hB1nn)
    _ = B1 k₀ R (W k₀) T * (k₀ : ℝ) ^ 3 := by ring

/-! ## Part G — the `CompatFrontier` window -/

/-- **`CompatFrontier` holds** for every regime tuple width `k₀` with `3072 ≤ k₀`
and `300 ≤ log k₀`.  Mirrors the `∀ᶠ N'` setup of `analyticFrontier_holds'` and
feeds `hcheb` (`s2_tensor_lower_cheb`), `0 < B₁`, `0 ≤ A₁`, and the discharged
regime (`regime_discharge`) to `s2CompatFormM_ge_sixteenth_K`. -/
theorem compatFrontier_holds (k₀ : ℕ) (hk3072 : 3072 ≤ k₀) (hlogk : 300 ≤ Real.log k₀) :
    CompatFrontier k₀ ((k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀) := by
  classical
  have hk0pos : 0 < k₀ := by omega
  have hlogkpos : (0 : ℝ) < Real.log k₀ := by linarith
  set T := (k₀ : ℝ) ^ ((1 : ℝ) / 8) / Real.log k₀ with hTdef
  have hTpos : (0 : ℝ) < T := by rw [hTdef]; positivity
  have hT1 : 1 ≤ T := T_ge_one hk0pos hlogk
  have hρpos : (0 : ℝ) < T / (k₀ : ℝ) := div_pos hTpos (by exact_mod_cast hk0pos)
  have hTk : 5 * T ≤ (k₀ : ℝ) := by rw [hTdef]; exact five_T_le hk0pos hlogk
  have hWne : W k₀ ≠ 0 := (W_squarefree k₀).ne_zero
  unfold CompatFrontier
  have hcombined := (eventually_rho_logR_ge k₀ T (Real.log 8) hρpos).and
    ((eventually_logR_ge ((k₀ : ℝ) * Real.log k₀ * Real.log 2)).and
    ((eventually_phiW_logR_ge k₀ (100 * (k₀ : ℝ) * errA1 k₀ (W k₀))).and
    ((eventually_phiW_logR_ge k₀ (100 * (k₀ : ℝ) * Real.log k₀ * errB1 k₀ (W k₀))).and
    ((eventually_phiW_logR_ge k₀ (18 * (k₀ : ℝ) * errB1 k₀ (W k₀))).and
    (Filter.eventually_ge_atTop ((2 : ℕ) ^ 30))))))
  filter_upwards [hcombined] with N' hfacts
  obtain ⟨hρR, hlogRbig, hthrEAc, hthrEBc, hthrEBr, hgeB⟩ := hfacts
  intro m
  set R := ⌊(N' : ℝ) ^ ((1 : ℝ) / 5)⌋₊ with hRdef
  have hN'r2 : (2 : ℝ) ^ 30 ≤ (N' : ℝ) := by exact_mod_cast hgeB
  have h32 : (32 : ℝ) ≤ (N' : ℝ) := by
    have : (32 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
    linarith
  have hR : 2 ≤ R := R_ge_two N' h32
  have hX : 4 ≤ R0 k₀ R T := R0_ge_four k₀ R T hR hρR
  have hblog2 : bParam k₀ R * Real.log 2 ≤ 1 := bParam_log2_le k₀ R (by omega) hR hlogRbig
  have hbLo : (k₀ : ℝ) ^ ((1 : ℝ) / 9) ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1) :=
    hbLo_of k₀ R T hk3072 hR hlogk hTdef hρR hblog2
  have hb4 : 4 ≤ bParam k₀ R * Real.log ((R0 k₀ R T : ℝ) - 1) :=
    hb4_of k₀ R T hlogk hk0pos hbLo
  have hEAc := hEA_cheb_of k₀ R (by omega) hR hthrEAc
  have hEBc := hEB_cheb_of k₀ R (by omega) hR hthrEBc
  have hEBr := hEB_ratio_of k₀ R (by omega) hR hthrEBr
  have hB1nn : 0 ≤ B1 k₀ R (W k₀) T := B1_nonneg k₀ R (W k₀) T hR
  have hA1nn : 0 ≤ A1 k₀ R (W k₀) T := A1_nonneg k₀ R (W k₀) T
  -- `0 < B₁` from `B1_ratio_lower`'s strictly-positive lower bound
  have hBlo := B1_ratio_lower k₀ R (W k₀) T hWne (by omega) hR hT1 hX hbLo hEBr
  have hB1pos : 0 < B1 k₀ R (W k₀) T := by
    have hbppos : 0 < bParam k₀ R := bParam_pos (by omega) hR
    have hWpos : 0 < W k₀ := Nat.pos_of_ne_zero hWne
    have hφWWpos : (0 : ℝ) < (Nat.totient (W k₀) / W k₀ : ℝ) :=
      div_pos (by exact_mod_cast Nat.totient_pos.mpr hWpos) (by exact_mod_cast hWpos)
    have hpos : (0 : ℝ) < (Nat.totient (W k₀) / W k₀ : ℝ) * (bParam k₀ R)⁻¹ * Real.log k₀ / 18 := by
      apply div_pos
      · exact mul_pos (mul_pos hφWWpos (inv_pos.mpr hbppos)) hlogkpos
      · norm_num
    linarith [hBlo, hpos]
  have hcheb := s2_tensor_lower_cheb k₀ R m T (by omega) hR hTk hTdef hT1 hX hlogk hb4
    hEAc hEBc hB1nn
  have hreg := regime_discharge k₀ R T hk3072 hlogk hR hT1 hX hbLo hEBr
  exact s2CompatFormM_ge_sixteenth_K k₀ R T m hR hk3072 (le_max_left _ _) hB1pos hA1nn hcheb hreg

/-! ## Part H — the unconditional capstone -/

/-- **The Maynard capstone.** `bounded_gaps_from_eh_complete : BoundedGapsFromEH`,
unconditional (no residual hypotheses): `bounded_gaps_from_eh_final` fed with the
now-proved `CompatFrontier` atom for every regime tuple width. -/
theorem bounded_gaps_from_eh_complete : BoundedGapsFromEH :=
  bounded_gaps_from_eh_final (fun k₀ hk hlogk => compatFrontier_holds k₀ hk hlogk)

end Salt.Maynard
