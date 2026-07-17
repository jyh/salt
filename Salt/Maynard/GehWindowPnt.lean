/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.TripleCount
import Salt.Twelve.Params

/-!
# Discharging `WindowPNT` from the corpus PNT-with-rate (GEH-REV-R0)

`WindowPNT` (`Salt/Twelve/Params.lean`) asserts that the long window `(N, 64N]`
eventually holds `(63 − ε)·N/log N` primes:

  `∀ ε > 0, ∀ᶠ N, (63 − ε)·N/log N ≤ π(64N) − π(N)`.

It was stated as an interface "because mathlib has no PNT".  That premise is now
stale: the corpus carries unconditional PNT-with-rate through the SW gate,
`Salt.Chen.psiTot_pnt : ∃ K ≥ 0, ∀ x ≥ 3, |ψ(x) − x| ≤ K·x/log x`.  This module
discharges `WindowPNT` from that carrier alone, so the GEH door's analytic input
list drops `WindowPNT` (feed `windowPNT_holds`).

Route (the D3 `WindowMertensLower` ψ→θ→prime-count strip, run for a lower bound):

* `count · log(64N) ≥ θ-mass of the window primes` — each prime `p ≤ 64N` has
  `log p ≤ log(64N)`;
* `θ-mass = ψ-window − (non-prime Λ-mass)`, and the non-prime mass is bounded by
  `ψ(64N) − θ(64N) ≤ C·√(64N)` (mathlib `Chebyshev.psi_sub_theta_le_mul_sqrt`);
* `ψ-window = ψ(64N) − ψ(N) ≥ 63N − K·64N/log(64N) − K·N/log N` (`psiTot_pnt`).

Thus `count · log(64N) ≥ 63N − K·64N/log(64N) − K·N/log N − C·√(64N)`, and
dividing by `log(64N)`, the normalised lower bound `count·log N/N` tends to `63`
(the constant `63` survives because `log N/log(64N) → 1`, not a lossy factor), so
`count ≥ (63 − ε)·N/log N` eventually.  No `sorry`, no `native_decide`, no axioms.
-/

open Filter Topology

namespace Salt.Maynard

/-- `√(64N)/N → 0`: the prime-power strip term `C·√(64N)`, once normalised by the
window length `N`, is negligible. -/
private theorem windowPNT_sqrt_div :
    Tendsto (fun N : ℕ => Real.sqrt (64 * (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
  have hsqrt_inf : Tendsto (fun N : ℕ => Real.sqrt (64 * (N : ℝ))) atTop atTop := by
    have h64 : Tendsto (fun N : ℕ => 64 * (N : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    have hs : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
      have he : (fun x : ℝ => Real.sqrt x) = (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
        funext x; rw [Real.sqrt_eq_rpow]
      rw [he]; exact tendsto_rpow_atTop (by norm_num)
    exact hs.comp h64
  have hb : Tendsto (fun N : ℕ => 64 * (Real.sqrt (64 * (N : ℝ)))⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hsqrt_inf.inv_tendsto_atTop
  refine hb.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs0 : (0 : ℝ) ≤ 64 * (N : ℝ) := by positivity
  have hspos : (0 : ℝ) < Real.sqrt (64 * (N : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (64 * (N : ℝ)) * Real.sqrt (64 * (N : ℝ)) = 64 * (N : ℝ) :=
    Real.mul_self_sqrt hs0
  rw [inv_eq_one_div, mul_one_div, div_eq_div_iff (ne_of_gt hspos) (ne_of_gt hNpos), hsq]

/-- `log N / log(64N) → 1`: the window ratio.  The constant `63` in `WindowPNT`
survives precisely because this factor tends to `1` (not to `1/2`). -/
private theorem windowPNT_logratio :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.log (64 * (N : ℝ))) atTop (𝓝 1) := by
  have hlogN : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz0 : Tendsto (fun N : ℕ => (-Real.log 64) / (Real.log 64 + Real.log (N : ℝ)))
      atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds (tendsto_atTop_add_const_left _ (Real.log 64) hlogN)
  have hsum : Tendsto (fun N : ℕ => 1 + (-Real.log 64) / (Real.log 64 + Real.log (N : ℝ)))
      atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hz0
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h64N : Real.log (64 * (N : ℝ)) = Real.log 64 + Real.log (N : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hNpos)
  have h64pos : (0 : ℝ) < Real.log 64 := Real.log_pos (by norm_num)
  have hNnn : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hden : Real.log 64 + Real.log (N : ℝ) ≠ 0 := by positivity
  rw [h64N]
  field_simp
  ring

/-- **The discharge.**  The corpus PNT-with-rate `Salt.Chen.psiTot_pnt` proves the
long-window hypothesis `WindowPNT` unconditionally. -/
theorem windowPNT_holds : WindowPNT := by
  obtain ⟨K, hK0, hK⟩ := Salt.Chen.psiTot_pnt
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  -- `π m` as a filtered card, once and for all.
  have hpc : ∀ m : ℕ,
      Nat.primeCounting m = ((Finset.range (m + 1)).filter (fun n => n.Prime)).card := by
    intro m
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    unfold Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
  -- the auxiliary limits, assembled into `E(N) → 63`
  have hlog64_inf : Tendsto (fun N : ℕ => Real.log (64 * (N : ℝ))) atTop atTop := by
    have h64 : Tendsto (fun N : ℕ => 64 * (N : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp h64
  have hlogN_inf : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have t1 : Tendsto (fun N : ℕ => K * 64 / Real.log (64 * (N : ℝ))) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlog64_inf
  have t2 : Tendsto (fun N : ℕ => K / Real.log (N : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlogN_inf
  have t3 : Tendsto (fun N : ℕ => C * Real.sqrt (64 * (N : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
    have h := windowPNT_sqrt_div.const_mul C
    simpa [mul_div_assoc] using h
  have hfac : Tendsto (fun N : ℕ =>
      63 - K * 64 / Real.log (64 * (N : ℝ)) - K / Real.log (N : ℝ)
        - C * Real.sqrt (64 * (N : ℝ)) / (N : ℝ)) atTop (𝓝 63) := by
    have h := (((tendsto_const_nhds (x := (63 : ℝ))).sub t1).sub t2).sub t3
    simpa using h
  have hE : Tendsto (fun N : ℕ =>
      (63 - K * 64 / Real.log (64 * (N : ℝ)) - K / Real.log (N : ℝ)
        - C * Real.sqrt (64 * (N : ℝ)) / (N : ℝ))
        * (Real.log (N : ℝ) / Real.log (64 * (N : ℝ)))) atTop (𝓝 63) := by
    have h := hfac.mul windowPNT_logratio
    simpa using h
  -- peel `ε`
  intro ε hε
  filter_upwards [hE.eventually_const_le (show (63 : ℝ) - ε < 63 by linarith),
    eventually_ge_atTop 64] with N hEn hN64
  -- positivity scaffold
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hN64R : (64 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN64
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hM1 : (1 : ℝ) < 64 * (N : ℝ) := by nlinarith
  have hL64 : 0 < Real.log (64 * (N : ℝ)) := Real.log_pos hM1
  have hNe : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hLe : Real.log (N : ℝ) ≠ 0 := ne_of_gt hL
  have hL64e : Real.log (64 * (N : ℝ)) ≠ 0 := ne_of_gt hL64
  have hN3 : 3 ≤ N := by omega
  have hM3 : 3 ≤ 64 * N := by omega
  have hcast : ((64 * N : ℕ) : ℝ) = 64 * (N : ℝ) := by push_cast; ring
  -- ψ-window lower bound from `psiTot_pnt`
  have hpsiM := abs_le.mp (hK (64 * N) hM3)
  rw [hcast] at hpsiM
  have hpsiN := abs_le.mp (hK N hN3)
  have hPlo : 63 * (N : ℝ) - K * (64 * (N : ℝ)) / Real.log (64 * (N : ℝ))
        - K * (N : ℝ) / Real.log (N : ℝ)
      ≤ Salt.LS.psiTot (64 * N) - Salt.LS.psiTot N := by
    linarith [hpsiM.1, hpsiN.2]
  -- prime-power strip: non-prime window mass `≤ C·√(64N)`
  have hjunk : ∑ n ∈ (Finset.Ioc N (64 * N)).filter (fun n => ¬ n.Prime),
        ArithmeticFunction.vonMangoldt n ≤ C * Real.sqrt (64 * (N : ℝ)) := by
    have hsubJ : (Finset.Ioc N (64 * N)).filter (fun n => ¬ n.Prime)
        ⊆ (Finset.Ioc 0 (64 * N)).filter (fun n => ¬ n.Prime) :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc (Nat.zero_le _) (le_refl _))
    have hfloor : ⌊(64 * (N : ℝ))⌋₊ = 64 * N := by
      rw [show (64 * (N : ℝ)) = ((64 * N : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
    calc ∑ n ∈ (Finset.Ioc N (64 * N)).filter (fun n => ¬ n.Prime),
            ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ (Finset.Ioc 0 (64 * N)).filter (fun n => ¬ n.Prime),
            ArithmeticFunction.vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubJ
            (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi (64 * (N : ℝ)) - Chebyshev.theta (64 * (N : ℝ)) := by
          rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, hfloor]
      _ ≤ C * Real.sqrt (64 * (N : ℝ)) := hC (64 * (N : ℝ))
  -- ψ-window as a window Λ-sum, split prime / non-prime
  have hdiff : Salt.LS.psiTot (64 * N) - Salt.LS.psiTot N
      = ∑ n ∈ Finset.Ioc N (64 * N), ArithmeticFunction.vonMangoldt n := by
    have hun : Finset.Icc 1 (64 * N) = Finset.Icc 1 N ∪ Finset.Ioc N (64 * N) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
    have hdis : Disjoint (Finset.Icc 1 N) (Finset.Ioc N (64 * N)) := by
      rw [Finset.disjoint_left]; intro a
      simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have h : Salt.LS.psiTot (64 * N)
        = Salt.LS.psiTot N + ∑ n ∈ Finset.Ioc N (64 * N), ArithmeticFunction.vonMangoldt n := by
      unfold Salt.LS.psiTot
      rw [hun, Finset.sum_union hdis]
    linarith [h]
  have hsplit : ∑ n ∈ Finset.Ioc N (64 * N), ArithmeticFunction.vonMangoldt n
      = (∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime),
            ArithmeticFunction.vonMangoldt p)
        + (∑ n ∈ (Finset.Ioc N (64 * N)).filter (fun n => ¬ n.Prime),
            ArithmeticFunction.vonMangoldt n) :=
    (Finset.sum_filter_add_sum_filter_not (Finset.Ioc N (64 * N)) (fun n => n.Prime)
      (fun n => ArithmeticFunction.vonMangoldt n)).symm
  have hlogform : ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime), Real.log (p : ℝ)
      = ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime),
          ArithmeticFunction.vonMangoldt p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2]
  -- each window prime contributes `log p ≤ log(64N)`
  have hthetaW : ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime), Real.log (p : ℝ)
      ≤ (((Finset.Ioc N (64 * N)).filter (fun n => n.Prime)).card : ℝ)
          * Real.log (64 * (N : ℝ)) := by
    have hle : ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime), Real.log (p : ℝ)
        ≤ ∑ _p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime),
            Real.log (64 * (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      obtain ⟨⟨_, hpM⟩, hpp⟩ := hp
      apply Real.log_le_log (by exact_mod_cast hpp.pos)
      exact_mod_cast hpM
    rwa [Finset.sum_const, nsmul_eq_mul] at hle
  -- count identity `π(64N) − π(N) = #window primes`
  have hπR : (↑(Nat.primeCounting (64 * N)) : ℝ) - ↑(Nat.primeCounting N)
      = (((Finset.Ioc N (64 * N)).filter (fun n => n.Prime)).card : ℝ) := by
    have hcardnat : Nat.primeCounting (64 * N)
        = Nat.primeCounting N
          + ((Finset.Ioc N (64 * N)).filter (fun n => n.Prime)).card := by
      have hun : Finset.range (64 * N + 1)
          = Finset.range (N + 1) ∪ Finset.Ioc N (64 * N) := by
        ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]; omega
      have hdis : Disjoint (Finset.range (N + 1)) (Finset.Ioc N (64 * N)) := by
        rw [Finset.disjoint_left]; intro a
        simp only [Finset.mem_range, Finset.mem_Ioc]; omega
      rw [hpc (64 * N), hpc N, hun, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdis)]
    rw [hcardnat]; push_cast; ring
  -- MAIN: `count · log(64N) ≥ 63N − K·64N/log(64N) − K·N/log N − C·√(64N)`
  have hWmass : 63 * (N : ℝ) - K * (64 * (N : ℝ)) / Real.log (64 * (N : ℝ))
        - K * (N : ℝ) / Real.log (N : ℝ) - C * Real.sqrt (64 * (N : ℝ))
      ≤ ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime),
          ArithmeticFunction.vonMangoldt p := by
    linarith [hsplit, hdiff, hjunk, hPlo]
  have hMAIN : 63 * (N : ℝ) - K * (64 * (N : ℝ)) / Real.log (64 * (N : ℝ))
        - K * (N : ℝ) / Real.log (N : ℝ) - C * Real.sqrt (64 * (N : ℝ))
      ≤ ((↑(Nat.primeCounting (64 * N)) : ℝ) - ↑(Nat.primeCounting N))
          * Real.log (64 * (N : ℝ)) := by
    rw [hπR]
    calc 63 * (N : ℝ) - K * (64 * (N : ℝ)) / Real.log (64 * (N : ℝ))
            - K * (N : ℝ) / Real.log (N : ℝ) - C * Real.sqrt (64 * (N : ℝ))
        ≤ ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime),
            ArithmeticFunction.vonMangoldt p := hWmass
      _ = ∑ p ∈ (Finset.Ioc N (64 * N)).filter (fun n => n.Prime), Real.log (p : ℝ) :=
          hlogform.symm
      _ ≤ (((Finset.Ioc N (64 * N)).filter (fun n => n.Prime)).card : ℝ)
            * Real.log (64 * (N : ℝ)) := hthetaW
  -- convert MAIN + the `E → 63` limit into the target bound
  have hNL64 : (0 : ℝ) < (N : ℝ) * Real.log (64 * (N : ℝ)) := mul_pos hNpos hL64
  have hEeq : (63 - K * 64 / Real.log (64 * (N : ℝ)) - K / Real.log (N : ℝ)
        - C * Real.sqrt (64 * (N : ℝ)) / (N : ℝ))
        * (Real.log (N : ℝ) / Real.log (64 * (N : ℝ)))
      = (63 * (N : ℝ) - K * (64 * (N : ℝ)) / Real.log (64 * (N : ℝ))
          - K * (N : ℝ) / Real.log (N : ℝ) - C * Real.sqrt (64 * (N : ℝ)))
        * Real.log (N : ℝ) / ((N : ℝ) * Real.log (64 * (N : ℝ))) := by
    field_simp
  rw [hEeq, le_div_iff₀ hNL64] at hEn
  have hfrac : (63 - ε) * (N : ℝ) / Real.log (N : ℝ)
      ≤ (63 * (N : ℝ) - K * (64 * (N : ℝ)) / Real.log (64 * (N : ℝ))
          - K * (N : ℝ) / Real.log (N : ℝ) - C * Real.sqrt (64 * (N : ℝ)))
        / Real.log (64 * (N : ℝ)) := by
    rw [div_le_div_iff₀ hL hL64]
    have hassoc : (63 - ε) * (N : ℝ) * Real.log (64 * (N : ℝ))
        = (63 - ε) * ((N : ℝ) * Real.log (64 * (N : ℝ))) := by ring
    linarith [hEn, hassoc]
  exact le_trans hfrac ((div_le_iff₀ hL64).mpr hMAIN)

end Salt.Maynard
