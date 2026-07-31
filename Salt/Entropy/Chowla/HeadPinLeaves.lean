/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# ⟦THE PRICED LEAVES⟧ — the three head constants, CITABLE FROM BELOW (node EPSPIN)

`log_chowla_two_budget_head_g_sq_count_hloCap` (`HloExport.lean:389`) chooses its
`ε` by `exists_rat_btwn` under a four-arm `min` built from three `∃`-delivered
leaf constants, and emits `δ₀ = cD3/(16·C)·ε/4`.  Every one of those leaves is
destructed by `obtain`, i.e. is a `Classical.choose` the kernel cannot evaluate —
so the head's `δ₀` is UNBOUNDED BELOW as stated, and the register witness on the
capstone side can only be checked at closed-form stand-ins (the reachability
caveat of `Salt/MR/ConstantsExposed.lean`).

This file mints the ADDITIVE TWINS that close the gap at the leaves.  Each
declaration is a landed statement plus ONE conjunct pinning the landed `refine`
witness, with the landed body replayed verbatim underneath:

| twin | landed | conjunct |
|---|---|---|
| `primeWindow_sum_inv_ge_bounded` | `WindowMertensLower.lean:56` | `1/4 ≤ c` |
| `hbudget_holds_bounded` | `HBudget.lean:448` | `1/4 ≤ c` (carry) |
| `hreduce_holds_final_bounded` | `HBudget.lean:705` | `1/4 ≤ c` (carry) |
| `circle_method_estimate_sq_bounded` | `CircleMethod.lean:795` | `C ≤ 1 + 2·C₀` |

Nothing landed is touched; the two carries are the landed proofs reading the
previous twin (the `c` of `hbudget_holds`/`hreduce_holds_final` IS D3's `c`,
passed through unchanged — `HBudget.lean:462`, `HBudget.lean:721`).

⟦WHY THE BODIES ARE REPLAYED⟧  All four statements are `∃`-shaped and the
constant occurs ANTITONICALLY in each (a smaller `c`, a larger `C`, weakens the
statement), so no consequence of the landed form can recover the witness's value:
the only route is to re-run the landed proof with the numeral kept.  The replays
cite `private` helpers of their home files (`window_Z_pos`, `absX_le_one`,
`window_sum_inv_sq`, `IF_unfold`, `per_term`, `boundary_card_le` from `HBudget`;
`windowVal_c_norm_le`, `T_collapse`, `periodization_total` from `CircleMethod`),
reached here by `open private … from … in` — no landed file gains a declaration.

⟦WHAT THEY BUY⟧  `1/4 ≤ cD3` and `C ≤ 1 + 2·C₀ = CcmExpr ≤ 6.55` make all four
`ε`-arms citable at the numeral `ε = 1/500` (`ConstantsExposed.eps_admissible`),
and `1/4 ≤ cE` (the `hreduce` carry — the SAME leaf, D3's constant) covers the
one arm that is not a `cD3` arm.  Downstream: `HloExport.lean` §4.
-/
import Salt.Entropy.Chowla.HBudget
import Salt.Entropy.Chowla.CircleMethod
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open ArithmeticFunction

namespace Salt.Entropy.Chowla

/-! ## §1 The Mertens leaf, with its `1/4` kept -/

/-- **THE `D3` LEAF, PINNED** (`primeWindow_sum_inv_ge_bounded`) —
`WindowMertensLower.primeWindow_sum_inv_ge` plus the conjunct `1/4 ≤ c`, at the
landed `refine` witness `c = 1/4`.  The body is the landed one verbatim
(`WindowMertensLower.lean:63–245`); the only edit is the extra `le_rfl` in the
`refine`. -/
theorem primeWindow_sum_inv_ge_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H : ℕ), H₀ ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      c / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := Salt.Chen.lambda_mass_lower
  refine ⟨1 / 4, by norm_num, le_rfl, max (96 ^ 8) (⌈Real.exp (64 * K)⌉₊ + 1), ?_⟩
  intro eps H hH0 hreg heps1
  set N := ⌊eps ^ 2 * (H : ℚ)⌋₊ with hNdef
  -- H-side size facts
  have hH96 : (96 : ℝ) ^ 8 ≤ (H : ℝ) := by
    have h1 : 96 ^ 8 ≤ H := le_trans (le_max_left _ _) hH0
    exact_mod_cast h1
  have hHexp : Real.exp (64 * K) < (H : ℝ) := by
    have h1 : ⌈Real.exp (64 * K)⌉₊ + 1 ≤ H := le_trans (le_max_right _ _) hH0
    have h2 : (⌈Real.exp (64 * K)⌉₊ : ℝ) + 1 ≤ (H : ℝ) := by exact_mod_cast h1
    have h3 : Real.exp (64 * K) ≤ (⌈Real.exp (64 * K)⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  have hH1 : (1 : ℝ) < (H : ℝ) := lt_of_lt_of_le (by norm_num) hH96
  have hH0R : (0 : ℝ) ≤ (H : ℝ) := by positivity
  have hlogH_pos : 0 < Real.log (H : ℝ) := Real.log_pos hH1
  have hsqrtH1 : (1 : ℝ) ≤ Real.sqrt (H : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (le_of_lt hH1)
  -- N-side size facts
  have hfloorQ : eps ^ 2 * (H : ℚ) < (N : ℚ) + 1 := by
    rw [hNdef]; exact Nat.lt_floor_add_one _
  have hfloorR : (eps : ℝ) ^ 2 * (H : ℝ) < (N : ℝ) + 1 := by exact_mod_cast hfloorQ
  have hsqrtN : Real.sqrt (H : ℝ) ≤ (N : ℝ) := by linarith
  have hN96 : (96 : ℝ) ^ 4 ≤ (N : ℝ) := by
    have hsq : Real.sqrt ((96 : ℝ) ^ 8) = (96 : ℝ) ^ 4 := by
      rw [show ((96 : ℝ) ^ 8) = ((96 : ℝ) ^ 4) ^ 2 by ring]
      exact Real.sqrt_sq (by positivity)
    have h1 := Real.sqrt_le_sqrt hH96
    rw [hsq] at h1
    linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN96
  have hN1 : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le (by norm_num) hN96
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hN8 : 8 ≤ N := by
    have h1 : (8 : ℝ) ≤ (N : ℝ) := le_trans (by norm_num) hN96
    exact_mod_cast h1
  -- `N ≤ H` (this is where `ε² ≤ 1` enters)
  have heps1Q : eps ^ 2 ≤ (1 : ℚ) := by exact_mod_cast heps1
  have hNleH : N ≤ H := by
    rw [hNdef]
    have hq : eps ^ 2 * (H : ℚ) ≤ (H : ℚ) :=
      mul_le_of_le_one_left (by positivity) heps1Q
    have h2 := Nat.floor_le_floor hq
    rwa [Nat.floor_natCast] at h2
  have hNHR : (N : ℝ) ≤ (H : ℝ) := by exact_mod_cast hNleH
  have hlogNH : Real.log (N : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log hN_pos hNHR
  -- `log N ≥ 32K` (from `H > exp(64K)` through `log N ≥ (1/2) log H`)
  have hlogN32K : 32 * K ≤ Real.log (N : ℝ) := by
    have h64 : 64 * K < Real.log (H : ℝ) := by
      have h1 := Real.log_lt_log (Real.exp_pos _) hHexp
      rwa [Real.log_exp] at h1
    have hhalf : Real.log (H : ℝ) / 2 ≤ Real.log (N : ℝ) := by
      have h1 : Real.log (Real.sqrt (H : ℝ)) ≤ Real.log (N : ℝ) :=
        Real.log_le_log (lt_of_lt_of_le one_pos hsqrtH1) hsqrtN
      rwa [Real.log_sqrt hH0R] at h1
    linarith
  -- the `t = N^(1/4)` budget machinery
  set t : ℝ := (N : ℝ) ^ ((1 : ℝ) / 4) with htdef
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hN_pos _
  have ht4 : t ^ (4 : ℕ) = (N : ℝ) := by
    rw [htdef, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hN_pos.le]
    norm_num
  have ht2 : t ^ (2 : ℕ) = Real.sqrt (N : ℝ) := by
    rw [htdef, ← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hN_pos.le,
      Real.sqrt_eq_rpow]
    norm_num
  have ht96 : (96 : ℝ) ≤ t := by
    have h1 : ((96 : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hN96 (by norm_num)
    rwa [← Real.rpow_natCast (96 : ℝ) 4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 96),
      show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num, Real.rpow_one, ← htdef] at h1
  have hlogt : Real.log (N : ℝ) ≤ 4 * t := by
    have h2 : Real.log (N : ℝ) = 4 * Real.log t := by
      rw [← ht4, Real.log_pow]
      push_cast
      ring
    have h3 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht_pos
    linarith
  -- the three budget pieces: `1 + 2KN/log N + (log N + 2√N·log N) ≤ N/16 + N/16 + N/8 = N/4`
  have hb1 : (1 : ℝ) ≤ (N : ℝ) / 16 := by
    have h16 : (16 : ℝ) ≤ (96 : ℝ) ^ 4 := by norm_num
    linarith
  have hb2 : 2 * K * (N : ℝ) / Real.log (N : ℝ) ≤ (N : ℝ) / 16 := by
    rw [div_le_div_iff₀ hlogN_pos (by norm_num : (0 : ℝ) < 16)]
    have h1 := mul_le_mul_of_nonneg_left hlogN32K hN_pos.le
    nlinarith
  have hb3 : Real.log (N : ℝ) + 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ (N : ℝ) / 8 := by
    have e1 : 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ≤ 8 * t ^ 3 := by
      have h1 : 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)
          ≤ 2 * Real.sqrt (N : ℝ) * (4 * t) :=
        mul_le_mul_of_nonneg_left hlogt (by positivity)
      have h2 : 2 * Real.sqrt (N : ℝ) * (4 * t) = 8 * t ^ 3 := by
        rw [← ht2]; ring
      linarith
    have e2 : 4 * t + 8 * t ^ 3 ≤ t ^ 4 / 8 := by
      have hC : 0 ≤ (t - 96) * t ^ 3 := mul_nonneg (by linarith) (pow_pos ht_pos 3).le
      have hA : 0 ≤ (t - 1) * t := mul_nonneg (by linarith) ht_pos.le
      have hB : 0 ≤ (t - 1) * t * t := mul_nonneg hA ht_pos.le
      nlinarith [hA, hB, hC]
    linarith [hlogt, e1, e2, ht4]
  -- the Λ-mass over the twin window, boundary point split off
  have hmass0 := hK N hN8
  have htw : Salt.Chen.twinWindow N = Finset.Icc (N / 2) (N - 2) := rfl
  have hIcc : Finset.Icc (N / 2) (N - 2) = insert (N / 2) (Finset.Ioc (N / 2) (N - 2)) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hnm : N / 2 ∉ Finset.Ioc (N / 2) (N - 2) := by simp
  rw [htw, hIcc, Finset.sum_insert hnm] at hmass0
  have hbdry : vonMangoldt (N / 2) ≤ Real.log (N : ℝ) := by
    calc vonMangoldt (N / 2) ≤ Real.log ((N / 2 : ℕ) : ℝ) :=
          ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (N : ℝ) := by
          have hpos : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by
            have h1 : 0 < N / 2 := by omega
            exact_mod_cast h1
          exact Real.log_le_log hpos (by exact_mod_cast Nat.div_le_self N 2)
  -- prime / non-prime split over the `Ioc`
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc (N / 2) (N - 2)) (fun n => n.Prime) (fun n => vonMangoldt n)
  -- the prime-power junk: `≤ ψ(N) − θ(N) ≤ 2√N·log N`
  have hjunk : ∑ n ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => ¬n.Prime), vonMangoldt n
      ≤ 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    have hsubJ : (Finset.Ioc (N / 2) (N - 2)).filter (fun n => ¬n.Prime)
        ⊆ (Finset.Ioc 0 N).filter (fun n => ¬n.Prime) :=
      Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc (Nat.zero_le _) (by omega))
    calc ∑ n ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => ¬n.Prime), vonMangoldt n
        ≤ ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬n.Prime), vonMangoldt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubJ
            (fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi (N : ℝ) - Chebyshev.theta (N : ℝ) := by
          rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      _ ≤ 2 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) :=
          Chebyshev.psi_sub_theta_le (by linarith)
  -- the θ-mass of the window primes: `≥ N/4`
  have hquarter : (N : ℝ) / 4
      ≤ ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), Real.log (p : ℝ) := by
    have hlogform :
        ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), Real.log (p : ℝ)
          = ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), vonMangoldt p :=
      Finset.sum_congr rfl (fun p hp =>
        (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm)
    rw [hlogform]
    linarith [hmass0, hbdry, hjunk, hsplit, hb1, hb2, hb3]
  -- the window primes live in `primeWindow eps H`
  have hsub2 : (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime) ⊆ primeWindow eps H := by
    intro p hp
    obtain ⟨hmem, hpp⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_Ioc] at hmem
    rw [mem_primeWindow, ← hNdef]
    refine ⟨by omega, hpp, ?_⟩
    have h2p : (N : ℚ) + 1 ≤ 2 * (p : ℚ) := by exact_mod_cast (by omega : N + 1 ≤ 2 * p)
    linarith [hfloorQ]
  -- per-prime flip: `1/p ≥ log p / (N log N)`
  have hden_pos : 0 < (N : ℝ) * Real.log (N : ℝ) := mul_pos hN_pos hlogN_pos
  have hstep : ∀ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime),
      Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) ≤ 1 / (p : ℝ) := by
    intro p hp
    obtain ⟨hmem, hpp⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_Ioc] at hmem
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hpN : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : p ≤ N)
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hlogpN : Real.log (p : ℝ) ≤ Real.log (N : ℝ) := Real.log_le_log hp_pos hpN
    rw [div_le_div_iff₀ hden_pos hp_pos]
    nlinarith [mul_le_mul hpN hlogpN hlogp_nn hN_pos.le]
  -- assemble
  calc (1 / 4 : ℝ) / Real.log (H : ℝ)
      = 1 / (4 * Real.log (H : ℝ)) := by rw [div_div]
    _ ≤ 1 / (4 * Real.log (N : ℝ)) := by
        apply one_div_le_one_div_of_le
        · linarith
        · linarith
    _ ≤ (∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), Real.log (p : ℝ))
          / ((N : ℝ) * Real.log (N : ℝ)) := by
        rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < 4 * Real.log (N : ℝ)) hden_pos]
        nlinarith [mul_le_mul_of_nonneg_right hquarter hlogN_pos.le]
    _ = ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime),
          Real.log (p : ℝ) / ((N : ℝ) * Real.log (N : ℝ)) := by
        rw [Finset.sum_div]
    _ ≤ ∑ p ∈ (Finset.Ioc (N / 2) (N - 2)).filter (fun n => n.Prime), 1 / (p : ℝ) :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ p ∈ primeWindow eps H, 1 / (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p _ _ => by positivity)

/-! ## §2 The budget carry -/

set_option maxHeartbeats 1600000 in
-- The replayed budget aggregation (∫F unfold + three window totals + double-sum
-- reduction) is a large single elaboration, as at the landed `HBudget.lean:440`;
-- the ceiling here is that declaration's, unchanged.
open private window_Z_pos absX_le_one window_sum_inv_sq IF_unfold per_term boundary_card_le from
  Salt.Entropy.Chowla.HBudget in
/-- **HBUDGET, PINNED** (`hbudget_holds_bounded`) — `HBudget.hbudget_holds` plus
`1/4 ≤ c`.  A pure carry: the landed proof reads §1 in place of
`primeWindow_sum_inv_ge` and re-emits the conjunct (`HBudget.lean:462–463`); the
rest of the body is `HBudget.lean:464–699` verbatim. -/
theorem hbudget_holds_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      |(∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
          - (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
              (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))|
        ≤ (1 / 4) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
  obtain ⟨c, hc, hcge, H₀, hD3⟩ := primeWindow_sum_inv_ge_bounded
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig
  -- abbreviations kept raw (they interface with the window lemmas via linarith)
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hZpos : 0 < ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := window_Z_pos hx hω
  have hZlb : Real.log ω - 1 ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ :=
    (harmonic_window_bounds hx hω hωx).1
  have hlogH0 : (0 : ℝ) < Real.log H := by linarith
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hε2H0 : (0 : ℝ) < (eps : ℝ) ^ 2 * (H : ℝ) := by linarith
  have hSP_lb : c / Real.log H ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    hD3 eps H hH0 hsqrt hepssq
  have hSPpos : (0 : ℝ) < ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) :=
    lt_of_lt_of_le (by positivity) hSP_lb
  have habsX : |∫ n, (ArithmeticFunction.liouville n : ℝ)
      * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| ≤ 1 := absX_le_one hx hω
  have hcard : ((primeWindow eps H).card : ℝ)
      ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) :=
    primeWindow_card_le_of_regime eps H hsqrt hH3
  have hxωH : H ≤ x / ω := by
    have hpos : (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) := by positivity
    have h2 : ω * H ≤ x := by
      have : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by linarith
      exact_mod_cast this
    rw [Nat.le_div_iff_mul_le (by omega : 0 < ω), Nat.mul_comm]; exact h2
  have hωR : (0 : ℝ) < (ω : ℝ) := by exact_mod_cast (by omega : 0 < ω)
  have hε_le1 : (eps : ℝ) ≤ 1 := by nlinarith [hepssq, hepsR]
  have hlogε2H : (0 : ℝ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) := Real.log_nonneg (by linarith)
  have hple : ∀ p ∈ primeWindow eps H, (p : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) := by
    intro p hp
    have h3 : (p : ℚ) ≤ eps ^ 2 * (H : ℚ) :=
      le_trans (by exact_mod_cast (mem_primeWindow.mp hp).1) (Nat.floor_le (by positivity))
    exact_mod_cast h3
  have hZbig' : 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64
      ≤ (eps : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    have h2 : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ)
        ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hepsR.le
    have hlhs : (eps : ℝ) * ((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ))
        = 16 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 := by field_simp
    rw [hlhs] at h3; exact h3
  have hZ1 : (1 : ℝ) ≤ ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    nlinarith [hZbig', hlogε2H, hε_le1, hZpos, mul_le_mul_of_nonneg_right hε_le1 hZpos.le]
  -- === total 1: the Z-controlled (collapse+swap) slice ≤ (1/8)·SP·H·ε ===
  have hZεbound : (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
      / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) ≤ (eps : ℝ) / 8 := by
    rw [div_le_div_iff₀ hZpos (by norm_num)]
    nlinarith [hZbig']
  have hT1 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
        * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have hstep : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
          * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      have hle : ∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          ≤ ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpR : (0 : ℝ) < ((p : ℕ) : ℝ) := by
          exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < (p : ℕ))
        have hlogle : Real.log (p : ℕ) ≤ Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) :=
          Real.log_le_log hpR (hple p hp)
        gcongr
      have heq : ∑ p ∈ primeWindow eps H, (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
            / (((p : ℕ) : ℝ) * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
          = (2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [div_mul_eq_mul_div, mul_one_div, div_div]
      linarith [hle, heq.le, heq.ge]
    calc (H : ℝ) * (∑ p ∈ primeWindow eps H, (2 * Real.log (p : ℕ) + 8) / (((p : ℕ) : ℝ)
            * ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (H : ℝ) * ((2 * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 8)
              / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
            * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hstep hHR.le
      _ ≤ (H : ℝ) * ((eps : ℝ) / 8 * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hHR.le
          exact mul_le_mul_of_nonneg_right hZεbound hSPpos.le
      _ = (1 / 8) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by ring
  -- === total 2: the shift slice ≤ (1/16)·SP·H·ε ===
  have key2 : ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      = ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => (mul_one_div _ _).symm)
  have hHsq : (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2)
      ≤ (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left (window_sum_inv_sq eps H) hHR.le
    have h2 : (H : ℝ) * ((2 / ((eps : ℝ) ^ 2 * (H : ℝ))) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
        = (2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  have hSpos2 : (0 : ℝ) ≤ 3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹ := by
    positivity
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hle : (ω : ℝ) * (H : ℝ) ≤ (x : ℝ) := by
      nlinarith [hxbig, (show (0 : ℝ) ≤ 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        by positivity)]
    nlinarith [hle, mul_pos hωR hHR]
  have hxbound : 3 * (ω : ℝ) / (x : ℝ) / (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
      ≤ (eps : ℝ) / (16 * (1 + 2 / (eps : ℝ) ^ 2)) := by
    have hxZ : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) := by
      have hx1 : 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := by
        nlinarith [hxbig, (show (0 : ℝ) ≤ (ω : ℝ) * (H : ℝ) by positivity)]
      calc 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) := hx1
        _ = (x : ℝ) * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) * (∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hZ1 hxpos.le
    rw [div_le_iff₀ hepsR] at hxZ
    rw [div_div, div_le_div_iff₀ (mul_pos hxpos hZpos) (by positivity)]
    nlinarith [hxZ]
  have hT2 : (H : ℝ) * (∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) + (H : ℝ) / ((p : ℕ) : ℝ) ^ 2)
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    rw [key2]
    have hfac : ((∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          + (H : ℝ) * ∑ p ∈ primeWindow eps H, (1 / ((p : ℕ) : ℝ) ^ 2))
        * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹)
        ≤ ((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hHsq]) hSpos2
    have hmul : (H : ℝ) * (((1 + 2 / (eps : ℝ) ^ 2) * ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)))
          * (3 * (ω : ℝ) / (x : ℝ) / ∑ n ∈ Finset.Ioc (x / ω) x, (n : ℝ)⁻¹))
        ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
      have hCbound := hxbound
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (1 + 2 / (eps : ℝ) ^ 2))] at hCbound
      nlinarith [mul_le_mul_of_nonneg_left hCbound
        (mul_nonneg (mul_nonneg hHR.le hSPpos.le) (by norm_num : (0:ℝ) ≤ (1:ℝ)/16))]
    exact le_trans (mul_le_mul_of_nonneg_left hfac hHR.le) hmul
  -- === total 3: the boundary slice ≤ (1/16)·SP·H·ε ===
  have hT3 : ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
        * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
      ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) := by
    have h32 : (eps : ℝ) * (32 * Real.log 4) ≤ c := (le_div_iff₀ (by positivity)).mp heps_small
    have hkey3' : 2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))
        ≤ (1 / 16) * c * (H : ℝ) * (eps : ℝ) := by
      nlinarith [h32, mul_nonneg (mul_nonneg hepsR.le hHR.le) hepsR.le, hlog4]
    calc ((primeWindow eps H).card : ℝ) * |_|
        ≤ ((primeWindow eps H).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left habsX (Nat.cast_nonneg _)
      _ = ((primeWindow eps H).card : ℝ) := mul_one _
      _ ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) := hcard
      _ = (2 * Real.log 4 * ((eps : ℝ) ^ 2 * (H : ℝ))) / Real.log H := by ring
      _ ≤ ((1 / 16) * c * (H : ℝ) * (eps : ℝ)) / Real.log H := by
          gcongr
      _ = (1 / 16) * (c / Real.log H) * (H : ℝ) * (eps : ℝ) := by ring
      _ ≤ (1 / 16) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ) * (eps : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hSP_lb (by norm_num)) hHR.le) hepsR.le
  -- === the reduction: |IF − MAIN| ≤ H·ΣB + card·|X| ≤ T1 + T2 + T3 ===
  have hIF : (∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) ∂(logMeasure x ω))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
            (ArithmeticFunction.liouville (n + j + 1) : ℝ)
              * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ)
            else 0) ∂(logMeasure x ω) := by
    rw [IF_unfold eps H]
    exact Finset.sum_coe_sort (primeWindow eps H)
      (fun p => ∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod p) = 0 then
        (ArithmeticFunction.liouville (n + j + 1) : ℝ)
          * (windowVal H (liouvilleWindow H n) (j + p) : ℝ) else 0) ∂(logMeasure x ω))
  have hMAIN : (∑ p ∈ primeWindow eps H, (H : ℝ) / (p : ℝ) * (∫ n,
        (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)))
      = ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
          (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hIF, hMAIN, ← Finset.sum_sub_distrib]
  have hcombine : ∀ p ∈ primeWindow eps H,
      (∑ j ∈ Finset.range H, ∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
          (ArithmeticFunction.liouville (n + j + 1) : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
        - ∑ j ∈ Finset.range H, (1 / (p : ℝ)) * (∫ n,
            (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))
      = ∑ j ∈ Finset.range H,
          ((∫ n, (if ((n + j + 1 : ℕ) : ZMod (p : ℕ)) = 0 then
              (ArithmeticFunction.liouville (n + j + 1) : ℝ)
                * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) else 0) ∂(logMeasure x ω))
            - (1 / (p : ℝ)) * (∫ n, (ArithmeticFunction.liouville n : ℝ)
                * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω))) :=
    fun p _ => by rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl hcombine]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.abs_sum_le_sum_abs _ _)).trans ?_
  refine (Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun j hj =>
    per_term eps H hx hω hωx hxωH p hp j (Finset.mem_range.mp hj)))).trans ?_
  -- split the inner sum (per-pair bound j-independent; boundary term counted separately)
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hbnd_total : ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
      (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0)
      ≤ ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
    have hbnd : ∀ p ∈ primeWindow eps H, (∑ j ∈ Finset.range H,
        (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0))
        ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
      intro p hp
      have hpR : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast (by have := (prime_of_mem_primeWindow hp).two_le; omega : 0 < p)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcardp : (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast boundary_card_le H p
      calc (((Finset.range H).filter (fun j => H ≤ j + p)).card : ℝ) * ((1 / (p : ℝ)) * |_|)
          ≤ (p : ℝ) * ((1 / (p : ℝ)) * |_|) :=
            mul_le_mul_of_nonneg_right hcardp (by positivity)
        _ = |_| := by rw [← mul_assoc, mul_one_div, div_self hpR.ne', one_mul]
    calc ∑ p ∈ primeWindow eps H, ∑ j ∈ Finset.range H,
          (if H ≤ j + p then (1 / (p : ℝ)) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| else 0)
        ≤ ∑ p ∈ primeWindow eps H, |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| :=
          Finset.sum_le_sum hbnd
      _ = ((primeWindow eps H).card : ℝ) * |∫ n, (ArithmeticFunction.liouville n : ℝ)
            * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| := by
          rw [Finset.sum_const, nsmul_eq_mul]
  linarith [hT1, hT2, hT3, hbnd_total]

/-- **HREDUCE-FINAL, PINNED** (`hreduce_holds_final_bounded`) —
`HBudget.hreduce_holds_final` plus `1/4 ≤ c`, the second verbatim carry
(`HBudget.lean:721–725` reading §2).  This is the `cE` the head consumes. -/
theorem hreduce_holds_final_bounded :
    ∃ c : ℝ, 0 < c ∧ 1 / 4 ≤ c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H x ω : ℕ),
      2 ≤ x → 2 ≤ ω → ω ≤ x → 0 < eps → (eps : ℝ) ^ 2 ≤ 1 →
      3 ≤ H → 1 ≤ Real.log H → (4 : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      H₀ ≤ H →
      (eps : ℝ) ≤ c / (32 * Real.log 4) →
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (H : ℝ)) + 64 / (eps : ℝ) + 1 ≤ Real.log ω →
      (ω : ℝ) * (H : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (x : ℝ) →
      (eps : ℝ) / 2 ≤ |∫ n, (ArithmeticFunction.liouville n : ℝ)
          * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)| →
      (1 / 2) * (∑ p ∈ primeWindow eps H, (1 / (p : ℝ))) * (H : ℝ)
          * |∫ n, (ArithmeticFunction.liouville n : ℝ)
              * (ArithmeticFunction.liouville (n + 1) : ℝ) ∂(logMeasure x ω)|
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)| := by
  obtain ⟨c, hc, hcge, H₀, hbud⟩ := hbudget_holds_bounded
  refine ⟨c, hc, hcge, H₀, ?_⟩
  intro eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig hseed
  exact hreduce_holds eps H hseed
    (hbud eps H x ω hx hω hωx heps hepssq hH3 hlogH hH4 hsqrt hH0 heps_small hωbig hxbig)

/-! ## §3 The circle-method constant, capped -/

open private windowVal_c_norm_le T_collapse periodization_total from
  Salt.Entropy.Chowla.CircleMethod in
/-- **THE SQUARED CIRCLE-METHOD ESTIMATE, CAPPED**
(`circle_method_estimate_sq_bounded`) — `CircleMethod.circle_method_estimate_sq`
plus the conjunct `C ≤ 1 + 2·C₀`, at the landed `refine` witness `C = 1 + 2·C₀`.
The body is `CircleMethod.lean:808–911` verbatim; the only edit is the extra
`le_rfl`. -/
theorem circle_method_estimate_sq_bounded (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ C ≤ 1 + 2 * C₀ ∧
      ∀ (eps : ℚ) (H : ℕ) [NeZero H] (x1 : Fin H → ℤ),
      (∀ i, |x1 i| ≤ 1) →
      ((primeWindow eps H).card : ℝ)
          ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) →
      |∑ p : primeWindow eps H, (1 / (p : ℝ)) *
          ∑ j ∈ Finset.range H,
            (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)|
        ≤ C * ((H : ℝ) / Real.log (H : ℝ)) *
            ((eps : ℝ) ^ 2 + ∑ ξ ∈ bigXi eps H, (1 / (H : ℝ) ^ 2) *
              ‖(ZMod.dft (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℂ))) ξ‖ ^ 2) := by
  refine ⟨1 + 2 * C₀, by positivity, le_rfl, ?_⟩
  intro eps H _ x1 hx1 hcard
  by_cases hH2 : 2 ≤ H
  · -- main regime: H ≥ 2, so log H > 0
    have hH1r : (1 : ℝ) < (H : ℝ) := by exact_mod_cast hH2
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos hH1r
    have hHpos : (0 : ℝ) < (H : ℝ) := by linarith
    set Φ₁ : ZMod H → ℂ := fun m => ((windowVal H x1 m.val : ℤ) : ℂ) with hΦ₁
    have h1 : ∀ j, ‖Φ₁ j‖ ≤ 1 := fun j => windowVal_c_norm_le hx1 j
    -- the reality reflection at the (real, integer-valued) window datum
    have hreal : Φ₁ = fun j : ZMod H => ((windowVal H x1 (ZMod.val j) : ℝ) : ℂ) := by
      funext j
      simp only [hΦ₁]
      push_cast
      ring
    have hrefl : ∀ ξ : ZMod H, ‖ZMod.dft Φ₁ (-ξ)‖ = ‖ZMod.dft Φ₁ ξ‖ := by
      intro ξ
      rw [hreal]
      exact norm_dft_neg_of_real (fun j : ZMod H => (windowVal H x1 (ZMod.val j) : ℝ)) ξ
    set S : ℝ := ∑ ξ ∈ bigXi eps H, ‖ZMod.dft Φ₁ ξ‖ ^ 2 with hS
    set L : ℝ := ∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ) with hL
    set T : ℂ := ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ∑ m : ZMod H, Φ₁ m * Φ₁ (m + ((p : ℕ) : ZMod H)) with hT
    set W : ℂ := ∑ ξ : ZMod H, ZMod.dft Φ₁ ξ * ZMod.dft Φ₁ (-ξ) *
        expSum eps H (-(ξ.val : ℝ) / (H : ℝ)) with hW
    -- collapse and split (the SQUARED major arm)
    have hWT : (H : ℂ) * T = W := T_collapse Φ₁ Φ₁
    have hTnorm : (H : ℝ) * ‖T‖ = ‖W‖ := by
      rw [← hWT, norm_mul, Complex.norm_natCast]
    have hnormW : ‖W‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
        + (2 * C₀ / Real.log (H : ℝ)) * S :=
      fourier_split_sq Φ₁ h1 hrefl hC₀ hlog hcard
    -- cast L and periodization (the diagonal instance of `periodization_total`)
    have hLcast : ((L : ℝ) : ℂ) = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        ((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
          (windowVal H x1 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ) := by
      rw [hL, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      push_cast
      ring
    have hdiff : ((L : ℝ) : ℂ) - T = ∑ p : primeWindow eps H, (1 / ((p : ℕ) : ℂ)) *
        (((∑ j ∈ Finset.range H, (windowVal H x1 j : ℝ) *
            (windowVal H x1 (j + (p : ℕ)) : ℝ) : ℝ) : ℂ)
          - ∑ m : ZMod H, ((windowVal H x1 m.val : ℤ) : ℂ) *
              ((windowVal H x1 (m + ((p : ℕ) : ZMod H)).val : ℤ) : ℂ)) := by
      rw [hLcast, hT, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun p _ => by rw [mul_sub])
    have hperiod : ‖((L : ℝ) : ℂ) - T‖ ≤ ((primeWindow eps H).card : ℝ) := by
      rw [hdiff]; exact periodization_total hx1 hx1
    -- assemble
    have hLT : |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by
      have h := norm_add_le T (((L : ℝ) : ℂ) - T)
      rw [add_sub_cancel] at h
      calc |L| = ‖((L : ℝ) : ℂ)‖ := (Complex.norm_real L).symm
        _ ≤ ‖T‖ + ‖((L : ℝ) : ℂ) - T‖ := h
        _ ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := by linarith [hperiod]
    have hH0 : (H : ℝ) ≠ 0 := ne_of_gt hHpos
    have hLe0 : Real.log (H : ℝ) ≠ 0 := ne_of_gt hlog
    have hTle : ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
        + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S := by
      have hHTle : (H : ℝ) * ‖T‖ ≤ (eps : ℝ) ^ 2 * (H : ℝ) ^ 2 / Real.log (H : ℝ)
          + (2 * C₀ / Real.log (H : ℝ)) * S := hTnorm ▸ hnormW
      have key : (H : ℝ) * ‖T‖ ≤ (H : ℝ) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
          + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S) := by
        refine hHTle.trans (le_of_eq ?_)
        field_simp
      exact le_of_mul_le_mul_left key hHpos
    rw [← Finset.mul_sum, ← hS]
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun ξ _ => sq_nonneg _)
    have hquot_nn : 0 ≤ (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) := by positivity
    have hrem_nn : 0 ≤ C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
        + (1 / (H : ℝ)) * S / Real.log (H : ℝ) :=
      add_nonneg (mul_nonneg hC₀.le hquot_nn)
        (div_nonneg (mul_nonneg (by positivity) hS_nn) hlog.le)
    have heq : (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
          * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S)
        = ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * C₀ / Real.log (H : ℝ) * (1 / (H : ℝ)) * S)
          + C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
          + (C₀ * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))
              + (1 / (H : ℝ)) * S / Real.log (H : ℝ)) := by
      field_simp
      ring
    calc |L| ≤ ‖T‖ + ((primeWindow eps H).card : ℝ) := hLT
      _ ≤ (1 + 2 * C₀) * ((H : ℝ) / Real.log (H : ℝ))
            * ((eps : ℝ) ^ 2 + 1 / (H : ℝ) ^ 2 * S) := by
          rw [heq]; linarith [hTle, hcard, hrem_nn]
  · -- degenerate: H = 1
    have hH1 : H = 1 := by have := NeZero.pos H; omega
    have hlog0 : Real.log (H : ℝ) = 0 := by rw [hH1]; simp
    have hL0 : (∑ p : primeWindow eps H, (1 / (p : ℝ)) *
        ∑ j ∈ Finset.range H,
          (windowVal H x1 j : ℝ) * (windowVal H x1 (j + (p : ℕ)) : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun p _ => ?_)
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hp2 := (prime_of_mem_primeWindow p.2).two_le
      have hge : ¬ (j + (p : ℕ) < H) := by omega
      have hz : windowVal H x1 (j + (p : ℕ)) = 0 := by rw [windowVal, dif_neg hge]
      rw [hz]; simp
    rw [hL0, abs_zero]
    have hmid : (H : ℝ) / Real.log (H : ℝ) = 0 := by rw [hlog0, div_zero]
    rw [hmid]; simp

end Salt.Entropy.Chowla

