/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The prime-window Mertens LOWER bound (spine node D3)

The W3-F gap flagged in `docs/exploration/s3-a3-design.md` (the 🚩 D3 paragraph): Tao's
"by the prime number theorem" on the (2.4)→(2.11) chain hides the LOWER windowed Mertens
bound `∑_{p ∈ 𝒫_H} 1/p ≥ c / log H`.  Only upper bounds existed in the tree
(`primeWindow_card_le_of_regime` here, `Salt.BrunLower.sum_inv_prime_window_le` on the Brun
track); the crude Chebyshev lower constants (mathlib `Chebyshev.theta_ge`, `psi_ge`: `log 2`
against the `log 4` uppers) cancel EXACTLY over a dyadic window, so no elementary
differencing closes it.  The carrier that does: the Chen track's unconditional PNT-with-rate
(`Salt.Chen.psiTot_pnt`, from the SW `siegelWalfisz_holds` gate), already differenced over
the dyadic window as `Salt.Chen.lambda_mass_lower`:
`x/2 − 1 − 2K·x/log x ≤ ∑_{n ∈ Icc (x/2) (x−2)} Λ(n)`.

Route, at `N = ⌊ε²H⌋₊`:

1. `lambda_mass_lower` puts Λ-mass `≥ N/2 − 1 − 2K·N/log N` on `Icc (N/2) (N−2)`.
2. Drop the nat-div boundary point `N/2` (cost `≤ log N`, via `vonMangoldt_le_log`); the
   remaining support `Ioc (N/2) (N−2)` sits strictly above the rational cut `ε²H/2`.
3. Strip prime powers: the non-prime Λ-mass up to `N` is `ψ(N) − θ(N) ≤ 2√N·log N`
   (mathlib `Chebyshev.psi_sub_theta_eq_sum_not_prime` + `psi_sub_theta_le`).
4. Every surviving prime `p ∈ Ioc (N/2) (N−2)` lies in `primeWindow eps H` and contributes
   `1/p ≥ log p / (N log N)`, so `∑ 1/p ≥ θ-mass/(N log N) ≥ (N/4)/(N log N) = 1/(4 log N)`.
5. The regime `√H ≤ ε²H/2` gives `N ≥ √H` (so `log N ≥ (1/2) log H` absorbs the error
   thresholds uniformly in `eps`), and the new hypothesis `ε² ≤ 1` gives `N ≤ H`, hence
   `1/(4 log N) ≥ (1/4)/log H`.

**Constant: `c = 1/4`, uniform in `eps`** (as expected: the true window value is
`≈ log 2 / log N ≈ 0.69/log H`; the `1/4` keeps every threshold elementary).  The regime
hypotheses mirror `primeWindow_card_le_of_regime`, plus `(eps : ℝ)² ≤ 1` (Tao's "ε small";
needed so the window top `ε²H` stays `≤ H`).  `H₀` absorbs the PNT constant `K` (which is
existential, from the SW gate), so no smoke instance of the full theorem is computable; the
smoke below checks the `c = 1/4` numerology at the `regime_nonvacuous` point instead.
-/
import Salt.Entropy.Chowla.PrimeWindow
import Salt.Chen.MertensPNT
import Mathlib

open scoped BigOperators
open ArithmeticFunction

namespace Salt.Entropy.Chowla

/-- **The prime-window Mertens LOWER bound** (spine node D3, the W3-F 🚩 gap).

There are `c > 0` (here `c = 1/4`) and a threshold `H₀` such that for all `H ≥ H₀` and all
`eps` in the regime `√H ≤ ε²H/2` (Tao's "ε small, H large" gate, as in
`primeWindow_card_le_of_regime`) with `ε² ≤ 1`,
`∑_{p ∈ 𝒫_H} 1/p ≥ c / log H`.

Carrier: the unconditional dyadic Λ-mass lower bound `Salt.Chen.lambda_mass_lower`
(PNT-with-rate through the SW gate), boundary- and prime-power-stripped. -/
theorem primeWindow_sum_inv_ge :
    ∃ c : ℝ, 0 < c ∧ ∃ H₀ : ℕ, ∀ (eps : ℚ) (H : ℕ), H₀ ≤ H →
      Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2 →
      (eps : ℝ) ^ 2 ≤ 1 →
      c / Real.log (H : ℝ) ≤ ∑ p ∈ primeWindow eps H, (1 / (p : ℝ)) := by
  obtain ⟨K, hK0, hK⟩ := Salt.Chen.lambda_mass_lower
  refine ⟨1 / 4, by norm_num, max (96 ^ 8) (⌈Real.exp (64 * K)⌉₊ + 1), ?_⟩
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

/-- **Smoke instance** for the `c = 1/4` numerology, at the `regime_nonvacuous` point
`eps = 1`, `H = 4` (regime holds with equality, window `= {3}`): the D3 inequality shape
`(1/4)/log H ≤ ∑_{p ∈ 𝒫_H} 1/p` checks concretely — `(1/4)/log 4 ≈ 0.18 ≤ 1/3`.  (The full
theorem's `H₀` absorbs the existential PNT constant, so this is the shape check, not an
instantiation.) -/
theorem primeWindow_sum_inv_ge_smoke :
    (1 / 4 : ℝ) / Real.log 4 ≤ ∑ p ∈ primeWindow 1 4, (1 / (p : ℝ)) := by
  have h3 : (3 : ℕ) ∈ primeWindow 1 4 :=
    mem_primeWindow.mpr ⟨Nat.le_floor (by norm_num), by norm_num, by norm_num⟩
  have hsum : (1 / 3 : ℝ) ≤ ∑ p ∈ primeWindow 1 4, (1 / (p : ℝ)) := by
    have hsub : ({3} : Finset ℕ) ⊆ primeWindow 1 4 := Finset.singleton_subset_iff.mpr h3
    have h1 : ∑ p ∈ ({3} : Finset ℕ), (1 / (p : ℝ)) = 1 / 3 := by norm_num
    calc (1 / 3 : ℝ) = ∑ p ∈ ({3} : Finset ℕ), (1 / (p : ℝ)) := h1.symm
      _ ≤ ∑ p ∈ primeWindow 1 4, (1 / (p : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have hlog4 : (3 / 4 : ℝ) ≤ Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h3' := Real.log_two_gt_d9
    linarith
  have hlogpos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  calc (1 / 4 : ℝ) / Real.log 4 ≤ 1 / 3 := by
        rw [div_le_iff₀ hlogpos]
        linarith
    _ ≤ _ := hsum

end Salt.Entropy.Chowla
