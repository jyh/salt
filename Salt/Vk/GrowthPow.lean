/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Mid
import Salt.Vk.Growth
import Salt.ExpSum.Strip
import Salt.Tactic.ExpLogNum

/-!
# VMVT-VK rung R6 (body) — the dyadic ladder `zeta_growth_pow` (`VK-GROWTH`) + THE COMPOSE

WALL 2, THE LAST WALL.  This file assembles the front end (`zeta_sub_dirichlet_bound`, ζ reduced to
its length-`⌈t²⌉` Dirichlet tail up to an absolute `4`) with the mid-band window (`vk_window_mid`,
promoted here to a **prefix** form `vk_window_mid_prefix` for the Abel weighting) and the landed
sub-Weyl trichotomy (`zeta_block_dispatch`) into the Vinogradov–Korobov strip growth
`‖ζ(σ+it)‖ ≤ K·log t` on `σ ≥ 1 − vkTheta t`, then composes with the emission
`zeta_zero_free_region_pow_of_growth` to produce **the first power zero-free region** (θ = 3/4).

## Route

`‖ζ − ∑_{n≤⌈t²⌉} n^{−s}‖ ≤ 4` (front end).  For `σ ≥ 1` the Dirichlet sum is `≤ 1 + log⌈t²⌉`
(harmonic).  For `σ ∈ [1−Θ, 1)` a dyadic ladder over the blocks `(M, x']` routes each block by
`j = log M`:
* **low** (`Θ·j < log 2`): trivial `∑ n^{−σ} ≤ M^{1−σ} ≤ M^Θ < 2`;
* **mid** (`log 2 ≤ Θ·j`, `10·j < log t`): `vk_window_mid_prefix` + `zeta_weighted_block` ⇒ `≤ 10`;
* **high** (`10·j ≥ log t`): `zeta_block_dispatch` at `k = 12` (`Θ ≤ 2^{−14}`) ⇒ `≤ 1348`.
Each block `≤ 1348`; `≤ 3(1+log t)` blocks ⇒ `∑_{(1,X]} n^{−s} ≤ 1348·3(1+log t)`, giving `K·log t`.

## The prefix promotion

`zeta_weighted_block` needs a bound on **every prefix** `∑_{(M,y]} eR` of the block, not just the
full block.  `vk_window_mid` bounds only the full dyadic window.  `vk_window_mid_prefix` recovers
the prefix bound by the *min-trick* `c' i = min (c i) y`: the prefix `(N, y]` re-telescopes into the
same `⌈N/P⌉` sub-blocks clipped at `y`, each a prefix of a `vk_block_core` sub-block, so the ladder
bound `10·N·P^{−ρ}` survives unchanged (`vk_ladder_prefix` → `vk_window_prefix` →
`vk_window_scale_prefix` → `vk_window_mid_prefix`, mirroring the landed full-window chain;
all four live in `Mid` since O13-e row 219, where `vk_window_mid` is the `y = 2N` case).
-/

namespace Salt.Vk

open Complex Finset Real Salt.ExpSum
open scoped BigOperators

/-! ## The per-block trichotomy (low / mid / high) -/

set_option maxHeartbeats 1000000 in
-- The three-way case split threads many staged rpow/exp/log facts through `nlinarith`.
/-- **Per-block trichotomy bound.**  On the sub-unit strip `σ ∈ [1−vkTheta t, 1)` and `t` above the
schedule floor `log t ≥ e^100`, every dyadic block `(M, x']` (`1 ≤ M`, `M < x' ≤ 2M`, `M ≤ t²`) of
the `n^{−s}` sum obeys `‖∑_{(M,x']} n^{−s}‖ ≤ 1348`.  Routes by `j = log M`: trivial (low), the mid
window `vk_window_mid_prefix` + `zeta_weighted_block`, or the landed dispatch (`k = 12`, high). -/
lemma vk_dirichlet_block_le {σ t : ℝ} {M x' : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσlo : 1 - vkTheta t ≤ σ) (hσ1 : σ < 1)
    (hM1 : 1 ≤ M) (hMx' : M < x') (hx'2 : x' ≤ 2 * M) (hMt2 : (M : ℝ) ≤ t ^ 2) :
    ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hlogt1 : 1 < Real.log t := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith [hL100]
  have ht1 : (1 : ℝ) ≤ t := by
    have h := Real.exp_lt_exp.mpr hlogtpos
    rw [Real.exp_zero, Real.exp_log ht0] at h; linarith
  have hΘpos : 0 < vkTheta t := vkTheta_pos hlogt1
  -- Θ ≤ 1/2^14
  have hΘ14 : vkTheta t ≤ 1 / (2 : ℝ) ^ 14 := by
    rw [vkTheta]
    have h1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    have h2 : (100 : ℝ) ≤ Real.log (Real.log t) := le_log_of_exp_le hL100
    have h3 : (10000 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := by nlinarith only [h2]
    have hDpos : 0 < (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
      positivity
    rw [div_le_iff₀ hDpos]
    linarith only [mul_le_mul h1 h3 (by norm_num) (by positivity)]
  have hσpos : 0 < σ := by
    have : (1 : ℝ) / (2 : ℝ) ^ 14 < 1 := by norm_num
    linarith [hσlo, hΘ14]
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hlogM0 : (0 : ℝ) ≤ Real.log M := Real.log_nonneg hM1R
  have hx'2Z : (x' : ℤ) ≤ 2 * (M : ℤ) := by exact_mod_cast hx'2
  rcases le_or_gt (Real.log t) (10 * Real.log M) with hhi | hjhiM
  · -- HIGH: dispatch at k = 12
    have hexp2601 : (2601 : ℝ) ≤ Real.exp 100 := by
      exact_mod_cast Salt.Tactic.le_exp_nat_of_le_pow 100 (by norm_num)
    have hlogM260 : (260 : ℝ) ≤ Real.log M := by linarith [hhi, hL100, hexp2601]
    have hMfac : ((Nat.factorial 12 : ℝ)) ^ 6 ≤ (M : ℝ) := by
      have hfac2 : (Nat.factorial 12 : ℝ) ≤ 2 ^ 29 := by norm_num [Nat.factorial]
      have hlog2le1 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
      have hlogfac : Real.log (Nat.factorial 12 : ℝ) ≤ 29 := by
        calc Real.log (Nat.factorial 12 : ℝ) ≤ Real.log ((2 : ℝ) ^ 29) :=
              Real.log_le_log (by positivity) hfac2
          _ = 29 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
          _ ≤ 29 := by linarith only [hlog2le1]
      have hlog6 : Real.log (((Nat.factorial 12 : ℝ)) ^ 6) ≤ 174 := by
        rw [Real.log_pow]; push_cast; linarith only [hlogfac]
      rw [show ((Nat.factorial 12 : ℝ)) ^ 6
            = Real.exp (Real.log (((Nat.factorial 12 : ℝ)) ^ 6)) from
            (Real.exp_log (by positivity)).symm]
      calc Real.exp (Real.log (((Nat.factorial 12 : ℝ)) ^ 6)) ≤ Real.exp 174 :=
            Real.exp_le_exp.mpr hlog6
        _ ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr (by linarith [hlogM260])
        _ = M := Real.exp_log hMpos
    have hσlo12 : 1 - 1 / (2 : ℝ) ^ (12 + 2) ≤ σ := by
      have he : (1 : ℝ) / (2 : ℝ) ^ (12 + 2) = 1 / (2 : ℝ) ^ 14 := by norm_num
      rw [he]; linarith [hσlo, hΘ14]
    have hguard : t ≤ (M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ)) := by
      have hfac11 : ((12 - 1).factorial : ℝ) ≤ 2 ^ 26 := by norm_num [Nat.factorial]
      have hfac11pos : (0 : ℝ) < ((12 - 1).factorial : ℝ) := by positivity
      have hlog2le1 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
      have hlog11 : Real.log ((12 - 1).factorial : ℝ) ≤ 26 := by
        calc Real.log ((12 - 1).factorial : ℝ) ≤ Real.log ((2 : ℝ) ^ 26) :=
              Real.log_le_log hfac11pos hfac11
          _ = 26 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
          _ ≤ 26 := by linarith only [hlog2le1]
      have hRHSpos : (0 : ℝ) < (M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ)) :=
        div_pos (Real.rpow_pos_of_pos hMpos _) hfac11pos
      have hlogRHS : Real.log ((M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ)))
          = (((12 : ℕ) : ℝ) - 1) * Real.log M - Real.log ((12 - 1).factorial : ℝ) := by
        rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hMpos _)) (ne_of_gt hfac11pos),
          Real.log_rpow hMpos]
      have hle : Real.log t
          ≤ Real.log ((M : ℝ) ^ (((12 : ℕ) : ℝ) - 1) / (((12 - 1).factorial : ℝ))) := by
        rw [hlogRHS]
        have h11 : ((12 : ℕ) : ℝ) - 1 = 11 := by norm_num
        rw [h11]; linarith [hhi, hlog11, hlogM260]
      have hexp := Real.exp_le_exp.mpr hle
      rwa [Real.exp_log ht0, Real.exp_log hRHSpos] at hexp
    exact zeta_block_dispatch 12 (by norm_num) σ t hσlo12 (by linarith) ht1 M x' hMfac hMx' hx'2
      hMt2 hguard
  · -- 10 log M < log t
    rcases le_or_gt (Real.log 2) (vkTheta t * Real.log M) with hmid | hlow
    · -- MID
      have hM2 : 2 ≤ M := by
        rcases Nat.lt_or_ge M 2 with h | h
        · exfalso
          have hM1' : M = 1 := by omega
          rw [hM1', Nat.cast_one, Real.log_one, mul_zero] at hmid
          linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
        · exact h
      set k : ℕ := max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊ with hkdef
      set r : ℕ := ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊ with hrdef
      set m : ℕ := ⌈Real.log t / Real.log M⌉₊ with hmdef
      have hBnn : (0 : ℝ) ≤ 10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M)) := by positivity
      have hpref : ∀ y : ℤ, (M : ℤ) < y → y ≤ (x' : ℤ) →
          ‖∑ n ∈ Finset.Ioc (M : ℤ) y, eR (phi t n)‖
            ≤ 10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M)) := by
        intro y hy1 hy2
        exact vk_window_mid_prefix ht0 hL100 hM2 hkdef hrdef hmdef hmid hjhiM y hy1
          (le_trans hy2 hx'2Z)
      refine le_trans (zeta_weighted_block σ t hσpos M x' hM1 hMx' _ hBnn hpref) ?_
      -- M^{−σ}·(10 M exp(−Θ logM)) = 10·exp((1−σ−Θ)·logM) ≤ 10
      have hkey : (M : ℝ) ^ (-σ) * (10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M))) ≤ 10 := by
        have hcollapse : (M : ℝ) ^ (-σ) * (M : ℝ)
            = Real.exp ((1 - σ) * Real.log M) := by
          rw [← Real.rpow_add_one (ne_of_gt hMpos) (-σ), Real.rpow_def_of_pos hMpos]
          congr 1; ring
        have hexpprod : Real.exp ((1 - σ) * Real.log M) * Real.exp (-(vkTheta t * Real.log M))
            = Real.exp ((1 - σ - vkTheta t) * Real.log M) := by
          rw [← Real.exp_add]; congr 1; ring
        have harg : (1 - σ - vkTheta t) * Real.log M ≤ 0 := by
          apply mul_nonpos_of_nonpos_of_nonneg _ hlogM0
          linarith [hσlo]
        calc (M : ℝ) ^ (-σ) * (10 * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M)))
            = 10 * ((M : ℝ) ^ (-σ) * (M : ℝ) * Real.exp (-(vkTheta t * Real.log M))) := by ring
          _ = 10 * Real.exp ((1 - σ - vkTheta t) * Real.log M) := by
              rw [hcollapse, hexpprod]
          _ ≤ 10 * Real.exp 0 := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact Real.exp_le_exp.mpr harg
          _ = 10 := by rw [Real.exp_zero]; ring
      linarith [hkey]
    · -- LOW: trivial
      have hnorm : ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ) := by
        refine le_trans (norm_sum_le _ _) ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [Finset.mem_Ioc] at hn
        have hn0 : 0 < n := by omega
        rw [norm_natCast_cpow_of_pos hn0]
        apply le_of_eq
        congr 1
        simp [Complex.add_re, Complex.mul_re]
      have hsum : ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ) ≤ (M : ℝ) ^ (1 - σ) := by
        have hbound : ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ)
            ≤ ∑ _n ∈ Finset.Ioc M x', (M : ℝ) ^ (-σ) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Ioc] at hn
          exact Real.rpow_le_rpow_of_nonpos hMpos (by exact_mod_cast (by omega : M ≤ n))
            (by linarith)
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul] at hbound
        have hcard : ((x' - M : ℕ) : ℝ) ≤ (M : ℝ) := by
          have : x' - M ≤ M := by omega
          exact_mod_cast this
        have hMσnn : (0 : ℝ) ≤ (M : ℝ) ^ (-σ) := Real.rpow_nonneg hMpos.le _
        refine le_trans hbound ?_
        calc ((x' - M : ℕ) : ℝ) * (M : ℝ) ^ (-σ) ≤ (M : ℝ) * (M : ℝ) ^ (-σ) :=
              mul_le_mul_of_nonneg_right hcard hMσnn
          _ = (M : ℝ) ^ (1 - σ) := by
              rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hMpos) (-σ)]
              congr 1; ring
      have hlt2 : (M : ℝ) ^ (1 - σ) < 2 := by
        have hle : (M : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (vkTheta t) :=
          Real.rpow_le_rpow_of_exponent_le hM1R (by linarith [hσlo])
        have heq : (M : ℝ) ^ (vkTheta t) = Real.exp (vkTheta t * Real.log M) := by
          rw [Real.rpow_def_of_pos hMpos, mul_comm]
        rw [heq] at hle
        have : Real.exp (vkTheta t * Real.log M) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hlow
        rw [Real.exp_log (by norm_num)] at this
        linarith [hle]
      calc ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ∑ n ∈ Finset.Ioc M x', (n : ℝ) ^ (-σ) := hnorm
        _ ≤ (M : ℝ) ^ (1 - σ) := hsum
        _ ≤ 1348 := by linarith [hlt2]

/-! ## The dyadic assembly over the length-`⌈t²⌉` Dirichlet sum -/

set_option maxHeartbeats 800000 in
-- The ladder induction + `Nat.find` block-count arithmetic exceeds the default budget.
/-- **The Dirichlet-tail bound.**  On `1 − vkTheta t ≤ σ ≤ 3`, `log t ≥ e^100`, the length-`⌈t²⌉`
Dirichlet partial sum obeys `‖∑_{n≤⌈t²⌉} n^{−s}‖ ≤ 4050·(1+log t)`.  For `σ ≥ 1` the harmonic
bound; for `σ ∈ [1−Θ,1)` the dyadic ladder over `vk_dirichlet_block_le` (`≤ 3(1+log t)` blocks,
each `≤ 1348`). -/
lemma vk_dirichlet_sum_le {σ t : ℝ} (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t)
    (hσlo : 1 - vkTheta t ≤ σ) (_hσ3 : σ ≤ 3) :
    ‖∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ 4050 * (1 + Real.log t) := by
  have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hlogt1 : 1 < Real.log t := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith [hL100]
  have ht1 : (1 : ℝ) ≤ t := by
    have h := Real.exp_lt_exp.mpr hlogtpos
    rw [Real.exp_zero, Real.exp_log ht0] at h; linarith
  have hlogtnn : (0 : ℝ) ≤ Real.log t := hlogtpos.le
  set N : ℕ := ⌈t ^ 2⌉₊ with hNdef
  have ht2pos : (0 : ℝ) < t ^ 2 := by positivity
  have hN1 : 1 ≤ N := by rw [hNdef, Nat.one_le_ceil_iff]; positivity
  have hNt2u : (N : ℝ) ≤ 2 * t ^ 2 := by
    rw [hNdef]
    calc (⌈t ^ 2⌉₊ : ℝ) ≤ t ^ 2 + 1 := le_of_lt (Nat.ceil_lt_add_one (by positivity))
      _ ≤ 2 * t ^ 2 := by nlinarith only [ht0, ht1]
  rcases le_or_gt 1 σ with hσ1 | hσ1
  · -- σ ≥ 1: harmonic bound
    have hnorm : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hn0 : 0 < n := by omega
      rw [norm_natCast_cpow_of_pos hn0]
      apply le_of_eq; congr 1
      simp [Complex.add_re, Complex.mul_re]
    have hharm : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) ≤ 1 + Real.log N :=
      sum_Icc_rpow_neg_le' hσ1 hN1
    have hlogN : Real.log N ≤ Real.log 2 + 2 * Real.log t := by
      have h1 : Real.log N ≤ Real.log (2 * t ^ 2) :=
        Real.log_le_log (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1) hNt2u
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
      push_cast at h1; linarith [h1]
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
    calc ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ) := hnorm
      _ ≤ 1 + Real.log N := hharm
      _ ≤ 4050 * (1 + Real.log t) := by linarith only [hlog2, hlogN, hlogt1]
  · -- σ < 1: dyadic ladder
    have hblock : ∀ M x' : ℕ, 1 ≤ M → M < x' → x' ≤ 2 * M → x' ≤ N →
        ‖∑ n ∈ Finset.Ioc M x', (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 := by
      intro M x' hM1 hMx' hx'2 hx'N
      have hMt2 : (M : ℝ) ≤ t ^ 2 := by
        have hMN : M ≤ N - 1 := by omega
        have hMNR : (M : ℝ) ≤ (N : ℝ) - 1 := by
          have : (M : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hMN
          rw [Nat.cast_sub hN1, Nat.cast_one] at this; exact this
        have hNu : (N : ℝ) ≤ t ^ 2 + 1 := by
          rw [hNdef]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
        linarith [hMNR, hNu]
      exact vk_dirichlet_block_le ht0 hL100 hσlo hσ1 hM1 hMx' hx'2 hMt2
    have hlad : ∀ (J Y : ℕ), 1 ≤ Y → Y ≤ 2 ^ J → Y ≤ N →
        ‖∑ n ∈ Finset.Ioc 1 Y, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1348 * J := by
      intro J
      induction J with
      | zero =>
          intro Y hY0 hY1 hYN
          simp only [pow_zero] at hY1
          have : Y = 1 := le_antisymm hY1 hY0
          subst this; simp
      | succ J ih =>
          intro Y hY0 hY1 hYN
          by_cases hc : Y ≤ 2 ^ J
          · refine le_trans (ih Y hY0 hc hYN) ?_
            have : (0 : ℝ) ≤ (J : ℝ) := by positivity
            push_cast; linarith only []
          · push_neg at hc
            have hmid : 1 ≤ 2 ^ J := Nat.one_le_pow J 2 (by norm_num)
            have hsplit : ∑ n ∈ Finset.Ioc 1 Y, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
                = ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ J), (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
                  + ∑ n ∈ Finset.Ioc (2 ^ J) Y, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) :=
              (Finset.sum_Ioc_consecutive _ hmid (le_of_lt hc)).symm
            rw [hsplit]
            refine le_trans (norm_add_le _ _) ?_
            have hb1 := ih (2 ^ J) hmid (le_refl _) (le_trans (le_of_lt hc) hYN)
            have hY2M : Y ≤ 2 * 2 ^ J := by
              rw [show 2 * 2 ^ J = 2 ^ (J + 1) from by rw [pow_succ]; ring]; exact hY1
            have hb2 := hblock (2 ^ J) Y hmid hc hY2M hYN
            calc _ ≤ 1348 * (J : ℝ) + 1348 := add_le_add hb1 hb2
              _ = 1348 * ((J + 1 : ℕ) : ℝ) := by push_cast; ring
    have hex : ∃ J : ℕ, N ≤ 2 ^ J := ⟨N, le_of_lt Nat.lt_two_pow_self⟩
    set J := Nat.find hex with hJdef
    have hmain := hlad J N hN1 (Nat.find_spec hex) (le_refl N)
    have hJcount : (J : ℝ) ≤ 3 + 3 * Real.log t := by
      rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
      · rw [hJ0]; push_cast; linarith [hlogtnn]
      · have hJm1 : ¬ N ≤ 2 ^ (J - 1) := Nat.find_min hex (show J - 1 < J by omega)
        push_neg at hJm1
        have h2lt : (2 : ℝ) ^ (J - 1) < 2 * t ^ 2 := by
          have : ((2 : ℝ) ^ (J - 1)) < (N : ℝ) := by exact_mod_cast hJm1
          linarith [hNt2u]
        have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
        have hlogineq : ((J : ℝ) - 1) * Real.log 2 < Real.log 2 + 2 * Real.log t := by
          have h := Real.log_lt_log (by positivity) h2lt
          rw [Real.log_pow, Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h
          have hcast : ((J - 1 : ℕ) : ℝ) = (J : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]; push_cast; ring
          rw [hcast] at h; push_cast at h; linarith [h]
        have h23 : (2 : ℝ) ≤ 3 * Real.log 2 := by
          have := Real.log_two_gt_d9; linarith only [this, hlog2pos]
        nlinarith only [hlog2pos, hlogt1, h23, hlogineq, (Nat.cast_nonneg _ : 0 ≤ ↑J)]
    -- head: Icc 1 N = insert 1 (Ioc 1 N)
    have hins : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
    have h1notin : (1 : ℕ) ∉ Finset.Ioc 1 N := by simp
    rw [hins, Finset.sum_insert h1notin]
    refine le_trans (norm_add_le _ _) ?_
    have hh1 : ‖((1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 1 := by
      rw [Nat.cast_one, Complex.one_cpow, norm_one]
    calc ‖((1 : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
          + ‖∑ n ∈ Finset.Ioc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ 1 + 1348 * (J : ℝ) := add_le_add hh1 hmain
      _ ≤ 4050 * (1 + Real.log t) := by linarith only [hJcount, hlogt1]

/-! ## THE R6 BODY — `zeta_growth_pow` -/

/-- **`zeta_growth_pow` (R6 body, WALL 2).**  The Vinogradov–Korobov strip growth: on the power
strip `σ ≥ 1 − vkTheta t`, `σ ≤ 3`, `t ≥ t₀`, `‖ζ(σ+it)‖ ≤ K·log t`.  Front end
`zeta_sub_dirichlet_bound` (`≤ 4`) + the dyadic σ-weighted ladder `vk_dirichlet_sum_le`
(`≤ 4050(1+log t)`), with witnesses `K = 8104`, `t₀ = exp(exp 100)`. -/
theorem zeta_growth_pow : ZetaGrowthPow := by
  refine ⟨8104, Real.exp (Real.exp 100), by norm_num, ?_, ?_⟩
  · have h1 : (3 : ℝ) ≤ Real.exp 100 := by
      have := Real.add_one_le_exp (100 : ℝ); linarith
    have h2 : Real.exp 3 ≤ Real.exp (Real.exp 100) := Real.exp_le_exp.mpr h1
    have h3 : (3 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ); linarith
    linarith [h2, h3]
  · intro σ t htge hσlo hσ3
    have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) htge
    have hL100 : Real.exp 100 ≤ Real.log t := by
      have h := Real.log_le_log (Real.exp_pos _) htge
      rwa [Real.log_exp] at h
    have hlogtpos : 0 < Real.log t := lt_of_lt_of_le (Real.exp_pos 100) hL100
    have hlogt1 : 1 ≤ Real.log t := by
      have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
      linarith [hL100]
    have ht100 : (100 : ℝ) ≤ t := by
      have h1 : (100 : ℝ) ≤ Real.exp (Real.exp 100) := by
        have h100 : (100 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
        linarith [Real.add_one_le_exp (Real.exp 100), h100]
      linarith [htge, h1]
    -- σ ≥ 3/4 (since vkTheta t ≤ 1/4)
    have hΘsmall : vkTheta t ≤ 1 / 4 := by
      rw [vkTheta]
      have h1 : (1 : ℝ) ≤ (Real.log t) ^ ((3 : ℝ) / 4) :=
        Real.one_le_rpow hlogt1 (by norm_num)
      have h2 : (1 : ℝ) ≤ Real.log (Real.log t) := by
        have h100 : (100 : ℝ) ≤ Real.log (Real.log t) := le_log_of_exp_le hL100
        linarith
      have h3 : (1 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := one_le_pow₀ h2
      have hDpos : 0 < (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
        positivity
      rw [div_le_iff₀ hDpos]
      linarith only [hDpos, mul_le_mul h1 h3 (by norm_num) (by positivity)]
    have hσ34 : 3 / 4 ≤ σ := by linarith [hσlo, hΘsmall]
    -- front end + Dirichlet bound
    have hfront := zeta_sub_dirichlet_bound hσ34 hσ3 ht100
    have hdir := vk_dirichlet_sum_le ht0 hL100 hσlo hσ3
    have hcombine : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 4050 * (1 + Real.log t) + 4 := by
      have htri := norm_sub_le (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        (∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
      -- ‖ζ‖ ≤ ‖ζ − D‖ + ‖D‖ ≤ 4 + 4050(1+log t)
      have h := norm_le_norm_add_norm_sub' (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        (∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
      -- ‖ζ‖ ≤ ‖D‖ + ‖ζ − D‖
      have hsub : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ 4 :=
        hfront
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
            + ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              - ∑ n ∈ Finset.Icc 1 ⌈t ^ 2⌉₊, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ := h
        _ ≤ 4050 * (1 + Real.log t) + 4 := add_le_add hdir hsub
    -- 4050(1+log t)+4 ≤ 8104 log t
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ 4050 * (1 + Real.log t) + 4 := hcombine
      _ ≤ 8104 * Real.log t := by linarith only [hlogt1]

/-! ## THE COMPOSE — the first power zero-free region -/

/-- **THE POWER ZERO-FREE REGION.**  `zeta_zero_free_region_pow_of_growth` applied to the
machine-checked strip growth `zeta_growth_pow`: an explicit `c > 0`, `T₀` with every ζ-zero `ρ`
of height `|Im ρ| ≥ T₀` obeying `Re ρ ≤ 1 − c/((log|Im ρ|)^{3/4}(log log|Im ρ|)³)` — the **power**
shape `θ = 3/4 < 1`. -/
theorem zeta_zero_free_region_pow :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c / ((Real.log |ρ.im|) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log |ρ.im|)) ^ (3 : ℕ)) :=
  zeta_zero_free_region_pow_of_growth zeta_growth_pow

end Salt.Vk
