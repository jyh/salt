/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.BandRows

/-!
# G-BANDROWS-2 — the crumb tower close at the operating conductor (A₃, deliverable 2)

`BandClose2.gold_hSum_geo_band` routes the box crumb `goldBtailMinSlot` and the band crumb
`goldBandBtailSlot` through the additive tail slots `htail` / `hbandtail`.  This file discharges
those slots — the flagged **(D) tower close** — at the operating conductor
`D := opD N ≈ N^{1/2−9/100000}`, `bnd := QR·opDlev ≲ N^{1/2}`.

## The deficit-exponent estimate (why the sum is small)

Both per-box conversions (`BandPrice2.gold_btail_slot_firing_le`,
`Surv.gold_band_btail_slot_firing_le`) bound a crumb, on the firing branch, by
`2·(2·B²/Q·(1+log bnd) + 2·B·bnd)` with `B := D·L^{18}`, `L := log((2^{i+1}−1)·pieceM k')`.  On the
`O(L²)` boxes (`≤ 3` per `(k',k)` cell — `dyadicBoundary_card_le_three`; `(Nat.log 2 N + 1)²` cells)
we have the UNIFORM box-scale bound `L ≤ 3·log N` (`X·M ≤ N·2N ≤ N³`), so `B ≤ D·(3 log N)^{18}`,
against the conductor,

* `B² ≤ N^{1−177/10⁶}·polylog`  (the `(D·L^{18})²` head), and
* `B·bnd ≤ N^{1−89/10⁶}·polylog`  (the `(D·L^{18})·bnd` head, the DOMINANT deficit).

Multiplying by the `O((log N)²)` box count and one power of `log N` from the `(1+log bnd)` factor
keeps a genuine deficit `N^{−88/10⁶}`; the tower `log N ≥ 2·10⁹` makes `N^{88/10⁶}` dwarf every
polylog, so the whole sum is `≤ 96·Kc·N/(log N)^{11}` (per leg, `Kc ≥ 1`).  The polylog-vs-power
close is `a12_logpow_le_rpow` at exponent `80`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Goldbach

open Finset
open scoped BigOperators
open Salt.Chen

/-! ## 0. The shared triple-sum deficit engine -/

set_option maxHeartbeats 1600000 in
-- The deficit engine elaborates a long rpow/sqrt-bearing bound chain (the polylog-kill toolkit, the
-- per-box `L ≤ 3 log N` reduction, and the triple-sum count) above the default heartbeat budget.
/-- **`gold_crumb_triple_tower`.**  The deficit engine.  Given a slot `slot k' i` bounded per box by
the firing RHS `2·(2·(D·L^{18})²/Q·(1+log bnd) + 2·(D·L^{18})·bnd)` and the conductor scales
`D ≤ N^{1/2−9/100000}`, `bnd ≤ N^{1/2}`, the annulus/survivor triple sum over
`dyadicBoundary (Ne k') (pieceM k') …` is `≤ 96·Kc·N/(log N)^{11}` (`Kc ≥ 1`).  Carrier
`Ne`-agnostic (box/low `pieceN k'`, sym `max (opY N) (pieceN k')`). -/
theorem gold_crumb_triple_tower :
    ∃ x₁ : ℕ, ∀ (N : ℕ), x₁ ≤ N →
      ∀ (D Q K : ℕ) (bnd Kc : ℝ) (Ne : ℕ → ℕ) (slot : ℕ → ℕ → ℝ),
        1 ≤ Q → 1 ≤ bnd → 1 ≤ Kc →
        (D : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) →
        bnd ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
        (∀ k', pieceM k' ≤ 2 * (Ne k' + 1)) →
        (∀ k' i, slot k' i ≤ 2 * (2 * ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ)
              * (pieceM k' : ℝ))) ^ ((13 : ℝ) + 5)) ^ 2 / Q * (1 + Real.log bnd)
            + 2 * ((D : ℝ) * (Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)))
              ^ ((13 : ℝ) + 5)) * bnd)) →
        (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
              (opZ N * opY N) K, slot k' i)
          ≤ 96 * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  obtain ⟨xt, ht⟩ := a12_log_ge 10
  obtain ⟨xpk, hpkfun⟩ := a12_logpow_le_rpow 80 (1 / 1000000) (by norm_num) (by norm_num)
  refine ⟨max (max xt xpk) 2, fun N hN D Q K bnd Kc Ne slot hQ1 hbnd1 hKc1 hD hbnd hMcard hfire =>
    ?_⟩
  have hxt : xt ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hxpk : xpk ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨_, hlog10⟩ := ht N hxt
  have hpk80 : (Real.log N) ^ (80 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 1000000) := hpkfun N hxpk
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlog0 : (0 : ℝ) ≤ Real.log N := by linarith [hlog10]
  have hlog1 : (1 : ℝ) ≤ Real.log N := by linarith [hlog10]
  have hlog2 : (2 : ℝ) ≤ Real.log N := by linarith [hlog10]
  have hlog3 : (3 : ℝ) ≤ Real.log N := by linarith [hlog10]
  have hlogpos : (0 : ℝ) < Real.log N := by linarith
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
  have hlogbnd0 : (0 : ℝ) ≤ Real.log bnd := Real.log_nonneg hbnd1
  have hbnd0 : (0 : ℝ) ≤ bnd := by linarith
  have h1logbnd : (0 : ℝ) ≤ 1 + Real.log bnd := by linarith
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := by positivity
  set ε : ℝ := (1 : ℝ) / 1000000 with hεdef
  -- ============ polylog-kill toolkit ============
  have h3lelogsq : 3 * Real.log N ≤ (Real.log N) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two]
    nlinarith [hlog3, hlog0]
  have hlogpk : ∀ E : ℝ, 0 ≤ E → E ≤ 80 → (Real.log N) ^ E ≤ (N : ℝ) ^ ε := by
    intro E _ hE80
    exact le_trans (Real.rpow_le_rpow_of_exponent_le hlog1 hE80) hpk80
  have h3logpk : ∀ E : ℝ, 0 ≤ E → E ≤ 40 → (3 * Real.log N) ^ E ≤ (N : ℝ) ^ ε := by
    intro E hE0 hE40
    have h3nn : (0 : ℝ) ≤ 3 * Real.log N := by linarith
    calc (3 * Real.log N) ^ E ≤ ((Real.log N) ^ (2 : ℝ)) ^ E :=
          Real.rpow_le_rpow h3nn h3lelogsq hE0
      _ = (Real.log N) ^ (2 * E) := (Real.rpow_mul hlog0 2 E).symm
      _ ≤ (N : ℝ) ^ ε := hlogpk (2 * E) (by linarith) (by linarith)
  -- ============ the uniform per-box max crumb ============
  set Lmax : ℝ := 3 * Real.log N with hLmaxdef
  have hLmax_nn : (0 : ℝ) ≤ Lmax := by rw [hLmaxdef]; linarith
  set Bmax : ℝ := (D : ℝ) * Lmax ^ ((13 : ℝ) + 5) with hBmaxdef
  have hLmaxpow_nn : (0 : ℝ) ≤ Lmax ^ ((13 : ℝ) + 5) := Real.rpow_nonneg hLmax_nn _
  have hBmax_nn : (0 : ℝ) ≤ Bmax := by rw [hBmaxdef]; positivity
  set RHSmax : ℝ := 2 * (2 * Bmax ^ 2 / Q * (1 + Real.log bnd) + 2 * Bmax * bnd) with hRHSmaxdef
  have hRHSmax_nn : (0 : ℝ) ≤ RHSmax := by
    rw [hRHSmaxdef]
    have t1 : (0 : ℝ) ≤ 2 * Bmax ^ 2 / Q * (1 + Real.log bnd) := by positivity
    have t2 : (0 : ℝ) ≤ 2 * Bmax * bnd := by positivity
    linarith
  have hslot_max : ∀ k' ∈ Finset.range (Nat.log 2 N + 1), ∀ k ∈ Finset.range (Nat.log 2 N + 1),
      ∀ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
      slot k' i ≤ RHSmax := by
    intro k' hk' k _ i hi
    have hk'le : k' ≤ Nat.log 2 N := by rw [Finset.mem_range] at hk'; omega
    set L : ℝ := Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ)) with hLdef
    set B : ℝ := (D : ℝ) * L ^ ((13 : ℝ) + 5) with hBdef
    -- L ≤ Lmax  (from `X·M ≤ N³`)
    have hmem := hi
    rw [dyadicBoundary, Finset.mem_filter] at hmem
    have hcorner : 2 ^ i * (Ne k' + 1) ≤ goldCut N (k + 1) := hmem.2.1
    have hgchalf : goldCut N (k + 1) ≤ N / 2 := goldCut_le_half N (k + 1)
    have hmul : 2 ^ i ≤ 2 ^ i * (Ne k' + 1) :=
      le_mul_of_one_le_right (Nat.zero_le _) (by omega)
    have h2i : 2 ^ i ≤ N / 2 := by omega
    have hpow : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    have hXnat : (2 ^ (i + 1) - 1 : ℕ) ≤ N := by omega
    have hMk : (2 : ℕ) ^ k' ≤ N :=
      le_trans (Nat.pow_le_pow_right (by norm_num) hk'le) (Nat.pow_log_le_self 2 (by omega))
    have hMnat : pieceM k' ≤ 2 * N := by have := pieceM_le_two_pow k'; omega
    have hX1nat : (1 : ℕ) ≤ 2 ^ (i + 1) - 1 := by
      have : (2 : ℕ) ≤ 2 ^ (i + 1) := by
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hM1nat : (1 : ℕ) ≤ pieceM k' :=
      le_trans (Nat.one_le_pow _ _ (by norm_num)) (two_pow_le_pieceM k')
    have hXR : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hXnat
    have hMR : (pieceM k' : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hMnat
    have hXR1 : (1 : ℝ) ≤ ((2 ^ (i + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast hX1nat
    have hMR1 : (1 : ℝ) ≤ (pieceM k' : ℝ) := by exact_mod_cast hM1nat
    have hXMpos : (0 : ℝ) < ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) := by positivity
    have hXM_le : ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) ≤ (N : ℝ) ^ 3 := by
      calc ((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ) ≤ (N : ℝ) * (2 * (N : ℝ)) :=
            mul_le_mul hXR hMR (by positivity) (by positivity)
        _ = 2 * (N : ℝ) ^ 2 := by ring
        _ ≤ (N : ℝ) ^ 3 := by nlinarith [hN2R, sq_nonneg (N : ℝ)]
    have hLle : L ≤ Lmax := by
      rw [hLdef, hLmaxdef]
      calc Real.log (((2 ^ (i + 1) - 1 : ℕ) : ℝ) * (pieceM k' : ℝ))
          ≤ Real.log ((N : ℝ) ^ 3) := Real.log_le_log hXMpos hXM_le
        _ = 3 * Real.log N := by rw [Real.log_pow]; push_cast; ring
    have hL0 : (0 : ℝ) ≤ L := by
      rw [hLdef]; exact Real.log_nonneg (by nlinarith [hXR1, hMR1])
    have hLpow_le : L ^ ((13 : ℝ) + 5) ≤ Lmax ^ ((13 : ℝ) + 5) :=
      Real.rpow_le_rpow hL0 hLle (by norm_num)
    have hB_le : B ≤ Bmax := by
      rw [hBdef, hBmaxdef]; exact mul_le_mul_of_nonneg_left hLpow_le hDnn
    have hB_nn : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
    have hB2 : B ^ 2 ≤ Bmax ^ 2 := by nlinarith [hB_le, hB_nn, hBmax_nn]
    have hdiv : 2 * B ^ 2 / (Q : ℝ) ≤ 2 * Bmax ^ 2 / (Q : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith [hB2]) (by positivity)
    have hterm1 : 2 * B ^ 2 / Q * (1 + Real.log bnd) ≤ 2 * Bmax ^ 2 / Q * (1 + Real.log bnd) :=
      mul_le_mul_of_nonneg_right hdiv h1logbnd
    have hterm2 : 2 * B * bnd ≤ 2 * Bmax * bnd :=
      mul_le_mul_of_nonneg_right (by linarith [hB_le]) hbnd0
    have hRHS_mono : 2 * (2 * B ^ 2 / Q * (1 + Real.log bnd) + 2 * B * bnd) ≤ RHSmax := by
      rw [hRHSmaxdef]; linarith [hterm1, hterm2]
    have hf := hfire k' i
    rw [← hLdef, ← hBdef] at hf
    exact le_trans hf hRHS_mono
  -- ============ count reduction: triple sum ≤ cR·(cR·(3·RHSmax)) ============
  set c : ℕ := Nat.log 2 N + 1 with hcdef
  have hcR : ((c : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have := nat_log2_count_le hN2 hlog2
    rw [hcdef]; push_cast; linarith
  have hcR_nn : (0 : ℝ) ≤ ((c : ℕ) : ℝ) := by positivity
  have hinner : ∀ k' ∈ Finset.range c, ∀ k ∈ Finset.range c,
      (∑ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
          (opZ N * opY N) K, slot k' i) ≤ 3 * RHSmax := by
    intro k' hk' k hk
    have hcard : (dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
        (opZ N * opY N) K).card ≤ 3 :=
      dyadicBoundary_card_le_three (hMcard k') (goldCut_succ_le_two_mul N k)
    calc (∑ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
              (opZ N * opY N) K, slot k' i)
        ≤ ∑ _i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
              (opZ N * opY N) K, RHSmax :=
          Finset.sum_le_sum (fun i hi => hslot_max k' hk' k hk i hi)
      _ = (dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
              (opZ N * opY N) K).card • RHSmax := Finset.sum_const _
      _ = ((dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
              (opZ N * opY N) K).card : ℝ) * RHSmax := nsmul_eq_mul _ _
      _ ≤ 3 * RHSmax := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hRHSmax_nn
  have hmid : ∀ k' ∈ Finset.range c,
      (∑ k ∈ Finset.range c, ∑ i ∈ dyadicBoundary (Ne k') (pieceM k')
          (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, slot k' i)
        ≤ ((c : ℕ) : ℝ) * (3 * RHSmax) := by
    intro k' hk'
    calc (∑ k ∈ Finset.range c, ∑ i ∈ dyadicBoundary (Ne k') (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, slot k' i)
        ≤ ∑ _k ∈ Finset.range c, 3 * RHSmax :=
          Finset.sum_le_sum (fun k hk => hinner k' hk' k hk)
      _ = ((c : ℕ) : ℝ) * (3 * RHSmax) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htriple : (∑ k' ∈ Finset.range c, ∑ k ∈ Finset.range c,
        ∑ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
          (opZ N * opY N) K, slot k' i)
      ≤ ((c : ℕ) : ℝ) * (((c : ℕ) : ℝ) * (3 * RHSmax)) := by
    calc (∑ k' ∈ Finset.range c, ∑ k ∈ Finset.range c,
            ∑ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
              (opZ N * opY N) K, slot k' i)
        ≤ ∑ _k' ∈ Finset.range c, ((c : ℕ) : ℝ) * (3 * RHSmax) := Finset.sum_le_sum hmid
      _ = ((c : ℕ) : ℝ) * (((c : ℕ) : ℝ) * (3 * RHSmax)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- ============ the numeric deficit ============
  set a : ℝ := (1 : ℝ) / 2 - 9 / 100000 with hadef
  have hLmax18 : Lmax ^ ((13 : ℝ) + 5) ≤ (N : ℝ) ^ ε := by
    have := h3logpk ((13 : ℝ) + 5) (by norm_num) (by norm_num)
    rwa [hLmaxdef] at this
  have hae_nn : (0 : ℝ) ≤ (N : ℝ) ^ (a + ε) := Real.rpow_nonneg hNpos.le _
  have hBmax_ub : Bmax ≤ (N : ℝ) ^ (a + ε) := by
    rw [hBmaxdef]
    calc (D : ℝ) * Lmax ^ ((13 : ℝ) + 5) ≤ (N : ℝ) ^ a * (N : ℝ) ^ ε :=
          mul_le_mul hD hLmax18 hLmaxpow_nn (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (a + ε) := (Real.rpow_add hNpos _ _).symm
  have hBmaxsq_ub : Bmax ^ 2 ≤ (N : ℝ) ^ (2 * (a + ε)) := by
    calc Bmax ^ 2 ≤ ((N : ℝ) ^ (a + ε)) ^ 2 := by nlinarith [hBmax_ub, hBmax_nn, hae_nn]
      _ = (N : ℝ) ^ (2 * (a + ε)) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (a + ε)) 2, ← Real.rpow_mul hNpos.le]
          congr 1; push_cast; ring
  have h1logbnd_ub : 1 + Real.log bnd ≤ (N : ℝ) ^ ε := by
    have hlbnd : Real.log bnd ≤ (1 / 2) * Real.log N := by
      have := Real.log_le_log (by linarith) hbnd
      rwa [Real.log_rpow hNpos] at this
    calc 1 + Real.log bnd ≤ 3 * Real.log N := by linarith [hlbnd, hlog3]
      _ = (3 * Real.log N) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ ε := h3logpk 1 (by norm_num) (by norm_num)
  have hterm1_ub : 2 * Bmax ^ 2 / Q * (1 + Real.log bnd) ≤ 2 * (N : ℝ) ^ (2 * (a + ε) + ε) := by
    have hstep1 : 2 * Bmax ^ 2 / Q ≤ 2 * Bmax ^ 2 :=
      div_le_self (by positivity) hQ1R
    calc 2 * Bmax ^ 2 / Q * (1 + Real.log bnd)
        ≤ 2 * Bmax ^ 2 * (1 + Real.log bnd) := mul_le_mul_of_nonneg_right hstep1 h1logbnd
      _ ≤ 2 * (N : ℝ) ^ (2 * (a + ε)) * (N : ℝ) ^ ε :=
          mul_le_mul (by linarith [hBmaxsq_ub]) h1logbnd_ub h1logbnd (by positivity)
      _ = 2 * (N : ℝ) ^ (2 * (a + ε) + ε) := by rw [Real.rpow_add hNpos]; ring
  have hterm2_ub : 2 * Bmax * bnd ≤ 2 * (N : ℝ) ^ ((a + ε) + 1 / 2) := by
    calc 2 * Bmax * bnd ≤ 2 * (N : ℝ) ^ (a + ε) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul (by linarith [hBmax_ub]) hbnd hbnd0 (by positivity)
      _ = 2 * (N : ℝ) ^ ((a + ε) + 1 / 2) := by rw [Real.rpow_add hNpos (a + ε) (1 / 2)]; ring
  have hexp1 : 2 * (a + ε) + ε ≤ (1 : ℝ) - 89 / 1000000 := by rw [hadef, hεdef]; norm_num
  have hexp2 : (a + ε) + 1 / 2 ≤ (1 : ℝ) - 89 / 1000000 := by rw [hadef, hεdef]; norm_num
  have hpow1 : (N : ℝ) ^ (2 * (a + ε) + ε) ≤ (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000) :=
    Real.rpow_le_rpow_of_exponent_le hN1R hexp1
  have hpow2 : (N : ℝ) ^ ((a + ε) + 1 / 2) ≤ (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000) :=
    Real.rpow_le_rpow_of_exponent_le hN1R hexp2
  have hRHSmax_ub : RHSmax ≤ 8 * (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000) := by
    rw [hRHSmaxdef]
    have h1 : 2 * (N : ℝ) ^ (2 * (a + ε) + ε) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000) := by
      linarith [hpow1]
    have h2 : 2 * (N : ℝ) ^ ((a + ε) + 1 / 2) ≤ 2 * (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000) := by
      linarith [hpow2]
    linarith [hterm1_ub, hterm2_ub, h1, h2]
  have hcR2 : ((c : ℕ) : ℝ) * ((c : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ ε := by
    have hsq : ((c : ℕ) : ℝ) * ((c : ℕ) : ℝ) ≤ (2 * Real.log N) * (2 * Real.log N) :=
      mul_le_mul hcR hcR hcR_nn (by linarith [hcR, hcR_nn])
    have hlp := hlogpk 2 (by norm_num) (by norm_num)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_two] at hlp
    nlinarith [hsq, hlp]
  have htriple_ub : ((c : ℕ) : ℝ) * (((c : ℕ) : ℝ) * (3 * RHSmax))
      ≤ 96 * (N : ℝ) ^ ((1 : ℝ) - 88 / 1000000) := by
    have hstep : ((c : ℕ) : ℝ) * (((c : ℕ) : ℝ) * (3 * RHSmax))
        = 3 * (((c : ℕ) : ℝ) * ((c : ℕ) : ℝ)) * RHSmax := by ring
    rw [hstep]
    calc 3 * (((c : ℕ) : ℝ) * ((c : ℕ) : ℝ)) * RHSmax
        ≤ 3 * (4 * (N : ℝ) ^ ε) * (8 * (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000)) :=
          mul_le_mul (by linarith [hcR2]) hRHSmax_ub hRHSmax_nn (by positivity)
      _ = 96 * ((N : ℝ) ^ ε * (N : ℝ) ^ ((1 : ℝ) - 89 / 1000000)) := by ring
      _ = 96 * (N : ℝ) ^ (ε + ((1 : ℝ) - 89 / 1000000)) := by rw [Real.rpow_add hNpos]
      _ = 96 * (N : ℝ) ^ ((1 : ℝ) - 88 / 1000000) := by
          rw [show ε + ((1 : ℝ) - 89 / 1000000) = (1 : ℝ) - 88 / 1000000 from by
            rw [hεdef]; norm_num]
  -- final: SUM ≤ 96·N^{1−88/10⁶} ≤ 96·Kc·N/(log N)^11
  have hlog11pos : (0 : ℝ) < (Real.log N) ^ 11 := by positivity
  rw [le_div_iff₀ hlog11pos]
  have hlog11_ub : (Real.log N) ^ 11 ≤ (N : ℝ) ^ ε := by
    have h := hlogpk ((11 : ℕ) : ℝ) (by norm_num) (by norm_num)
    rwa [Real.rpow_natCast] at h
  calc (∑ k' ∈ Finset.range c, ∑ k ∈ Finset.range c,
          ∑ i ∈ dyadicBoundary (Ne k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
            (opZ N * opY N) K, slot k' i) * (Real.log N) ^ 11
      ≤ (96 * (N : ℝ) ^ ((1 : ℝ) - 88 / 1000000)) * (Real.log N) ^ 11 :=
        mul_le_mul_of_nonneg_right (le_trans htriple htriple_ub) hlog11pos.le
    _ ≤ (96 * (N : ℝ) ^ ((1 : ℝ) - 88 / 1000000)) * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hlog11_ub (by positivity)
    _ = 96 * (N : ℝ) ^ (((1 : ℝ) - 88 / 1000000) + ε) := by rw [Real.rpow_add hNpos]; ring
    _ ≤ 96 * (N : ℝ) ^ (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le hN1R; rw [hεdef]; norm_num
    _ = 96 * (N : ℝ) := by rw [Real.rpow_one]
    _ ≤ 96 * Kc * (N : ℝ) := by nlinarith [hKc1, hNpos.le]

/-! ## 1. The two crumb legs (the terminal's `htail` / `hbandtail` slots) -/

/-- **`gold_box_crumb_tower`.**  The box crumb tower close — the `htail` slot of `gold_hSum_geo` /
`gold_hSum_geo_band`.  `Σ_{k',k,i} goldBtailMinSlot N D Q bnd k' i ≤ 96·Kc·N/(log N)^{11}` at the
conductor `D ≤ N^{1/2−9/100000}`, `bnd ≤ N^{1/2}`. -/
theorem gold_box_crumb_tower :
    ∃ x₁ : ℕ, ∀ (N : ℕ), x₁ ≤ N → ∀ (D Q K : ℕ) (bnd Kc : ℝ),
      1 ≤ Q → 1 ≤ bnd → 1 ≤ Kc →
      (D : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) → bnd ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
      (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
            (opZ N * opY N) K, goldBtailMinSlot N D Q bnd k' i)
        ≤ 96 * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  obtain ⟨x₁, h⟩ := gold_crumb_triple_tower
  refine ⟨x₁, fun N hN D Q K bnd Kc hQ1 hbnd1 hKc1 hD hbnd => ?_⟩
  have hMcard : ∀ k', pieceM k' ≤ 2 * (pieceN k' + 1) := by
    intro k'
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  exact h N hN D Q K bnd Kc (fun k' => pieceN k') (fun k' i => goldBtailMinSlot N D Q bnd k' i)
    hQ1 hbnd1 hKc1 hD hbnd hMcard (fun k' i => gold_btail_slot_firing_le k' i hQ1 hbnd1)

/-- **`gold_band_crumb_tower`.**  The band crumb tower close — the `hbandtail` slot of
`gold_hSum_geo_band`.  The routed `(1/2)·Σ sym + Σ low ≤ 144·Kc·N/(log N)^{11}` (sym on
`dyadicBoundary (max (opY N) (pieceN k')) …`, low on `dyadicBoundary (pieceN k') …`). -/
theorem gold_band_crumb_tower :
    ∃ x₁ : ℕ, ∀ (N : ℕ), x₁ ≤ N → ∀ (D Q K : ℕ) (bnd Kc : ℝ),
      1 ≤ Q → 1 ≤ bnd → 1 ≤ Kc →
      (D : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) → bnd ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
      (1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, goldBandBtailSlot D Q bnd k' i)
        + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
            ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
              (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, goldBandBtailSlot D Q bnd k' i)
        ≤ 144 * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  obtain ⟨x₁, h⟩ := gold_crumb_triple_tower
  refine ⟨x₁, fun N hN D Q K bnd Kc hQ1 hbnd1 hKc1 hD hbnd => ?_⟩
  have hMlow : ∀ k', pieceM k' ≤ 2 * (pieceN k' + 1) := by
    intro k'
    have h1 : (1 : ℕ) ≤ 2 ^ k' := Nat.one_le_pow _ _ (by norm_num)
    have h2 : (2 : ℕ) ^ (k' + 1) = 2 * 2 ^ k' := by rw [pow_succ]; ring
    unfold pieceM pieceN; omega
  have hMsym : ∀ k', pieceM k' ≤ 2 * (max (opY N) (pieceN k') + 1) := by
    intro k'
    have hl := hMlow k'
    have hle : pieceN k' ≤ max (opY N) (pieceN k') := le_max_right _ _
    omega
  have hlow := h N hN D Q K bnd Kc (fun k' => pieceN k')
    (fun k' i => goldBandBtailSlot D Q bnd k' i) hQ1 hbnd1 hKc1 hD hbnd hMlow
    (fun k' i => gold_band_btail_slot_firing_le k' i hQ1 hbnd1)
  have hsym := h N hN D Q K bnd Kc (fun k' => max (opY N) (pieceN k'))
    (fun k' i => goldBandBtailSlot D Q bnd k' i) hQ1 hbnd1 hKc1 hD hbnd hMsym
    (fun k' i => gold_band_btail_slot_firing_le k' i hQ1 hbnd1)
  have hhalf : (1 / 2 : ℝ) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1),
        ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
            (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, goldBandBtailSlot D Q bnd k' i)
      ≤ (1 / 2) * (96 * Kc * (N : ℝ) / (Real.log N) ^ 11) :=
    mul_le_mul_of_nonneg_left hsym (by norm_num)
  have harith : (1 / 2 : ℝ) * (96 * Kc * (N : ℝ) / (Real.log N) ^ 11)
      + 96 * Kc * (N : ℝ) / (Real.log N) ^ 11 = 144 * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
    ring
  linarith [hlow, hhalf, harith]

/-- **`gold_crumb_tower_close`.**  The full **(D) tower close**: the box crumb sum PLUS the routed
band crumb sum is `≤ Ctail_total·Kc·N/(log N)^{11}` with `Ctail_total := 240`, at the conductor
`D ≤ N^{1/2−9/100000}`, `bnd ≤ N^{1/2}`.  Composes `gold_box_crumb_tower` (`htail`, `96`) with
`gold_band_crumb_tower` (`hbandtail`, `144`) — the two `gold_hSum_geo_band` inputs, discharged. -/
theorem gold_crumb_tower_close :
    ∃ x₁ : ℕ, ∀ (N : ℕ), x₁ ≤ N → ∀ (D Q K : ℕ) (bnd Kc : ℝ),
      1 ≤ Q → 1 ≤ bnd → 1 ≤ Kc →
      (D : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 9 / 100000) → bnd ≤ (N : ℝ) ^ ((1 : ℝ) / 2) →
      (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
          ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k') (goldCut N k) (goldCut N (k + 1))
            (opZ N * opY N) K, goldBtailMinSlot N D Q bnd k' i)
        + ((1 / 2) * (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (max (opY N) (pieceN k')) (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K, goldBandBtailSlot D Q bnd k' i)
          + (∑ k' ∈ Finset.range (Nat.log 2 N + 1), ∑ k ∈ Finset.range (Nat.log 2 N + 1),
              ∑ i ∈ dyadicBoundary (pieceN k') (pieceM k')
                (goldCut N k) (goldCut N (k + 1)) (opZ N * opY N) K,
                goldBandBtailSlot D Q bnd k' i))
        ≤ 240 * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
  obtain ⟨xb, hb⟩ := gold_box_crumb_tower
  obtain ⟨xd, hd⟩ := gold_band_crumb_tower
  refine ⟨max xb xd, fun N hN D Q K bnd Kc hQ1 hbnd1 hKc1 hD hbnd => ?_⟩
  have hNb : xb ≤ N := le_trans (le_max_left _ _) hN
  have hNd : xd ≤ N := le_trans (le_max_right _ _) hN
  have h1 := hb N hNb D Q K bnd Kc hQ1 hbnd1 hKc1 hD hbnd
  have h2 := hd N hNd D Q K bnd Kc hQ1 hbnd1 hKc1 hD hbnd
  have hsum : (96 : ℝ) * Kc * (N : ℝ) / (Real.log N) ^ 11
      + 144 * Kc * (N : ℝ) / (Real.log N) ^ 11 = 240 * Kc * (N : ℝ) / (Real.log N) ^ 11 := by
    ring
  linarith [h1, h2, hsum]

end Salt.Goldbach
