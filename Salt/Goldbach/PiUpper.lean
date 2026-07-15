/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Count

/-!
# G-PIUPPER — the sharp per-pair `π`-upper count on the non-dyadic Goldbach interval

Design: `docs/exploration/q1-design.md`, node **G-PIUPPER** (the dyadic-tear re-cut of G-COUNT,
`docs/exploration/pilot.md` 2026-07-15 ~17:00).  The landed reduction `goldCard_le_pairSum`
(`Salt/Goldbach/Count.lean`) prices the Goldbach triple carriers by
`Σ_{q ∈ pairSet'} primeCountIoc y (Lfun N q)` — a count over the **non-dyadic** interval
`(y, M]` with `M = Lfun N q = ⌊N/(2p₁p₂)⌋`.  The twin's crude engine `prime_count_Ioc_le`
(`Salt/Chen/TripleCount.lean`) prices at the lower endpoint `L = y`, giving the weight
`1/log y` — over the sharp weight `1/logND = 1/log(N/p₁p₂)` by the region-dependent factor
`logND/log y = 3(1−β−σ) ∈ [1, 13/8]`.  A constant overshoot BREAKS the razor margin
`2log3 − log6 − c̄ ≈ 0.037` (`Salt/Chen/SwitchConstant.lean`); the overshoot must cost `o(1)`.

## The construction (dyadic decomposition + Abel summation)

Decompose `(y, M]` into the dyadic pieces `(⌊M/2^{k+1}⌋, ⌊M/2^k⌋]`, `k = 0 … K−1`, where
`K` is the first level with `⌊M/2^K⌋ ≤ y` (so the pieces cover `(y, M]` — going ALL the way
down to `y`, whose log `log y = ⅓ log N` keeps every piece's denominator `≥ log⌊y/2⌋ > 0`;
no negative-denominator split is needed, unlike a `√M`-threshold cut).  Price each piece by
`prime_count_Ioc_le` at its OWN lower endpoint `⌊M/2^{k+1}⌋`, whose log `≈ log M − (k+1)log 2`.

Writing `1/log dₖ₊₁ = 1/log M + (log M − log dₖ₊₁)/(log M · log dₖ₊₁)`, the leading part
telescopes EXACTLY to `(M − ⌊M/2^K⌋)/log M ≤ M/log M` (no floor slack), and the correction
part is controlled by the **Abel identity**

  `Σ_{k<K} (dₖ − dₖ₊₁)·(k+1) = (Σ_{k<K} dₖ) − K·d_K ≤ Σ_{k<K} dₖ ≤ 2M`,

using `log M − log dₖ₊₁ ≤ (k+1)·log 3` (each halving-with-floor loses `≤ log 3`).  The Abel
identity is what kills the additive remainder: the mass concentrates at the top piece and the
correction is a PURELY multiplicative `1 + O(1/log y)` factor — no `o(1)`-per-pair `+1/L₀`.

## What this file lands

`goldPerPair_pi_upper` : for `q ∈ pairSet' N z y` under the SATISFIABLE operating relation
`log N ≤ 3 log y + log z` (using the pairSet' bound `p₁ ≥ z`; at op `z ≈ N^{1/8}`, `y ≈ N^{1/3}`,
so the RHS has a `~⅛ log N` margin — unlike the old `log N ≤ 3 log y`, which fails for non-cube
`N`) and `y` past an explicit threshold,

  `primeCountIoc y (Lfun N q) ≤ (1 + C_K/log y)·(N/2)·1/(p₁p₂·logND N q)`,

with `C_K = 20 + 32 K` (`K` the unconditional PNT-error constant of `psiTot_pnt`) — an explicit
`1 + O(1/log y)` correction fitting the ledger's error budget.  This slots into G-COUNT-2's
`weightedPairSum'`-reduction (the Goldbach mirror of `tripleSum_le_weighted_pairSum'`), after
which `weightedPairSum'_le_cbar` (`Salt/Chen/CountFinal.lean`) is reused VERBATIM to the same
`c̄/2` leading constant.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen Salt.LS

namespace Salt.Goldbach

/-! ## Section 0 — the dyadic points and the telescoping of `primeCountIoc` -/

/-- The `k`-th dyadic point of `M`: `⌊M/2^k⌋`. -/
private def dpt (M k : ℕ) : ℕ := M / 2 ^ k

private lemma dpt_zero (M : ℕ) : dpt M 0 = M := by simp [dpt]

private lemma dpt_succ (M k : ℕ) : dpt M (k + 1) = dpt M k / 2 := by
  simp only [dpt, pow_succ]
  rw [Nat.div_div_eq_div_mul]

private lemma dpt_antitone (M k : ℕ) : dpt M (k + 1) ≤ dpt M k := by
  rw [dpt_succ]; exact Nat.div_le_self _ _

private lemma dpt_le (M k : ℕ) : dpt M k ≤ M := by
  simp only [dpt]; exact Nat.div_le_self M (2 ^ k)

/-- **The `primeCountIoc` split.**  For `L ≤ m ≤ U`,
`primeCountIoc L U = primeCountIoc L m + primeCountIoc m U`. -/
private lemma primeCountIoc_split {L m U : ℕ} (h1 : L ≤ m) (h2 : m ≤ U) :
    primeCountIoc L U = primeCountIoc L m + primeCountIoc m U := by
  have hdisj : Disjoint (Finset.Ioc L m) (Finset.Ioc m U) := by
    simp only [Finset.disjoint_left, Finset.mem_Ioc]; intro n hn hn2; omega
  simp only [primeCountIoc]
  rw [← Nat.cast_add, Nat.cast_inj, ← Finset.Ioc_union_Ioc_eq_Ioc h1 h2, Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]

/-- **The dyadic telescoping.**  `primeCountIoc (⌊M/2^K⌋) M = Σ_{k<K} primeCountIoc dₖ₊₁ dₖ`. -/
private lemma primeCountIoc_dpt_telescope (M K : ℕ) :
    primeCountIoc (dpt M K) M
      = ∑ k ∈ Finset.range K, primeCountIoc (dpt M (k + 1)) (dpt M k) := by
  induction K with
  | zero => simp [dpt_zero, primeCountIoc]
  | succ K ih =>
      rw [Finset.sum_range_succ, ← ih, primeCountIoc_split (dpt_antitone M K) (dpt_le M K)]
      ring

/-- Lowering the left endpoint only increases the prime count. -/
private lemma primeCountIoc_le_of_lower {a b U : ℕ} (h : a ≤ b) :
    primeCountIoc b U ≤ primeCountIoc a U := by
  simp only [primeCountIoc]
  exact_mod_cast Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_left h))

/-- **The count reduction.**  Whenever the `K`-th dyadic point `⌊M/2^K⌋ ≤ y`, the prime
count on `(y, M]` is at most the dyadic-piece sum. -/
private lemma primeCountIoc_y_le_dyadic {M K y : ℕ} (hKy : dpt M K ≤ y) :
    primeCountIoc y M ≤ ∑ k ∈ Finset.range K, primeCountIoc (dpt M (k + 1)) (dpt M k) := by
  rw [← primeCountIoc_dpt_telescope]
  exact primeCountIoc_le_of_lower hKy

/-! ## Section 1 — the arithmetic helpers (geometric mass, telescope, Abel, per-step log) -/

/-- The dyadic masses sum to `< 2M`: `Σ_{k<K} ⌊M/2^k⌋ ≤ 2M`. -/
private lemma dpt_sum_le (M K : ℕ) :
    ∑ k ∈ Finset.range K, (dpt M k : ℝ) ≤ 2 * M := by
  have hgeom : ∑ k ∈ Finset.range K, ((1 : ℝ) / 2) ^ k ≤ 2 := by
    have h : ∑ k ∈ Finset.range K, ((1 : ℝ) / 2) ^ k = 2 - 2 * ((1 : ℝ) / 2) ^ K := by
      rw [geom_sum_eq (by norm_num) K]; ring
    rw [h]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2) K]
  calc ∑ k ∈ Finset.range K, (dpt M k : ℝ)
      ≤ ∑ k ∈ Finset.range K, (M : ℝ) * ((1 : ℝ) / 2) ^ k := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        simp only [dpt]
        have h1 : ((M / 2 ^ k : ℕ) : ℝ) ≤ (M : ℝ) / (2 : ℝ) ^ k := by
          rw [show (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) by push_cast; ring]
          exact Nat.cast_div_le
        rw [div_pow, one_pow, mul_one_div]; exact h1
    _ = (M : ℝ) * ∑ k ∈ Finset.range K, ((1 : ℝ) / 2) ^ k := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * 2 := by
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 * M := by ring

/-- **The Abel summation identity.**  `Σ_{k<K}(f k − f(k+1))·(k+1) = (Σ_{k<K} f k) − K·f K`. -/
private lemma abel_sum (f : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, (f k - f (k + 1)) * ((k : ℝ) + 1)
      = (∑ k ∈ Finset.range K, f k) - (K : ℝ) * f K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]; push_cast; ring

/-- One halving-with-floor loses `≤ log 3` of the log (since `dₖ ≤ 3·dₖ₊₁` for `dₖ₊₁ ≥ 1`). -/
private lemma dpt_log_step {M j : ℕ} (h : 1 ≤ dpt M (j + 1)) :
    Real.log (dpt M j) - Real.log (dpt M (j + 1)) ≤ Real.log 3 := by
  have hh : 1 ≤ dpt M j / 2 := by rw [dpt_succ] at h; exact h
  have hjpos : (0 : ℝ) < (dpt M (j + 1) : ℝ) := by exact_mod_cast h
  have hjpos0 : (0 : ℝ) < (dpt M j : ℝ) :=
    lt_of_lt_of_le hjpos (by exact_mod_cast dpt_antitone M j)
  have hle : dpt M j ≤ 3 * dpt M (j + 1) := by rw [dpt_succ]; omega
  have hleR : (dpt M j : ℝ) ≤ 3 * (dpt M (j + 1) : ℝ) := by exact_mod_cast hle
  have hlog : Real.log (dpt M j) ≤ Real.log (3 * (dpt M (j + 1) : ℝ)) :=
    Real.log_le_log hjpos0 hleR
  rw [Real.log_mul (by norm_num) hjpos.ne'] at hlog
  linarith [hlog]

/-- **The telescoped log gap.**  `log M − log ⌊M/2^{k+1}⌋ ≤ (k+1)·log 3`. -/
private lemma dpt_log_gap (M : ℕ) : ∀ k, 1 ≤ dpt M (k + 1) →
    Real.log (dpt M 0) - Real.log (dpt M (k + 1)) ≤ ((k : ℝ) + 1) * Real.log 3 := by
  intro k
  induction k with
  | zero => intro h; have := dpt_log_step (M := M) (j := 0) h; push_cast; linarith [this]
  | succ k ih =>
      intro h
      have h1 : 1 ≤ dpt M (k + 1) := le_trans h (dpt_antitone M (k + 1))
      have hstep := dpt_log_step (M := M) (j := k + 1) h
      have hih := ih h1
      push_cast at hih ⊢
      linarith [hih, hstep]

/-- `dpt` is antitone in the level index. -/
private lemma dpt_anti_index {M a b : ℕ} (hab : a ≤ b) : dpt M b ≤ dpt M a := by
  simp only [dpt]
  refine (Nat.le_div_iff_mul_le (by positivity)).mpr ?_
  calc M / 2 ^ b * 2 ^ a
      ≤ M / 2 ^ b * 2 ^ b := Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_right (by norm_num) hab)
    _ ≤ M := Nat.div_mul_le_self M (2 ^ b)

/-! ## Section 2 — the per-piece bound and the dyadic-sum core -/

/-- **The per-piece bound.**  The crude-engine numerator on a piece `(b, a]`, divided by
`log b`, is bounded by the `1/log M`-leading term plus a correction weighted by `w ≥ log M − log b`
and a PNT-error term at the floor log `Ld3`.  (Abstract real form; `a = dₖ`, `b = dₖ₊₁`,
`LM = log M`, `Ld3 = log ⌊M/2^K⌋`, `w = (k+1)·log 3`.) -/
private lemma piece_le {Kp a b LM Ld3 w : ℝ}
    (hKp : 0 ≤ Kp) (hLd3pos : 0 < Ld3) (hb : Ld3 ≤ Real.log b) (ha : Ld3 ≤ Real.log a)
    (hLMpos : 0 < LM) (hab : b ≤ a) (hbpos : 0 < b) (hgap : LM - Real.log b ≤ w) (hw : 0 ≤ w) :
    (a - b + Kp * a / Real.log a + Kp * b / Real.log b) / Real.log b
      ≤ (a - b) / LM + (a - b) * w / (LM * Ld3) + Kp * (a + b) / Ld3 ^ 2 := by
  have hlogb_pos : 0 < Real.log b := lt_of_lt_of_le hLd3pos hb
  have hloga_pos : 0 < Real.log a := lt_of_lt_of_le hLd3pos ha
  have hab0 : 0 ≤ a - b := by linarith
  have hapos : 0 < a := lt_of_lt_of_le hbpos hab
  have hLd3sq : 0 < Ld3 ^ 2 := pow_pos hLd3pos 2
  -- scalar inverse bound: 1/log b ≤ 1/LM + w/(LM·Ld3)
  have e : 1 / Real.log b - 1 / LM = (LM - Real.log b) / (Real.log b * LM) := by field_simp
  have hcross : (LM - Real.log b) / (Real.log b * LM) ≤ w / (LM * Ld3) :=
    div_le_div₀ hw hgap (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hb hLMpos.le])
  have hinv : 1 / Real.log b ≤ 1 / LM + w / (LM * Ld3) := by
    rw [← e] at hcross; linarith [hcross]
  have hA : (a - b) / Real.log b ≤ (a - b) / LM + (a - b) * w / (LM * Ld3) := by
    calc (a - b) / Real.log b = (a - b) * (1 / Real.log b) := by rw [mul_one_div]
      _ ≤ (a - b) * (1 / LM + w / (LM * Ld3)) := mul_le_mul_of_nonneg_left hinv hab0
      _ = (a - b) / LM + (a - b) * w / (LM * Ld3) := by ring
  have hb1 : Kp * a / Real.log a / Real.log b ≤ Kp * a / Ld3 ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (mul_nonneg hKp hapos.le) hLd3sq
    nlinarith [mul_le_mul ha hb hLd3pos.le hloga_pos.le]
  have hb2 : Kp * b / Real.log b / Real.log b ≤ Kp * b / Ld3 ^ 2 := by
    rw [div_div]
    apply div_le_div_of_nonneg_left (mul_nonneg hKp hbpos.le) hLd3sq
    nlinarith [mul_le_mul hb hb hLd3pos.le hlogb_pos.le]
  rw [add_div, add_div]
  have hsum : Kp * a / Ld3 ^ 2 + Kp * b / Ld3 ^ 2 = Kp * (a + b) / Ld3 ^ 2 := by ring
  linarith [hA, hb1, hb2, hsum]

/-- **The dyadic-sum core.**  With `3 ≤ ⌊M/2^K⌋` (so every piece endpoint is `≥ 3`), the sum of
the dyadic-piece counts is bounded by the sharp leading `M/log M` plus two `O(1/log)` corrections:
the log-drift correction `2M·log3/(log M · log⌊M/2^K⌋)` and the PNT-error term
`4·Kp·M/log⌊M/2^K⌋²`.  The Abel identity (`abel_sum`) is what makes the drift correction purely
multiplicative — no additive per-piece slack survives. -/
private lemma dyadic_count_le {Kp : ℝ} (hK0 : 0 ≤ Kp)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ Kp * n / Real.log n)
    {M K : ℕ} (hK3 : 3 ≤ dpt M K) :
    ∑ k ∈ Finset.range K, primeCountIoc (dpt M (k + 1)) (dpt M k)
      ≤ (M : ℝ) / Real.log M
        + 2 * (M : ℝ) * Real.log 3 / (Real.log M * Real.log (dpt M K))
        + 4 * Kp * (M : ℝ) / Real.log (dpt M K) ^ 2 := by
  set Ld3 := Real.log (dpt M K) with hLd3def
  set LM := Real.log M with hLMdef
  have hd3_le_M : dpt M K ≤ M := dpt_le M K
  have hMgt1 : 1 < M := by omega
  have hd3gt1 : 1 < dpt M K := by omega
  have hLd3pos : 0 < Ld3 := by rw [hLd3def]; exact Real.log_pos (by exact_mod_cast hd3gt1)
  have hLMpos : 0 < LM := by rw [hLMdef]; exact Real.log_pos (by exact_mod_cast hMgt1)
  have hlog3nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  -- termwise bound via `piece_le`
  have hterm : ∀ k ∈ Finset.range K,
      primeCountIoc (dpt M (k + 1)) (dpt M k)
        ≤ ((dpt M k : ℝ) - dpt M (k + 1)) / LM
          + ((dpt M k : ℝ) - dpt M (k + 1)) * (((k : ℝ) + 1) * Real.log 3) / (LM * Ld3)
          + Kp * ((dpt M k : ℝ) + dpt M (k + 1)) / Ld3 ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hLk3 : 3 ≤ dpt M (k + 1) := le_trans hK3 (dpt_anti_index hk)
    have hLkU : dpt M (k + 1) ≤ dpt M k := dpt_antitone M k
    have hbpos : (0 : ℝ) < (dpt M (k + 1) : ℝ) := by exact_mod_cast (by omega : 0 < dpt M (k + 1))
    have hb : Ld3 ≤ Real.log (dpt M (k + 1) : ℝ) := by
      rw [hLd3def]
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < dpt M K))
        (by exact_mod_cast dpt_anti_index hk)
    have ha : Ld3 ≤ Real.log (dpt M k : ℝ) := by
      rw [hLd3def]
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < dpt M K))
        (by exact_mod_cast dpt_anti_index (le_of_lt hk))
    have hab : (dpt M (k + 1) : ℝ) ≤ (dpt M k : ℝ) := by exact_mod_cast hLkU
    have hgap : LM - Real.log (dpt M (k + 1) : ℝ) ≤ ((k : ℝ) + 1) * Real.log 3 := by
      have hg := dpt_log_gap M k (by omega)
      rw [dpt_zero] at hg; rw [hLMdef]; exact hg
    have hw : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.log 3 := by positivity
    have hraw := prime_count_Ioc_le hK0 hpsi hLk3 hLkU
    exact le_trans hraw (piece_le hK0 hLd3pos hb ha hLMpos hab hbpos hgap hw)
  -- sum the termwise bound and evaluate the three sums
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hgeom := dpt_sum_le M K
  -- S1 : telescoping leading sum
  have hS1 : ∑ k ∈ Finset.range K, ((dpt M k : ℝ) - dpt M (k + 1)) / LM ≤ (M : ℝ) / LM := by
    rw [← Finset.sum_div, Finset.sum_range_sub' (fun j => (dpt M j : ℝ)) K, dpt_zero,
      div_le_div_iff_of_pos_right hLMpos]
    linarith [Nat.cast_nonneg (α := ℝ) (dpt M K)]
  -- S2 : Abel-controlled drift sum
  have hS2 : ∑ k ∈ Finset.range K,
        ((dpt M k : ℝ) - dpt M (k + 1)) * (((k : ℝ) + 1) * Real.log 3) / (LM * Ld3)
      ≤ 2 * (M : ℝ) * Real.log 3 / (LM * Ld3) := by
    have hrw : ∑ k ∈ Finset.range K,
          ((dpt M k : ℝ) - dpt M (k + 1)) * (((k : ℝ) + 1) * Real.log 3) / (LM * Ld3)
        = (Real.log 3 / (LM * Ld3))
            * ∑ k ∈ Finset.range K, ((dpt M k : ℝ) - dpt M (k + 1)) * ((k : ℝ) + 1) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hrw, abel_sum (fun j => (dpt M j : ℝ)) K]
    have hcnn : (0 : ℝ) ≤ Real.log 3 / (LM * Ld3) := by positivity
    have hbnd : (∑ k ∈ Finset.range K, (dpt M k : ℝ)) - (K : ℝ) * (dpt M K : ℝ) ≤ 2 * M := by
      have : (0 : ℝ) ≤ (K : ℝ) * (dpt M K : ℝ) := by positivity
      linarith [hgeom]
    calc (Real.log 3 / (LM * Ld3))
            * ((∑ k ∈ Finset.range K, (dpt M k : ℝ)) - (K : ℝ) * (dpt M K : ℝ))
        ≤ (Real.log 3 / (LM * Ld3)) * (2 * M) := mul_le_mul_of_nonneg_left hbnd hcnn
      _ = 2 * (M : ℝ) * Real.log 3 / (LM * Ld3) := by ring
  -- S3 : PNT-error sum
  have hS3 : ∑ k ∈ Finset.range K, Kp * ((dpt M k : ℝ) + dpt M (k + 1)) / Ld3 ^ 2
      ≤ 4 * Kp * (M : ℝ) / Ld3 ^ 2 := by
    have hrw : ∑ k ∈ Finset.range K, Kp * ((dpt M k : ℝ) + dpt M (k + 1)) / Ld3 ^ 2
        = (Kp / Ld3 ^ 2)
            * ∑ k ∈ Finset.range K, ((dpt M k : ℝ) + dpt M (k + 1)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hrw]
    have hsucc : ∑ k ∈ Finset.range K, (dpt M (k + 1) : ℝ) ≤ ∑ k ∈ Finset.range K, (dpt M k : ℝ) :=
      Finset.sum_le_sum (fun k _ => by exact_mod_cast dpt_antitone M k)
    have hsplit : ∑ k ∈ Finset.range K, ((dpt M k : ℝ) + dpt M (k + 1))
        = (∑ k ∈ Finset.range K, (dpt M k : ℝ)) + ∑ k ∈ Finset.range K, (dpt M (k + 1) : ℝ) :=
      Finset.sum_add_distrib
    have hcnn : (0 : ℝ) ≤ Kp / Ld3 ^ 2 := by positivity
    calc (Kp / Ld3 ^ 2) * ∑ k ∈ Finset.range K, ((dpt M k : ℝ) + dpt M (k + 1))
        ≤ (Kp / Ld3 ^ 2) * (4 * M) := by
          apply mul_le_mul_of_nonneg_left ?_ hcnn
          rw [hsplit]; linarith [hgeom, hsucc]
      _ = 4 * Kp * (M : ℝ) / Ld3 ^ 2 := by ring
  linarith [hS1, hS2, hS3]

/-! ## Section 3 — the log/floor conversion and the keystone -/

/-- **The conversion.**  The dyadic bound (in `LM = log M`, `Ld3 = log⌊M/2^K⌋`) is repackaged
against the target weight `t/lN` (`t = N/(2p₁p₂)`, `lN = logND = log(N/p₁p₂)`) as the sharp
`(1 + C_K/log y)` multiple, using the floor-log lower bounds `log y ≤ 2·log M`, `log y ≤ 2·Ld3`
and the endpoint bounds `logND ≤ log M + 2log2`, `logND ≤ 2 log y`. -/
private lemma convert_final {Kp M3 LM Ld3 t lN ly P : ℝ}
    (hKp : 0 ≤ Kp) (hMt : M3 ≤ t) (hM3nn : 0 ≤ M3)
    (hLMpos : 0 < LM) (hLd3pos : 0 < Ld3) (hlypos : 0 < ly) (hNDpos : 0 < lN)
    (hLM_ge : ly ≤ 2 * LM) (hLd3_ge : ly ≤ 2 * Ld3)
    (hND_le_LM : lN ≤ LM + 2 * Real.log 2) (hND_le_ly : lN ≤ 2 * ly)
    (hP : P ≤ M3 / LM + 2 * M3 * Real.log 3 / (LM * Ld3) + 4 * Kp * M3 / Ld3 ^ 2) :
    P ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * Kp) / ly) * (t / lN) := by
  have htnn : 0 ≤ t := le_trans hM3nn hMt
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog3nn : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hly2 : ly ^ 2 ≤ 4 * Ld3 ^ 2 := by nlinarith [hLd3_ge, hlypos.le]
  have hlyLMLd3 : ly ^ 2 ≤ 4 * (LM * Ld3) := by nlinarith [hLM_ge, hLd3_ge, hlypos.le]
  -- T1 : the leading term
  have hT1 : M3 / LM ≤ t * (ly + 4 * Real.log 2) / (lN * ly) := by
    rw [div_le_div_iff₀ hLMpos (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg htnn hlog2nn) (by linarith [hLM_ge] : (0:ℝ) ≤ 2 * LM - ly),
      mul_nonneg (sub_nonneg.mpr hMt) (mul_nonneg hNDpos.le hlypos.le),
      mul_nonneg (mul_nonneg htnn hlypos.le)
        (by linarith [hND_le_LM] : (0:ℝ) ≤ LM + 2 * Real.log 2 - lN)]
  -- T2 : the log-drift correction
  have hT2 : 2 * M3 * Real.log 3 / (LM * Ld3) ≤ 16 * t * Real.log 3 / (lN * ly) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg htnn hlog3nn) hlypos.le)
        (by linarith [hND_le_ly] : (0:ℝ) ≤ 2 * ly - lN),
      mul_nonneg (mul_nonneg hlog3nn (sub_nonneg.mpr hMt)) (mul_nonneg hNDpos.le hlypos.le),
      mul_nonneg (mul_nonneg htnn hlog3nn)
        (by linarith [hlyLMLd3] : (0:ℝ) ≤ 4 * (LM * Ld3) - ly ^ 2), hlypos.le, hNDpos.le]
  -- T3 : the PNT-error correction
  have hT3 : 4 * Kp * M3 / Ld3 ^ 2 ≤ 32 * Kp * t / (lN * ly) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hKp htnn) hlypos.le)
        (by linarith [hND_le_ly] : (0:ℝ) ≤ 2 * ly - lN),
      mul_nonneg (mul_nonneg hKp (sub_nonneg.mpr hMt)) (mul_nonneg hNDpos.le hlypos.le),
      mul_nonneg (mul_nonneg hKp htnn)
        (by linarith [hly2] : (0:ℝ) ≤ 4 * Ld3 ^ 2 - ly ^ 2), hlypos.le, hNDpos.le]
  have hcombine : t * (ly + 4 * Real.log 2) / (lN * ly) + 16 * t * Real.log 3 / (lN * ly)
      + 32 * Kp * t / (lN * ly)
      = (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * Kp) / ly) * (t / lN) := by
    field_simp; ring
  linarith [hP, hT1, hT2, hT3, hcombine.ge, hcombine.le]

set_option maxHeartbeats 1200000 in
-- maxHeartbeats bump: this keystone chains the dyadic count reduction, the `dyadic_count_le`
-- sum core, and the log/floor conversion (`convert_final`, three nlinarith cross-multiplications)
-- in a single proof, so it exceeds the 200000 default.
set_option maxHeartbeats 1200000 in
/-- **G-PIUPPER — the sharp per-pair `π`-upper count.**  For an admissible Goldbach pair
`q = (p₁, p₂) ∈ pairSet' N z y`, under the SATISFIABLE operating relation `log N ≤ 3 log y + log z`
(derived through the pairSet' bound `p₁ ≥ z`; op-satisfiable since `z ≈ N^{1/8}` adds a `~⅛ log N`
margin) and `y ≥ 6`, the prime count on the non-dyadic Goldbach interval `(y, ⌊N/(2p₁p₂)⌋]` is
bounded by the sharp weight `(N/2)·1/(p₁p₂·logND)` up to the explicit `1 + O(1/log y)` factor

  `primeCountIoc y (Lfun N q) ≤ (1 + (4log2 + 16log3 + 32K)/log y)·(N/2)·1/(p₁p₂·logND N q)`,

`K` the unconditional PNT-error constant of `psiTot_pnt`.  This is the dyadic-tear fix: the
correction costs `o(1)`, NOT the `13/8` constant factor of crude `L = y` pricing. -/
theorem goldPerPair_pi_upper {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {N z y : ℕ} (hy : 6 ≤ y) (hlogNz : Real.log N ≤ 3 * Real.log y + Real.log z)
    {q : ℕ × ℕ} (hq : q ∈ pairSet' N z y) :
    primeCountIoc y (Lfun N q)
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y)
          * ((N : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logND N q)) := by
  rw [pairSet', Finset.mem_filter, Finset.mem_product] at hq
  obtain ⟨_, hz1, _hy1, hyq2, hsharp, hp1, hp2⟩ := hq
  have hp1pos : 0 < q.1 := hp1.pos
  have hp2pos : 0 < q.2 := hp2.pos
  have hq2ge : 2 ≤ q.2 := by omega
  -- q₁·q₂ < N  (from `q₁·q₂² ≤ N` and `q₂ ≥ 2`)
  have hq1q2_lt_N : q.1 * q.2 < N := by
    calc q.1 * q.2 < q.1 * q.2 * q.2 := by nlinarith [hp1pos, hp2pos, hq2ge]
      _ = q.1 * (q.2 * q.2) := by ring
      _ ≤ N := hsharp
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hq1q2_lt_N
  -- the target weight `logND N q = log(N/(q₁q₂)) > 0`
  have hq1q2R : (0 : ℝ) < (q.1 : ℝ) * q.2 := by positivity
  have hND1 : (1 : ℝ) < (N : ℝ) / ((q.1 : ℝ) * q.2) := by
    rw [lt_div_iff₀ hq1q2R, one_mul]; exact_mod_cast hq1q2_lt_N
  have hNDpos : 0 < logND N q := by rw [logND]; exact Real.log_pos hND1
  have hlypos : 0 < Real.log y := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hCnn : (0 : ℝ) ≤ 4 * Real.log 2 + 16 * Real.log 3 + 32 * K := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hcoefnn : (0 : ℝ) ≤ 1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y := by
    have : (0 : ℝ) ≤ (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y :=
      div_nonneg hCnn hlypos.le
    linarith
  set M := Lfun N q with hMdef
  -- trivial case: empty interval
  by_cases hMy : M ≤ y
  · have hempty : primeCountIoc y M = 0 := by
      simp only [primeCountIoc, Finset.Ioc_eq_empty (by omega : ¬ y < M), Finset.filter_empty,
        Finset.card_empty, Nat.cast_zero]
    rw [hempty]
    positivity
  -- main case: `y < M`
  rw [not_le] at hMy
  have hMgt3 : 3 ≤ M := by omega
  have hM3nn : (0 : ℝ) ≤ (M : ℝ) := by positivity
  -- the dyadic stopping level `J`
  have hex : ∃ k, dpt M k ≤ y :=
    ⟨M, by simp only [dpt]; rw [Nat.div_eq_of_lt (Nat.lt_two_pow_self)]; exact Nat.zero_le y⟩
  set J := Nat.find hex with hJdef
  have hJy : dpt M J ≤ y := Nat.find_spec hex
  have hJpos : 0 < J := by
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · exfalso; rw [h0, dpt_zero] at hJy; omega
    · exact hpos
  have hprev : y < dpt M (J - 1) := by
    have := Nat.find_min hex (show J - 1 < J by omega)
    omega
  have hJsucc : dpt M J = dpt M (J - 1) / 2 := by
    conv_lhs => rw [show J = (J - 1) + 1 by omega]
    exact dpt_succ M (J - 1)
  have hdptJ3 : 3 ≤ dpt M J := by rw [hJsucc]; omega
  have h2dptJ : y ≤ 2 * dpt M J := by rw [hJsucc]; omega
  -- `y ≤ (dpt M J)²`  (from `dpt M J ≥ 3` and `2·dpt M J ≥ y`)
  have hyle_nat : y ≤ dpt M J * dpt M J := by nlinarith [hdptJ3, h2dptJ]
  have hdptJ_le_M : dpt M J ≤ M := dpt_le M J
  -- real log facts feeding `convert_final`
  have hLd3pos : 0 < Real.log (dpt M J) := Real.log_pos (by exact_mod_cast (by omega : 1 < dpt M J))
  have hLMpos : 0 < Real.log M := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hLd3_ge : Real.log y ≤ 2 * Real.log (dpt M J) := by
    have hyleR : (y : ℝ) ≤ (dpt M J : ℝ) ^ 2 := by rw [pow_two]; exact_mod_cast hyle_nat
    have h1 : Real.log (y : ℝ) ≤ Real.log ((dpt M J : ℝ) ^ 2) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < y)) hyleR
    rw [Real.log_pow] at h1; push_cast at h1; linarith [h1]
  have hLM_ge : Real.log y ≤ 2 * Real.log M := by
    have : Real.log (dpt M J) ≤ Real.log M :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < dpt M J)) (by exact_mod_cast hdptJ_le_M)
    linarith [hLd3_ge]
  -- `M ≤ t` and `t < M+1`, with `t = N/(2 q₁ q₂)`
  have hd_pos : 0 < 2 * q.1 * q.2 := by positivity
  have hMt : (M : ℝ) ≤ (N : ℝ) / (2 * (q.1 : ℝ) * q.2) := by
    rw [hMdef, Lfun]
    calc ((N / (2 * q.1 * q.2) : ℕ) : ℝ) ≤ (N : ℝ) / ((2 * q.1 * q.2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (N : ℝ) / (2 * (q.1 : ℝ) * q.2) := by push_cast; ring
  have htMp1 : (N : ℝ) / (2 * (q.1 : ℝ) * q.2) < (M : ℝ) + 1 := by
    have hlt : N < (M + 1) * (2 * q.1 * q.2) := by
      have hdm := Nat.div_add_mod N (2 * q.1 * q.2)
      have hmod := Nat.mod_lt N hd_pos
      rw [hMdef, Lfun]; nlinarith [hdm, hmod]
    rw [div_lt_iff₀ (by positivity)]
    exact_mod_cast hlt
  -- `logND N q = log(2t)` and the two endpoint bounds
  have h2t : 2 * ((N : ℝ) / (2 * (q.1 : ℝ) * q.2)) = (N : ℝ) / ((q.1 : ℝ) * q.2) := by
    field_simp
  have hlNeq : logND N q = Real.log (2 * ((N : ℝ) / (2 * (q.1 : ℝ) * q.2))) := by
    rw [h2t, logND]
  have hND_le_LM : logND N q ≤ Real.log M + 2 * Real.log 2 := by
    rw [hlNeq]
    have h4M : 2 * ((N : ℝ) / (2 * (q.1 : ℝ) * q.2)) ≤ 4 * M := by
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
      linarith [htMp1, hM1]
    have hpos : 0 < 2 * ((N : ℝ) / (2 * (q.1 : ℝ) * q.2)) := by
      rw [h2t]; positivity
    calc Real.log (2 * ((N : ℝ) / (2 * (q.1 : ℝ) * q.2)))
        ≤ Real.log (4 * M) := Real.log_le_log hpos h4M
      _ = Real.log M + 2 * Real.log 2 := by
          rw [Real.log_mul (by norm_num) (by positivity),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- The SHARP endpoint bound `logND ≤ 2·log y`, via the pairSet' lower bound `z ≤ q.1`
  -- (not the loose `logND ≤ log N − log y`): `logND = log N − log q₁ − log q₂ ≤ log N − log z
  -- − log y ≤ 2·log y` under the satisfiable relation `log N ≤ 3·log y + log z`.
  have hND_le_ly : logND N q ≤ 2 * Real.log y := by
    have hq1pos : (0 : ℝ) < (q.1 : ℝ) := by exact_mod_cast hp1pos
    have hq2pos : (0 : ℝ) < (q.2 : ℝ) := by exact_mod_cast hp2pos
    have hlogz_le : Real.log (z : ℝ) ≤ Real.log (q.1 : ℝ) := by
      rcases Nat.eq_zero_or_pos z with hz0 | hzpos
      · simp only [hz0, Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by exact_mod_cast hp1.one_lt.le)
      · exact Real.log_le_log (by exact_mod_cast hzpos) (by exact_mod_cast hz1)
    have hlogy_le : Real.log (y : ℝ) ≤ Real.log (q.2 : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < y))
      exact_mod_cast (by omega : y ≤ q.2)
    rw [logND, Real.log_div (Nat.cast_ne_zero.mpr hNpos.ne') (mul_ne_zero hq1pos.ne' hq2pos.ne'),
      Real.log_mul hq1pos.ne' hq2pos.ne']
    linarith [hlogz_le, hlogy_le, hlogNz]
  -- assemble the dyadic bound and convert
  have hPdyad : primeCountIoc y M ≤ (M : ℝ) / Real.log M
      + 2 * (M : ℝ) * Real.log 3 / (Real.log M * Real.log (dpt M J))
      + 4 * K * (M : ℝ) / Real.log (dpt M J) ^ 2 :=
    le_trans (primeCountIoc_y_le_dyadic hJy) (dyadic_count_le hK0 hpsi hdptJ3)
  have hfin := convert_final (Kp := K) (M3 := (M : ℝ)) (LM := Real.log M)
    (Ld3 := Real.log (dpt M J)) (t := (N : ℝ) / (2 * (q.1 : ℝ) * q.2)) (lN := logND N q)
    (ly := Real.log y) (P := primeCountIoc y M)
    hK0 hMt hM3nn hLMpos hLd3pos hlypos hNDpos hLM_ge hLd3_ge hND_le_LM hND_le_ly hPdyad
  calc primeCountIoc y M
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y)
          * ((N : ℝ) / (2 * (q.1 : ℝ) * q.2) / logND N q) := hfin
    _ = (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y)
          * ((N : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logND N q)) := by ring

/-! ## Section 4 — regression: the G-COUNT-2 reduction shape -/

/-- **Regression (shape alignment, compile-time).**  Summing `goldPerPair_pi_upper` over
`pairSet'` yields exactly `(coef)·(N/2)·weightedPairSum'` — the Goldbach mirror of the twin's
`tripleSum_le_weighted_pairSum'` (`Salt/Chen/CountFinal.lean`).  Since the per-pair weight is
BYTE-IDENTICAL to the `weightedPairSum'` summand `1/(p₁p₂·logND N q)`, G-COUNT-2 reuses
`weightedPairSum'_le_cbar` verbatim on the result.  This is the sanity check that the per-pair
bound's shape slots into the downstream `c̄/2` chain. -/
example {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {N z y : ℕ} (hy : 6 ≤ y) (hlogNz : Real.log N ≤ 3 * Real.log y + Real.log z) :
    ∑ q ∈ pairSet' N z y, primeCountIoc y (Lfun N q)
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y) * ((N : ℝ) / 2)
          * weightedPairSum' N z y := by
  rw [weightedPairSum', Finset.mul_sum]
  refine Finset.sum_le_sum (fun q hq => ?_)
  have h := goldPerPair_pi_upper hK0 hpsi hy hlogNz hq
  calc primeCountIoc y (Lfun N q)
      ≤ (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y)
          * ((N : ℝ) / 2) * (1 / ((q.1 : ℝ) * q.2 * logND N q)) := h
    _ = (1 + (4 * Real.log 2 + 16 * Real.log 3 + 32 * K) / Real.log y) * ((N : ℝ) / 2)
          * (1 / ((q.1 : ℝ) * q.2 * logND N q)) := by ring

end Salt.Goldbach
