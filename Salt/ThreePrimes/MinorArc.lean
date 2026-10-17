/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.MR.MinorArcExit
import Salt.ThreePrimes.MajorArc

/-!
# Three primes: Vinogradov's minor-arc estimate

This is lemma L19 of the three-primes plan (`docs/plans/three-primes-PLAN.md`, Step 6), the heart of
the proof:

  `|S(α)| ≤ K (N/√q + N^{7/8} + √(Nq)) (log N)³`  whenever `|α − a/q| ≤ 1/q²` and `gcd(a, q) = 1`.

The corpus already proves the hard part, in a different shape. `Salt.MR.lambdaPhase_le` bounds
`Σ_{n ≤ x} Λ(n) e(αn)` by an explicit expression `vinoBd`, built from Vaughan's identity with both
parameters equal to `W`, two type I sums, and the type II sum cut into dyadic blocks. This file only
**chooses the parameters and simplifies**.

* **The Vaughan parameter** is `W = ⌊N^{1/4}⌋`, taken as two integer square roots so that `W² ≤ N`
  is a fact about integers. The textbook takes `W = N^{2/5}`, which gives `N^{4/5}` in place of
  `N^{7/8}`. Either exponent below `1` serves three primes: Step 7 needs only `N^{7/8} ≤ N/√P`, and
  `P` is a power of `log N`.
* **The dyadic blocks** run up to `W · 2^K` with `2^K` about `N/W²`, so the widest block has width
  about `N/W`. The type II term `√(width · N)` is then about `N/√W = N^{7/8}`: a real power saving.
  A cut taken too high would make that term about `N`, and the bound would say nothing.
* **Each term of `vinoBd` then sits under one of the three.** The type I outputs `(N/q) log²N`
  and `(W + q) log²N` are at most `N/√q` and `√(Nq)` times logs, once `q ≤ N`. The type II outputs
  are `N/√q`, `N^{7/8}` and `√(Nq)` times `log x`, the `√(log q)` from the reciprocal-sum lemma, and
  the number of blocks `K ≤ 3 log N`. That makes at most three logs. When `q > N` the trivial bound
  `|S(α)| ≤ ψ(N) ≤ 2N` is already below `√(Nq) (log N)³` up to the constant.
-/

namespace Salt.ThreePrimes

open ArithmeticFunction
open Salt.ExpSum (eR norm_eR)

/-- The integer fourth root `W = ⌊√⌊√N⌋⌋` satisfies `W⁴ ≤ N < (W + 1)⁴`; that is, `W = ⌊N^{1/4}⌋`,
the Vaughan parameter of this file. -/
theorem isqrt_isqrt_pow_four (N : ℕ) :
    Nat.sqrt (Nat.sqrt N) ^ 4 ≤ N ∧ N < (Nat.sqrt (Nat.sqrt N) + 1) ^ 4 := by
  have h1 := Nat.sqrt_le (Nat.sqrt N)
  have h2 := Nat.sqrt_le N
  have h3 := Nat.succ_le_succ_sqrt (Nat.sqrt N)
  have h4 := Nat.succ_le_succ_sqrt N
  constructor
  · calc Nat.sqrt (Nat.sqrt N) ^ 4
        = (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N))
          * (Nat.sqrt (Nat.sqrt N) * Nat.sqrt (Nat.sqrt N)) := by ring
      _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul h1 h1
      _ ≤ N := h2
  · calc N < (Nat.sqrt N + 1) * (Nat.sqrt N + 1) := by omega
      _ ≤ ((Nat.sqrt (Nat.sqrt N) + 1) * (Nat.sqrt (Nat.sqrt N) + 1))
          * ((Nat.sqrt (Nat.sqrt N) + 1) * (Nat.sqrt (Nat.sqrt N) + 1)) := Nat.mul_le_mul h3 h3
      _ = (Nat.sqrt (Nat.sqrt N) + 1) ^ 4 := by ring

/-- With `W² ≤ N` and `K = ⌊log₂(N / W²)⌋ + 1`, the dyadic cut overshoots `N` by at most a factor
`2`: `2^K · W² ≤ 2N`. So the widest block, of width at most `W · 2^K`, has width at most `2N/W`. -/
theorem two_pow_dyadic_mul_le {N W : ℕ} (hWN : W * W ≤ N) :
    2 ^ (Nat.log 2 (N / (W * W)) + 1) * (W * W) ≤ 2 * N := by
  rcases Nat.eq_zero_or_pos (N / (W * W)) with h | h
  · rw [h, Nat.log_zero_right, zero_add, pow_one]
    exact Nat.mul_le_mul_left 2 hWN
  · have h1 : 2 ^ Nat.log 2 (N / (W * W)) ≤ N / (W * W) := Nat.pow_log_le_self 2 h.ne'
    have h2 : N / (W * W) * (W * W) ≤ N := Nat.div_mul_le_self N (W * W)
    calc 2 ^ (Nat.log 2 (N / (W * W)) + 1) * (W * W)
        = 2 * (2 ^ Nat.log 2 (N / (W * W)) * (W * W)) := by ring
      _ ≤ 2 * (N / (W * W) * (W * W)) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h1)
      _ ≤ 2 * N := Nat.mul_le_mul_left 2 h2

/-- The same dyadic cut does reach `N`: `N ≤ W² · 2^K` for `K = ⌊log₂(N / W²)⌋ + 1`, which is
what lets the truncated dyadic decomposition stop at block `K`. -/
theorem le_mul_two_pow_dyadic {N W : ℕ} (hW : 1 ≤ W) :
    N ≤ W * W * 2 ^ (Nat.log 2 (N / (W * W)) + 1) := by
  have hWW : 0 < W * W := Nat.mul_pos hW hW
  have h1 : N < (N / (W * W) + 1) * (W * W) :=
    (Nat.div_lt_iff_lt_mul hWW).mp (Nat.lt_succ_self _)
  have h2 : N / (W * W) < 2 ^ (Nat.log 2 (N / (W * W)) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 : (N / (W * W) + 1) * (W * W) ≤ 2 ^ (Nat.log 2 (N / (W * W)) + 1) * (W * W) :=
    Nat.mul_le_mul_right _ (by omega)
  have h4 : 2 ^ (Nat.log 2 (N / (W * W)) + 1) * (W * W)
      = W * W * 2 ^ (Nat.log 2 (N / (W * W)) + 1) := by ring
  omega

/-- The number of dyadic blocks is logarithmic: for `m ≤ N` and `N ≥ 1`,
`⌊log₂ m⌋ ≤ 2 log N` (using `log 2 > 1/2`). -/
theorem nat_log_two_le_two_mul_log {m N : ℕ} (hmN : m ≤ N) (hN : 1 ≤ N) :
    (Nat.log 2 m : ℝ) ≤ 2 * Real.log N := by
  have hj : Nat.log 2 m ≤ Nat.log 2 N := Nat.log_mono_right hmN
  have hp : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hpR : (2 : ℝ) ^ Nat.log 2 N ≤ (N : ℝ) := by exact_mod_cast hp
  have hlog : (Nat.log 2 N : ℝ) * Real.log 2 ≤ Real.log N := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hpR
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hjR : (Nat.log 2 m : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hj
  have h0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  nlinarith

/-- The trivial bound `|S(α)| ≤ N log N`, from `Λ(n) ≤ log n ≤ log N` and `|e(nα)| = 1`. It is the
bound used when `q > N`. -/
theorem norm_primeExpSum_le_trivial (N : ℕ) (α : ℝ) :
    ‖primeExpSum N α‖ ≤ (N : ℝ) * Real.log N := by
  unfold primeExpSum
  calc ‖∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℂ) * eR ((n : ℝ) * α)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖(vonMangoldt n : ℂ) * eR ((n : ℝ) * α)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log (N : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
        have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        have hnNR : (n : ℝ) ≤ N := by exact_mod_cast hnN
        rw [norm_mul, norm_eR, mul_one, Complex.norm_real,
          Real.norm_of_nonneg vonMangoldt_nonneg]
        exact le_trans vonMangoldt_le_log (Real.log_le_log (by linarith) hnNR)
    _ = (N : ℝ) * Real.log N := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-- **The type II output, simplified.** With `N = s⁸`, `s² < 2W`, `hi · W ≤ 2N`, `A² = N²/q`,
`C² = Nq` and `1 + log q ≤ 6L²`, the four square roots in `vinoBd` sum to at most
`24 L (A + s⁷ + C)`. -/
theorem typeII_sqrt_sum_le {N q W : ℕ} {hi s L A C : ℝ} (hNpos : (0 : ℝ) < N)
    (hqpos : (0 : ℝ) < q) (hs0 : 0 < s) (hs8 : (N : ℝ) = s ^ 8) (hWR0 : (0 : ℝ) < W)
    (hs2W : s ^ 2 < 2 * (W : ℝ)) (hhi0 : 0 ≤ hi) (hhiW : hi * W ≤ 2 * N) (hL0 : 0 < L)
    (hLh : 1 ≤ 2 * L) (hlq0' : 0 ≤ 1 + Real.log q) (hlq6 : 1 + Real.log q ≤ 6 * L ^ 2)
    (hA0 : 0 ≤ A) (hAsq : A ^ 2 = (N : ℝ) ^ 2 / q) (hC0 : 0 ≤ C) (hCsq : C ^ 2 = N * q) :
    Real.sqrt (7 * hi * (N : ℝ)) + Real.sqrt (6 * (N : ℝ) ^ 2 / q)
        + Real.sqrt (12 * (N : ℝ) ^ 2 * (1 + Real.log q) / W)
        + Real.sqrt (12 * (N : ℝ) * q * (1 + Real.log q))
      ≤ 2 * L * (12 * (A + s ^ 7 + C)) := by
  have hs7 : 0 < s ^ 7 := pow_pos hs0 7
  have hLh' : 0 ≤ 2 * L - 1 := by linarith
  have hS1 : Real.sqrt (7 * hi * (N : ℝ)) ≤ 6 * s ^ 7 := by
    rw [Real.sqrt_le_left (by linarith)]
    have hY0 : 0 ≤ 7 * hi * (N : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hhi0) hNpos.le
    have h1 : 7 * hi * (N : ℝ) * s ^ 2 ≤ 7 * hi * N * (2 * W) :=
      mul_le_mul_of_nonneg_left hs2W.le hY0
    have h2 : 7 * hi * (N : ℝ) * (2 * W) ≤ 28 * s ^ 16 := by
      have e : 7 * hi * (N : ℝ) * (2 * W) = 14 * N * (hi * W) := by ring
      rw [e]
      have h3 := mul_le_mul_of_nonneg_left hhiW (by positivity : (0 : ℝ) ≤ 14 * N)
      have h4 : (14 : ℝ) * N * (2 * N) = 28 * s ^ 16 := by rw [hs8]; ring
      linarith
    have h5 : 7 * hi * (N : ℝ) * s ^ 2 ≤ (6 * s ^ 7) ^ 2 * s ^ 2 := by
      have e : (6 * s ^ 7) ^ 2 * s ^ 2 = 36 * s ^ 16 := by ring
      have : 0 ≤ s ^ 16 := by positivity
      linarith
    exact le_of_mul_le_mul_right h5 (pow_pos hs0 2)
  have hS2 : Real.sqrt (6 * (N : ℝ) ^ 2 / q) ≤ 3 * A := by
    rw [Real.sqrt_le_left (by linarith)]
    have e1 : (3 * A) ^ 2 = 9 * ((N : ℝ) ^ 2 / q) := by rw [mul_pow, hAsq]; ring
    have e2 : 6 * (N : ℝ) ^ 2 / q = 6 * ((N : ℝ) ^ 2 / q) := by ring
    rw [e1, e2]
    have : 0 ≤ (N : ℝ) ^ 2 / q := by positivity
    linarith
  have hS3 : Real.sqrt (12 * (N : ℝ) ^ 2 * (1 + Real.log q) / W) ≤ 12 * s ^ 7 * L := by
    rw [Real.sqrt_le_left (by have := mul_pos hs7 hL0; linarith)]
    have hX : 12 * (N : ℝ) ^ 2 * (1 + Real.log q) / W * W
        = 12 * (N : ℝ) ^ 2 * (1 + Real.log q) := div_mul_cancel₀ _ hWR0.ne'
    have hX0 : 0 ≤ 12 * (N : ℝ) ^ 2 * (1 + Real.log q) / W :=
      div_nonneg (mul_nonneg (by positivity) hlq0') hWR0.le
    obtain ⟨X, hXdef⟩ : ∃ X, 12 * (N : ℝ) ^ 2 * (1 + Real.log q) / W = X := ⟨_, rfl⟩
    rw [hXdef] at hX hX0 ⊢
    have h1 : X * s ^ 2 ≤ X * (2 * W) := mul_le_mul_of_nonneg_left hs2W.le hX0
    have h3 : 12 * (N : ℝ) ^ 2 * (1 + Real.log q) ≤ 12 * (N : ℝ) ^ 2 * (6 * L ^ 2) :=
      mul_le_mul_of_nonneg_left hlq6 (by positivity)
    have h4 : (N : ℝ) ^ 2 = s ^ 16 := by rw [hs8]; ring
    have h2 : X * (2 * W) ≤ 144 * s ^ 16 * L ^ 2 := by
      have e : X * (2 * W) = 2 * (X * W) := by ring
      rw [e, hX]
      rw [h4] at h3 ⊢
      linarith
    have h5 : X * s ^ 2 ≤ (12 * s ^ 7 * L) ^ 2 * s ^ 2 := by
      have e : (12 * s ^ 7 * L) ^ 2 * s ^ 2 = 144 * s ^ 16 * L ^ 2 := by ring
      linarith
    exact le_of_mul_le_mul_right h5 (pow_pos hs0 2)
  have hS4 : Real.sqrt (12 * (N : ℝ) * q * (1 + Real.log q)) ≤ 9 * C * L := by
    rw [Real.sqrt_le_left (by have := mul_nonneg hC0 hL0.le; linarith)]
    have e : (9 * C * L) ^ 2 = 81 * ((N : ℝ) * q) * L ^ 2 := by
      rw [show (9 * C * L) ^ 2 = 81 * C ^ 2 * L ^ 2 by ring, hCsq]
    rw [e]
    have h1 : 12 * (N : ℝ) * q * (1 + Real.log q) ≤ 12 * (N : ℝ) * q * (6 * L ^ 2) :=
      mul_le_mul_of_nonneg_left hlq6 (by positivity)
    have : 0 ≤ (N : ℝ) * q * L ^ 2 := by positivity
    linarith
  linarith [mul_nonneg hs7.le hLh', mul_nonneg hA0 hLh', mul_nonneg hA0 hL0.le,
    mul_nonneg hC0 hL0.le, mul_nonneg hs7.le hL0.le]

/-- **`vinoBd` at the chosen parameters is at most `1000 (N/√q + s⁷ + √(Nq)) L³`**, where
`s = N^{1/8}` and `L = log N`, given the parameter facts collected in the main proof and `q ≤ N`. -/
theorem vinoBd_le_cube {N q W K : ℕ} {hi s L A C : ℝ} (hN : 2 ≤ N) (hq : 1 ≤ q) (hqN : q ≤ N)
    (hLdef : Real.log N = L) (hs0 : 0 < s) (hs1 : 1 ≤ s) (hs8 : (N : ℝ) = s ^ 8)
    (hW1 : 1 ≤ W) (hWW : W * W ≤ N) (hWs : (W : ℝ) ≤ s ^ 2) (hs2W : s ^ 2 < 2 * (W : ℝ))
    (hhi0 : 0 ≤ hi) (hhiW : hi * W ≤ 2 * N) (hKL : (K : ℝ) ≤ 4 * L)
    (hAdef : (N : ℝ) / Real.sqrt q = A) (hCdef : Real.sqrt ((N : ℝ) * q) = C) :
    Salt.MR.vinoBd q N W K hi ≤ 1000 * (A + s ^ 7 + C) * L ^ 3 := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  -- the logarithm `L = log N ≥ log 2 > 1/2`
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hL2 : Real.log 2 ≤ L := by rw [← hLdef]; exact Real.log_le_log (by norm_num) hNR
  have hLh : 1 ≤ 2 * L := by linarith
  have hL0 : 0 < L := by linarith
  have hLh' : 0 ≤ 2 * L - 1 := by linarith
  have hL3 : L ^ 2 ≤ 2 * L ^ 3 := by nlinarith [mul_nonneg (sq_nonneg L) hLh']
  have hL1 : L ≤ 4 * L ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hL0.le hLh') (by linarith : (0 : ℝ) ≤ 2 * L + 1)]
  have hL30 : 0 ≤ L ^ 3 := by positivity
  -- the scales
  have hs7 : 0 < s ^ 7 := pow_pos hs0 7
  have hA0 : 0 ≤ A := by rw [← hAdef]; positivity
  have hC0 : 0 ≤ C := by rw [← hCdef]; exact Real.sqrt_nonneg _
  have hT0 : 0 ≤ A + s ^ 7 + C := by linarith
  have hCsq : C ^ 2 = N * q := by rw [← hCdef, Real.sq_sqrt (by positivity)]
  have hAsq : A ^ 2 = (N : ℝ) ^ 2 / q := by rw [← hAdef, div_pow, Real.sq_sqrt hqpos.le]
  have hqC : (q : ℝ) ≤ C := by
    rw [← hCdef]
    calc (q : ℝ) = Real.sqrt ((q : ℝ) * q) := (Real.sqrt_mul_self hqpos.le).symm
      _ ≤ Real.sqrt ((N : ℝ) * q) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hqNR hqpos.le)
  have hNqA : (N : ℝ) / q ≤ A := by
    rw [← hAdef]
    have hsq : Real.sqrt q ≤ q := by
      rw [Real.sqrt_le_left hqpos.le]; nlinarith
    exact div_le_div_of_nonneg_left hNpos.le (Real.sqrt_pos.mpr hqpos) hsq
  have hlq : Real.log q ≤ L := by rw [← hLdef]; exact Real.log_le_log hqpos hqNR
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hqR
  have hlq0' : 0 ≤ 1 + Real.log q := by linarith
  have hlq3 : 1 + Real.log q ≤ 3 * L := by linarith
  have hlq6 : 1 + Real.log q ≤ 6 * L ^ 2 := by nlinarith [mul_nonneg hL0.le hLh']
  -- the Vaughan parameter
  have hWR1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWR0 : (0 : ℝ) < W := by linarith
  have hWB : (W : ℝ) ≤ s ^ 7 := by linarith [pow_le_pow_right₀ hs1 (by norm_num : 2 ≤ 7)]
  have hWWR : ((W * W : ℕ) : ℝ) ≤ s ^ 7 := by
    push_cast
    have : (W : ℝ) * W ≤ s ^ 2 * s ^ 2 := mul_le_mul hWs hWs (by positivity) (by positivity)
    linarith [pow_le_pow_right₀ hs1 (by norm_num : 4 ≤ 7), show s ^ 2 * s ^ 2 = s ^ 4 by ring]
  have h11 : 1 ≤ W * W := Nat.mul_le_mul hW1 hW1
  have hWWpos : (1 : ℝ) ≤ ((W * W : ℕ) : ℝ) := by exact_mod_cast h11
  have hWWne : ((W * W : ℕ) : ℝ) ≠ 0 := by positivity
  -- the logarithms
  have hlogW : Real.log W ≤ L := by
    rw [← hLdef]
    exact Real.log_le_log hWR0 (by exact_mod_cast le_trans (Nat.le_mul_of_pos_left W hW1) hWW)
  have hlogW0 : 0 ≤ Real.log W := Real.log_nonneg hWR1
  have hlogWW : Real.log ((W * W : ℕ) : ℝ) ≤ L := by
    rw [← hLdef]; exact Real.log_le_log (by linarith) (by exact_mod_cast hWW)
  have hlogWW0 : 0 ≤ Real.log ((W * W : ℕ) : ℝ) := Real.log_nonneg hWWpos
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2W : Real.log (2 * (W : ℝ)) = Real.log 2 + Real.log W :=
    Real.log_mul two_ne_zero hWR0.ne'
  have hlog2WW : Real.log (2 * ((W * W : ℕ) : ℝ)) = Real.log 2 + Real.log ((W * W : ℕ) : ℝ) :=
    Real.log_mul two_ne_zero hWWne
  -- the head and the two type I outputs
  have hP0 : (W : ℝ) * Real.log W ≤ 4 * s ^ 7 * L ^ 3 := by
    have h1 : (W : ℝ) * Real.log W ≤ s ^ 7 * L := mul_le_mul hWB hlogW hlogW0 hs7.le
    have h2 : s ^ 7 * L ≤ s ^ 7 * (4 * L ^ 3) := mul_le_mul_of_nonneg_left hL1 hs7.le
    linarith
  have hI1 : 30 * ((N : ℝ) / q) * (1 + Real.log (2 * (W : ℝ)))
        + 12 * ((W : ℝ) + q) * (1 + Real.log q)
        ≤ 30 * A * (4 * L) + 12 * (s ^ 7 + C) * (3 * L) := by
    have h1 : 30 * ((N : ℝ) / q) * (1 + Real.log (2 * (W : ℝ))) ≤ 30 * A * (4 * L) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : 12 * ((W : ℝ) + q) * (1 + Real.log q) ≤ 12 * (s ^ 7 + C) * (3 * L) :=
      mul_le_mul (by linarith) hlq3 hlq0' (by linarith)
    linarith
  have hP1 : 2 * L * (30 * ((N : ℝ) / q) * (1 + Real.log (2 * (W : ℝ)))
        + 12 * ((W : ℝ) + q) * (1 + Real.log q))
        ≤ 2 * L * (30 * A * (4 * L) + 12 * (s ^ 7 + C) * (3 * L)) :=
    mul_le_mul_of_nonneg_left hI1 (by linarith)
  have hI2 : 30 * ((N : ℝ) / q) * (1 + Real.log (2 * ((W * W : ℕ) : ℝ)))
        + 12 * (((W * W : ℕ) : ℝ) + q) * (1 + Real.log q)
        ≤ 30 * A * (4 * L) + 12 * (s ^ 7 + C) * (3 * L) := by
    have h1 : 30 * ((N : ℝ) / q) * (1 + Real.log (2 * ((W * W : ℕ) : ℝ)))
        ≤ 30 * A * (4 * L) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : 12 * (((W * W : ℕ) : ℝ) + q) * (1 + Real.log q) ≤ 12 * (s ^ 7 + C) * (3 * L) :=
      mul_le_mul (by linarith) hlq3 hlq0' (by linarith)
    linarith
  have hI20 : 0 ≤ 30 * ((N : ℝ) / q) * (1 + Real.log (2 * ((W * W : ℕ) : ℝ)))
        + 12 * (((W * W : ℕ) : ℝ) + q) * (1 + Real.log q) :=
    add_nonneg (mul_nonneg (by positivity) (by linarith)) (mul_nonneg (by positivity) hlq0')
  have hP2 : Real.log ((W * W : ℕ) : ℝ) * (30 * ((N : ℝ) / q)
        * (1 + Real.log (2 * ((W * W : ℕ) : ℝ)))
        + 12 * (((W * W : ℕ) : ℝ) + q) * (1 + Real.log q))
        ≤ L * (30 * A * (4 * L) + 12 * (s ^ 7 + C) * (3 * L)) :=
    mul_le_mul hlogWW hI2 hI20 hL0.le
  -- the type II output
  have hbr := typeII_sqrt_sum_le (W := W) hNpos hqpos hs0 hs8 hWR0 hs2W hhi0 hhiW hL0 hLh
    hlq0' hlq6 hA0 hAsq hC0 hCsq
  have hbr0 : 0 ≤ Real.sqrt (7 * hi * (N : ℝ)) + Real.sqrt (6 * (N : ℝ) ^ 2 / q)
        + Real.sqrt (12 * (N : ℝ) ^ 2 * (1 + Real.log q) / W)
        + Real.sqrt (12 * (N : ℝ) * q * (1 + Real.log q)) := by positivity
  have hsq2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hY := mul_le_mul (mul_le_mul_of_nonneg_right hsq2 hL0.le) hbr hbr0 (by linarith)
  have hY0 := mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hL0.le) hbr0
  have hP3 := mul_le_mul hKL hY hY0 (by linarith : (0 : ℝ) ≤ 4 * L)
  -- assembly
  unfold Salt.MR.vinoBd
  rw [hLdef]
  linarith [mul_le_mul_of_nonneg_left hL3 hT0,
    mul_nonneg (add_nonneg hA0 hC0) hL30, mul_nonneg hT0 hL30,
    mul_nonneg (add_nonneg hs7.le hC0) (sq_nonneg L), mul_nonneg hA0 (sq_nonneg L)]

/-- **Vinogradov's minor-arc estimate:** there is a `K` such that for every `N ≥ 2`, every `q ≥ 1`,
every `a` with `gcd(a, q) = 1` and every `α` with `|α − a/q| ≤ 1/q²`,
`|S(α)| ≤ K (N/√q + N^{7/8} + √(Nq)) (log N)³`. -/
theorem norm_primeExpSum_le_minor :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N q : ℕ) (a : ℤ) (α : ℝ), 2 ≤ N → 1 ≤ q → Int.gcd a (q : ℤ) = 1 →
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
        ‖primeExpSum N α‖
          ≤ K * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ ((7 : ℝ) / 8) + Real.sqrt ((N : ℝ) * q))
              * Real.log N ^ 3 := by
  refine ⟨1000, by norm_num, ?_⟩
  intro N q a α hN hq hcop happ
  have hN1 : 1 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, Real.log (N : ℝ) = L := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A, (N : ℝ) / Real.sqrt q = A := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C, Real.sqrt ((N : ℝ) * q) = C := ⟨_, rfl⟩
  -- `s = N^{1/8}`, so that `N = s⁸` and `N^{7/8} = s⁷`
  obtain ⟨s, hs0, hs8, hB⟩ : ∃ s : ℝ, 0 < s ∧ (N : ℝ) = s ^ 8 ∧
      (N : ℝ) ^ ((7 : ℝ) / 8) = s ^ 7 := by
    refine ⟨(N : ℝ) ^ ((1 : ℝ) / 8), by positivity, ?_, ?_⟩
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
  have hs1 : 1 ≤ s := by
    by_contra h
    rw [not_le] at h
    have : s ^ 8 ≤ 1 := pow_le_one₀ hs0.le h.le
    linarith
  rw [hB, hAdef, hCdef, hLdef]
  have hl2 : (1 : ℝ) / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hL2 : Real.log 2 ≤ L := by rw [← hLdef]; exact Real.log_le_log (by norm_num) hNR
  have hL0 : 0 < L := by linarith
  have hA0 : 0 ≤ A := by rw [← hAdef]; positivity
  have hC0 : 0 ≤ C := by rw [← hCdef]; exact Real.sqrt_nonneg _
  have hs7 : 0 < s ^ 7 := pow_pos hs0 7
  rcases le_or_gt q N with hqN | hqN
  swap
  · -- `q > N`: the trivial bound `|S| ≤ N log N ≤ √(Nq) log N`
    have hNC : (N : ℝ) ≤ C := by
      rw [← hCdef]
      calc (N : ℝ) = Real.sqrt ((N : ℝ) * N) := (Real.sqrt_mul_self hNpos.le).symm
        _ ≤ Real.sqrt ((N : ℝ) * q) := Real.sqrt_le_sqrt (by
            have : (N : ℝ) ≤ q := by exact_mod_cast hqN.le
            nlinarith)
    have htriv := norm_primeExpSum_le_trivial N α
    rw [hLdef] at htriv
    have hL1 : L ≤ 4 * L ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hL0.le (by linarith : (0 : ℝ) ≤ 2 * L - 1))
        (by linarith : (0 : ℝ) ≤ 2 * L + 1)]
    have hL30 : 0 ≤ L ^ 3 := by positivity
    calc ‖primeExpSum N α‖ ≤ (N : ℝ) * L := htriv
      _ ≤ C * (4 * L ^ 3) := mul_le_mul hNC hL1 hL0.le hC0
      _ ≤ 1000 * (A + s ^ 7 + C) * L ^ 3 := by
          linarith [mul_nonneg hA0 hL30, mul_nonneg hs7.le hL30, mul_nonneg hC0 hL30]
  -- `q ≤ N`: the Vaughan parameter `W = ⌊N^{1/4}⌋`
  obtain ⟨W, hWdef⟩ : ∃ W, Nat.sqrt (Nat.sqrt N) = W := ⟨_, rfl⟩
  have hW4 := isqrt_isqrt_pow_four N
  rw [hWdef] at hW4
  have hW1 : 1 ≤ W := by
    rw [← hWdef]
    exact Nat.le_sqrt.mpr (by simpa using (Nat.le_sqrt.mpr (by simpa using hN1) : 1 ≤ Nat.sqrt N))
  have hWW : W * W ≤ N := by rw [← hWdef]; exact le_trans (Nat.sqrt_le _) (Nat.sqrt_le_self _)
  have hW4R : (W : ℝ) ^ 4 ≤ s ^ 8 := by rw [← hs8]; exact_mod_cast hW4.1
  have hW4R' : s ^ 8 < (2 * (W : ℝ)) ^ 4 := by
    rw [← hs8]
    have h1 : (N : ℝ) < ((W : ℝ) + 1) ^ 4 := by exact_mod_cast hW4.2
    have hWR1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    have h2 : ((W : ℝ) + 1) ^ 4 ≤ (2 * (W : ℝ)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 4
    linarith
  have hWs : (W : ℝ) ≤ s ^ 2 := by
    by_contra h
    rw [not_le] at h
    have := pow_lt_pow_left₀ h (by positivity) (n := 4) (by norm_num)
    linarith [show (s ^ 2) ^ 4 = s ^ 8 by ring]
  have hs2W : s ^ 2 < 2 * (W : ℝ) := by
    by_contra h
    rw [not_lt] at h
    have := pow_le_pow_left₀ (by positivity) h 4
    linarith [show (s ^ 2) ^ 4 = s ^ 8 by ring]
  -- the dyadic cut `K` and the block width `hi = W · 2^K`
  have hNle := le_mul_two_pow_dyadic (N := N) hW1
  have hpow := two_pow_dyadic_mul_le hWW
  have hKL0 := nat_log_two_le_two_mul_log (Nat.div_le_self N (W * W)) hN1
  obtain ⟨K, hKdef⟩ : ∃ K, Nat.log 2 (N / (W * W)) + 1 = K := ⟨_, rfl⟩
  rw [hKdef] at hNle hpow
  have hKL : (K : ℝ) ≤ 4 * L := by
    rw [hLdef] at hKL0
    rw [← hKdef]; push_cast; linarith
  obtain ⟨hi, hhidef⟩ : ∃ hi : ℝ, ((W * 2 ^ K : ℕ) : ℝ) = hi := ⟨_, rfl⟩
  have hhi0 : 0 ≤ hi := by rw [← hhidef]; positivity
  have hhiW : hi * W ≤ 2 * N := by
    have h' : ((2 ^ K * (W * W) : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hpow
    rw [← hhidef]; push_cast at h' ⊢; linarith
  have hcut : N ≤ min N (W * 2 ^ K) * (W + 1) := by
    rcases le_or_gt N (W * 2 ^ K) with h | h
    · rw [min_eq_left h]; exact Nat.le_mul_of_pos_right N (by omega)
    · rw [min_eq_right h.le]
      calc N ≤ W * W * 2 ^ K := hNle
        _ ≤ W * W * 2 ^ K + W * 2 ^ K := Nat.le_add_right _ _
        _ = W * 2 ^ K * (W + 1) := by ring
  have hhi : ∀ k, k < K →
      ((min N (W * 2 ^ (k + 1)) : ℕ) : ℝ) - ((min N (W * 2 ^ k) : ℕ) : ℝ) ≤ hi := by
    intro k hk
    have hab : W * 2 ^ (k + 1) = W * 2 ^ k + W * 2 ^ k := by ring
    have hstep : min N (W * 2 ^ (k + 1)) ≤ min N (W * 2 ^ k) + W * 2 ^ k := by
      rcases le_or_gt N (W * 2 ^ k) with h | h
      · rw [min_eq_left h]
        exact le_trans (min_le_left _ _) (Nat.le_add_right _ _)
      · rw [min_eq_right h.le, hab]
        exact min_le_right _ _
    have hpk : W * 2 ^ k ≤ W * 2 ^ K :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (le_of_lt hk))
    have h1 : ((min N (W * 2 ^ (k + 1)) : ℕ) : ℝ)
        ≤ ((min N (W * 2 ^ k) : ℕ) : ℝ) + ((W * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hstep
    have h2 : ((W * 2 ^ k : ℕ) : ℝ) ≤ ((W * 2 ^ K : ℕ) : ℝ) := by exact_mod_cast hpk
    rw [← hhidef]
    linarith
  -- the corpus bound, and its simplification
  have hmain : ‖Salt.MR.lambdaPhase α N‖ ≤ Salt.MR.vinoBd q N W K hi :=
    Salt.MR.lambdaPhase_le (c := 1) hq (by norm_num) hcop happ hW1 hWW hcut hhi
  have hbridge : primeExpSum N α = Salt.MR.lambdaPhase α N := by
    unfold primeExpSum Salt.MR.lambdaPhase
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_comm (n : ℝ) α]
  rw [hbridge]
  exact le_trans hmain (vinoBd_le_cube hN hq hqN hLdef hs0 hs1 hs8 hW1 hWW hWs hs2W hhi0 hhiW
    hKL hAdef hCdef)

end Salt.ThreePrimes
