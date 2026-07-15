/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.WeightTrivia

/-!
# G-WEIGHT — the Goldbach mirror of the Chen window-arithmetic trivia (Q1, wave W1)

Design: `docs/exploration/q1-design.md`, the G-WEIGHT node.  This file mirrors the *window/
structural half* of `Salt/Chen/WeightTrivia.lean` under the Goldbach substitution
`n + 2 ↦ N − n`.

The Chen sieve counts window points `n ∈ [N/2, N−2]` with `n` prime and the paired value a `P₂`.
For the **twin** problem the paired value is `n + 2` (running over the *top* half `[N/2, N]`); for
the **Goldbach** problem `N = p + q` the paired value is `N − n` (running over the *bottom* half
`[2, N/2]` as `n` sweeps `[N/2, N−2]`).  The window *finset* is identical, so we reuse
`Salt.Chen.twinWindow N = Finset.Icc (N/2) (N−2)`; only the value map changes.  Three mirrors:

* `window_two_thirds_lt` — the weight-validity size bounds `2 ≤ N − n ≤ (N+1)/2` (the twin's
  large-value bound `x^{2/3} < n+2` reflects, by the complementary `[2, N/2]` range, to the
  small-value bounds Chen's weight structure needs: `2 ≤ m` for `chen_weight_struct`'s `hm2`,
  and `m ≤ (N+1)/2 < N < (y+1)³` for its `hmy`).
* `card_window_dvd_le` — `#{n ∈ window : d ∣ N − n} ≤ N / d`, via the reflection bijection
  `n ↦ N − n` (injective on the window since `n ≤ N`) into the multiples of `d` in `(0, N]`.
* `stripSum_le` — the coprimality-cut prime-power strip against the window `Λ`-mass at the value
  `N − n`, bounded by `log N · N/(z−1) ≈ N^{7/8} log N`, hence `o(N/log N)`.

The strip carrier `sqStripZ`/`primeItv` and the window `Λ`-weight are Goldbach-invariant (they read
only the paired value and the prime `n`), so `stripSum_le` mirrors verbatim with `n + 2 ↦ N − n`.
-/

open Finset ArithmeticFunction Salt.Chen

namespace Salt.Goldbach

/-! ## Part A — the weight-validity size bounds on the Goldbach window -/

/-- **The weight-validity threshold, Goldbach mirror.**  For `N ≥ 8` and `n` in the window
`[N/2, N−2]`, the weight argument `m = N − n` satisfies `2 ≤ m ≤ (N+1)/2`.  The lower bound
(`m ≥ 2`, the ℕ-subtraction floor from `n ≤ N − 2`) is `chen_weight_struct`'s `hm2`; the upper
bound puts `m` below the midpoint, so `m ≤ (N+1)/2 < N < (y+1)³` supplies `hmy` — Chen's weight
structure applies at every window point.  (Reflects the twin's `x^{2/3} < n+2 ≤ x`: the large-value
range on the top half becomes the small-value range on the bottom half.) -/
theorem window_two_thirds_lt {N : ℕ} (hN : 8 ≤ N) {n : ℕ} (hn : n ∈ twinWindow N) :
    2 ≤ ((N - n : ℕ) : ℝ) ∧ ((N - n : ℕ) : ℝ) ≤ ((N : ℝ) + 1) / 2 := by
  rw [twinWindow, Finset.mem_Icc] at hn
  obtain ⟨hlo, hhi⟩ := hn
  refine ⟨?_, ?_⟩
  · -- n ≤ N − 2 keeps N − n ≥ 2
    exact_mod_cast (by omega : 2 ≤ N - n)
  · -- n ≥ N/2 puts N − n ≤ ⌈N/2⌉ = (N+1)/2
    have hnat : N - n ≤ (N + 1) / 2 := by omega
    have h1 : ((N - n : ℕ) : ℝ) ≤ (((N + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    have h2 : (((N + 1) / 2 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
    push_cast at h2
    linarith

/-! ## Part B — the per-divisor window count at the reflected value `N − n` -/

/-- **Per-divisor interval count, Goldbach mirror.**  The number of window points `n` with
`d ∣ N − n` is at most `N/d`: the reflection `n ↦ N − n` is injective on the window (every
`n ≤ N`) and maps `{n : d ∣ N − n}` into the multiples of `d` in `(0, N]`. -/
theorem card_window_dvd_le {N d : ℕ} (hN : 2 ≤ N) :
    (((twinWindow N).filter (fun n => d ∣ (N - n))).card : ℝ) ≤ (N : ℝ) / (d : ℝ) := by
  have hcard : ((twinWindow N).filter (fun n => d ∣ (N - n))).card
      ≤ ((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card := by
    apply Finset.card_le_card_of_injOn (fun n => N - n)
    · intro n hn
      rw [Finset.mem_coe, Finset.mem_filter] at hn
      rw [Finset.mem_coe, Finset.mem_filter]
      obtain ⟨hnw, hnd⟩ := hn
      rw [twinWindow, Finset.mem_Icc] at hnw
      obtain ⟨hlo, hhi⟩ := hnw
      have h0 : 0 < N - n := by omega
      have h1 : N - n ≤ N := by omega
      exact ⟨Finset.mem_Ioc.mpr ⟨h0, h1⟩, hnd⟩
    · intro a ha b hb h
      simp only [Finset.mem_coe, Finset.mem_filter, twinWindow, Finset.mem_Icc] at ha hb
      obtain ⟨⟨_, ha2⟩, _⟩ := ha
      obtain ⟨⟨_, hb2⟩, _⟩ := hb
      have h' : N - a = N - b := h
      omega
  have hdiv : ((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card = N / d :=
    Nat.Ioc_filter_dvd_card_eq_div N d
  calc (((twinWindow N).filter (fun n => d ∣ (N - n))).card : ℝ)
      ≤ (((Finset.Ioc 0 N).filter (fun m => d ∣ m)).card : ℝ) := by exact_mod_cast hcard
    _ = ((N / d : ℕ) : ℝ) := by rw [hdiv]
    _ ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le

/-! ## Part C — the prime-power strip against the window `Λ`-mass at `N − n` -/

/-- **The prime-power strip bound, Goldbach mirror.**  With the coprimality restriction (`z ≤ p`),
the window `Λ`-mass weighted by the strip count of the reflected value `N − n` is
`≤ log N · N/(z−1) ≈ N^{7/8} log N`, hence `o(N/log N)`. -/
theorem stripSum_le {N z y : ℕ} (hN : 2 ≤ N) (hz : 2 ≤ z) :
    ∑ n ∈ twinWindow N, vonMangoldt n * (sqStripZ z y (N - n) : ℝ)
      ≤ Real.log N * (N : ℝ) / ((z : ℝ) - 1) := by
  have hlogx : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  -- rewrite the count as a sum of indicators over primeItv
  have hcount : ∀ n, (sqStripZ z y (N - n) : ℝ)
      = ∑ p ∈ primeItv z y, (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
    intro n
    unfold sqStripZ
    rw [Finset.card_filter]
    push_cast
    rfl
  -- expand, swap the order of summation
  have hexpand : ∑ n ∈ twinWindow N, vonMangoldt n * (sqStripZ z y (N - n) : ℝ)
      = ∑ p ∈ primeItv z y,
          ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
    have hstep : ∑ n ∈ twinWindow N, vonMangoldt n * (sqStripZ z y (N - n) : ℝ)
        = ∑ n ∈ twinWindow N,
            ∑ p ∈ primeItv z y, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hcount n, Finset.mul_sum]
    rw [hstep, Finset.sum_comm]
  rw [hexpand]
  -- per-prime bound
  have hper : ∀ p ∈ primeItv z y,
      ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        ≤ Real.log N * ((N : ℝ) / ((p : ℝ) ^ 2)) := by
    intro p hp
    have hstep1 : ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        ≤ ∑ n ∈ twinWindow N, Real.log N * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hd : p ^ 2 ∣ (N - n)
      · simp only [hd, if_true, mul_one]
        refine le_trans vonMangoldt_le_log (Real.log_le_log ?_ ?_)
        · exact_mod_cast (by rw [twinWindow, Finset.mem_Icc] at hn; omega : 1 ≤ n)
        · rw [twinWindow, Finset.mem_Icc] at hn
          exact_mod_cast (by omega : n ≤ N)
      · simp [hd]
    have hstep2 : ∑ n ∈ twinWindow N, Real.log N * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        = Real.log N * (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.card_filter]
      push_cast
      rfl
    have hstep3 : (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ)
        ≤ (N : ℝ) / ((p : ℝ) ^ 2) := by
      have := Salt.Goldbach.card_window_dvd_le (N := N) (d := p ^ 2) hN
      calc (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ)
          ≤ (N : ℝ) / ((p ^ 2 : ℕ) : ℝ) := this
        _ = (N : ℝ) / ((p : ℝ) ^ 2) := by push_cast; ring
    calc ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
        ≤ Real.log N * (((twinWindow N).filter (fun n => p ^ 2 ∣ (N - n))).card : ℝ) := by
          rw [← hstep2]; exact hstep1
      _ ≤ Real.log N * ((N : ℝ) / ((p : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep3 hlogx
  -- assemble the per-prime bounds and the 1/p² telescope
  calc ∑ p ∈ primeItv z y,
          ∑ n ∈ twinWindow N, vonMangoldt n * (if p ^ 2 ∣ (N - n) then (1 : ℝ) else 0)
      ≤ ∑ p ∈ primeItv z y, Real.log N * ((N : ℝ) / ((p : ℝ) ^ 2)) := Finset.sum_le_sum hper
    _ = Real.log N * (N : ℝ) * ∑ p ∈ primeItv z y, (1 : ℝ) / ((p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
    _ ≤ Real.log N * (N : ℝ) * (1 / ((z : ℝ) - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlogx (by positivity))
        have hsub : ∑ p ∈ primeItv z y, (1 : ℝ) / ((p : ℝ) ^ 2)
            ≤ ∑ m ∈ Finset.Icc z y, (1 : ℝ) / ((m : ℝ) ^ 2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp; rw [primeItv, Finset.mem_filter] at hp; exact hp.1
          · intro _ _ _; positivity
        exact le_trans hsub (Salt.BrunLower.sum_one_div_sq_le hz)
    _ = Real.log N * (N : ℝ) / ((z : ℝ) - 1) := by ring

end Salt.Goldbach
