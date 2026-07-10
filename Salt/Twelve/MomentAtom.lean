/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.PhiAtom

/-!
# P1 — the one-dimensional moment atom (explicit-gaps sieve, card C2)

Two-sided evaluation, sharp up to an explicit `(W', a)`-constant `C`, of the
polynomial-weight moment sum

`∑_{r < z, sqf, (r,W')=1} (log r)^a / φ(r)
   = (φW'/W')·(log z)^{a+1}/(a+1) + O_{W',a}((1 + log z)^a)`.

The density is `φW'/W'` (NOT a `6/π²`-polluted squarefree density — the
coprimality restriction threads through and the classic Euler-product `6/π²`
cancels against `ζ(2)` per-prime; see the reassembly note in
`Salt/Maynard/PhiAtom.lean`).

## What lands here (sorry-free)

* `abel_lift` — the fully general Abel lift `a ↦ a+1`.  Given ANY weight `w`
  whose partial sums `T n = ∑_{i<n} w i` satisfy a two-sided base
  `|T n − M·log n| ≤ C₀` (`n ≥ 2`), partial summation against `(log ·)^a`
  produces `∑_{i<z} (log i)^a·w i = M·(log z)^{a+1}/(a+1) + O((1+log z)^a)`,
  with the main constant `1/(a+1)` EXACT (from the left-Riemann sum
  `∑ (log r)^a·(log(r+1)−log r)` for `∫ u^a du`).
* `moment_atom` — the card-C2 goal, reduced to the two-sided a=0 base.

## PORT-BLOCKER (sanctioned floor: "the a=0 two-sided base only")

The a=0 base is `phiAtomSum z W' = (φW'/W')·log z + O(1)`.  Its LOWER half is
`Salt.Maynard.phiAtom_lower` (landed, exact constant, elementary block
counting).  Its sharp UPPER half `phiAtom_upper` is a documented pre-existing
blocker (`Salt/Maynard/PhiAtom.lean`, lines 918-953): a C-node requiring
signed multiplicative-convolution + convergent Euler products
(`∑_d h(d)/d = 1`), out of scope for this card.  It enters `moment_atom` as the
explicit hypothesis `PhiUpperAtom W'`.  The Abel lift — the mandated floor —
lands unconditionally.
-/

open Finset

namespace Salt.Twelve

/-! ## Cast/log monotonicity helpers -/

private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma log_nat_mono_le {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

/-- `log ↑r ≤ log (↑r + 1)` (the `↑r + 1` cast form, for the Riemann sum). -/
private lemma log_le_log_succ (r : ℕ) :
    Real.log (r : ℝ) ≤ Real.log ((r : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  · exact Real.log_le_log (by exact_mod_cast h) (by linarith)

/-! ## L1 — the two-sided power-difference (finite-difference of `u^{a+1}`) -/

/-- For `0 ≤ u ≤ v`: `(a+1)·u^a·(v−u) ≤ v^{a+1} − u^{a+1} ≤ (a+1)·v^a·(v−u)`.
The mean-value bracket for `∫_u^v t^a dt`, proved via `geom_sum₂_mul`. -/
private lemma pow_sub_bounds (a : ℕ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ((a : ℝ) + 1) * u ^ a * (v - u) ≤ v ^ (a + 1) - u ^ (a + 1) ∧
      v ^ (a + 1) - u ^ (a + 1) ≤ ((a : ℝ) + 1) * v ^ a * (v - u) := by
  have hv : 0 ≤ v := hu.trans huv
  have hvu : 0 ≤ v - u := by linarith
  have hgeo : v ^ (a + 1) - u ^ (a + 1)
      = (∑ i ∈ Finset.range (a + 1), v ^ i * u ^ (a - i)) * (v - u) := by
    have h := geom_sum₂_mul v u (a + 1)
    simpa only [Nat.add_sub_cancel] using h.symm
  have hterm_lo : ∀ i ∈ Finset.range (a + 1), u ^ a ≤ v ^ i * u ^ (a - i) := by
    intro i hi
    have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hua : u ^ a = u ^ i * u ^ (a - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hia]
    rw [hua]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huv i) (pow_nonneg hu _)
  have hterm_hi : ∀ i ∈ Finset.range (a + 1), v ^ i * u ^ (a - i) ≤ v ^ a := by
    intro i hi
    have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hva : v ^ a = v ^ i * v ^ (a - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hia]
    rw [hva]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu huv (a - i)) (pow_nonneg hv _)
  have hsum_lo : ((a : ℝ) + 1) * u ^ a
      ≤ ∑ i ∈ Finset.range (a + 1), v ^ i * u ^ (a - i) := by
    have h := Finset.card_nsmul_le_sum _ _ _ hterm_lo
    rwa [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  have hsum_hi : (∑ i ∈ Finset.range (a + 1), v ^ i * u ^ (a - i))
      ≤ ((a : ℝ) + 1) * v ^ a := by
    have h := Finset.sum_le_card_nsmul _ _ _ hterm_hi
    rwa [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  refine ⟨?_, ?_⟩
  · rw [hgeo]
    calc ((a : ℝ) + 1) * u ^ a * (v - u)
        = (((a : ℝ) + 1) * u ^ a) * (v - u) := by ring
      _ ≤ (∑ i ∈ Finset.range (a + 1), v ^ i * u ^ (a - i)) * (v - u) :=
          mul_le_mul_of_nonneg_right hsum_lo hvu
  · rw [hgeo]
    calc (∑ i ∈ Finset.range (a + 1), v ^ i * u ^ (a - i)) * (v - u)
        ≤ (((a : ℝ) + 1) * v ^ a) * (v - u) := mul_le_mul_of_nonneg_right hsum_hi hvu
      _ = ((a : ℝ) + 1) * v ^ a * (v - u) := by ring

/-! ## L2 — the left-Riemann sum `Afwd = ∑ (log r)^a·(log(r+1)−log r)`

`Afwd z` under-approximates `∫_0^{log z} u^a du = (log z)^{a+1}/(a+1)`, with a
gap `≤ log 2 · (log z)^a` (increments `log(r+1)−log r ≤ log 2`).  This is where
the EXACT main constant `1/(a+1)` comes from. -/

private lemma afwd_bounds (a z : ℕ) :
    0 ≤ (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)
          - ∑ r ∈ Finset.range z,
              (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ))
      ∧ (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)
          - ∑ r ∈ Finset.range z,
              (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ))
        ≤ Real.log 2 * (Real.log (z : ℝ)) ^ a := by
  have hpos1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- telescoping identity for any power `k`
  have htele : ∀ k : ℕ,
      (∑ r ∈ Finset.range z, ((Real.log ((r : ℝ) + 1)) ^ k - (Real.log (r : ℝ)) ^ k))
        = (Real.log (z : ℝ)) ^ k - (0 : ℝ) ^ k := by
    intro k
    have h := Finset.sum_range_sub (fun n : ℕ => (Real.log (n : ℝ)) ^ k) z
    simpa only [Nat.cast_add_one, Nat.cast_zero, Real.log_zero] using h
  -- per-increment bound `log(r+1) − log r ≤ log 2`
  have hdiff_le : ∀ r : ℕ, Real.log ((r : ℝ) + 1) - Real.log (r : ℝ) ≤ Real.log 2 := by
    intro r
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simpa using hlog2
    · have hr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
      rw [← Real.log_div (by positivity) (by positivity)]
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ (by positivity)]
      linarith
  -- `Afwd ≤ midsum`
  have hle1 : (∑ r ∈ Finset.range z,
        (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ)))
      ≤ ∑ r ∈ Finset.range z,
          ((Real.log ((r : ℝ) + 1)) ^ (a + 1) - (Real.log (r : ℝ)) ^ (a + 1)) / ((a : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro r _
    set u : ℝ := Real.log (r : ℝ) with hu
    set v : ℝ := Real.log ((r : ℝ) + 1) with hv
    have hunn : (0 : ℝ) ≤ u := log_nat_nonneg r
    have huv : u ≤ v := log_le_log_succ r
    have hb := (pow_sub_bounds a hunn huv).1
    rw [le_div_iff₀ hpos1]
    nlinarith [hb]
  -- `midsum = target`
  have hmidsum : (∑ r ∈ Finset.range z,
        ((Real.log ((r : ℝ) + 1)) ^ (a + 1) - (Real.log (r : ℝ)) ^ (a + 1)) / ((a : ℝ) + 1))
      = (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1) := by
    rw [← Finset.sum_div, htele (a + 1), zero_pow (by omega : a + 1 ≠ 0), sub_zero]
  refine ⟨by linarith [hle1, hmidsum], ?_⟩
  -- upper on the gap
  rw [← hmidsum, ← Finset.sum_sub_distrib]
  calc (∑ r ∈ Finset.range z,
          (((Real.log ((r : ℝ) + 1)) ^ (a + 1) - (Real.log (r : ℝ)) ^ (a + 1)) / ((a : ℝ) + 1)
            - (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ))))
      ≤ ∑ r ∈ Finset.range z,
          ((Real.log ((r : ℝ) + 1)) ^ a - (Real.log (r : ℝ)) ^ a) * Real.log 2 := by
        apply Finset.sum_le_sum
        intro r _
        set u : ℝ := Real.log (r : ℝ) with hu
        set v : ℝ := Real.log ((r : ℝ) + 1) with hv
        have huv : u ≤ v := log_le_log_succ r
        have hvu : 0 ≤ v - u := by linarith
        have hbnd := pow_sub_bounds a (log_nat_nonneg r) huv
        have hvamua : 0 ≤ v ^ a - u ^ a := by
          have := pow_le_pow_left₀ (log_nat_nonneg r) huv a; linarith
        have hmid_le : (v ^ (a + 1) - u ^ (a + 1)) / ((a : ℝ) + 1) ≤ v ^ a * (v - u) := by
          rw [div_le_iff₀ hpos1]
          have hcomm : v ^ a * (v - u) * ((a : ℝ) + 1) = ((a : ℝ) + 1) * v ^ a * (v - u) := by ring
          rw [hcomm]; exact hbnd.2
        calc (v ^ (a + 1) - u ^ (a + 1)) / ((a : ℝ) + 1) - u ^ a * (v - u)
            ≤ v ^ a * (v - u) - u ^ a * (v - u) := by linarith [hmid_le]
          _ = (v ^ a - u ^ a) * (v - u) := by ring
          _ ≤ (v ^ a - u ^ a) * Real.log 2 :=
              mul_le_mul_of_nonneg_left (hdiff_le r) hvamua
    _ = Real.log 2 * ((Real.log (z : ℝ)) ^ a - (0 : ℝ) ^ a) := by
        rw [← htele a, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ => by ring)
    _ ≤ Real.log 2 * (Real.log (z : ℝ)) ^ a := by
        have h0 : (0 : ℝ) ≤ (0 : ℝ) ^ a := pow_nonneg le_rfl a
        nlinarith [h0, hlog2]

/-! ## The Abel lift (generic; the mandated floor)

Given a weight `w` with two-sided base `|∑_{i<n} w i − M·log n| ≤ C₀` for
`n ≥ 2`, partial summation against `(log ·)^a` lifts the estimate to the
`a`-th log-moment, with the main constant `1/(a+1)` EXACT and an
`(a`-uniform!) error constant `2·C₀ + M·log 2`. -/

private lemma abel_lift (w : ℕ → ℝ) (M C₀ : ℝ) (hM0 : 0 ≤ M)
    (hbase : ∀ n : ℕ, 2 ≤ n → |(∑ i ∈ Finset.range n, w i) - M * Real.log (n : ℝ)| ≤ C₀)
    (a z : ℕ) (hz : 2 ≤ z) :
    |(∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
        - M * (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)|
      ≤ (2 * C₀ + M * Real.log 2) * (1 + Real.log (z : ℝ)) ^ a := by
  classical
  have hC0 : 0 ≤ C₀ := (abs_nonneg _).trans (hbase 2 le_rfl)
  set g : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 1) - Real.log (i : ℝ) with hg
  set E : ℕ → ℝ := fun n => (∑ i ∈ Finset.range n, w i) - M * Real.log (n : ℝ) with hE
  have hbaseE : ∀ n : ℕ, 2 ≤ n → |E n| ≤ C₀ := by
    intro n hn; simpa only [hE] using hbase n hn
  -- partial sums of `g` telescope to `log`
  have hgsum : ∀ n : ℕ, (∑ i ∈ Finset.range n, g i) = Real.log (n : ℝ) := by
    intro n
    have h := Finset.sum_range_sub (fun m : ℕ => Real.log (m : ℝ)) n
    simp only [Nat.cast_zero, Real.log_zero, sub_zero] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hg, Nat.cast_add_one])
  -- Abel #1 (for the moment sum) and #2 (for `Afwd`)
  have hAbel1 : (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
      = (Real.log ((z - 1 : ℕ) : ℝ)) ^ a * (∑ i ∈ Finset.range z, w i)
        - ∑ i ∈ Finset.range (z - 1),
            ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a)
              * (∑ j ∈ Finset.range (i + 1), w j) := by
    simpa only [smul_eq_mul]
      using Finset.sum_range_by_parts (fun i => (Real.log (i : ℝ)) ^ a) w z
  have hAbel2 : (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)
      = (Real.log ((z - 1 : ℕ) : ℝ)) ^ a * Real.log (z : ℝ)
        - ∑ i ∈ Finset.range (z - 1),
            ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a)
              * Real.log ((i + 1 : ℕ) : ℝ) := by
    simpa only [smul_eq_mul, hgsum]
      using Finset.sum_range_by_parts (fun i => (Real.log (i : ℝ)) ^ a) g z
  -- master identity: `moment − M·Afwd = boundary·E − ∑ Δf·E`
  have hmaster :
      (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
        - M * (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)
      = (Real.log ((z - 1 : ℕ) : ℝ)) ^ a * E z
        - ∑ i ∈ Finset.range (z - 1),
            ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1) := by
    have hR :
        (∑ i ∈ Finset.range (z - 1),
            ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1))
          = (∑ i ∈ Finset.range (z - 1),
              ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a)
                * (∑ j ∈ Finset.range (i + 1), w j))
            - M * (∑ i ∈ Finset.range (z - 1),
                ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a)
                  * Real.log ((i + 1 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [hE]; ring)
    rw [hAbel1, hAbel2, hR, show E z
      = (∑ i ∈ Finset.range z, w i) - M * Real.log (z : ℝ) from rfl]
    ring
  -- error bound `|moment − M·Afwd| ≤ 2·C₀·(log z)^a`
  have hlogz : (0 : ℝ) ≤ Real.log (z : ℝ) := log_nat_nonneg z
  have hfz1 : (Real.log ((z - 1 : ℕ) : ℝ)) ^ a ≤ (Real.log (z : ℝ)) ^ a :=
    pow_le_pow_left₀ (log_nat_nonneg (z - 1)) (log_nat_mono_le (by omega : z - 1 ≤ z)) a
  have hfz1nn : 0 ≤ (Real.log ((z - 1 : ℕ) : ℝ)) ^ a := pow_nonneg (log_nat_nonneg (z - 1)) a
  -- telescoping of the increments `Δf`
  have hDisum : (∑ i ∈ Finset.range (z - 1),
        ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a))
      = (Real.log ((z - 1 : ℕ) : ℝ)) ^ a - (Real.log ((0 : ℕ) : ℝ)) ^ a :=
    Finset.sum_range_sub (fun n : ℕ => (Real.log (n : ℝ)) ^ a) (z - 1)
  have hper : ∀ i ∈ Finset.range (z - 1),
      |((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)|
        ≤ ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * C₀ := by
    intro i _
    have hDnn : 0 ≤ (Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a := by
      have := pow_le_pow_left₀ (log_nat_nonneg i)
        (log_nat_mono_le (by omega : i ≤ i + 1)) a
      linarith
    rcases Nat.eq_zero_or_pos i with h0 | hp
    · subst h0
      have : (Real.log ((0 + 1 : ℕ) : ℝ)) ^ a - (Real.log ((0 : ℕ) : ℝ)) ^ a = 0 := by
        norm_num
      rw [this]; simp
    · rw [abs_mul, abs_of_nonneg hDnn]
      exact mul_le_mul_of_nonneg_left (hbaseE (i + 1) (by omega)) hDnn
  have hbound : |(∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
        - M * (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)|
      ≤ 2 * C₀ * (Real.log (z : ℝ)) ^ a := by
    rw [hmaster]
    have htri : |(Real.log ((z - 1 : ℕ) : ℝ)) ^ a * E z
          - ∑ i ∈ Finset.range (z - 1),
              ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)|
        ≤ |(Real.log ((z - 1 : ℕ) : ℝ)) ^ a * E z|
          + |∑ i ∈ Finset.range (z - 1),
              ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans (by rw [abs_neg])
    have h1 : |(Real.log ((z - 1 : ℕ) : ℝ)) ^ a * E z| ≤ (Real.log (z : ℝ)) ^ a * C₀ := by
      rw [abs_mul, abs_of_nonneg hfz1nn]
      exact mul_le_mul hfz1 (hbaseE z hz) (abs_nonneg _) (pow_nonneg hlogz a)
    have h2 : |∑ i ∈ Finset.range (z - 1),
          ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)|
        ≤ (Real.log (z : ℝ)) ^ a * C₀ := by
      calc |∑ i ∈ Finset.range (z - 1),
              ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)|
          ≤ ∑ i ∈ Finset.range (z - 1),
              |((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range (z - 1),
              ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * C₀ :=
            Finset.sum_le_sum hper
        _ = ((Real.log ((z - 1 : ℕ) : ℝ)) ^ a - (Real.log ((0 : ℕ) : ℝ)) ^ a) * C₀ := by
            rw [← Finset.sum_mul, hDisum]
        _ ≤ (Real.log (z : ℝ)) ^ a * C₀ := by
            have h00 : 0 ≤ (Real.log ((0 : ℕ) : ℝ)) ^ a := pow_nonneg (log_nat_nonneg 0) a
            nlinarith [hfz1, h00, hC0]
    calc |(Real.log ((z - 1 : ℕ) : ℝ)) ^ a * E z
            - ∑ i ∈ Finset.range (z - 1),
                ((Real.log ((i + 1 : ℕ) : ℝ)) ^ a - (Real.log (i : ℝ)) ^ a) * E (i + 1)|
        ≤ (Real.log (z : ℝ)) ^ a * C₀ + (Real.log (z : ℝ)) ^ a * C₀ :=
          htri.trans (add_le_add h1 h2)
      _ = 2 * C₀ * (Real.log (z : ℝ)) ^ a := by ring
  -- main-term bound `|M·Afwd − M·(log z)^{a+1}/(a+1)| ≤ M·log 2·(log z)^a`
  obtain ⟨haf_lo, haf_hi⟩ := afwd_bounds a z
  have hAfwd_eq : (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)
      = ∑ r ∈ Finset.range z,
          (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ)) := by
    exact Finset.sum_congr rfl (fun r _ => by rw [hg])
  have hmain : |M * (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)
        - M * (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)|
      ≤ M * Real.log 2 * (Real.log (z : ℝ)) ^ a := by
    rw [hAfwd_eq]
    have hnn : 0 ≤ M * ((Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)
        - ∑ r ∈ Finset.range z,
            (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ))) :=
      mul_nonneg hM0 haf_lo
    rw [show M * (∑ r ∈ Finset.range z,
          (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ)))
        - M * (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)
        = -(M * ((Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)
            - ∑ r ∈ Finset.range z,
                (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ)))) from by ring,
      abs_neg, abs_of_nonneg hnn]
    calc M * ((Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)
            - ∑ r ∈ Finset.range z,
                (Real.log (r : ℝ)) ^ a * (Real.log ((r : ℝ) + 1) - Real.log (r : ℝ)))
        ≤ M * (Real.log 2 * (Real.log (z : ℝ)) ^ a) :=
          mul_le_mul_of_nonneg_left haf_hi hM0
      _ = M * Real.log 2 * (Real.log (z : ℝ)) ^ a := by ring
  -- triangle-combine
  have hfin : |(∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
        - M * (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)|
      ≤ (2 * C₀ + M * Real.log 2) * (Real.log (z : ℝ)) ^ a := by
    calc |(∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
            - M * (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)|
        ≤ |(∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i)
              - M * (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)|
          + |M * (∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * g i)
              - M * (Real.log (z : ℝ)) ^ (a + 1) / ((a : ℝ) + 1)| :=
          abs_sub_le _ _ _
      _ ≤ 2 * C₀ * (Real.log (z : ℝ)) ^ a + M * Real.log 2 * (Real.log (z : ℝ)) ^ a :=
          add_le_add hbound hmain
      _ = (2 * C₀ + M * Real.log 2) * (Real.log (z : ℝ)) ^ a := by ring
  -- absorb `(log z)^a ≤ (1 + log z)^a`
  refine hfin.trans ?_
  have hCnn : 0 ≤ 2 * C₀ + M * Real.log 2 :=
    add_nonneg (by linarith) (mul_nonneg hM0 (Real.log_nonneg (by norm_num)))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogz (by linarith) a) hCnn

/-! ## The a=0 base and the PORT-BLOCKER atom -/

/-- The narrow PORT-BLOCKER atom: the SHARP-constant UPPER bound of the a=0
base `∑_{r<x, sqf, (r,W')=1} 1/φ(r) ≤ (φW'/W')·log x + C`.

This is strictly narrower than `moment_atom` (a=0, upper direction only).  Its
matching LOWER bound `Salt.Maynard.phiAtom_lower` is landed (elementary block
counting, exact constant `φW'/W'`).  The sharp upper bound is the documented
blocker in `Salt/Maynard/PhiAtom.lean` (lines 918-953): a C-node requiring
signed multiplicative-convolution + convergent Euler products
(`∑_d h(d)/d = 1`, per-prime cancellation of the `6/π²`), out of scope here.
`phiAtom_upper_lossy` (4×-lossy) and `phiAtom_upper_fallback` are the landed
non-sharp substitutes; neither is sharp enough for the O(1) a=0 error. -/
def PhiUpperAtom (W' : ℕ) : Prop :=
  ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    Salt.Maynard.phiAtomSum x W' ≤ (Nat.totient W' / W' : ℝ) * Real.log (x : ℝ) + C

/-- **P1 — the one-dimensional moment atom (card C2).**

Two-sided (note the `|·|`), sharp up to the explicit `(W', a)`-constant `C`
(bound BEFORE `z`, preserving R-uniformity), with density `φW'/W'` (NOT
`6/π²`-polluted).  Conditional on the narrow a=0 sharp-upper PORT-BLOCKER
`PhiUpperAtom W'`; discharging that (i.e. `phiAtom_upper`) makes this
unconditional with no other change. -/
theorem moment_atom (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (a : ℕ)
    (hUpper : PhiUpperAtom W') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℕ, 2 ≤ z →
      |(∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r) ^ a / (Nat.totient r : ℝ))
        - (Nat.totient W' / W' : ℝ) * (Real.log z) ^ (a + 1) / (a + 1)|
      ≤ C * (1 + Real.log z) ^ a := by
  classical
  obtain ⟨CU, hCU⟩ := hUpper
  obtain ⟨CL, hCL⟩ := Salt.Maynard.phiAtom_lower W' hW'.ne_zero
  set M : ℝ := (Nat.totient W' / W' : ℝ) with hM
  set w : ℕ → ℝ := fun i =>
    if (Squarefree i ∧ i.Coprime W') then (1 : ℝ) / (Nat.totient i : ℝ) else 0 with hw
  set C₀ : ℝ := max CL CU with hC0def
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  -- partial sums of `w` are `phiAtomSum`
  have hTsum : ∀ n : ℕ, (∑ i ∈ Finset.range n, w i) = Salt.Maynard.phiAtomSum n W' := by
    intro n
    rw [Salt.Maynard.phiAtomSum, Salt.Maynard.sqfCop, Finset.sum_filter]
  -- two-sided base for `w`
  have hbase : ∀ n : ℕ, 2 ≤ n →
      |(∑ i ∈ Finset.range n, w i) - M * Real.log (n : ℝ)| ≤ C₀ := by
    intro n hn
    rw [hTsum n, abs_le]
    have hlo := hCL n hn
    have hhi := hCU n hn
    refine ⟨?_, ?_⟩
    · have : -CL ≤ Salt.Maynard.phiAtomSum n W' - M * Real.log (n : ℝ) := by linarith
      have hCL0 : -C₀ ≤ -CL := neg_le_neg (le_max_left _ _)
      linarith
    · have : Salt.Maynard.phiAtomSum n W' - M * Real.log (n : ℝ) ≤ CU := by linarith
      have hCU0 : CU ≤ C₀ := le_max_right _ _
      linarith
  -- rewrite the moment sum into `∑ (log i)^a · w i`
  have hmom : ∀ z : ℕ,
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r) ^ a / (Nat.totient r : ℝ))
        = ∑ i ∈ Finset.range z, (Real.log (i : ℝ)) ^ a * w i := by
    intro z
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hw]
    by_cases hP : Squarefree i ∧ i.Coprime W'
    · rw [if_pos hP, if_pos hP, mul_one_div]
    · rw [if_neg hP, if_neg hP, mul_zero]
  have hC0nn : 0 ≤ C₀ := (abs_nonneg _).trans (hbase 2 le_rfl)
  refine ⟨2 * C₀ + M * Real.log 2, ?_, ?_⟩
  · have : 0 ≤ M * Real.log 2 := mul_nonneg hMnn (Real.log_nonneg (by norm_num))
    linarith
  · intro z hz
    rw [hmom z]
    exact abel_lift w M C₀ hMnn hbase a z hz

/-! ## PORT-BLOCKER — the `gMult`-weight corollary `moment_atom_g`

Deferred (card: "if time permits — else PORT-BLOCKER as a separate lemma").
The intended statement (NOT frozen; needs Fable-tier design of the exact form):
for `r` with all prime factors `> D` (so `gMult r = ∏_{p∣r}(p−2) > 0`; note
`gMult` VANISHES when `2 ∣ r`, hence the coprime-to-`W' = primorial D`
restriction is load-bearing, not cosmetic),

    ∑_{r<z, sqf, (r,W')=1} (log r)^a / gMult r
      = (φW'/W')·(log z)^{a+1}/(a+1)·(1 + O(1/D)) + O_{W',a}((1+log z)^a).

Route (the sum-level `∏(p−1)/(p−2)` transfer, landed pattern
`Salt.Maynard.Ag_le_A1_mul` + `euler_tail_L` in `Salt/Maynard/EulerTailL.lean`):
`φ(r)/gMult(r) = ∏_{p∣r}(1 + 1/(p−2)) = 1 + O(ω(r)/D)` for primes `> D`, a
multiplicative `1 + O(1/D)` correction absorbed into `C` (or stated explicitly).
Two obstructions keep this out of THIS card's scope: (i) `Ag_le_A1_mul` is
hardwired to `W k`/`D₀ k`, needing the C3 free-`W` generalization sweep first;
(ii) the exact `(D, W')`-parameterized statement shape is a design decision
gated on C1's `F★` degree.  Once `moment_atom` is unconditional (i.e.
`phiAtom_upper` lands), `moment_atom_g` is `moment_atom` composed with the
transfer atom. -/

end Salt.Twelve
