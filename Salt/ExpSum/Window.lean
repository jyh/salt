/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.ExpSum.ZetaBlock

/-!
# The per-`k` window discharge of the ζ-block sandwich (`LITT-COVER`)

`zeta_block_bound` (`ZetaBlock.lean`) collapses the block estimate once the
scale `λ = (t/2π)·(k−1)!·(2N+k)^{−k}` sits in the honest van der Corput band
`[N^{−3+8/2^k}, N^{−1}]`.  This file discharges that band from a clean window
in `(t, N)` alone.

* `zeta_block_window` (`k ≥ 4`): for `N ≥ (k!)^6` and
  `t ∈ [N^{k−2}/(k−2)!, N^{k−1}/(k−1)!]` (the factorial-shifted window),
  `‖∑_{N<n≤2N} eR(φ t n)‖ ≤ C·N^{1−1/(2^k−2)}`.
* `zeta_block_window_meet`: adjacent windows tile exactly — window `k`'s upper
  edge equals window `(k+1)`'s lower edge (for `LITT-STRIP`'s gluing).
* `zeta_block_window_three` (the `k=3` seam): the third-derivative regime
  `t ∈ [27π·N, N²/2]`, via `zeta_block_bound 3`.

The floor `N₀ = (k!)^6` is honest: the lower edge needs
`2π·3^k ≤ N^{1−8/2^k}`, and with `N ≥ (k!)^6` this reduces to
`(k!)^3 ≥ 8·3^k ≥ 2π·3^k`, exactly `eight_mul_three_pow_le_factorial_cube`.
The upper edge needs no floor (`λ ≤ N^{−1}/(2π·2^k)` for every `N ≥ 1`).
-/

namespace Salt.ExpSum

open Real Finset

/-- Factorial-vs-exponential floor: `8·3^k ≤ (k!)^3` for `k ≥ 4`.  This is the
arithmetic heart of the `N₀ = (k!)^6` window floor: it feeds `(k!)^3 ≤ N^{1/2}`
into the lower-edge margin `2π·3^k ≤ N^{1−8/2^k}` (with `2π ≤ 8`). -/
lemma eight_mul_three_pow_le_factorial_cube (k : ℕ) (hk : 4 ≤ k) :
    8 * 3 ^ k ≤ (k.factorial) ^ 3 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      have h3 : 3 ≤ (n + 1) ^ 3 := by
        have hle : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
        omega
      calc 8 * 3 ^ (n + 1) = 3 * (8 * 3 ^ n) := by ring
        _ ≤ (n + 1) ^ 3 * n.factorial ^ 3 := Nat.mul_le_mul h3 ih
        _ = (n + 1).factorial ^ 3 := by rw [Nat.factorial_succ]; ring

/-- **Stone 1 — the `k ≥ 4` window (`LITT-COVER`).**  On the factorial-shifted
window `t ∈ [N^{k−2}/(k−2)!, N^{k−1}/(k−1)!]` with floor `N₀ = (k!)^6`, the
block estimate collapses to the single power `C·N^{1−1/(2^k−2)}`.  The proof
discharges `zeta_block_bound`'s `λ`-sandwich from the window inequalities. -/
theorem zeta_block_window (k : ℕ) (hk : 4 ≤ k) : ∃ C N₀ : ℝ, 1 ≤ C ∧
    ∀ (t : ℝ) (N : ℕ), N₀ ≤ (N : ℝ) →
      (N : ℝ) ^ ((k : ℝ) - 2) / ((k - 2).factorial : ℝ) ≤ t →
      t ≤ (N : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ) →
      ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖
        ≤ C * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ k - 2)) := by
  obtain ⟨C, hC1, hCb⟩ := zeta_block_bound k (by omega)
  refine ⟨C, (k.factorial : ℝ) ^ 6, hC1, ?_⟩
  intro t N hN0 hlo hhi
  -- basic positivity / range facts
  have hfac1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans (one_le_pow₀ hfac1) hN0
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hkN : k ≤ N := by
    have h1 : (k : ℝ) ≤ (N : ℝ) :=
      calc (k : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.self_le_factorial k
        _ ≤ (k.factorial : ℝ) ^ 6 := le_self_pow₀ hfac1 (by norm_num)
        _ ≤ (N : ℝ) := hN0
    exact_mod_cast h1
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  have h2πpos : (0 : ℝ) < 2 * π := by positivity
  have hf1 : (1 : ℝ) ≤ ((k - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 1)
  have hf2 : (1 : ℝ) ≤ ((k - 2).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - 2)
  have hf1pos : (0 : ℝ) < ((k - 1).factorial : ℝ) := lt_of_lt_of_le one_pos hf1
  have hf2pos : (0 : ℝ) < ((k - 2).factorial : ℝ) := lt_of_lt_of_le one_pos hf2
  have hbaseN : 0 < 2 * N + k := by omega
  have hbase_pos : (0 : ℝ) < ((2 * N + k : ℕ) : ℝ) := by exact_mod_cast hbaseN
  have hden_pos : (0 : ℝ) < ((2 * N + k : ℕ) : ℝ) ^ k := pow_pos hbase_pos k
  have hDne : (((2 * N + k : ℕ) : ℝ) ^ k) ≠ 0 := ne_of_gt hden_pos
  have htpos : 0 < t := by
    have hp : (0 : ℝ) < (N : ℝ) ^ ((k : ℝ) - 2) / ((k - 2).factorial : ℝ) :=
      div_pos (Real.rpow_pos_of_pos hNpos _) hf2pos
    linarith
  -- the scale and the clearing identity  λ·(2π·D) = t·(k−1)!
  set lam : ℝ := t / (2 * π) * ((k - 1).factorial : ℝ) * (((2 * N + k : ℕ) : ℝ) ^ k)⁻¹
    with hlam_def
  have hlam_eq :
      lam * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k)) = t * ((k - 1).factorial : ℝ) := by
    rw [hlam_def]; field_simp
  -- base bounds:  (2N)^k ≤ (2N+k)^k ≤ (3N)^k
  have hbase_up : ((2 * N + k : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
    have h : 2 * N + k ≤ 3 * N := by omega
    calc ((2 * N + k : ℕ) : ℝ) ≤ ((3 * N : ℕ) : ℝ) := by exact_mod_cast h
      _ = 3 * (N : ℝ) := by push_cast; ring
  have hbase_lo : 2 * (N : ℝ) ≤ ((2 * N + k : ℕ) : ℝ) := by
    have h : 2 * N ≤ 2 * N + k := by omega
    calc 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 * N + k : ℕ) : ℝ) := by exact_mod_cast h
  have hden_up : ((2 * N + k : ℕ) : ℝ) ^ k ≤ (3 : ℝ) ^ k * (N : ℝ) ^ k := by
    calc ((2 * N + k : ℕ) : ℝ) ^ k ≤ (3 * (N : ℝ)) ^ k :=
          pow_le_pow_left₀ (le_of_lt hbase_pos) hbase_up k
      _ = (3 : ℝ) ^ k * (N : ℝ) ^ k := by rw [mul_pow]
  have hden_lo : (2 : ℝ) ^ k * (N : ℝ) ^ k ≤ ((2 * N + k : ℕ) : ℝ) ^ k := by
    calc (2 : ℝ) ^ k * (N : ℝ) ^ k = (2 * (N : ℝ)) ^ k := by rw [mul_pow]
      _ ≤ ((2 * N + k : ℕ) : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hbase_lo k
  -- lower-edge margin:  2π·3^k ≤ N^{1−8/2^k}  (the honest N₀ = (k!)^6 absorption)
  have hmargin : 2 * π * (3 : ℝ) ^ k ≤ (N : ℝ) ^ (1 - 8 / (2 : ℝ) ^ k) := by
    have hs1 : 2 * π * (3 : ℝ) ^ k ≤ 8 * (3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_le_four]) (by positivity)
    have hs2 : (8 : ℝ) * (3 : ℝ) ^ k ≤ (k.factorial : ℝ) ^ 3 := by
      exact_mod_cast eight_mul_three_pow_le_factorial_cube k hk
    have hhalf : ((k.factorial : ℝ) ^ 6) ^ (1 / 2 : ℝ) = (k.factorial : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast (k.factorial : ℝ) 6, ← Real.rpow_mul (by positivity),
          ← Real.rpow_natCast (k.factorial : ℝ) 3]
      norm_num
    have hs3 : (k.factorial : ℝ) ^ 3 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← hhalf]; exact Real.rpow_le_rpow (by positivity) hN0 (by norm_num)
    have hs4 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 - 8 / (2 : ℝ) ^ k) := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ k :=
        calc (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
          _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk
      have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hbnd : 8 / (2 : ℝ) ^ k ≤ 1 / 2 := by
        rw [div_le_div_iff₀ h2kpos (by norm_num)]; linarith
      linarith
    linarith [hs1, hs2, hs3, hs4]
  -- numerator lower bound:  N^{k−2} ≤ t·(k−1)!  (keeps (k−1)!, no (k−2)! penalty)
  have hnum : (N : ℝ) ^ ((k : ℝ) - 2) ≤ t * ((k - 1).factorial : ℝ) := by
    have e1 : (N : ℝ) ^ ((k : ℝ) - 2) ≤ t * ((k - 2).factorial : ℝ) :=
      (div_le_iff₀ hf2pos).mp hlo
    have hfle : ((k - 2).factorial : ℝ) ≤ ((k - 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : k - 2 ≤ k - 1)
    exact le_trans e1 (mul_le_mul_of_nonneg_left hfle (le_of_lt htpos))
  -- assemble the lower sandwich:  N^{−3+8/2^k} ≤ λ
  have hcore : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k))
      ≤ t * ((k - 1).factorial : ℝ) := by
    have hA : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k))
        ≤ (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * ((3 : ℝ) ^ k * (N : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_up (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hB : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * ((3 : ℝ) ^ k * (N : ℝ) ^ k))
        ≤ (N : ℝ) ^ ((k : ℝ) - 2) := by
      have heq1 : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) * (2 * π * ((3 : ℝ) ^ k * (N : ℝ) ^ k))
          = (2 * π * (3 : ℝ) ^ k) * (N : ℝ) ^ ((-3 + 8 / (2 : ℝ) ^ k) + (k : ℝ)) := by
        rw [← Real.rpow_natCast (N : ℝ) k,
            Real.rpow_add hNpos (-3 + 8 / (2 : ℝ) ^ k) (k : ℝ)]
        ring
      rw [heq1]
      have heq2 : (N : ℝ) ^ (1 - 8 / (2 : ℝ) ^ k)
            * (N : ℝ) ^ ((-3 + 8 / (2 : ℝ) ^ k) + (k : ℝ)) = (N : ℝ) ^ ((k : ℝ) - 2) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      rw [← heq2]
      exact mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg (le_of_lt hNpos) _)
    exact le_trans (le_trans hA hB) hnum
  have hrlo : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ k) ≤ lam := by
    rw [← hlam_eq] at hcore
    exact le_of_mul_le_mul_right hcore (mul_pos h2πpos hden_pos)
  -- assemble the upper sandwich:  λ ≤ N^{−1}
  have hnum_up : t * ((k - 1).factorial : ℝ) ≤ (N : ℝ) ^ ((k : ℝ) - 1) :=
    (le_div_iff₀ hf1pos).mp hhi
  have hconst1 : (1 : ℝ) ≤ 2 * π * (2 : ℝ) ^ k := by
    have h2π1 : (1 : ℝ) ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h2k1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc (1 : ℝ) ≤ 2 * π := h2π1
      _ ≤ 2 * π * (2 : ℝ) ^ k := le_mul_of_one_le_right (le_of_lt h2πpos) h2k1
  have hcore_up : t * ((k - 1).factorial : ℝ)
      ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k)) := by
    have hA' : (N : ℝ) ^ ((k : ℝ) - 1)
        ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * ((2 : ℝ) ^ k * (N : ℝ) ^ k)) := by
      have heq : (N : ℝ) ^ (-1 : ℝ) * (2 * π * ((2 : ℝ) ^ k * (N : ℝ) ^ k))
          = (2 * π * (2 : ℝ) ^ k) * (N : ℝ) ^ ((-1 : ℝ) + (k : ℝ)) := by
        rw [← Real.rpow_natCast (N : ℝ) k, Real.rpow_add hNpos (-1) (k : ℝ)]
        ring
      rw [heq]
      have heq2 :
          (N : ℝ) ^ ((k : ℝ) - 1) = (1 : ℝ) * (N : ℝ) ^ ((-1 : ℝ) + (k : ℝ)) := by
        rw [one_mul]
        congr 1
        ring
      rw [heq2]
      exact mul_le_mul_of_nonneg_right hconst1 (Real.rpow_nonneg (le_of_lt hNpos) _)
    have hB' : (N : ℝ) ^ (-1 : ℝ) * (2 * π * ((2 : ℝ) ^ k * (N : ℝ) ^ k))
        ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + k : ℕ) : ℝ) ^ k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_lo (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNpos) _)
    exact le_trans hnum_up (le_trans hA' hB')
  have hrhi : lam ≤ (N : ℝ) ^ (-1 : ℝ) := by
    rw [← hlam_eq] at hcore_up
    exact le_of_mul_le_mul_right hcore_up (mul_pos h2πpos hden_pos)
  exact hCb t N lam htpos hkN hlam_def hrlo hrhi

/-- **Stone 2a — window meet (for `LITT-STRIP`).**  Window `k`'s upper edge
`N^{k−1}/(k−1)!` equals window `(k+1)`'s lower edge `N^{(k+1)−2}/((k+1)−2)!`:
the factorial-shifted windows tile the `t`-axis exactly (`rfl`-grade after the
Nat-subtraction and cast normalise). -/
lemma zeta_block_window_meet (N k : ℕ) :
    (N : ℝ) ^ (((k + 1 : ℕ) : ℝ) - 2) / (((k + 1) - 2).factorial : ℝ)
      = (N : ℝ) ^ ((k : ℝ) - 1) / ((k - 1).factorial : ℝ) := by
  have hfac : (k + 1) - 2 = k - 1 := by omega
  have hexp : ((k + 1 : ℕ) : ℝ) - 2 = (k : ℝ) - 1 := by push_cast; ring
  rw [hfac, hexp]

/-- **Stone 2b — the `k=3` seam (the third-derivative regime).**  On the window
`t ∈ [27π·N, N²/2]` with floor `N ≥ 3`, the block estimate collapses to
`C·N^{1−1/(2³−2)} = C·N^{5/6}` via `zeta_block_bound 3` (the `k=3` instance of
the tower is exactly the third-derivative test).  The upper edge
`N²/2 = N^{(3)−1}/(3−1)!` meets window `4`'s lower edge (`zeta_block_window_meet
3`).  The lower edge is constant-shifted (`27π·N`, not `N`): at `k=3` the
exponent `1−8/2³` is `0`, so the sandwich `λ ≥ N^{−2}` cannot be won from the
unshifted edge `t ≥ N` (it misses by the constant `54π`).  RESIDUAL: the strip
`t ∈ [N, 27π·N]` between this seam and `zeta_block_kusmin` (`t ≤ N`) is left
uncovered — a bounded multiplicative strip (see the module docstring). -/
theorem zeta_block_window_three : ∃ C N₀ A : ℝ, 1 ≤ C ∧ 0 < A ∧
    ∀ (t : ℝ) (N : ℕ), N₀ ≤ (N : ℝ) → A * (N : ℝ) ≤ t →
      t ≤ (N : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ) →
      ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), eR (phi t n)‖
        ≤ C * (N : ℝ) ^ (1 - 1 / ((2 : ℝ) ^ 3 - 2)) := by
  obtain ⟨C, hC1, hCb⟩ := zeta_block_bound 3 (by norm_num)
  refine ⟨C, 3, 27 * π, hC1, by positivity, ?_⟩
  intro t N hN0 hlo hhi
  have hN3 : 3 ≤ N := by exact_mod_cast hN0
  have hNRpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hπpos : (0 : ℝ) < π := Real.pi_pos
  have h2πpos : (0 : ℝ) < 2 * π := by positivity
  have htpos : 0 < t := lt_of_lt_of_le (mul_pos (by positivity) hNRpos) hlo
  have hbaseN : 0 < 2 * N + 3 := by omega
  have hbase_pos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) := by exact_mod_cast hbaseN
  have hden_pos : (0 : ℝ) < ((2 * N + 3 : ℕ) : ℝ) ^ 3 := pow_pos hbase_pos 3
  have hDne : (((2 * N + 3 : ℕ) : ℝ) ^ 3) ≠ 0 := ne_of_gt hden_pos
  have hfac2 : ((3 - 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  set lam : ℝ := t / (2 * π) * ((3 - 1).factorial : ℝ) * (((2 * N + 3 : ℕ) : ℝ) ^ 3)⁻¹
    with hlam_def
  have hlam_eq0 :
      lam * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) = t * ((3 - 1).factorial : ℝ) := by
    rw [hlam_def]; field_simp
  have hlam_eq : lam * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) = 2 * t := by
    rw [hlam_eq0, hfac2]; ring
  -- window upper edge is N²/2
  have hue : (N : ℝ) ^ ((3 : ℝ) - 1) / ((3 - 1).factorial : ℝ) = (N : ℝ) ^ 2 / 2 := by
    have e2 : ((3 : ℝ) - 1) = ((2 : ℕ) : ℝ) := by norm_num
    rw [hfac2, e2, Real.rpow_natCast]
  rw [hue] at hhi
  -- base bounds:  8N³ ≤ (2N+3)³ ≤ 27N³
  have hden_up : ((2 * N + 3 : ℕ) : ℝ) ^ 3 ≤ 27 * (N : ℝ) ^ 3 := by
    have h : ((2 * N + 3 : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
      have hn : 2 * N + 3 ≤ 3 * N := by omega
      calc ((2 * N + 3 : ℕ) : ℝ) ≤ ((3 * N : ℕ) : ℝ) := by exact_mod_cast hn
        _ = 3 * (N : ℝ) := by push_cast; ring
    calc ((2 * N + 3 : ℕ) : ℝ) ^ 3 ≤ (3 * (N : ℝ)) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h 3
      _ = 27 * (N : ℝ) ^ 3 := by ring
  have hden_lo : 8 * (N : ℝ) ^ 3 ≤ ((2 * N + 3 : ℕ) : ℝ) ^ 3 := by
    have h : 2 * (N : ℝ) ≤ ((2 * N + 3 : ℕ) : ℝ) := by
      have hn : 2 * N ≤ 2 * N + 3 := by omega
      calc 2 * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 * N + 3 : ℕ) : ℝ) := by exact_mod_cast hn
    calc 8 * (N : ℝ) ^ 3 = (2 * (N : ℝ)) ^ 3 := by ring
      _ ≤ ((2 * N + 3 : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  -- lower sandwich:  N^{−2} ≤ λ
  have hprod : (N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hNRpos,
        show (-2 : ℝ) + ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  have hcore_lo :
      (N : ℝ) ^ (-2 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) ≤ 2 * t := by
    have hA : (N : ℝ) ^ (-2 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3))
        ≤ (N : ℝ) ^ (-2 : ℝ) * (2 * π * (27 * (N : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_up (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNRpos) _)
    have hB : (N : ℝ) ^ (-2 : ℝ) * (2 * π * (27 * (N : ℝ) ^ 3)) = 54 * π * (N : ℝ) := by
      rw [show (N : ℝ) ^ (-2 : ℝ) * (2 * π * (27 * (N : ℝ) ^ 3))
            = 2 * π * 27 * ((N : ℝ) ^ (-2 : ℝ) * (N : ℝ) ^ 3) by ring, hprod]
      ring
    calc (N : ℝ) ^ (-2 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3))
        ≤ 54 * π * (N : ℝ) := by rw [← hB]; exact hA
      _ ≤ 2 * t := by nlinarith [hlo]
  have hrlo : (N : ℝ) ^ (-3 + 8 / (2 : ℝ) ^ 3) ≤ lam := by
    rw [show (-3 + 8 / (2 : ℝ) ^ 3 : ℝ) = -2 by norm_num]
    rw [← hlam_eq] at hcore_lo
    exact le_of_mul_le_mul_right hcore_lo (mul_pos h2πpos hden_pos)
  -- upper sandwich:  λ ≤ N^{−1}
  have hprod1 : (N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ 3 = (N : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hNRpos,
        show (-1 : ℝ) + ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcore_up :
      2 * t ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) := by
    have hstep : (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3))
        ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden_lo (le_of_lt h2πpos))
        (Real.rpow_nonneg (le_of_lt hNRpos) _)
    have hEq :
        (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3)) = 16 * π * (N : ℝ) ^ 2 := by
      rw [show (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3))
            = 2 * π * 8 * ((N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ 3) by ring, hprod1]
      ring
    calc 2 * t ≤ (N : ℝ) ^ 2 := by linarith [hhi]
      _ ≤ 16 * π * (N : ℝ) ^ 2 := by
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * π - 1 by linarith [Real.pi_gt_three])
            (sq_nonneg (N : ℝ))]
      _ = (N : ℝ) ^ (-1 : ℝ) * (2 * π * (8 * (N : ℝ) ^ 3)) := hEq.symm
      _ ≤ (N : ℝ) ^ (-1 : ℝ) * (2 * π * (((2 * N + 3 : ℕ) : ℝ) ^ 3)) := hstep
  have hrhi : lam ≤ (N : ℝ) ^ (-1 : ℝ) := by
    rw [← hlam_eq] at hcore_up
    exact le_of_mul_le_mul_right hcore_up (mul_pos h2πpos hden_pos)
  exact hCb t N lam htpos hN3 hlam_def hrlo hrhi

end Salt.ExpSum
