/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Mid
import Salt.Vk.Growth
import Salt.ExpSum.Strip

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
`vk_window_scale_prefix` → `vk_window_mid_prefix`, mirroring the landed full-window chain).
-/

namespace Salt.Vk

open Complex Finset Real Salt.ExpSum
open scoped BigOperators

/-! ## The prefix ladder (min-trick) -/

/-- **Prefix ladder.**  The prefix-of-window analogue of `vk_ladder_bound`: given per-sub-block
**prefix** bounds `‖∑_{(c i, z]} f‖ ≤ 8·P^{1−ρ}` (`c i = min(N+iP)(2N)`, any `z ≤ c(i+1)`), every
prefix `(N, y]` (`N < y ≤ 2N`) obeys `‖∑_{(N,y]} f‖ ≤ 10·N·P^{−ρ}`.  Via the clipped endpoint
sequence `c' i = min (c i) y` (monotone, `c' 0 = N`, `c' Q = y`) fed through `vk_sum_Ioc_split`. -/
theorem vk_ladder_prefix {E : Type*} [NormedAddCommGroup E] (f : ℤ → E)
    {P N : ℕ} {ρ : ℝ} (hP : 1 ≤ P) (h4P : 4 * P ≤ N)
    (hBp : ∀ i, i < ⌈(N : ℝ) / (P : ℝ)⌉₊ → ∀ z : ℤ,
      min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) < z →
      z ≤ min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) →
      ‖∑ n ∈ Finset.Ioc (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)) z, f n‖
        ≤ 8 * (P : ℝ) ^ (1 - ρ))
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, f n‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h4PR : 4 * (P : ℝ) ≤ (N : ℝ) := by exact_mod_cast h4P
  set Q : ℕ := ⌈(N : ℝ) / (P : ℝ)⌉₊ with hQdef
  set c : ℕ → ℤ := fun i => min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) with hc
  set c' : ℕ → ℤ := fun i => min (c i) y with hc'
  have hc0 : c 0 = (N : ℤ) := by simp only [hc, Nat.cast_zero, zero_mul, add_zero]; omega
  have hQP : (N : ℝ) ≤ (Q : ℝ) * (P : ℝ) := by
    have hle : (N : ℝ) / (P : ℝ) ≤ (Q : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hP0] at hle; exact hle
  have hcQ : c Q = 2 * (N : ℤ) := by
    simp only [hc]
    apply min_eq_right
    have : (N : ℤ) ≤ (Q : ℤ) * (P : ℤ) := by exact_mod_cast hQP
    linarith
  -- c' is monotone; c' 0 = N, c' Q = y
  have hc'mono : Monotone c' := by
    intro i j hij
    simp only [hc', hc]
    have : (i : ℤ) * (P : ℤ) ≤ (j : ℤ) * (P : ℤ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
    omega
  have hc'0 : c' 0 = (N : ℤ) := by simp only [hc', hc0]; omega
  have hc'Q : c' Q = y := by simp only [hc', hcQ]; omega
  -- telescope the prefix
  have hsplit := vk_sum_Ioc_split f c' hc'mono Q
  rw [hc'0, hc'Q] at hsplit
  rw [hsplit]
  -- per-block prefix bound
  have hblk : ∀ i ∈ Finset.range Q,
      ‖∑ n ∈ Finset.Ioc (c' i) (c' (i + 1)), f n‖ ≤ 8 * (P : ℝ) ^ (1 - ρ) := by
    intro i hi
    have hiQ : i < Q := Finset.mem_range.mp hi
    by_cases hlt : c' i < c' (i + 1)
    · -- nonempty prefix of block i: c' i = c i
      have hci : c' i = c i := by
        simp only [hc'] at hlt ⊢
        have hle : c' (i + 1) ≤ y := by simp only [hc']; omega
        omega
      have hz2 : c' (i + 1) ≤ min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N) := by
        simp only [hc', hc]; push_cast; omega
      rw [hci]
      refine hBp i hiQ (c' (i + 1)) ?_ hz2
      change c i < c' (i + 1)
      rw [← hci]; exact hlt
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
      positivity
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hblk) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- arithmetic: Q · 8 P^{1-ρ} ≤ 10 N P^{-ρ}   (identical to vk_ladder_bound)
  have hQlt : (Q : ℝ) < (N : ℝ) / (P : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hQPub : (Q : ℝ) * (P : ℝ) ≤ (N : ℝ) + (P : ℝ) := by
    calc (Q : ℝ) * (P : ℝ) ≤ ((N : ℝ) / (P : ℝ) + 1) * (P : ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt hQlt) hP0.le
      _ = (N : ℝ) + (P : ℝ) := by field_simp
  have h4PQ : 4 * (P : ℝ) * (Q : ℝ) ≤ 5 * (N : ℝ) := by nlinarith [hQPub, h4PR, hP0]
  have hPsplit : (P : ℝ) ^ (1 - ρ) = (P : ℝ) * (P : ℝ) ^ (-ρ) := by
    rw [show (1 : ℝ) - ρ = 1 + (-ρ) by ring, Real.rpow_add hP0, Real.rpow_one]
  have hPρnn : (0 : ℝ) ≤ (P : ℝ) ^ (-ρ) := Real.rpow_nonneg hP0.le _
  rw [hPsplit]
  have hstep : (Q : ℝ) * (8 * ((P : ℝ) * (P : ℝ) ^ (-ρ)))
      = (8 * ((P : ℝ) * (Q : ℝ))) * (P : ℝ) ^ (-ρ) := by ring
  rw [hstep]
  apply mul_le_mul_of_nonneg_right _ hPρnn
  nlinarith [h4PQ]

/-! ## The prefix window bound (schedule-agnostic) -/

/-- Per-block `vk_block_core` at an interior block `N₀ ∈ [N, 2N]` (copy of `Window.vk_block_at`,
the private full-window helper, re-exposed here to feed the prefix ladder). -/
private lemma vk_block_prefix_at {k r P P' Y N N₀ : ℕ} {t ρ : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hP' : P' ≤ P)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hNle : N ≤ N₀) (hN₀le : N₀ ≤ 2 * N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ)) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖ ≤ 8 * (P : ℝ) ^ (1 - ρ) := by
  have hN0pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN1
  have hN₀0 : (0 : ℝ) < (N₀ : ℝ) := lt_of_lt_of_le hN0pos (by exact_mod_cast hNle)
  have hNleR : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hNle
  have hN₀leR : (N₀ : ℝ) ≤ (2 * N : ℝ) := by exact_mod_cast hN₀le
  have hπ : (0 : ℝ) < 2 * π := by positivity
  refine vk_block_core hk hr hρ hP' hY hD ?_ ⟨js, ?_, ?_, ?_, ?_⟩
  · have hkey : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k :=
      le_trans hW1 (by gcongr)
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    calc t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N₀ : ℝ) ^ k := hkey
      _ = ((N₀ : ℝ))⁻¹ * (N₀ : ℝ) ^ (k + 1) := by
          rw [pow_succ, mul_comm ((N₀ : ℝ) ^ k) (N₀ : ℝ), ← mul_assoc,
            inv_mul_cancel₀ (ne_of_gt hN₀0), one_mul]
  · rw [Finset.mem_Icc]; exact ⟨hjs2, hjsk⟩
  · have hpow : ((N₀ : ℝ)) ^ (js + 1) ≤ ((2 * N : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN₀0.le hN₀leR _
    calc (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
        ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)) := hW2a
      _ ≤ t / (2 * π * ((N₀ : ℝ)) ^ (js + 1)) := by gcongr
  · have hpow : ((N : ℝ)) ^ (js + 1) ≤ ((N₀ : ℝ)) ^ (js + 1) :=
      pow_le_pow_left₀ hN0pos.le hNleR _
    calc t * (Y : ℝ) / (2 * π * ((N₀ : ℝ)) ^ (js + 1))
        ≤ t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) := by gcongr
      _ ≤ 1 / 6 := hW2b
  · calc 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ) := hW2c
      _ ≤ (N₀ : ℝ) := hNleR

/-- **Prefix window bound.**  Prefix-of-window analogue of `vk_window_bound`: same five per-scale
worst-case `vk_block_core` hypotheses, but concluding the *prefix* bound
`‖∑_{(N,y]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}` for every `N < y ≤ 2N`.  Via `vk_ladder_prefix` with the
per-sub-block prefix bounds from `vk_block_prefix_at`. -/
theorem vk_window_prefix {k r P Y N : ℕ} {t ρ : ℝ} {js : ℕ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r)) (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (hP : 1 ≤ P) (h4P : 4 * P ≤ N) (hN1 : 1 ≤ N)
    (hjs2 : 2 ≤ js) (hjsk : js ≤ k - 1) (htpos : 0 < t)
    (hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ Real.log P)
    (hW1 : t * (((P + Y : ℕ) : ℝ)) ^ (k + 1) ≤ (N : ℝ) ^ k)
    (hW2a : (P : ℝ) ^ (-(js : ℝ) - ρ) / (4 * k)
      ≤ t / (2 * π * ((2 * N : ℝ)) ^ (js + 1)))
    (hW2b : t * (Y : ℝ) / (2 * π * ((N : ℝ)) ^ (js + 1)) ≤ 1 / 6)
    (hW2c : 4 * (k : ℝ) ^ 2 * (Y : ℝ) ≤ (N : ℝ))
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n)‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  apply vk_ladder_prefix (fun n => eR (phi t n)) hP h4P ?_ y hy1 hy2
  intro i hi z hz1 hz2
  have hN0Z : (0 : ℤ) ≤ (N : ℤ) := by positivity
  have hiP0 : (0 : ℤ) ≤ (i : ℤ) * (P : ℤ) := by positivity
  have hage : (N : ℤ) ≤ min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    le_min (by linarith) (by linarith)
  have hbma : min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)
      - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) ≤ (P : ℤ) := by
    have hstep : ((i : ℤ) + 1) * (P : ℤ) = (i : ℤ) * (P : ℤ) + (P : ℤ) := by ring
    have hP0Z : (0 : ℤ) ≤ (P : ℤ) := by positivity
    omega
  set N₀ : ℕ := (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hN₀def
  set P' : ℕ := (z - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N)).toNat with hP'def
  have haN₀ : (N₀ : ℤ) = min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (le_trans hN0Z hage)
  have hP'val : (P' : ℤ) = z - min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) :=
    Int.toNat_of_nonneg (by linarith [hz1])
  have hzval : z = (N₀ : ℤ) + (P' : ℤ) := by rw [haN₀, hP'val]; ring
  have hNleN₀ : N ≤ N₀ := by
    have : (N : ℤ) ≤ (N₀ : ℤ) := by rw [haN₀]; exact hage
    exact_mod_cast this
  have hN₀le2N : N₀ ≤ 2 * N := by
    have : (N₀ : ℤ) ≤ 2 * N := by rw [haN₀]; exact min_le_right _ _
    exact_mod_cast this
  have hP'le : P' ≤ P := by
    have : (P' : ℤ) ≤ (P : ℤ) := by rw [hP'val]; linarith [hz2, hbma]
    exact_mod_cast this
  rw [haN₀.symm, hzval]
  exact vk_block_prefix_at hk hr hρ hP'le hY hNleN₀ hN₀le2N hN1 hjs2 hjsk htpos hD hW1 hW2a hW2b
    hW2c

/-! ## The per-scale prefix discharge (schedule witness) -/

/-- Exp-monotone (copy of `Window.vk_exp_mono_le`, private). -/
private lemma vk_exp_mono_le {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : Real.log A ≤ Real.log B) : A ≤ B := by
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_log hA, Real.exp_log hB] at this

set_option maxHeartbeats 1600000 in
-- The ~30 margin discharges (copied from `vk_window_scale`) exceed the default budget.
/-- **Prefix per-scale theorem** — prefix-of-window analogue of `vk_window_scale`.  Same schedule
witness `P = ⌈N^{1−(m+2)/(k+1)}⌉`, `Y = ⌈P^{1/2}⌉`, `js = m+2` and margins; concludes the prefix
bound `‖∑_{(N,y]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}` for `N < y ≤ 2N`.  Body identical to `vk_window_scale`
except the final consumer is `vk_window_prefix`. -/
theorem vk_window_scale_prefix {k r m N P Y : ℕ} {t ρ : ℝ}
    (hk : 19 ≤ k) (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hρ : ρ = 1 / (16 * (k : ℝ) * r))
    (hm11 : 11 ≤ m) (hmk : m + 8 ≤ k) (hN1 : 1 ≤ N)
    (hP : P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊)
    (hY : Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊)
    (htlo : (N : ℝ) ^ (m - 1) < t) (hthi : t ≤ (N : ℝ) ^ m)
    (hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N)
    (hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N)
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n)‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := ⟨_, rfl⟩
  rw [← hqdef] at hP hDf
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmR11 : (11 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm11
  have hmkR : (m : ℝ) + 8 ≤ (k : ℝ) := by exact_mod_cast hmk
  have humc : (0 : ℝ) ≤ (m : ℝ) - 11 := by linarith
  have hvmc : (0 : ℝ) ≤ (k : ℝ) - (m : ℝ) - 8 := by linarith
  have hq0 : 0 ≤ q := by
    rw [hqdef, sub_nonneg, div_le_one hk1R]; linarith
  have hq1 : q ≤ 1 := by
    rw [hqdef]
    have : 0 ≤ ((m : ℝ) + 2) / ((k : ℝ) + 1) := by positivity
    linarith
  have hNR1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hj0 : 0 ≤ Real.log N := Real.log_nonneg hNR1
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlk0 : 0 ≤ Real.log (k : ℝ) := by
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ k by omega)
  have hkl2nn : 0 ≤ ((k : ℝ) + 1) * Real.log 2 := by positivity
  have hj8 : 8 ≤ Real.log N := by linarith [hjf, hkl2nn, hlk0]
  have hP1 : 1 ≤ P := by
    rw [hP, Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hNpos _
  have hPR1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
  have hPpos : (0 : ℝ) < (P : ℝ) := by linarith
  have hlP0 : 0 ≤ Real.log P := Real.log_nonneg hPR1
  have hY1 : 1 ≤ Y := by
    rw [hY, Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hPpos _
  have htpos : 0 < t :=
    lt_trans (show (0 : ℝ) < (N : ℝ) ^ (m - 1) by positivity) htlo
  have hlPlo : q * Real.log N ≤ Real.log P := vk_logP_ge hN1 hP
  have hlPub : Real.log P ≤ Real.log 2 + q * Real.log N := vk_logP_ub hN1 hq0 hP
  have hlYub : Real.log Y ≤ Real.log 2 + 1 / 2 * Real.log P := by
    have h := vk_logP_ub hP1 (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) hY
    linarith [h]
  have hltub : Real.log t ≤ (m : ℝ) * Real.log N := by
    calc Real.log t ≤ Real.log ((N : ℝ) ^ m) := Real.log_le_log htpos hthi
      _ = (m : ℝ) * Real.log N := by rw [Real.log_pow]
  have hltlo : ((m : ℝ) - 1) * Real.log N ≤ Real.log t := by
    have h1 : Real.log ((N : ℝ) ^ (m - 1)) ≤ Real.log t :=
      Real.log_le_log (by positivity) htlo.le
    rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h1
    exact h1
  have h2kl2 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ Real.log N := by linarith [hjf, hlk0]
  have h13 : 3 * Real.log 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * Real.log N := by
    nlinarith [h2kl2, mul_nonneg humc hj0, mul_nonneg hl20 hk1R.le]
  have h1mq : (1 - q) * Real.log N = ((m : ℝ) + 2) * Real.log N / ((k : ℝ) + 1) := by
    rw [hqdef]; field_simp; ring
  have h3l2q : 3 * Real.log 2 ≤ (1 - q) * Real.log N := by
    rw [h1mq, le_div_iff₀ hk1R]; linarith [h13]
  have hguardR : (4 : ℝ) * (P : ℝ) ≤ (N : ℝ) := by
    apply vk_exp_mono_le (by positivity) hNpos
    have h4P : Real.log (4 * (P : ℝ)) = 2 * Real.log 2 + Real.log P := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hPpos),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [h4P]; linarith [hlPub, h3l2q]
  have h4PN : 4 * P ≤ N := by exact_mod_cast hguardR
  have hD : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ Real.log P := le_trans hDf hlPlo
  have hYP : Y ≤ P := by
    rw [hY]
    apply Nat.ceil_le.mpr
    calc (P : ℝ) ^ ((1 : ℝ) / 2) ≤ (P : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hPR1 (by norm_num)
      _ = (P : ℝ) := Real.rpow_one _
  have hlogPY : Real.log ((P + Y : ℕ) : ℝ) ≤ 2 * Real.log 2 + q * Real.log N := by
    have hYR : (Y : ℝ) ≤ (P : ℝ) := by exact_mod_cast hYP
    calc Real.log ((P + Y : ℕ) : ℝ) ≤ Real.log (2 * (P : ℝ)) := by
          apply Real.log_le_log (by push_cast; positivity)
          push_cast; linarith
      _ = Real.log 2 + Real.log P := Real.log_mul (by norm_num) (ne_of_gt hPpos)
      _ ≤ 2 * Real.log 2 + q * Real.log N := by linarith [hlPub]
  have hW1m : Real.log t + ((k + 1 : ℕ) : ℝ) * Real.log ((P + Y : ℕ) : ℝ)
      ≤ (k : ℝ) * Real.log N := by
    have hexp : ((k : ℝ) + 1) * (2 * Real.log 2 + q * Real.log N)
        = 2 * ((k : ℝ) + 1) * Real.log 2 + ((k : ℝ) - (m : ℝ) - 1) * Real.log N := by
      rw [hqdef]; field_simp; ring
    have h2 : ((k : ℝ) + 1) * Real.log ((P + Y : ℕ) : ℝ)
        ≤ 2 * ((k : ℝ) + 1) * Real.log 2 + ((k : ℝ) - (m : ℝ) - 1) * Real.log N := by
      rw [← hexp]; exact mul_le_mul_of_nonneg_left hlogPY (by positivity)
    have hkcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hkcast]
    nlinarith [hltub, h2, hjf, hlk0]
  have hW2cm : Real.log 8 + 2 * Real.log k + 1 / 2 * Real.log P ≤ Real.log N := by
    have hl8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by nlinarith [hq1, hj0]
    have hkl2 : 3 * Real.log 2 ≤ (k : ℝ) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20
      exact_mod_cast (show 3 ≤ k by omega)
    rw [hl8]
    linarith [hjf, hlPub, hqj_le, hkl2, hlk0, hl20]
  have hW2bm : Real.log t + Real.log Y ≤ ((m + 2 + 1 : ℕ) : ℝ) * Real.log N := by
    have hc : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hqj_le : q * Real.log N ≤ Real.log N := by nlinarith [hq1, hj0]
    rw [hc]
    nlinarith [hltub, hlYub, hlPub, hqj_le, hj8, hl21, hl20]
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hf : 9 / 2 * ((k : ℝ) + 1) ≤ ((m : ℝ) + 2) * ((k : ℝ) - (m : ℝ) - 1) := by
    nlinarith [mul_nonneg humc hvmc]
  have hqj : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * (q * Real.log N) := by
    have hqeq : q * Real.log N = ((k : ℝ) - (m : ℝ) - 1) * Real.log N / ((k : ℝ) + 1) := by
      rw [hqdef]; field_simp; ring
    rw [hqeq, mul_div_assoc', le_div_iff₀ hk1R]
    nlinarith [mul_le_mul_of_nonneg_right hf hj0]
  have hlPq : ((m : ℝ) + 2) * (q * Real.log N) ≤ ((m : ℝ) + 2) * Real.log P :=
    mul_le_mul_of_nonneg_left hlPlo (by linarith)
  have hl2π : Real.log (2 * π) ≤ 7 := by
    have hπ4 : π ≤ 4 := Real.pi_le_four
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * π by positivity)
    linarith
  have hl2lb : (1 : ℝ) / 2 ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hl4k : 0 ≤ Real.log (4 * (k : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    linarith
  have hW2am : (-((m + 2 : ℕ) : ℝ) - ρ) * Real.log P - Real.log (4 * (k : ℝ))
      ≤ Real.log t - Real.log (2 * π) - ((m + 2 + 1 : ℕ) : ℝ) * Real.log (2 * (N : ℝ)) := by
    have hcjs : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    have hcjs1 : ((m + 2 + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by push_cast; ring
    have hl2N : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
      Real.log_mul (by norm_num) (ne_of_gt hNpos)
    have hml2 : ((m : ℝ) + 9) * Real.log 2 ≤ ((k : ℝ) + 1) * Real.log 2 := by
      apply mul_le_mul_of_nonneg_right _ hl20; linarith
    have hkey : 9 / 2 * Real.log N ≤ ((m : ℝ) + 2) * Real.log P := le_trans hqj hlPq
    rw [hcjs, hcjs1, hl2N]
    nlinarith [hltlo, hkey, hl2π, hl4k, hjf, hml2, mul_nonneg hρ0 hlP0, hlk0, hl2lb]
  exact vk_window_prefix (js := m + 2) hk hr hρ hY hP1 h4PN hN1 (by omega) (by omega) htpos hD
    (vk_hW1_form htpos hP1 hN1 hW1m)
    (vk_hW2a_form (by omega) hP1 hN1 htpos hW2am)
    (vk_hW2b_form htpos hY1 hN1 hW2bm)
    (vk_hW2c_form (by omega) hP1 hN1 hY hW2cm)
    y hy1 hy2

/-! ## The mid-branch prefix window (schedule) — copies of the `Mid.lean` helpers -/

/-- Copy of `Mid.vk_lnD_budget` (private). -/
private lemma vk_lnD_budget {k r : ℕ} {A ℓ : ℝ}
    (hkR_lo : A ≤ (k : ℝ)) (hkR_ub : (k : ℝ) ≤ 11 / 10 * A) (hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ)
    (hlnk_ub : Real.log k ≤ 28 / 100 * ℓ) (hlnk0 : 0 ≤ Real.log k) (hr0R : (0 : ℝ) < (r : ℝ))
    (hk0R : (0 : ℝ) < (k : ℝ)) (hl21 : Real.log 2 ≤ 1) (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) :
    8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k) ≤ 52 * A ^ 3 * ℓ ^ 2 := by
  have hlog16k : Real.log (16 * (k : ℝ)) ≤ 4 + 28 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hk0R)]
    have h16 : Real.log 16 ≤ 4 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith [hl21]
    linarith [hlnk_ub]
  have hT1 : (k : ℝ) * Real.log (16 * k) ≤ 4 / 10 * A * ℓ := by
    have h1 : (k : ℝ) * Real.log (16 * k) ≤ (11 / 10 * A) * (4 + 28 / 100 * ℓ) := by
      apply mul_le_mul hkR_ub hlog16k _ (by positivity)
      apply Real.log_nonneg; nlinarith [hkR_lo, hA26]
    nlinarith [h1, hA0, hℓ100, mul_nonneg hA0.le (show (0 : ℝ) ≤ ℓ by linarith)]
  have hk2 : (k : ℝ) ^ 2 ≤ (11 / 10 * A) ^ 2 := by nlinarith [hkR_ub, hkR_lo, hA0]
  have hrk : (r : ℝ) ≤ 6 / 10 * (11 / 10 * A) * ℓ := by
    apply le_trans hr_ub; nlinarith [hkR_ub, hℓ100]
  have hkr_lnk : (k : ℝ) ^ 2 * (r : ℝ) * Real.log k
      ≤ (11 / 10 * A) ^ 2 * (6 / 10 * (11 / 10 * A) * ℓ) * (28 / 100 * ℓ) :=
    mul_le_mul (mul_le_mul hk2 hrk hr0R.le (by positivity)) hlnk_ub hlnk0 (by positivity)
  have hT2 : 24 * (k : ℝ) ^ 2 * (r : ℝ) * Real.log k ≤ 6 * A ^ 3 * ℓ ^ 2 := by
    nlinarith [hkr_lnk, hA0, hℓ0, mul_pos (pow_pos hA0 3) (pow_pos hℓ0 2)]
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have hAℓ : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
    have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith [hA2, hℓ100, hℓ0]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]
  linarith [hT1, hT2, hAℓ]

/-- Copy of `Mid.vk_Aℓ_cube` (private). -/
private lemma vk_Aℓ_cube {A ℓ : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hA0 : (0 : ℝ) < A) (hℓ0 : (0 : ℝ) < ℓ) : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := by
  have hA2 : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have h1 : (1 : ℝ) ≤ A ^ 2 * ℓ := by nlinarith [hA2, hℓ100, hℓ0]
  nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hA0.le hℓ0.le)]

/-- Copy of `Mid.vk_theta_saving` (private). -/
private lemma vk_theta_saving {A ℓ j ρ LP : ℝ} (hA26 : (26 : ℝ) ≤ A) (hℓ100 : (100 : ℝ) ≤ ℓ)
    (hj0 : (0 : ℝ) < j) (hρpos : (0 : ℝ) < ρ)
    (hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ) (hLP : j / 2 ≤ LP) :
    (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j ≤ ρ * LP := by
  have hD0 : (0 : ℝ) < A ^ 3 * ℓ ^ 2 := by positivity
  have hstep2 : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) ≤ ρ * LP :=
    mul_le_mul hρlo hLP (by positivity) hρpos.le
  have hcompare : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j ≤ (1 / (12 * A ^ 2 * ℓ)) * (j / 2) := by
    have hAℓ2600 : (2600 : ℝ) ≤ A * ℓ := by nlinarith [hA26, hℓ100]
    have hden : 24 * (A ^ 2 * ℓ) ≤ 1000 * (A ^ 3 * ℓ ^ 2) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ A ^ 2 * ℓ by positivity)
        (show (0 : ℝ) ≤ 1000 * (A * ℓ) - 24 by linarith [hAℓ2600])]
    have hL : (1 / 1000 / (A ^ 3 * ℓ ^ 2)) * j = j / (1000 * (A ^ 3 * ℓ ^ 2)) := by
      field_simp
    have hR : (1 / (12 * A ^ 2 * ℓ)) * (j / 2) = j / (24 * (A ^ 2 * ℓ)) := by field_simp; ring
    rw [hL, hR]
    gcongr
  linarith [hstep2, hcompare]

set_option maxHeartbeats 4000000 in
-- The ~55-hypothesis schedule bookkeeping (copied from `vk_window_mid`) exceeds the budget.
/-- **Mid-branch prefix window** — prefix-of-window analogue of `vk_window_mid`.  Same schedule
and routing predicates; concludes the prefix bound `‖∑_{(N,y]} eR(phi t n)‖ ≤ 10·N·exp(−Θ·logN)` for
every `N < y ≤ 2N`.  Body identical to `vk_window_mid` except the consumer is
`vk_window_scale_prefix` threaded with `(y, hy1, hy2)`. -/
theorem vk_window_mid_prefix {t : ℝ} {N k r m : ℕ}
    (ht0 : 0 < t) (hL100 : Real.exp 100 ≤ Real.log t) (hN2 : 2 ≤ N)
    (hk : k = max 19 ⌈Real.log t ^ ((1 : ℝ) / 4)⌉₊)
    (hr : r = ⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊)
    (hm : m = ⌈Real.log t / Real.log N⌉₊)
    (hroute : Real.log 2 ≤ vkTheta t * Real.log N)
    (hjhi : 10 * Real.log N < Real.log t)
    (y : ℤ) (hy1 : (N : ℤ) < y) (hy2 : y ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) y, eR (phi t n)‖
      ≤ 10 * (N : ℝ) * Real.exp (-(vkTheta t * Real.log N)) := by
  obtain ⟨L, hLdef⟩ : ∃ x : ℝ, x = Real.log t := ⟨_, rfl⟩
  obtain ⟨j, hjdef⟩ : ∃ x : ℝ, x = Real.log N := ⟨_, rfl⟩
  rw [← hLdef] at hL100 hk hm hjhi
  rw [← hjdef] at hm hjhi hroute ⊢
  obtain ⟨ℓ, hℓdef⟩ : ∃ x : ℝ, x = Real.log L := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ x : ℝ, x = L ^ ((1 : ℝ) / 4) := ⟨_, rfl⟩
  rw [← hAdef] at hk
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (Real.exp_pos 100) hL100
  have hL1 : (1 : ℝ) < L := by
    have : (101 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
    linarith
  have hℓ100 : (100 : ℝ) ≤ ℓ := by
    rw [hℓdef, ← Real.log_exp 100]
    exact Real.log_le_log (Real.exp_pos _) hL100
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hN1R : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hN0R : (0 : ℝ) < (N : ℝ) := by linarith
  have hj0 : (0 : ℝ) < j := by rw [hjdef]; exact Real.log_pos hN1R
  have hN1 : 1 ≤ N := by omega
  have hAexp : A = Real.exp (ℓ * (1 / 4)) := by
    rw [hAdef, Real.rpow_def_of_pos hL0, hℓdef]
  have hA25 : Real.exp 25 ≤ A := by
    rw [hAexp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hA26 : (26 : ℝ) ≤ A := by
    have : (26 : ℝ) ≤ Real.exp 25 := by linarith [Real.add_one_le_exp (25 : ℝ)]
    linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hkA : k = ⌈A⌉₊ := by
    rw [hk, max_eq_right]
    have h1 : (19 : ℝ) ≤ (⌈A⌉₊ : ℝ) := le_trans (by linarith) (Nat.le_ceil A)
    exact_mod_cast h1
  have hkR_lo : A ≤ (k : ℝ) := by rw [hkA]; exact Nat.le_ceil A
  have hkR_ub : (k : ℝ) ≤ 11 / 10 * A := by
    rw [hkA]
    have h1 : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0.le
    linarith [hA26]
  have hk19 : 19 ≤ k := by rw [hk]; exact le_max_left _ _
  have hk0R : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hA0 hkR_lo
  have hl20 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl21 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogA : Real.log A = ℓ / 4 := by
    rw [hAdef, Real.log_rpow hL0, ← hℓdef]; ring
  have hlnk_ub : Real.log k ≤ 28 / 100 * ℓ := by
    have h1 : Real.log k ≤ Real.log (11 / 10 * A) := Real.log_le_log hk0R hkR_ub
    rw [Real.log_mul (by norm_num) (ne_of_gt hA0), hlogA] at h1
    have h2 : Real.log (11 / 10) ≤ 1 / 10 := by
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 11 / 10 by norm_num)]
    linarith [hℓ100]
  have hlnk0 : (0 : ℝ) ≤ Real.log k := by
    apply Real.log_nonneg; exact_mod_cast (show 1 ≤ k by omega)
  have hlog4k2 : Real.log (4 * (k : ℝ) ^ 2) ≤ 2 + 56 / 100 * ℓ := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; linarith [hl21]
    push_cast; linarith [hlnk_ub]
  have hr_ub : (r : ℝ) ≤ 6 / 10 * (k : ℝ) * ℓ := by
    rw [hr]
    have h0 : (0 : ℝ) ≤ (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) := by
      apply mul_nonneg hk0R.le
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
      nlinarith
    have h1 : (⌈(k : ℝ) * Real.log (4 * (k : ℝ) ^ 2)⌉₊ : ℝ)
        < (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) + 1 := Nat.ceil_lt_add_one h0
    have h2 : (k : ℝ) * Real.log (4 * (k : ℝ) ^ 2) ≤ (k : ℝ) * (2 + 56 / 100 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog4k2 hk0R.le
    have h3 : (k : ℝ) * 100 ≤ (k : ℝ) * ℓ := mul_le_mul_of_nonneg_left hℓ100 hk0R.le
    nlinarith [h1, h2, h3, hk0R]
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_ceil_iff]
    apply mul_pos hk0R
    apply Real.log_pos
    have : (1 : ℝ) ≤ (k : ℝ) := by linarith [hA26, hkR_lo]
    nlinarith
  have hr0R : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  have hA3eq : L ^ ((3 : ℝ) / 4) = A ^ 3 := by
    rw [hAdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 3, ← Real.rpow_mul hL0.le]
    norm_num
  have hΘval : vkTheta t = 1 / 1000 / (A ^ 3 * ℓ ^ 2) := by
    rw [vkTheta, ← hLdef, ← hℓdef, hA3eq]
  have hD0 : (0 : ℝ) < A ^ 3 * ℓ ^ 2 := by positivity
  have hjlo : 693 * (A ^ 3 * ℓ ^ 2) ≤ j := by
    have h1 := hroute
    rw [hΘval] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hD0] at h1
    nlinarith [Real.log_two_gt_d9, hD0.le, h1]
  have hLj10 : (10 : ℝ) < L / j := by rw [lt_div_iff₀ hj0]; linarith
  have hm11 : 11 ≤ m := by
    have h1 : 10 < m := by
      rw [hm]
      exact_mod_cast Nat.lt_ceil.mpr (by exact_mod_cast hLj10)
    omega
  have hLj0 : (0 : ℝ) ≤ L / j := by positivity
  have hm_ub : (m : ℝ) < L / j + 1 := by
    rw [hm]; exact Nat.ceil_lt_add_one hLj0
  have hL_A4 : L = A ^ 4 := by
    rw [hAdef, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 4)) 4, ← Real.rpow_mul hL0.le]
    norm_num
  have hℓ2ge : (10000 : ℝ) ≤ ℓ ^ 2 := by nlinarith [hℓ100]
  have hA2ge : (676 : ℝ) ≤ A ^ 2 := by nlinarith [hA26]
  have hLj_ub : L / j ≤ A / 693 := by
    have hstep : L * 693 ≤ A * j := by
      have h1 : A * (693 * (A ^ 3 * ℓ ^ 2)) ≤ A * j := mul_le_mul_of_nonneg_left hjlo hA0.le
      have h2 : A * (693 * (A ^ 3 * ℓ ^ 2)) = 693 * L * ℓ ^ 2 := by rw [hL_A4]; ring
      rw [h2] at h1
      nlinarith [h1, hℓ2ge, hL0.le]
    rw [div_le_div_iff₀ hj0 (by norm_num)]
    linarith [hstep]
  have hmA : (m : ℝ) ≤ A / 693 + 1 := le_trans hm_ub.le (by linarith [hLj_ub])
  have hmk : m + 8 ≤ k := by
    have h1 : (m : ℝ) + 8 ≤ (k : ℝ) := by nlinarith [hmA, hA26, hkR_lo]
    exact_mod_cast h1
  have hNexp : ∀ n : ℕ, (N : ℝ) ^ n = Real.exp ((n : ℝ) * j) := by
    intro n
    rw [Real.exp_nat_mul, hjdef, Real.exp_log hN0R]
  have htexp : t = Real.exp L := by rw [hLdef, Real.exp_log ht0]
  have hthi : t ≤ (N : ℝ) ^ m := by
    have h1 : L / j ≤ (m : ℝ) := by rw [hm]; exact Nat.le_ceil _
    have h2 : L ≤ (m : ℝ) * j := by rw [div_le_iff₀ hj0] at h1; linarith
    rw [htexp, hNexp m]
    exact Real.exp_le_exp.mpr h2
  have htlo : (N : ℝ) ^ (m - 1) < t := by
    have h1 : (m : ℝ) - 1 < L / j := by linarith [hm_ub]
    have h2 : ((m : ℝ) - 1) * j < L := by rw [lt_div_iff₀ hj0] at h1; linarith
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [htexp, hNexp (m - 1), hcast]
    exact Real.exp_lt_exp.mpr h2
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ, P = ⌈(N : ℝ) ^ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1))⌉₊ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ, Y = ⌈(P : ℝ) ^ ((1 : ℝ) / 2)⌉₊ := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = 1 / (16 * (k : ℝ) * r) := ⟨_, rfl⟩
  have hk1R : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hβ0 : (0 : ℝ) ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hk1R]
    have : (m : ℝ) + 2 ≤ (k : ℝ) := by
      have : (m : ℝ) + 8 ≤ (k : ℝ) := by exact_mod_cast hmk
      linarith
    linarith
  have hlnD_ub : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ 52 * A ^ 3 * ℓ ^ 2 :=
    vk_lnD_budget hkR_lo hkR_ub hr_ub hlnk_ub hlnk0 hr0R hk0R hl21 hA26 hℓ100 hA0 hℓ0
  have hDf : 8 * ((k : ℝ) * Real.log (16 * k) + 24 * (k : ℝ) ^ 2 * r * Real.log k)
      ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N := by
    rw [← hjdef]
    have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 654 / 1000 := by
      rw [div_le_iff₀ hk1R]
      nlinarith [hmA, hkR_lo, hA26]
    have hβj : (346 / 1000) * j ≤ (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * j := by
      apply mul_le_mul_of_nonneg_right _ hj0.le
      linarith [hle]
    have hfloor : 52 * A ^ 3 * ℓ ^ 2 ≤ (346 / 1000) * j := by
      have h : (346 / 1000) * (693 * (A ^ 3 * ℓ ^ 2)) ≤ (346 / 1000) * j :=
        mul_le_mul_of_nonneg_left hjlo (by norm_num)
      nlinarith [h, hD0.le]
    linarith only [hlnD_ub, hfloor, hβj]
  have hjf : 2 * ((k : ℝ) + 1) * Real.log 2 + 4 * Real.log k + 8 ≤ Real.log N := by
    rw [← hjdef]
    have hkℓ : 2 * ((k : ℝ) + 1) + 4 * (28 / 100) * ℓ + 8 ≤ (346 / 1000) * j := by
      have hbig : A * ℓ ≤ A ^ 3 * ℓ ^ 2 := vk_Aℓ_cube hA26 hℓ100 hA0 hℓ0
      have hjge : 693 * (A * ℓ) ≤ j := le_trans (by nlinarith [hbig, hD0.le]) hjlo
      nlinarith [hjge, hkR_ub, hA0, hℓ100, hA26]
    have h1 : 2 * ((k : ℝ) + 1) * Real.log 2 ≤ 2 * ((k : ℝ) + 1) := by nlinarith [hl21, hk0R]
    have h2 : 4 * Real.log k ≤ 4 * (28 / 100) * ℓ := by linarith [hlnk_ub]
    have hj346 : (346 / 1000) * j ≤ j := by nlinarith [hj0]
    linarith only [h1, h2, hkℓ, hj346]
  have hlPlo : (1 - ((m : ℝ) + 2) / ((k : ℝ) + 1)) * Real.log N ≤ Real.log P :=
    vk_logP_ge hN1 hPdef
  have hlogN0 : (0 : ℝ) ≤ Real.log N := by rw [← hjdef]; exact hj0.le
  have hlP_half : j / 2 ≤ Real.log P := by
    have hβle : (1 : ℝ) / 2 ≤ 1 - ((m : ℝ) + 2) / ((k : ℝ) + 1) := by
      have hle : ((m : ℝ) + 2) / ((k : ℝ) + 1) ≤ 1 / 2 := by
        rw [div_le_iff₀ hk1R]; nlinarith [hmA, hkR_lo, hA26]
      linarith [hle]
    have hstep : (1 : ℝ) / 2 * Real.log N ≤ Real.log P :=
      le_trans (mul_le_mul_of_nonneg_right hβle hlogN0) hlPlo
    rw [hjdef]; linarith only [hstep]
  have hρpos : (0 : ℝ) < ρ := by rw [hρdef]; positivity
  have hr_ub2 : (16 * (k : ℝ) * r) ≤ 16 * (11 / 10 * A) * (6 / 10 * (11 / 10 * A) * ℓ) := by
    apply mul_le_mul (by nlinarith [hkR_ub, hA0]) _ hr0R.le (by positivity)
    apply le_trans hr_ub; nlinarith [hkR_ub, hℓ100]
  have h16kr : (0 : ℝ) < 16 * (k : ℝ) * r := mul_pos (mul_pos (by norm_num) hk0R) hr0R
  have hρlo : 1 / (12 * A ^ 2 * ℓ) ≤ ρ := by
    rw [hρdef, div_le_div_iff₀ (by positivity) h16kr]
    nlinarith [hr_ub2, hA0, hℓ0]
  have hΘlogN : vkTheta t * j ≤ ρ * Real.log P := by
    rw [hΘval]
    exact vk_theta_saving hA26 hℓ100 hj0 hρpos hρlo hlP_half
  have hbound := vk_window_scale_prefix (k := k) (r := r) (m := m) (N := N) (P := P) (Y := Y)
    (ρ := ρ) (t := t) hk19 hr hρdef hm11 hmk hN1 hPdef hYdef htlo hthi hDf hjf y hy1 hy2
  refine le_trans hbound ?_
  have hPρ : (P : ℝ) ^ (-ρ) = Real.exp (-(ρ * Real.log P)) := by
    have hPpos : (0 : ℝ) < (P : ℝ) := by
      rw [hPdef]; exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one
        (by rw [Nat.one_le_ceil_iff]; exact Real.rpow_pos_of_pos hN0R _)
    rw [Real.rpow_def_of_pos hPpos]; congr 1; ring
  rw [hPρ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (by linarith [hΘlogN])

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
    have h2 : (100 : ℝ) ≤ Real.log (Real.log t) := by
      rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hL100
    have h3 : (10000 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := by nlinarith [h2]
    have hDpos : 0 < (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
      positivity
    rw [div_le_iff₀ hDpos]
    nlinarith [h1, h3, mul_le_mul h1 h3 (by norm_num) (by positivity)]
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
      have h50 : (51 : ℝ) ≤ Real.exp 50 := by linarith [Real.add_one_le_exp (50 : ℝ)]
      have he : Real.exp 100 = Real.exp 50 * Real.exp 50 := by rw [← Real.exp_add]; norm_num
      nlinarith [h50, he, Real.exp_pos 50]
    have hlogM260 : (260 : ℝ) ≤ Real.log M := by linarith [hhi, hL100, hexp2601]
    have hMfac : ((Nat.factorial 12 : ℝ)) ^ 6 ≤ (M : ℝ) := by
      have hfac2 : (Nat.factorial 12 : ℝ) ≤ 2 ^ 29 := by norm_num [Nat.factorial]
      have hlog2le1 : Real.log 2 ≤ 1 := by
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
      have hlogfac : Real.log (Nat.factorial 12 : ℝ) ≤ 29 := by
        calc Real.log (Nat.factorial 12 : ℝ) ≤ Real.log ((2 : ℝ) ^ 29) :=
              Real.log_le_log (by positivity) hfac2
          _ = 29 * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
          _ ≤ 29 := by nlinarith [hlog2le1]
      have hlog6 : Real.log (((Nat.factorial 12 : ℝ)) ^ 6) ≤ 174 := by
        rw [Real.log_pow]; push_cast; nlinarith [hlogfac]
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
          _ ≤ 26 := by nlinarith [hlog2le1]
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
      _ ≤ 2 * t ^ 2 := by nlinarith [ht1]
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
      _ ≤ 4050 * (1 + Real.log t) := by nlinarith [hlogN, hlog2, hlogtnn]
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
            push_cast; nlinarith
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
          have := Real.log_two_gt_d9; nlinarith
        nlinarith [hlogineq, hlog2pos, h23, hlogtnn]
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
      _ ≤ 4050 * (1 + Real.log t) := by nlinarith [hJcount, hlogtnn]

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
        have h100 : (100 : ℝ) ≤ Real.log (Real.log t) := by
          rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hL100
        linarith
      have h3 : (1 : ℝ) ≤ (Real.log (Real.log t)) ^ (2 : ℕ) := one_le_pow₀ h2
      have hDpos : 0 < (Real.log t) ^ ((3 : ℝ) / 4) * (Real.log (Real.log t)) ^ (2 : ℕ) := by
        positivity
      rw [div_le_iff₀ hDpos]
      nlinarith [h1, h3, mul_le_mul h1 h3 (by norm_num) (by positivity)]
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
      _ ≤ 8104 * Real.log t := by nlinarith [hlogt1]

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
