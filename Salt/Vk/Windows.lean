/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.Scale

/-!
# VMVT-VK rung R5b (ladder half) — the `⌈N/P⌉`-block window assembly (`VK-WINDOW`)

`vk_ladder_bound` assembles the dyadic window `(N, 2N]` from the `Q = ⌈N/P⌉` equal-length
`vk_block_core` sub-blocks `c i = min (N + i·P) (2N)`, turning a uniform per-block Weyl bound
`8·P^{1−ρ}` into the freeze's `‖∑_{(N,2N]} eR(phi t n)‖ ≤ 10·N·P^{−ρ}` under the guard `4P ≤ N`.

This is the *geometric* half of R5b (the freeze's window arithmetic), built on the landed abstract
split `vk_sum_Ioc_split_norm_le`.  The remaining, transcendental, half — the per-block `VkSpaced`
discharge (proving `vk_block_core`'s `hD ∧ hW1 ∧ hW2` hold at the pre-computed window parameters
`j = log N`, `r₀ = ⌈L/j⌉`, `β = (r₀+1)/(k+1)`, `P = ⌈N^{1−β}⌉`, `j* = r₀+2` for every
`N₀ ∈ (N, 2N]`) is the flagged heaviest bookkeeping, tracked in `docs/blueprints/flags.md`.

The arithmetic: `⌈N/P⌉ ≤ N/P + 1 ≤ (5/4)(N/P)` (the `+1` absorbed by `4P ≤ N`), and
`⌈N/P⌉·8·P^{1−ρ} = ⌈N/P⌉·8P·P^{−ρ} ≤ (5N/(4P))·8P·P^{−ρ} = 10·N·P^{−ρ}`.
-/

namespace Salt.Vk

open Finset

/-- **R5b ladder half — the `⌈N/P⌉`-block window assembly.**  For any normed target and any block
map `f`, given a uniform per-block Weyl bound `‖∑_{(c i, c (i+1)]} f‖ ≤ 8·P^{1−ρ}` over the
`Q = ⌈N/P⌉` blocks `c i = min (N + i·P) (2N)` (the `vk_block_core` output), the window sum satisfies
`‖∑_{(N,2N]} f‖ ≤ 10·N·P^{−ρ}` under the guard `4P ≤ N`.  Generic in `f`; instantiated at
`f = eR ∘ phi t` by the per-block `VkSpaced` discharge. -/
theorem vk_ladder_bound {E : Type*} [NormedAddCommGroup E] (f : ℤ → E)
    {P N : ℕ} {ρ : ℝ} (hP : 1 ≤ P) (h4P : 4 * P ≤ N)
    (hB : ∀ i, i < ⌈(N : ℝ) / (P : ℝ)⌉₊ →
      ‖∑ n ∈ Finset.Ioc (min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N))
          (min ((N : ℤ) + ((i : ℤ) + 1) * (P : ℤ)) (2 * N)), f n‖ ≤ 8 * (P : ℝ) ^ (1 - ρ)) :
    ‖∑ n ∈ Finset.Ioc (N : ℤ) (2 * N), f n‖ ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
  have hP0 : (0 : ℝ) < (P : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hP
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have h4PR : 4 * (P : ℝ) ≤ (N : ℝ) := by exact_mod_cast h4P
  set Q : ℕ := ⌈(N : ℝ) / (P : ℝ)⌉₊ with hQdef
  set c : ℕ → ℤ := fun i => min ((N : ℤ) + (i : ℤ) * (P : ℤ)) (2 * N) with hc
  -- monotone endpoint sequence
  have hcmono : Monotone c := by
    intro i j hij
    simp only [hc]
    apply min_le_min _ (le_refl _)
    have : (i : ℤ) * (P : ℤ) ≤ (j : ℤ) * (P : ℤ) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
    linarith
  -- endpoints
  have hc0 : c 0 = (N : ℤ) := by
    simp only [hc, Nat.cast_zero, zero_mul, add_zero]
    exact min_eq_left (by omega)
  have hQP : (N : ℝ) ≤ (Q : ℝ) * (P : ℝ) := by
    have hle : (N : ℝ) / (P : ℝ) ≤ (Q : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hP0] at hle; exact hle
  have hcQ : c Q = 2 * (N : ℤ) := by
    simp only [hc]
    apply min_eq_right
    have : (N : ℤ) ≤ (Q : ℤ) * (P : ℤ) := by
      have : (N : ℝ) ≤ (Q : ℝ) * (P : ℝ) := hQP
      exact_mod_cast this
    linarith
  -- apply the abstract split
  have hsplit := vk_sum_Ioc_split_norm_le f c hcmono Q (B := 8 * (P : ℝ) ^ (1 - ρ)) (fun i hi => by
    have hbi := hB i hi
    simpa only [hc, Nat.cast_add, Nat.cast_one] using hbi)
  rw [hc0, hcQ] at hsplit
  -- arithmetic: Q · 8 P^{1-ρ} ≤ 10 N P^{-ρ}
  have hQlt : (Q : ℝ) < (N : ℝ) / (P : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hQPub : (Q : ℝ) * (P : ℝ) ≤ (N : ℝ) + (P : ℝ) := by
    calc (Q : ℝ) * (P : ℝ) ≤ ((N : ℝ) / (P : ℝ) + 1) * (P : ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt hQlt) hP0.le
      _ = (N : ℝ) + (P : ℝ) := by field_simp
  have h4PQ : 4 * (P : ℝ) * (Q : ℝ) ≤ 5 * (N : ℝ) := by nlinarith [hQPub, h4PR, hP0]
  have hPsplit : (P : ℝ) ^ (1 - ρ) = (P : ℝ) * (P : ℝ) ^ (-ρ) := by
    rw [show (1 : ℝ) - ρ = 1 + (-ρ) by ring, Real.rpow_add hP0, Real.rpow_one]
  have hPρnn : (0 : ℝ) ≤ (P : ℝ) ^ (-ρ) := Real.rpow_nonneg hP0.le _
  have hfinal : (Q : ℝ) * (8 * (P : ℝ) ^ (1 - ρ)) ≤ 10 * (N : ℝ) * (P : ℝ) ^ (-ρ) := by
    rw [hPsplit]
    have hstep : (Q : ℝ) * (8 * ((P : ℝ) * (P : ℝ) ^ (-ρ)))
        = (8 * ((P : ℝ) * (Q : ℝ))) * (P : ℝ) ^ (-ρ) := by ring
    rw [hstep]
    apply mul_le_mul_of_nonneg_right _ hPρnn
    nlinarith [h4PQ]
  exact le_trans hsplit hfinal

end Salt.Vk
