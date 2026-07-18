/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# VMVT-VK rung R5 (assembly core) — the equal-length block split (`VK-SCALE`, assembly half)

`vk_sum_Ioc_split` telescopes an exponential-sum window `(c 0, c Q]` into the `Q` consecutive
sub-blocks `(c i, c (i+1)]` cut by any monotone endpoint sequence `c : ℕ → ℤ`;
`vk_sum_Ioc_split_norm_le` is its triangle bound `‖∑_{(c 0, c Q]}‖ ≤ Q · B` given a uniform
per-block bound `B`.

This is the equal-length / general-partition analogue of `Salt.ExpSum.dyadic_sum_split` (which
only handles power-of-2 windows) — the assembly primitive the `⌈N/P⌉`-block VK-SCALE ladder needs.
Instantiating `c i = min (N + i·P) (2N)` with the `vk_block_core` per-block bound (`Q = ⌈N/P⌉`, each
block `≤ 8·P^{1-ρ}`) yields the freeze's `‖∑_{(N,2N]} eR(phi t n)‖ ≤ 10·N·P^{-ρ}` — the remaining
step is the `VkSpaced` window discharge (R5b, the freeze's window arithmetic), tracked in
`docs/blueprints/flags.md`.
-/

namespace Salt.Vk

open Finset

/-- **Equal-length / general-partition block split.**  For a monotone endpoint sequence
`c : ℕ → ℤ`, the window `(c 0, c Q]` telescopes into the `Q` consecutive blocks `(c i, c (i+1)]`. -/
theorem vk_sum_Ioc_split {G : Type*} [AddCommGroup G] (f : ℤ → G) (c : ℕ → ℤ) (hc : Monotone c) :
    ∀ Q : ℕ, ∑ n ∈ Finset.Ioc (c 0) (c Q), f n
      = ∑ i ∈ Finset.range Q, ∑ n ∈ Finset.Ioc (c i) (c (i + 1)), f n := by
  intro Q
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [Finset.sum_range_succ, ← ih,
        ← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le (le_refl (c Q))),
        Finset.Ioc_union_Ioc_eq_Ioc (hc (Nat.zero_le Q)) (hc (show Q ≤ Q + 1 by omega))]

/-- **Triangle bound for the block split.**  A uniform per-block bound `B` over the `Q` blocks
gives `‖∑_{(c 0, c Q]} f‖ ≤ Q · B`. -/
theorem vk_sum_Ioc_split_norm_le {E : Type*} [NormedAddCommGroup E] (f : ℤ → E) (c : ℕ → ℤ)
    (hc : Monotone c) (Q : ℕ) {B : ℝ}
    (hB : ∀ i, i < Q → ‖∑ n ∈ Finset.Ioc (c i) (c (i + 1)), f n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc (c 0) (c Q), f n‖ ≤ (Q : ℝ) * B := by
  rw [vk_sum_Ioc_split f c hc Q]
  calc ‖∑ i ∈ Finset.range Q, ∑ n ∈ Finset.Ioc (c i) (c (i + 1)), f n‖
      ≤ ∑ i ∈ Finset.range Q, ‖∑ n ∈ Finset.Ioc (c i) (c (i + 1)), f n‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range Q, B :=
        Finset.sum_le_sum (fun i hi => hB i (Finset.mem_range.mp hi))
    _ = (Q : ℝ) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Salt.Vk
