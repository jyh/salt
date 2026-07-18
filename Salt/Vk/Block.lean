/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Vk.BoxMeasure
import Salt.Vk.Pointwise

/-!
# VMVT-VK rung R4 — the block bridge (`VK-POINTWISE`), analytic reduction

The load-bearing reduction of `vk_block_core`: from the ζ-phase block sum to the
mean-value-controlled orbit `genFun` moments.  Landed here (sorry-free):

* `genFun_fract` — `‖genFun‖` is invariant under reducing each coordinate mod 1
  (`genFun_add_int`); lets R4 feed the arbitrary-real orbit centers into R3's `[0,1]^k`
  hypothesis after `Int.fract` reduction.
* `vkOrbitPoint`, `vk_shift_genFun_phase` — the shifted degree-`k` polynomial phase
  regrouped (via the landed `poly_shift_orbit`) as constant orbit term + `genFun` phase.
* **`norm_vk_shift_sum`** — THE orbit → `genFun` norm bridge (the pointwise-from-mean-value
  crux): the shifted polynomial-phase block sum has the same norm as `genFun` at the orbit
  point.
* `vk_pow_sum_le` — power-mean over the `Y` shifts (Jensen, from Chebyshev).
* `vk_shift_average` — the Vinogradov shift-averaging bound.
* **`vk_shift_to_orbit`** — the full reduction of the polynomial-phase block sum to the
  average of orbit `genFun` norms (shift boundary `sum_Ioc_shift_boundary` + orbit bridge +
  shift averaging).
* **`vk_block_taylor_reduce`** — the front end: the ζ-phase block sum reduces to a pure
  polynomial-phase Weyl sum plus the R1 Taylor cost (`phi_taylor_block_PY` through
  `block_reduction`, after reindexing).

Chaining `vk_block_taylor_reduce → vk_shift_to_orbit → vk_pow_sum_le → R3
(`vk_box_disjoint_avg_of_centers`) → `vmvt` gives the complete measure/analytic machinery
of the bridge.  The residual `VMVT-VK/R4-assembly` (see `docs/blueprints/flags.md`) is the
final stitch: the orbit's `j*`-coordinate Diophantine spacing (from the freeze `VkSpaced`
hypothesis) and the closing `ρ`-ledger `rpow` arithmetic.
-/


namespace Salt.Vk

open Finset Real MeasureTheory Salt.ExpSum Salt.Vmvt
open scoped BigOperators

/-- **genFun invariance under mod-1 reduction.**  Reducing each coordinate to its
fractional part leaves `‖genFun‖` unchanged (integer shift, `genFun_add_int`).  This lets R4
feed the arbitrary-real orbit centers into R3 after reducing them into `[0,1)^k`. -/
lemma genFun_fract (k : ℕ) (A : Finset ℤ) (α : Deg k → ℝ) :
    genFun k A (fun j => Int.fract (α j)) = genFun k A α := by
  have h := genFun_add_int k A (fun j => Int.fract (α j)) (fun j => ⌊α j⌋)
  have he : (fun j => Int.fract (α j) + ((⌊α j⌋ : ℤ) : ℝ)) = α := by
    funext j; rw [Int.fract]; ring
  rw [he] at h; exact h.symm

/-- The fractional part lands in `[0,1]` (feeds R3's center hypothesis). -/
lemma fract_mem_Icc (x : ℝ) : 0 ≤ Int.fract x ∧ Int.fract x ≤ 1 :=
  ⟨Int.fract_nonneg x, le_of_lt (Int.fract_lt_one x)⟩

/-- The orbit torus point: degree `i ↦ β_i(y)`. -/
noncomputable def vkOrbitPoint (k : ℕ) (c : ℕ → ℝ) (y : ℝ) : Deg k → ℝ :=
  fun i => vkOrbit k c y (i : ℕ)

/-- The shifted degree-`k` polynomial phase, regrouped as the constant orbit term plus the
`genFun` polynomial phase at the orbit point. -/
theorem vk_shift_genFun_phase (k : ℕ) (c : ℕ → ℝ) (y m : ℝ) :
    ∑ j ∈ Finset.range (k + 1), c j * (m + y) ^ j
      = vkOrbit k c y 0 + ∑ j : Deg k, vkOrbitPoint k c y j * m ^ (j : ℕ) := by
  rw [poly_shift_orbit k c m y]
  rw [show Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) from by
        ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega]
  rw [Finset.sum_insert (by simp)]
  congr 1
  · simp
  · rw [← Finset.sum_coe_sort (Finset.Icc 1 k) (fun i => vkOrbit k c y i * m ^ i)]
    rfl

/-- **The orbit → `genFun` norm bridge** (the pointwise-from-mean-value crux).  The shifted
polynomial-phase block sum has the same norm as `genFun` at the orbit point (the constant
orbit term is a unit-modulus global phase). -/
theorem norm_vk_shift_sum (k P' : ℕ) (c : ℕ → ℝ) (y : ℝ) :
    ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
        eR (∑ j ∈ Finset.range (k + 1), c j * ((m : ℝ) + y) ^ j)‖
      = ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (vkOrbitPoint k c y)‖ := by
  have hLHS : ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
        eR (∑ j ∈ Finset.range (k + 1), c j * ((m : ℝ) + y) ^ j)
      = eR (vkOrbit k c y 0) * genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (vkOrbitPoint k c y) := by
    rw [genFun, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [vk_shift_genFun_phase k c y (m : ℝ), eR_add, eR_sum]
  rw [hLHS, norm_mul, norm_eR, one_mul]

/-- **Power-mean over the `Y` shifts** (Jensen, from Chebyshev's sum inequality):
`(∑_y a_y)^{2b} ≤ Y^{2b−1}·∑_y a_y^{2b}`. -/
theorem vk_pow_sum_le (b Y : ℕ) (a : Fin Y → ℝ) (ha : ∀ y, 0 ≤ a y) (hb : 1 ≤ 2 * b) :
    (∑ y : Fin Y, a y) ^ (2 * b) ≤ (Y : ℝ) ^ (2 * b - 1) * ∑ y : Fin Y, a y ^ (2 * b) := by
  have h := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin Y)))
    (f := a) (fun y _ => ha y) (2 * b - 1)
  rw [Nat.sub_add_cancel hb, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- **The shift-average bound.**  If the block sum `S` agrees with each of the `Y` shifted
sums `T y` up to `B`, then `Y·‖S‖ ≤ ∑_y ‖T y‖ + Y·B` (the Vinogradov shift averaging). -/
theorem vk_shift_average {Y : ℕ} (S : ℂ) (T : Fin Y → ℂ) (B : ℝ)
    (hB : ∀ y, ‖S - T y‖ ≤ B) :
    (Y : ℝ) * ‖S‖ ≤ (∑ y : Fin Y, ‖T y‖) + (Y : ℝ) * B := by
  have hpt : ∀ y, ‖S‖ ≤ ‖T y‖ + B := fun y => by
    calc ‖S‖ = ‖T y + (S - T y)‖ := by rw [add_sub_cancel]
      _ ≤ ‖T y‖ + ‖S - T y‖ := norm_add_le _ _
      _ ≤ ‖T y‖ + B := by linarith [hB y]
  calc (Y : ℝ) * ‖S‖ = ∑ _y : Fin Y, ‖S‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ y : Fin Y, (‖T y‖ + B) := Finset.sum_le_sum (fun y _ => hpt y)
    _ = (∑ y : Fin Y, ‖T y‖) + (Y : ℝ) * B := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **The shift → orbit reduction.**  The polynomial-phase block sum `S` is controlled by the
average of `genFun` norms at the `Y` orbit points (shifts `y = 1..Y`), up to the shift
boundary `2Y`: `Y·‖S‖ ≤ ∑_y ‖genFun(orbitPoint(y+1))‖ + Y·(2Y)`.  Combines the landed
`sum_Ioc_shift_boundary` (R2), the orbit bridge `norm_vk_shift_sum`, and `vk_shift_average`. -/
theorem vk_shift_to_orbit (k P' Y : ℕ) (c : ℕ → ℝ) (hYP' : Y ≤ P') :
    (Y : ℝ) * ‖∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
        eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j)‖
      ≤ (∑ y : Fin Y, ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ))
          (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ))‖) + (Y : ℝ) * (2 * (Y : ℝ)) := by
  set z : ℤ → ℂ := fun n => eR (∑ j ∈ Finset.range (k + 1), c j * (n : ℝ) ^ j) with hz
  have hzn : ∀ n, ‖z n‖ ≤ 1 := fun n => by rw [hz, norm_eR]
  set S : ℂ := ∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), z n with hS
  set T : Fin Y → ℂ := fun y => ∑ n ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
      eR (∑ j ∈ Finset.range (k + 1), c j * ((n : ℝ) + ((y : ℕ) + 1 : ℝ)) ^ j) with hT
  -- each shifted sum reindexes to a boundary-shifted window of z
  have hTre : ∀ y : Fin Y, T y = ∑ n ∈ Finset.Ioc (((y : ℕ) + 1 : ℤ))
      ((P' : ℤ) + ((y : ℕ) + 1 : ℤ)), z n := by
    intro y
    rw [hT]
    have hmap : Finset.Ioc (((y : ℕ) + 1 : ℤ)) ((P' : ℤ) + ((y : ℕ) + 1 : ℤ))
        = (Finset.Ioc (0 : ℤ) (P' : ℤ)).map (addRightEmbedding ((y : ℕ) + 1 : ℤ)) := by
      rw [Finset.map_add_right_Ioc]; norm_num
    rw [hmap, Finset.sum_map]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [hz]
    simp only [addRightEmbedding_apply]
    push_cast
    ring_nf
  -- the boundary bound ‖S − T y‖ ≤ 2Y
  have hB : ∀ y : Fin Y, ‖S - T y‖ ≤ 2 * (Y : ℝ) := by
    intro y
    have hyP : ((y : ℕ) + 1) ≤ P' := le_trans (by omega : (y : ℕ) + 1 ≤ Y) hYP'
    have hbd := sum_Ioc_shift_boundary hzn 0 P' ((y : ℕ) + 1) hyP
    simp only [zero_add, Nat.cast_add, Nat.cast_one] at hbd
    rw [hTre y, hS]
    refine le_trans hbd ?_
    have hle : (y : ℕ) + 1 ≤ Y := by omega
    have hc : (((y : ℕ) : ℝ) + 1) ≤ (Y : ℝ) := by exact_mod_cast hle
    linarith
  -- ‖T y‖ = ‖genFun(orbitPoint(y+1))‖
  have hTnorm : ∀ y : Fin Y, ‖T y‖
      = ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ)) (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ))‖ := by
    intro y; rw [hT]; exact norm_vk_shift_sum k P' c ((y : ℕ) + 1 : ℝ)
  have havg := vk_shift_average S T (2 * (Y : ℝ)) hB
  calc (Y : ℝ) * ‖S‖ ≤ (∑ y : Fin Y, ‖T y‖) + (Y : ℝ) * (2 * (Y : ℝ)) := havg
    _ = (∑ y : Fin Y, ‖genFun k (Finset.Ioc (0 : ℤ) (P' : ℤ))
          (vkOrbitPoint k c ((y : ℕ) + 1 : ℝ))‖) + (Y : ℝ) * (2 * (Y : ℝ)) := by
        rw [Finset.sum_congr rfl (fun y _ => hTnorm y)]

/-- **The block Taylor reduction (front end).**  The ζ-phase block sum reduces to a pure
polynomial-phase Weyl sum plus the Taylor cost `2π·P'·R` (`R` the R1 remainder).  Applies
the landed `phi_taylor_block_PY` (R1) through `block_reduction` (R2), after reindexing the
block `(N₀, N₀+P']` to `(0, P']`. -/
theorem vk_block_taylor_reduce (k N₀ P P' Y : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hN : 0 < N₀) (hP' : P' ≤ P) :
    ‖∑ n ∈ Finset.Ioc (N₀ : ℤ) (N₀ + P'), eR (phi t n)‖
      ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * (m : ℝ) ^ j)‖
        + 2 * π * ((P' : ℝ) * (2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1))) := by
  set R : ℝ := 2 * (t / (2 * π)) * (((P : ℝ) + Y) / N₀) ^ (k + 1) with hRdef
  set f : ℤ → ℝ := fun m => phi t (N₀ + m) with hf
  set g : ℤ → ℝ := fun m => phi t (N₀ : ℤ)
    + ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * (m : ℝ) ^ j with hg
  -- reindex the block to (0, P']
  have hmap : Finset.Ioc (N₀ : ℤ) ((N₀ : ℤ) + (P' : ℤ))
      = (Finset.Ioc (0 : ℤ) (P' : ℤ)).map (addLeftEmbedding (N₀ : ℤ)) := by
    rw [Finset.map_add_left_Ioc]; norm_num
  have hreindex : ∑ n ∈ Finset.Ioc (N₀ : ℤ) ((N₀ : ℤ) + (P' : ℤ)), eR (phi t n)
      = ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m) := by
    rw [hmap, Finset.sum_map]
    exact Finset.sum_congr rfl (fun m _ => by rw [hf]; simp [addLeftEmbedding_apply])
  -- the polynomial sum with the constant phase pulled out
  have hgsum : ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)
      = eR (phi t (N₀ : ℤ)) * ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * (m : ℝ) ^ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [hg, eR_add])
  -- the per-term Taylor bound
  have hR : ∀ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), |f m - g m| ≤ R := by
    intro m hm
    rw [Finset.mem_Ioc] at hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hm.1
    have hmP : (m : ℝ) ≤ (P : ℝ) + Y := by
      have : (m : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hm.2
      have hP'P : (P' : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP'
      have : (0 : ℝ) ≤ (Y : ℝ) := by positivity
      linarith
    have hbase := phi_taylor_block_PY t ht N₀ P Y (m : ℝ) (by exact_mod_cast hN) hm0 hmP k
    have hfg : f m - g m = (-(t / (2 * π)) * Real.log ((N₀ : ℝ) + (m : ℝ)))
        - (-(t / (2 * π)) * Real.log (N₀ : ℝ))
        - ∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * (m : ℝ) ^ j := by
      simp only [hf, hg, Salt.ExpSum.phi]
      push_cast
      ring
    rw [hfg]; exact hbase
  -- assemble
  rw [hreindex]
  have hbr := block_reduction (Finset.Ioc (0 : ℤ) (P' : ℤ)) f g R hR
  have hcard : ((Finset.Ioc (0 : ℤ) (P' : ℤ)).card : ℝ) = (P' : ℝ) := by
    rw [Int.card_Ioc]; simp
  rw [hcard] at hbr
  have hgn : ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖
      = ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * (m : ℝ) ^ j)‖ := by
    rw [hgsum, norm_mul, norm_eR, one_mul]
  calc ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m)‖
      ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖
        + ‖(∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m))
            - ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖ := by
        have h := norm_add_le (∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m))
          ((∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (f m))
            - ∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m))
        rw [add_sub_cancel] at h
        linarith [h]
    _ ≤ ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ), eR (g m)‖ + 2 * π * ((P' : ℝ) * R) := by
        linarith [hbr]
    _ = ‖∑ m ∈ Finset.Ioc (0 : ℤ) (P' : ℤ),
          eR (∑ j ∈ Finset.Icc 1 k, vkCoef t N₀ j * (m : ℝ) ^ j)‖
        + 2 * π * ((P' : ℝ) * R) := by rw [hgn]

end Salt.Vk
