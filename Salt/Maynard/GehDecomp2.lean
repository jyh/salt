/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Maynard.GehDecomp

/-!
# The GEH door — the DOUBLE-dyadic decomposition (node GEH-DOOR-2)

The single-dyadic supplier `Salt/Maynard/GehDecomp.lean` splits only the `μ`-side
of the Type-II bilinear form `vP3`, leaving the co-divisor as the *full*
`typeIIData (cbrt x)`.  This file adds the SECOND dyadic split — the co-divisor
into `tiiBlock b x` pieces via the same `dyadic_cover` pattern — producing the
double-dyadic block subadditivity `hdecomp_double` that the anchored multiblock
combinator (`pieceObligationU_of_anchored_multiblock`, `GehAnchor.lean`) consumes
through the vP3 family `α i x = muBlock (aIdx i x) x`, `β i x = tiiBlock (bIdx i x) x`
(the indexing convention frozen in `GehShiuWire.lean`).

## What is delivered (sorry-free)

* `sum_tiiBlock_eq` — the co-divisor dyadic blocks reconstruct `typeIIData`:
  `∑_{b < dCount x} tiiBlock b x m = typeIIData (cbrt x) m` for `m ≤ x` (the
  `tiiBlock` analogue of `sum_muBlock_eq`, using `dyadic_cover` + the vanishing of
  `typeIIData` below its threshold).
* `dconv_typeIIData_eq_sum_tiiBlock` — linearity of `dconv` in its 2nd argument:
  `dconv (muBlock a x) (typeIIData (cbrt x)) n = ∑_{b} dconv (muBlock a x) (tiiBlock b x) n`.
* `hdecomp_typeII_split` — the per-`a` co-divisor block subadditivity.
* `double_range_flatten` — the pair enumeration `i ↦ (i / dCount x, i % dCount x)`
  reindexing a `dCount x × dCount x` double range sum into a flat `range (dCount x²)`.
* `hdecomp_double` — **the double-dyadic block subadditivity** (rung 1).
* `m2 / aIdx / bIdx` — the explicit pair enumeration.
* `blockCount2_le` — **the double block count** (rung 2), `p = 2`.

## The anchor obstruction (RESOLVED — catch #96, see `docs/blueprints/flags.md`)

Rung 3 (`hanch`) originally demanded `2·N·M ≤ x` for every enumerated block, but
the topmost nonzero anti-diagonal of the double-dyadic grid has `N·M ∈ [x/2, x)`,
so `2·N·M ∈ [x, 2x)` — a factor-2 boundary overshoot; these blocks carry genuine
`vP3` mass for `n ∈ (N·M, x]` and cannot be dropped from `hdecomp_double`.  The
Fable-authorized fix (catch #96) relaxes the combinator's anchor cap to
`2·N·M ≤ 2x`, TRUE for all nonzero blocks.  The reusable Zeno stone below,
`anch_balance_of_le`, discharges the FOUR balance conjuncts under `2·N·M ≤ 2x`;
the fifth conjunct is now `2·N·M ≤ 2x` itself, satisfied by every nonzero block.
-/

namespace Salt.Maynard

open Finset
open scoped ArithmeticFunction ArithmeticFunction.Moebius
open ArithmeticFunction

/-! ## §0  `typeIIData` vanishes below its threshold (local, import-light) -/

/-- `typeIIData V m = 0` for `m ≤ V`: every divisor `c ∣ m` has `c ≤ m ≤ V`, so
the `V < c` filter is empty. -/
private theorem tiiData_zero_of_le {V m : ℕ} (h : m ≤ V) :
    Salt.LS.typeIIData V m = 0 := by
  rw [Salt.LS.typeIIData]
  apply Finset.sum_eq_zero
  intro c hc
  rw [Finset.mem_filter, Nat.mem_divisors] at hc
  obtain ⟨⟨hcdvd, hm0⟩, hVc⟩ := hc
  have hcm : c ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hcdvd
  omega

/-! ## §1  The co-divisor dyadic reconstruction -/

/-- **The co-divisor dyadic blocks reconstruct `typeIIData`.**  For `m ≤ x`,
summing the `tiiBlock` dyadic pieces recovers `typeIIData (cbrt x) m` — the
disjoint cover (`dyadic_cover`) whose top interval reaches past `x ≥ m`, with the
below-threshold tail killed by `tiiData_zero_of_le`. -/
theorem sum_tiiBlock_eq {x m : ℕ} (hx : 1 ≤ x) (hm : m ≤ x) :
    ∑ b ∈ Finset.range (dCount x), tiiBlock b x m = Salt.LS.typeIIData (cbrt x) m := by
  have hc1 : 1 ≤ cbrt x := by
    rw [cbrt]; apply Nat.le_floor; rw [Nat.cast_one]
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by rw [Real.one_rpow]
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)
  have hrw : ∀ b, tiiBlock b x m
      = (if m ∈ Finset.Ioc (2 ^ b * cbrt x) (2 * (2 ^ b * cbrt x)) then (1 : ℝ) else 0)
          * Salt.LS.typeIIData (cbrt x) m := by
    intro b; simp only [tiiBlock, nScale]; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun b _ => hrw b), ← Finset.sum_mul,
    dyadic_cover (cbrt x) m (dCount x)]
  have hupper : m ≤ 2 ^ (dCount x) * cbrt x := by
    have hlt : x < 2 ^ (dCount x) := by
      unfold dCount; exact Nat.lt_pow_succ_log_self (by norm_num) x
    calc m ≤ x := hm
      _ ≤ 2 ^ (dCount x) := le_of_lt hlt
      _ ≤ 2 ^ (dCount x) * cbrt x := Nat.le_mul_of_pos_right _ (by omega)
  by_cases hlt : cbrt x < m
  · rw [if_pos ⟨hlt, hupper⟩, one_mul]
  · rw [if_neg (fun hh => hlt hh.1)]
    rw [tiiData_zero_of_le (Nat.not_lt.mp hlt), mul_zero]

/-- **Linearity of `dconv` in its 2nd argument over the co-divisor cover.**  For
`n ≤ x`, the block convolution with the full `typeIIData` co-divisor equals the
sum of block convolutions with the dyadic `tiiBlock` pieces. -/
theorem dconv_typeIIData_eq_sum_tiiBlock {x : ℕ} (hx : 1 ≤ x) (a : ℕ) {n : ℕ}
    (hn : n ≤ x) :
    dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n
      = ∑ b ∈ Finset.range (dCount x), dconv (muBlock a x) (tiiBlock b x) n := by
  unfold dconv
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← Finset.mul_sum]
  congr 1
  have hndx : n / d ≤ x := le_trans (Nat.div_le_self n d) hn
  exact (sum_tiiBlock_eq hx hndx).symm

/-- **The per-`a` co-divisor block subadditivity.**  The `y`-cutoff discrepancy of
the `μ`-block against the full `typeIIData` co-divisor is bounded by the sum over
the dyadic `tiiBlock` pieces. -/
theorem hdecomp_typeII_split {x : ℕ} (hx : 1 ≤ x) (a : ℕ) (y q : ℕ) (hyx : y ≤ x) :
    seqDiscrepancy (fun n => dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n) y q
      ≤ ∑ b ∈ Finset.range (dCount x),
          seqDiscrepancy (fun n => dconv (muBlock a x) (tiiBlock b x) n) y q := by
  have hcongr : ∀ n ∈ Finset.Icc 1 y,
      dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n
        = ∑ b ∈ Finset.range (dCount x), dconv (muBlock a x) (tiiBlock b x) n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact dconv_typeIIData_eq_sum_tiiBlock hx a (le_trans hn.2 hyx)
  calc seqDiscrepancy (fun n => dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n) y q
      = seqDiscrepancy (fun n => ∑ b ∈ Finset.range (dCount x),
          dconv (muBlock a x) (tiiBlock b x) n) y q := seqDiscrepancy_congr_Icc q hcongr
    _ ≤ _ := seqDiscrepancy_sum_le (Finset.range (dCount x))
        (fun b n => dconv (muBlock a x) (tiiBlock b x) n) y q

/-! ## §2  The pair enumeration and the double-dyadic subadditivity -/

/-- **Flatten a `M × N` double range sum** via the pair enumeration
`i ↦ (i / N, i % N)`. -/
theorem double_range_flatten {G : Type*} [AddCommMonoid G] (M N : ℕ) (f : ℕ → ℕ → G) :
    ∑ i ∈ Finset.range (M * N), f (i / N) (i % N)
      = ∑ a ∈ Finset.range M, ∑ b ∈ Finset.range N, f a b := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_range] at hb
    have hN : 0 < N := by omega
    have hdiv : (M * N + b) / N = M := by
      rw [Nat.mul_comm, Nat.mul_add_div hN, Nat.div_eq_of_lt hb, Nat.add_zero]
    have hmod : (M * N + b) % N = b := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
    rw [hdiv, hmod]

/-- The double block count `m2 x = (dCount x)²`. -/
def m2 (x : ℕ) : ℕ := dCount x * dCount x

/-- The `μ`-side dyadic index of the flat pair index `i`. -/
def aIdx (i x : ℕ) : ℕ := i / dCount x

/-- The co-divisor dyadic index of the flat pair index `i`. -/
def bIdx (i x : ℕ) : ℕ := i % dCount x

/-- **The double-dyadic block subadditivity (rung 1).**  The `y`-cutoff
discrepancy of `vP3` is bounded by the sum over the flat pair enumeration of the
double-dyadic block-pair discrepancies `dconv (muBlock aIdx) (tiiBlock bIdx)`. -/
theorem hdecomp_double {x : ℕ} (hx : 1 ≤ x) (y q : ℕ) (hyx : y ≤ x) :
    seqDiscrepancy (fun n => vP3 (cbrt x) (cbrt x) n) y q
      ≤ ∑ i ∈ Finset.range (m2 x),
          seqDiscrepancy
            (fun n => dconv (muBlock (aIdx i x) x) (tiiBlock (bIdx i x) x) n) y q := by
  calc seqDiscrepancy (fun n => vP3 (cbrt x) (cbrt x) n) y q
      ≤ ∑ a ∈ Finset.range (dCount x),
          seqDiscrepancy
            (fun n => dconv (muBlock a x) (Salt.LS.typeIIData (cbrt x)) n) y q :=
        hdecomp_dyadic hx y q hyx
    _ ≤ ∑ a ∈ Finset.range (dCount x), ∑ b ∈ Finset.range (dCount x),
          seqDiscrepancy (fun n => dconv (muBlock a x) (tiiBlock b x) n) y q :=
        Finset.sum_le_sum (fun a _ => hdecomp_typeII_split hx a y q hyx)
    _ = ∑ i ∈ Finset.range (m2 x),
          seqDiscrepancy
            (fun n => dconv (muBlock (aIdx i x) x) (tiiBlock (bIdx i x) x) n) y q := by
        rw [m2]
        exact (double_range_flatten (dCount x) (dCount x)
          (fun a b => seqDiscrepancy (fun n => dconv (muBlock a x) (tiiBlock b x) n) y q)).symm

/-! ## §3  The double block count (rung 2) -/

/-- **The double block count is `polylog²`** (`hcount` with `p = 2`):
`m2 x ≤ (2/log 2)²·(log x)²` for `x ≥ 2`. -/
theorem blockCount2_le {x : ℕ} (hx : 2 ≤ x) :
    (m2 x : ℝ) ≤ (2 / Real.log 2) ^ 2 * Real.log x ^ (2 : ℝ) := by
  have hbc : (dCount x : ℝ) ≤ (2 / Real.log 2) * Real.log x := blockCount_le hx
  have hd0 : (0 : ℝ) ≤ (dCount x : ℝ) := Nat.cast_nonneg _
  have hsq : (dCount x : ℝ) ^ 2 ≤ ((2 / Real.log 2) * Real.log x) ^ 2 :=
    pow_le_pow_left₀ hd0 hbc 2
  have hlogx0 : (0 : ℝ) ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hrpow : Real.log x ^ (2 : ℝ) = Real.log x ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [m2]
  push_cast
  calc (dCount x : ℝ) * (dCount x : ℝ)
      = (dCount x : ℝ) ^ 2 := by ring
    _ ≤ ((2 / Real.log 2) * Real.log x) ^ 2 := hsq
    _ = (2 / Real.log 2) ^ 2 * Real.log x ^ (2 : ℝ) := by rw [mul_pow, hrpow]

/-! ## §4  The anchor balance Zeno stone (rung 3, relaxed cap — catch #96 resolved)

`hanch` demands FIVE conjuncts per block; the fifth was originally the anchor cap
`2·N·M ≤ x`, jointly unsatisfiable with `hdecomp_double` (the topmost nonzero
anti-diagonal has `N·M ∈ [x/2, x)`, so `2·N·M ∈ [x, 2x)`).  The Fable-authorized
fix (catch #96, GEH-DOOR-2) relaxes the cap to `2·N·M ≤ 2x`, TRUE for all nonzero
blocks (support ⟹ `N·M < x`).  `anch_balance_of_le` below is the reusable stone
supplying the four BALANCE conjuncts under `2·N·M ≤ 2x` at `ε = 1/4` (threshold
raised `27 → 64` for the `2x ≤ (cbrt x)⁴` margin); the relaxed combinator
`pieceObligationU_of_anchored_multiblock` consumes it. -/

/-- `1 ≤ cbrt x` for `x ≥ 1`. -/
private theorem one_le_cbrt {x : ℕ} (hx : 1 ≤ x) : 1 ≤ cbrt x := by
  rw [cbrt]; apply Nat.le_floor; rw [Nat.cast_one]
  calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 3) := by rw [Real.one_rpow]
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)

/-- `3 ≤ cbrt x` for `x ≥ 27` (the quartic-cover threshold). -/
private theorem cbrt_ge_three_of_le {x : ℕ} (hx : 27 ≤ x) : 3 ≤ cbrt x := by
  rw [cbrt]; apply Nat.le_floor
  have h27 : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
    rw [show (27 : ℝ) = (3 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast (3 : ℝ) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
  calc ((3 : ℕ) : ℝ) = (27 : ℝ) ^ ((1 : ℝ) / 3) := by rw [h27]; norm_num
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)

/-- `4 ≤ cbrt x` for `x ≥ 64` (the relaxed-cap `2·N·M ≤ 2x` quartic-cover
threshold: `2·(c+1)³ ≤ c⁴` needs `c ≥ 4`). -/
private theorem cbrt_ge_four_of_le {x : ℕ} (hx : 64 ≤ x) : 4 ≤ cbrt x := by
  rw [cbrt]; apply Nat.le_floor
  have h64 : (64 : ℝ) ^ ((1 : ℝ) / 3) = 4 := by
    rw [show (64 : ℝ) = (4 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast (4 : ℝ) 3,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show ((3 : ℕ) : ℝ) * ((1 : ℝ) / 3) = 1 by norm_num, Real.rpow_one]
  calc ((4 : ℕ) : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 3) := by rw [h64]; norm_num
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hx) (by norm_num)

/-- The real cube-root cubed: `(x^{1/3})³ = x`. -/
private theorem rpow_third_cube (x : ℕ) :
    ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (x : ℝ) := by
  rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 3,
    ← Real.rpow_mul (Nat.cast_nonneg x)]
  rw [show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]

/-- `(cbrt x)³ ≤ x`. -/
private theorem cbrt_cube_le (x : ℕ) : cbrt x ^ 3 ≤ x := by
  have h1 : (cbrt x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [cbrt]; exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) _)
  have h2 : (cbrt x : ℝ) ^ (3 : ℕ) ≤ (x : ℝ) := by
    calc (cbrt x : ℝ) ^ (3 : ℕ) ≤ ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) h1 3
      _ = (x : ℝ) := rpow_third_cube x
  exact_mod_cast h2

/-- `x < (cbrt x + 1)³`. -/
private theorem lt_cbrt_add_one_cube (x : ℕ) : x < (cbrt x + 1) ^ 3 := by
  have h1 : (x : ℝ) ^ ((1 : ℝ) / 3) < (cbrt x : ℝ) + 1 := by
    rw [cbrt]; exact_mod_cast Nat.lt_floor_add_one _
  have h2 : (x : ℝ) < ((cbrt x : ℝ) + 1) ^ (3 : ℕ) := by
    rw [← rpow_third_cube x]
    exact pow_lt_pow_left₀ h1 (Real.rpow_nonneg (Nat.cast_nonneg x) _) (by norm_num)
  exact_mod_cast h2

/-- `x ≤ (cbrt x)⁴` for `x ≥ 27` (the μ-side/co-divisor quartic cover). -/
private theorem x_le_cbrt_pow4 {x : ℕ} (hx : 27 ≤ x) : x ≤ cbrt x ^ 4 := by
  have hlt := lt_cbrt_add_one_cube x
  have hc3 := cbrt_ge_three_of_le hx
  have hstep : (cbrt x + 1) ^ 3 ≤ cbrt x ^ 4 := by
    nlinarith [hc3, mul_le_mul_of_nonneg_right hc3 (pow_nonneg (Nat.zero_le (cbrt x)) 3),
      mul_le_mul_of_nonneg_right hc3 (pow_nonneg (Nat.zero_le (cbrt x)) 2),
      mul_le_mul_of_nonneg_right hc3 (Nat.zero_le (cbrt x))]
  exact le_of_lt (lt_of_lt_of_le hlt hstep)

/-- `2·x ≤ (cbrt x)⁴` for `x ≥ 64` (the relaxed-cap `2·N·M ≤ 2x` quartic cover).
From `x < (cbrt x + 1)³` and `2·(cbrt x + 1)³ ≤ (cbrt x)⁴` (valid for `cbrt x ≥ 4`). -/
private theorem two_x_le_cbrt_pow4 {x : ℕ} (hx : 64 ≤ x) : 2 * x ≤ cbrt x ^ 4 := by
  have hlt := lt_cbrt_add_one_cube x
  have hc4 := cbrt_ge_four_of_le hx
  have hstep : 2 * (cbrt x + 1) ^ 3 ≤ cbrt x ^ 4 := by
    nlinarith [hc4, mul_le_mul_of_nonneg_right hc4 (pow_nonneg (Nat.zero_le (cbrt x)) 3),
      mul_le_mul_of_nonneg_right hc4 (pow_nonneg (Nat.zero_le (cbrt x)) 2),
      mul_le_mul_of_nonneg_right hc4 (Nat.zero_le (cbrt x))]
  exact le_of_lt (calc 2 * x < 2 * (cbrt x + 1) ^ 3 := by omega
    _ ≤ cbrt x ^ 4 := hstep)

/-- `x ≤ 8·(cbrt x)³` for `x ≥ 1` (the crude cube cover). -/
private theorem x_le_eight_cbrt_pow3 {x : ℕ} (hx : 1 ≤ x) : x ≤ 8 * cbrt x ^ 3 := by
  have hc1 := one_le_cbrt hx
  have hlt := lt_cbrt_add_one_cube x
  have hstep : (cbrt x + 1) ^ 3 ≤ 8 * cbrt x ^ 3 := by
    calc (cbrt x + 1) ^ 3 ≤ (2 * cbrt x) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * cbrt x ^ 3 := by ring
  exact le_of_lt (lt_of_lt_of_le hlt hstep)

/-- `s^{1/4} ≤ N` from `s ≤ N⁴` (both nonneg). -/
private theorem rpow_quarter_le {s N : ℝ} (hs : 0 ≤ s) (hN : 0 ≤ N)
    (h : s ≤ N ^ (4 : ℕ)) : s ^ ((1 : ℝ) / 4) ≤ N := by
  have h1 : s ^ ((1 : ℝ) / 4) ≤ (N ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hs h (by norm_num)
  have h2 : (N ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = N := by
    rw [← Real.rpow_natCast N 4, ← Real.rpow_mul hN,
      show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
  rwa [h2] at h1

/-- `N ≤ s^{3/4}` from `N⁴ ≤ s³` (both nonneg). -/
private theorem le_rpow_three_quarter {s N : ℝ} (hs : 0 ≤ s) (hN : 0 ≤ N)
    (h : N ^ (4 : ℕ) ≤ s ^ (3 : ℕ)) : N ≤ s ^ ((3 : ℝ) / 4) := by
  have hNeq : N = (N ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_natCast N 4, ← Real.rpow_mul hN,
      show ((4 : ℕ) : ℝ) * ((1 : ℝ) / 4) = 1 by norm_num, Real.rpow_one]
  have h1 : (N ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) ≤ (s ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (pow_nonneg hN 4) h (by norm_num)
  have hseq : (s ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) = s ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast s 3, ← Real.rpow_mul hs]
    congr 1; norm_num
  calc N = (N ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := hNeq
    _ ≤ (s ^ (3 : ℕ)) ^ ((1 : ℝ) / 4) := h1
    _ = s ^ ((3 : ℝ) / 4) := hseq

/-- **The anchor balance Zeno stone (rung 3, relaxed cap).**  For `x ≥ 64` and any
double-dyadic block whose anchor satisfies the RELAXED cap `2·N·M ≤ 2x` (with
`N = nScale a x`, `M = nScale b x`), the FOUR balance conjuncts of `hanch` hold at
`ε = 1/4`.  This is the stone the anchor-cap-relaxed combinator
(`pieceObligationU_of_anchored_multiblock`, resolving catch #96) consumes: the
fifth conjunct `2·N·M ≤ 2x` is now TRUE for all nonzero blocks (support ⟹
`N·M < x` ⟹ `2·N·M < 2x`).  Proof: both `N, M ≥ cbrt x`, so
`s = 2NM ≤ 2x ≤ (cbrt x)⁴ ≤ N⁴` gives `s^{1/4} ≤ N` (needs `2x ≤ (cbrt x)⁴`, i.e.
`cbrt x ≥ 4`, `x ≥ 64`); and — cap-tighter route — `N ≤ N·M ≤ x ≤ 8(cbrt x)³ ≤ 8M³`
gives `N⁴ ≤ 8N³M³ = s³`, i.e. `N ≤ s^{3/4}` (symmetrically for `M`).  The `N ≤ 8M³`
side uses only `N·M ≤ x` (from `2NM ≤ 2x`), so it is cap-value-independent. -/
theorem anch_balance_of_le {x a b : ℕ} (hx : 64 ≤ x)
    (hle : 2 * nScale a x * nScale b x ≤ 2 * x) :
    ((2 * nScale a x * nScale b x : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ (nScale a x : ℝ) ∧
    (nScale a x : ℝ) ≤ ((2 * nScale a x * nScale b x : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ∧
    ((2 * nScale a x * nScale b x : ℕ) : ℝ) ^ ((1 : ℝ) / 4) ≤ (nScale b x : ℝ) ∧
    (nScale b x : ℝ) ≤ ((2 * nScale a x * nScale b x : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := by
  have hx1 : 1 ≤ x := by omega
  have hc1 : 1 ≤ cbrt x := one_le_cbrt hx1
  have hcN : cbrt x ≤ nScale a x := by
    unfold nScale; exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) a)
  have hcM : cbrt x ≤ nScale b x := by
    unfold nScale; exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) b)
  set N := nScale a x with hNdef
  set M := nScale b x with hMdef
  have hN1 : 1 ≤ N := le_trans hc1 hcN
  have hM1 : 1 ≤ M := le_trans hc1 hcM
  have h2x4 : 2 * x ≤ cbrt x ^ 4 := two_x_le_cbrt_pow4 hx
  have hx3 : x ≤ 8 * cbrt x ^ 3 := x_le_eight_cbrt_pow3 hx1
  -- `N·M ≤ x` from the relaxed cap `2·N·M ≤ 2x` (the cap-tighter fact for conj. 2/4).
  have hNMnat : N * M ≤ x := by
    have h := hle
    rw [mul_assoc] at h
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hNr0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hMr0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hsr0 : (0 : ℝ) ≤ ((2 * N * M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcr0 : (0 : ℝ) ≤ (cbrt x : ℝ) := Nat.cast_nonneg _
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hMr1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hcNr : (cbrt x : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcN
  have hcMr : (cbrt x : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcM
  have hler : ((2 * N * M : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hle
  have hNMr : (N : ℝ) * (M : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNMnat
  have h2x4r : 2 * (x : ℝ) ≤ (cbrt x : ℝ) ^ 4 := by exact_mod_cast h2x4
  have hx3r : (x : ℝ) ≤ 8 * (cbrt x : ℝ) ^ 3 := by exact_mod_cast hx3
  have hseq : ((2 * N * M : ℕ) : ℝ) = 2 * (N : ℝ) * (M : ℝ) := by push_cast; ring
  have hsN4 : ((2 * N * M : ℕ) : ℝ) ≤ (N : ℝ) ^ (4 : ℕ) :=
    calc ((2 * N * M : ℕ) : ℝ) ≤ 2 * (x : ℝ) := hler
      _ ≤ (cbrt x : ℝ) ^ 4 := h2x4r
      _ ≤ (N : ℝ) ^ 4 := pow_le_pow_left₀ hcr0 hcNr 4
  have hsM4 : ((2 * N * M : ℕ) : ℝ) ≤ (M : ℝ) ^ (4 : ℕ) :=
    calc ((2 * N * M : ℕ) : ℝ) ≤ 2 * (x : ℝ) := hler
      _ ≤ (cbrt x : ℝ) ^ 4 := h2x4r
      _ ≤ (M : ℝ) ^ 4 := pow_le_pow_left₀ hcr0 hcMr 4
  -- `N ≤ 8M³` via `N ≤ N·M ≤ x ≤ 8(cbrt x)³ ≤ 8M³` (cap-value-independent).
  have hN8M3 : (N : ℝ) ≤ 8 * (M : ℝ) ^ 3 := by
    have hN_le_NM : (N : ℝ) ≤ (N : ℝ) * (M : ℝ) := le_mul_of_one_le_right hNr0 hMr1
    have hmono : 8 * (cbrt x : ℝ) ^ 3 ≤ 8 * (M : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hcr0 hcMr 3; linarith
    calc (N : ℝ) ≤ (N : ℝ) * (M : ℝ) := hN_le_NM
      _ ≤ (x : ℝ) := hNMr
      _ ≤ 8 * (cbrt x : ℝ) ^ 3 := hx3r
      _ ≤ 8 * (M : ℝ) ^ 3 := hmono
  have hM8N3 : (M : ℝ) ≤ 8 * (N : ℝ) ^ 3 := by
    have hM_le_NM : (M : ℝ) ≤ (N : ℝ) * (M : ℝ) := le_mul_of_one_le_left hMr0 hNr1
    have hmono : 8 * (cbrt x : ℝ) ^ 3 ≤ 8 * (N : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hcr0 hcNr 3; linarith
    calc (M : ℝ) ≤ (N : ℝ) * (M : ℝ) := hM_le_NM
      _ ≤ (x : ℝ) := hNMr
      _ ≤ 8 * (cbrt x : ℝ) ^ 3 := hx3r
      _ ≤ 8 * (N : ℝ) ^ 3 := hmono
  have hN4s3 : (N : ℝ) ^ (4 : ℕ) ≤ ((2 * N * M : ℕ) : ℝ) ^ (3 : ℕ) := by
    rw [hseq]
    nlinarith [mul_le_mul_of_nonneg_right hN8M3 (pow_nonneg hNr0 3)]
  have hM4s3 : (M : ℝ) ^ (4 : ℕ) ≤ ((2 * N * M : ℕ) : ℝ) ^ (3 : ℕ) := by
    rw [hseq]
    nlinarith [mul_le_mul_of_nonneg_right hM8N3 (pow_nonneg hMr0 3)]
  exact ⟨rpow_quarter_le hsr0 hNr0 hsN4, le_rpow_three_quarter hsr0 hNr0 hN4s3,
    rpow_quarter_le hsr0 hMr0 hsM4, le_rpow_three_quarter hsr0 hMr0 hM4s3⟩

end Salt.Maynard
