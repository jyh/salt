/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ArithPageLinear
import Salt.MR.DoorFrameH1
import Salt.MR.Eq26Compose
import Salt.MR.M4Residue

/-!
# `DoorLadderLinear` — the LADDER's door-frame layer at `AdoorL M = 2^36·M`

⟦LADDER-L, G1 §1⟧  `DoorLinear` cut the DOOR linear and `ArithPageLinear` carried the
ARITHMETIC page; what neither reached is the **ladder** copy of the door — the `calP`/`calQK`
family read at `Adoor M` inside `DoorFrameH1`, `Eq26Compose` and `M4Residue`, which the
register's re-cut missed (⟦COMPOSE-FLAT-2⟧'s `flat_landed_ladder_break`).

This page is **additive**: every landed declaration is untouched.  What is minted here is the
`_L` twin family of those three pages at the linear anchor, with the `G`-slot unchanged
(`3072·M`, resp. `s13GK K M`).

## What the re-cut costs, page by page

* **`DoorFrameH1`** — the corrected width `H₁ = P₁^{1/12}/(log 𝒬₁)^{1/3}` is
  `ArithPageLinear.H1doorL` already; what was missing is its FRAME (`H1_two`/`H1_pin`) and
  the G6 decay certificate at the linear anchor.  The anchor's quarter moves from
  `Kdoor M = 2^34(⌊log₂M⌋+1)` to `KdoorL M = 2^34·M`, and the `8M·A ≤ 2^{2L+41}` stone
  re-proves with `M ≤ 2^{L+1}` in BOTH slots (the landed proof paid `L+1 ≤ 2^{L+1}` in one
  of them).  Everything else is the landed text at `AdoorL`.
* **`Eq26Compose`** — the `k`-scaled frame's `A_gate_logK` certificate is the landed
  `gate_log_arith` with `(L+1)` replaced by `M`; the two are bridged by the single monotone
  step `(L+1)·k·log 2 ≤ M·k·log 2` (`Nat.log_lt_self`).  `Ah_L` is the `h`-dependent anchor
  over `AdoorL`, and its containment/one-sidedness are the landed arguments verbatim.
* **`M4Residue`** — the dilation gate reads only the door's BOTTOM block `𝒫₁ = 2^{A}`, and
  `2^{262144} ≤ 2^{AdoorL M}` needs `1 ≤ M` (where the landed `Adoor` floor was
  unconditional).  That hypothesis is threaded through the four gate lemmas; every door
  consumer already carries it.

⚠ **The `K`-ceiling is the WIDE one.**  `DoorLinear.calFrameK_satisfiable_doorL_gk` buys
`K ≤ 1.7·10⁸·M` where the landed cut bought `K ≤ 1.7·10⁸`; the `_gk` twins below inherit the
wide side condition, so a consumer holding the narrow bound weakens with
`Nat.le_mul_of_pos_right`.

Source pins: `docs/blueprints/flags.md` ⟦COMPOSE-FLAT-2⟧, ⟦LINEAR-PAGE⟧, ⟦FLAT-REF⟧
amendment 0.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §0 — the private rpow/arith stones, re-cut

`DoorFrameH1`'s and `Eq26Compose`'s helper stones are `private`, hence invisible across
modules; they are re-declared here verbatim (they are door-free, so no `_L` is warranted in
their names). -/

/-- `(x^a)^n = x^b` whenever `a·n = b` — the rpow-gate idiom, on an abstract base. -/
private lemma rpow_pow_eq {x : ℝ} (hx : 0 ≤ x) {a b : ℝ} (n : ℕ) (h : a * (n : ℝ) = b) :
    (x ^ a) ^ n = x ^ b := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx, h]

/-- `(x^a)^n = x` whenever `a·n = 1`. -/
private lemma rpow_pow_one {x : ℝ} (hx : 0 ≤ x) {a : ℝ} (n : ℕ) (h : a * (n : ℝ) = 1) :
    (x ^ a) ^ n = x := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx, h, Real.rpow_one]

/-- `(x^n)^a = x` whenever `n·a = 1` — the exact fourth root of `𝒫₁ = (2^{KdoorL M})^4`. -/
private lemma pow_rpow_one {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {a : ℝ} (h : (n : ℝ) * a = 1) :
    (x ^ n) ^ a = x := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, h, Real.rpow_one]

/-- The abstract shape behind the level-1 identity: `(w/z)²·z³·(w³)⁻¹ = z/w`. -/
private lemma level1_ratio {w z L P : ℝ} (hw : 0 < w) (hz : 0 < z)
    (hL : L = z ^ (3 : ℕ)) (hP : P = (w ^ (3 : ℕ))⁻¹) :
    (w / z) ^ 2 * L * P = z / w := by
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hz0 : z ≠ 0 := ne_of_gt hz
  subst hL
  subst hP
  field_simp

/-- The abstract §8.1 level-1 shape, at `α₁ = 1/8` and `H₁ ≥ 2`. -/
private lemma level1_shape {Ha Lq Pq R : ℝ} (hH2 : 2 ≤ Ha) (hLq : 1 ≤ Lq)
    (hPq : 0 < Pq) (hR : 0 ≤ R) :
    2 * (Ha * Lq + 1) * R * Pq
        * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
            + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
      ≤ 5280 * R * (Ha ^ 2 * Lq * Pq) := by
  have hHa0 : (0 : ℝ) < Ha := by linarith
  have he1 : Real.exp ((3 / 4 : ℝ) / Ha) ≤ 2.7182818286 := by
    have h : (3 / 4 : ℝ) / Ha ≤ 1 := by rw [div_le_one hHa0]; linarith
    exact le_trans (Real.exp_le_exp.mpr h) Real.exp_one_lt_d9.le
  have he2 : Real.exp ((1 / 2 : ℝ) / Ha) ≤ 2.7182818286 := by
    have h : (1 / 2 : ℝ) / Ha ≤ 1 := by rw [div_le_one hHa0]; linarith
    exact le_trans (Real.exp_le_exp.mpr h) Real.exp_one_lt_d9.le
  have hB1 : 4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
      ≤ 16 / 3 * Ha * 2.7182818286 := by
    have hEq : 4 * (Ha / (3 / 4 : ℝ)) = 16 / 3 * Ha := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_left he1 (by linarith)
  have hB2 : 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha)
      ≤ 480 * Ha * 2.7182818286 := by
    have hEq : 60 * (Ha / (1 / 8 : ℝ)) = 480 * Ha := by ring
    rw [hEq]
    exact mul_le_mul_of_nonneg_left he2 (by linarith)
  have hB : 4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
      + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha) ≤ 1320 * Ha := by linarith
  have hB0 : (0 : ℝ) ≤ 4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
      + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha) := by
    have hc1 : (0 : ℝ) ≤ 4 * (Ha / (3 / 4 : ℝ)) := by linarith
    have hc2 : (0 : ℝ) ≤ 60 * (Ha / (1 / 8 : ℝ)) := by linarith
    linarith [mul_nonneg hc1 (Real.exp_pos ((3 / 4 : ℝ) / Ha)).le,
      mul_nonneg hc2 (Real.exp_pos ((1 / 2 : ℝ) / Ha)).le]
  have hHL : (1 : ℝ) ≤ Ha * Lq := by nlinarith
  have key : 2 * (Ha * Lq + 1)
        * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
            + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
      ≤ 5280 * (Ha ^ 2 * Lq) := by
    calc 2 * (Ha * Lq + 1)
          * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
              + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
        ≤ (4 * (Ha * Lq)) * (1320 * Ha) :=
          mul_le_mul (by linarith) hB hB0 (by linarith)
      _ = 5280 * (Ha ^ 2 * Lq) := by ring
  calc 2 * (Ha * Lq + 1) * R * Pq
        * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
            + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))
      = (2 * (Ha * Lq + 1)
          * (4 * (Ha / (3 / 4 : ℝ)) * Real.exp ((3 / 4 : ℝ) / Ha)
              + 60 * (Ha / (1 / 8 : ℝ)) * Real.exp ((1 / 2 : ℝ) / Ha))) * (R * Pq) := by ring
    _ ≤ (5280 * (Ha ^ 2 * Lq)) * (R * Pq) :=
        mul_le_mul_of_nonneg_right key (mul_nonneg hR hPq.le)
    _ = 5280 * R * (Ha ^ 2 * Lq * Pq) := by ring

/-! ## §1 — `DoorFrameH1` at the linear anchor -/

/-- **The linear door anchor's quarter** `K_L(M) := 2^34·M`, so that `AdoorL M = 4·K_L(M)`
(`Adoor_eq_four_mul_L`).  Kept as a DEFINITION so `ring`/`linarith` treat `2^{K_L(M)}` as an
atom (the V9c law). -/
def KdoorL (M : ℕ) : ℕ := 17179869184 * M

lemma Adoor_eq_four_mul_L (M : ℕ) : AdoorL M = 4 * KdoorL M := by
  simp only [AdoorL, KdoorL]
  have h : (2 : ℕ) ^ 36 = 4 * 17179869184 := by norm_num
  rw [h, mul_assoc]

/-- `𝒫₁ ≥ 64` at the linear door: `e₁ = A_L(M) ≥ 2^36 ≥ 6` (`calE_one`, `AdoorL_ge`).  The
`1 ≤ M` is the one hypothesis the re-cut adds — `AdoorL 0 = 0`. -/
lemma calP_door_one_ge_L {M : ℕ} (hM : 1 ≤ M) :
    (64 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
  have hE : (6 : ℕ) ≤ calE (AdoorL M) (3072 * M) 1 := by
    rw [calE_one]
    exact le_trans (by norm_num) (AdoorL_ge hM)
  have h64 : (64 : ℕ) ≤ calP (AdoorL M) (3072 * M) 1 := by
    rw [calP, show (64 : ℕ) = 2 ^ 6 by norm_num]
    exact Nat.pow_le_pow_right (by norm_num) hE
  exact_mod_cast h64

/-- **`𝒫₁^{1/4}` EXACTLY, with no estimate**, at the linear anchor: `AdoorL M = 4·K_L(M)`,
so `𝒫₁ = (2^{K_L(M)})^4` and the fourth root is the base-2 power itself. -/
lemma calP_door_one_rpow_quarter_L (M : ℕ) :
    ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ KdoorL M := by
  have hnat : calP (AdoorL M) (3072 * M) 1 = (2 ^ KdoorL M) ^ 4 := by
    rw [calP, calE_one, Adoor_eq_four_mul_L, pow_mul']
  have hcast : ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) = ((2 : ℝ) ^ KdoorL M) ^ (4 : ℕ) := by
    rw [hnat]
    push_cast
    ring
  rw [hcast]
  exact pow_rpow_one (pow_nonneg (by norm_num) _) 4 (by norm_num)

/-- The linear door's `8MA`, bounded by a base-2 exponent: `8·M·A_L = 2^3·M·2^36·M
≤ 2^{2L+41}` with `M ≤ 2^{L+1}` in BOTH slots (the landed proof paid `L+1 ≤ 2^{L+1}` in
one of them). -/
private lemma door_MA_bound_L (M : ℕ) :
    8 * (M * AdoorL M) ≤ 2 ^ (2 * Nat.log 2 M + 41) := by
  have hMle : M ≤ 2 ^ (Nat.log 2 M + 1) := (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) M).le
  calc 8 * (M * AdoorL M) = 2 ^ 3 * (M * (2 ^ 36 * M)) := by
        rw [AdoorL]; ring
    _ ≤ 2 ^ 3 * (2 ^ (Nat.log 2 M + 1) * (2 ^ 36 * 2 ^ (Nat.log 2 M + 1))) :=
        Nat.mul_le_mul le_rfl (Nat.mul_le_mul hMle (Nat.mul_le_mul le_rfl hMle))
    _ = 2 ^ (2 * Nat.log 2 M + 41) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega

/-- **`log 𝒬₁ ≥ 1`** at the linear door family: `log 𝒬₁ = M·A_L(M)·log 2 ≥ 2^36·log 2`. -/
lemma one_le_log_calQK_door_one_L {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hA : (262144 : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) := by rw [AdoorL_cast]; linarith
  have hprod : (262144 : ℝ) * 0.6931471803 ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul hA Real.log_two_gt_d9.le (by norm_num) (by linarith)
  have hAL : (1 : ℝ) ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 := by linarith
  have hstep : ((AdoorL M : ℕ) : ℝ) * Real.log 2
      ≤ (M : ℝ) * (((AdoorL M : ℕ) : ℝ) * Real.log 2) :=
    le_mul_of_one_le_left (by linarith) hMR
  rw [log_calQK_doorL_one]
  linarith

/-- **`H1_two` at the linear corrected pin.**  Cubed, the gate is `8 log 𝒬₁ ≤ 𝒫₁^{1/4}`, i.e.
`8MA_L log 2 ≤ 2^{K_L(M)}`; the left side is `≤ 2^{2L+41}`, and `2L + 41 ≤ 2^34·M` at
`M ≥ 1` with vast room. -/
lemma H1door_two_L {M : ℕ} (hM : 1 ≤ M) : 2 ≤ H1doorL M := by
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hlogQ0 : (0 : ℝ) < Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP64 := calP_door_one_ge_L hM
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hz0 : (0 : ℝ)
      < (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlogQ0 _
  have hz3 : ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      = Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) :=
    rpow_pow_one hlogQ0.le 3 (by norm_num)
  have hw3 : (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ^ (3 : ℕ)
      = ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    rpow_pow_eq hP0.le 3 (by norm_num)
  have hMAR : (8 : ℝ) * ((M : ℝ) * ((AdoorL M : ℕ) : ℝ))
      ≤ (2 : ℝ) ^ (2 * Nat.log 2 M + 41) := by
    exact_mod_cast door_MA_bound_L M
  have hMA0 : (0 : ℝ) ≤ (M : ℝ) * ((AdoorL M : ℕ) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hshrink : (8 : ℝ) * ((M : ℝ) * ((AdoorL M : ℕ) : ℝ) * Real.log 2)
      ≤ (8 : ℝ) * ((M : ℝ) * ((AdoorL M : ℕ) : ℝ)) := by nlinarith
  have hexpgrow : (2 : ℝ) ^ (2 * Nat.log 2 M + 41) ≤ (2 : ℝ) ^ KdoorL M := by
    refine pow_le_pow_right₀ (by norm_num) ?_
    have hLs : Nat.log 2 M ≤ M := Nat.log_le_self 2 M
    simp only [KdoorL]
    omega
  have hfinal : (2 : ℝ) ^ (3 : ℕ) * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ KdoorL M := by
    have h8 : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
    rw [h8, log_calQK_doorL_one]
    linarith
  rw [H1doorL, le_div_iff₀ hz0]
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg hP0.le _) ?_
  rw [mul_pow, hz3, hw3, calP_door_one_rpow_quarter_L]
  exact hfinal

/-- **The cube of the linear corrected pin**: `H₁³ = 𝒫₁^{1/4}/log 𝒬₁`. -/
lemma H1door_cube_L {M : ℕ} (hM : 1 ≤ M) :
    (H1doorL M) ^ 3
      = ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
          / Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hlogQ0 : (0 : ℝ) < Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP64 := calP_door_one_ge_L hM
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hz3 : ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      = Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) :=
    rpow_pow_one hlogQ0.le 3 (by norm_num)
  have hw3 : (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ^ (3 : ℕ)
      = ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    rpow_pow_eq hP0.le 3 (by norm_num)
  rw [H1doorL, div_pow, hz3, hw3]

/-- **`H1_pin` at the linear corrected pin**, with room to spare. -/
lemma H1door_pin_L {M : ℕ} (hM : 1 ≤ M) :
    (H1doorL M) ^ 3 ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hP64 := calP_door_one_ge_L hM
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  rw [H1door_cube_L hM]
  calc ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4)
        / Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
      ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
        div_le_self (Real.rpow_nonneg hP0.le _) hlogQ1
    _ ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)

/-- **THE LINEAR DOOR'S K-STATION FRAME AT MR'S OWN `H₁`**
(`calFrameK_satisfiable_doorH1_L`).  Ten of the twelve fields are
`DoorLinear.calFrameK_satisfiable_doorL`'s — none of them sees the width — and the two that
do are `H1door_two_L`/`H1door_pin_L`. -/
theorem calFrameK_satisfiable_doorH1_L (M : ℕ) (hM : 1 ≤ M) :
    CalFrameK (1 / 12) (H1doorL M) (AdoorL M) (3072 * M) M 2
      (calQK (AdoorL M) (3072 * M) M 2) := by
  have hF := calFrameK_satisfiable_doorL M hM
  exact ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, H1door_two_L hM, H1door_pin_L hM, hF.Q_le_Xd⟩

/-- **The twelve `LevelGates` at the linear corrected door family**, free from the frame. -/
theorem levelGates_calibrated_doorH1_L (M : ℕ) (hM : 1 ≤ M) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M)
        (calH (H1doorL M)) (1 / 12)
        ((calP (AdoorL M) (3072 * M)) 1) (calQK (AdoorL M) (3072 * M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_doorH1_L M hM)

/-- **THE G6 CERTIFICATE AT THE LINEAR ANCHOR, as an exact identity**:
`H₁²·log 𝒬₁·𝒫₁^{−1/4} = (log 𝒬₁)^{1/3}/𝒫₁^{1/12}`. -/
theorem H1door_level1_identity_L {M : ℕ} (hM : 1 ≤ M) {e : ℝ} (he : e = -((1 : ℝ) / 4)) :
    (H1doorL M) ^ 2 * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
        * ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ e
      = (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) := by
  have hlogQ1 := one_le_log_calQK_door_one_L hM
  have hlogQ0 : (0 : ℝ) < Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by linarith
  have hP64 := calP_door_one_ge_L hM
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hz0 : (0 : ℝ)
      < (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlogQ0 _
  have hw0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hP0 _
  have hz3 : ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      = Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) :=
    rpow_pow_one hlogQ0.le 3 (by norm_num)
  have hw3 : (((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) ^ (3 : ℕ)
      = ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 4) :=
    rpow_pow_eq hP0.le 3 (by norm_num)
  rw [H1doorL]
  refine level1_ratio hw0 hz0 hz3.symm ?_
  rw [he, hw3, Real.rpow_neg hP0.le]

/-- The linear certificate in the `mrAlpha` form the §8.1 row actually carries. -/
theorem H1door_level1_certificate_L {M : ℕ} (hM : 1 ≤ M) :
    (H1doorL M) ^ 2 * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
        * ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12) 1))
      = (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
          / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
  H1door_level1_identity_L hM (by rw [mrAlpha_door_one]; norm_num)

/-- **G6 AT THE LINEAR ANCHOR — the §8.1 level-1 factor DECAYS in `𝒫₁`.**  The landed
`level1_term_door_decays` at `AdoorL`; the constant `5280` is the `H₁ ≥ 2`-ONLY constant and
does not move with the anchor. -/
theorem level1_term_door_decays_L {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    2 * (calH (H1doorL M) 1 * Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) + 1) * R
        * ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12) 1))
        * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12) 1))
              * Real.exp ((1 - 2 * mrAlpha (1 / 12) 1) / calH (H1doorL M) 1)
            + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12) 1)
                * Real.exp (4 * mrAlpha (1 / 12) 1 / calH (H1doorL M) 1))
      ≤ 5280 * R
          * ((Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
              / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
  have hP64 := calP_door_one_ge_L hM
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hcalH : calH (H1doorL M) 1 = H1doorL M := by
    rw [calH, Nat.cast_one, one_pow, one_mul]
  have hαe : (-(2 * mrAlpha (1 / 12 : ℝ) 1)) = -((1 : ℝ) / 4) := by
    rw [mrAlpha_door_one]; norm_num
  have hα1 : (1 - 2 * mrAlpha (1 / 12 : ℝ) 1) = 3 / 4 := by rw [mrAlpha_door_one]; norm_num
  have hα3 : (4 * mrAlpha (1 / 12 : ℝ) 1) = 1 / 2 := by rw [mrAlpha_door_one]; norm_num
  rw [hcalH, hαe, hα1, hα3, mrAlpha_door_one,
    ← H1door_level1_identity_L (M := M) hM (e := -((1 : ℝ) / 4)) rfl]
  exact level1_shape (H1door_two_L hM) (one_le_log_calQK_door_one_L hM)
    (Real.rpow_pos_of_pos hP0 _) hR

/-- **THE LINEAR WIDTH IS K-INVARIANT** — both of `H1doorL`'s ladder reads are at level 1. -/
lemma H1door_gk_eq_L (K M : ℕ) :
    ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)
        / (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
      = H1doorL M := by
  rw [calP_doorL_one_gk, calQK_gk_one_eq, H1doorL]

/-- `𝒫₁ ≥ 64` at the levered linear door — level-1 transport. -/
lemma calP_door_one_ge_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (64 : ℝ) ≤ ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) := by
  rw [calP_doorL_one_gk]
  exact calP_door_one_ge_L hM

/-- `log 𝒬₁ ≥ 1` at the levered linear door — level-1 transport. -/
lemma one_le_log_calQK_door_one_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) := by
  rw [calQK_gk_one_eq]
  exact one_le_log_calQK_door_one_L hM

/-- **G6 AT THE LEVERED LINEAR DOOR** — every symbol in the §8.1 level-1 factor is level-1,
so the lever leaves the decay certificate untouched. -/
theorem level1_term_door_decays_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    2 * (calH (H1doorL M) 1 * Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ) + 1) * R
        * ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ (-(2 * mrAlpha (1 / 12) 1))
        * (4 * (calH (H1doorL M) 1 / (1 - 2 * mrAlpha (1 / 12) 1))
              * Real.exp ((1 - 2 * mrAlpha (1 / 12) 1) / calH (H1doorL M) 1)
            + 60 * (calH (H1doorL M) 1 / mrAlpha (1 / 12) 1)
                * Real.exp (4 * mrAlpha (1 / 12) 1 / calH (H1doorL M) 1))
      ≤ 5280 * R
          * ((Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
              / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)) := by
  rw [calP_doorL_one_gk, calQK_gk_one_eq]
  exact level1_term_door_decays_L hM hR

/-- **THE LINEAR DOOR'S K-STATION FRAME AT MR'S OWN `H₁`, AT THE G-LEVER**.  The side
condition is the WIDE one (`K ≤ 1.7·10⁸·M`), inherited from
`DoorLinear.calFrameK_satisfiable_doorL_gk`. -/
theorem calFrameK_satisfiable_doorH1_L_gk (K M : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000 * M) :
    CalFrameK (1 / 12) (H1doorL M) (AdoorL M) (s13GK K M) M 2
      (calQK (AdoorL M) (s13GK K M) M 2) := by
  have hF := calFrameK_satisfiable_doorL_gk K M hM hK
  refine ⟨hF.eta_pos, hF.eta_lt, hF.one_le_Jb, hF.one_le_G, hF.one_le_M, hF.G_gateK,
    hF.A_gate_lin, hF.A_gate_logK, hF.A_floor, H1door_two_L hM, ?_, hF.Q_le_Xd⟩
  rw [calP_doorL_one_gk]
  exact H1door_pin_L hM

/-- **The twelve `LevelGates` at the levered linear corrected door family**. -/
theorem levelGates_calibrated_doorH1_L_gk (K M : ℕ) (hM : 1 ≤ M) (hK : K ≤ 170000000 * M) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
        (calH (H1doorL M)) (1 / 12)
        ((calP (AdoorL M) (s13GK K M)) 1) (calQK (AdoorL M) (s13GK K M) M 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_doorH1_L_gk K M hM hK)

/-! ## §2 — `Eq26Compose` at the linear anchor -/

/-- **`A_gate_logK`'s arithmetic at the scaled LINEAR anchor.**  The landed certificate with
`(L+1)` replaced by `MM`, bridged by the single monotone step `hstep`. -/
private lemma gate_log_arith_L {L MM kk a1 a2 a3 l2 : ℝ} (hl2 : 0.6931471803 < l2)
    (hL0' : 0 ≤ L * l2) (hb1 : a1 ≤ (L + 3) * l2) (hb2 : a3 ≤ (2 * L + 52) * l2)
    (hlogk : a2 ≤ kk - 1) (hp2 : 0 ≤ (kk - 1) * l2) (hp3 : 0 ≤ L * l2 * (kk - 1))
    (hkey : 16 * (kk - 1) ≤ 24 * ((kk - 1) * l2))
    (hstep : (L + 1) * kk * l2 ≤ MM * kk * l2) :
    4 * 2 ^ 2 * (a1 + (a2 + a3)) ≤ 1 / 12 / 2 * (68719476736 * MM * kk * l2 - 1) := by
  linarith

/-- `gate_log_arith_L` with the lever's `K log 2` on the left.  The `K`-ceiling is the WIDE
one, `KK ≤ 1.7·10⁸·MM`, which is what the linear re-cut buys. -/
private lemma gate_log_arith_L_gk {L MM kk KK a1 a2 a3 l2 : ℝ} (hl2 : 0.6931471803 < l2)
    (hL0' : 0 ≤ L * l2) (hb1 : a1 ≤ (L + 3) * l2) (hb2 : a3 ≤ (2 * L + 52 + KK) * l2)
    (hKl2 : KK * l2 ≤ 170000000 * (MM * l2))
    (hlogk : a2 ≤ kk - 1) (hp2 : 0 ≤ (kk - 1) * l2) (hp3 : 0 ≤ L * l2 * (kk - 1))
    (hkey : 16 * (kk - 1) ≤ 24 * ((kk - 1) * l2))
    (hstep : (L + 1) * kk * l2 ≤ MM * kk * l2)
    (hstep2 : MM * l2 ≤ MM * kk * l2) :
    4 * 2 ^ 2 * (a1 + (a2 + a3)) ≤ 1 / 12 / 2 * (68719476736 * MM * kk * l2 - 1) := by
  linarith

/-- **The `k`-scaled LINEAR door frame** — `CalFrameK` at the anchor `AdoorL M · k`, for
every `k ≥ 1` and every `M ≥ 1`.  At `k = 1` this IS
`DoorLinear.calFrameK_satisfiable_doorL`. -/
theorem calFrameK_satisfiable_scaled_L {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k) :
    CalFrameK (1 / 12)
      (((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (AdoorL M * k) (3072 * M) M 2 (calQK (AdoorL M * k) (3072 * M) M 2) := by
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL0' : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 := mul_nonneg hL0 hlog2nn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkR
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hLM : (Nat.log 2 M : ℝ) + 1 ≤ (M : ℝ) := by
    have h : Nat.log 2 M < M := Nat.log_lt_self 2 (by omega)
    have h' : (Nat.log 2 M : ℝ) < (M : ℝ) := by exact_mod_cast h
    have hn : (Nat.log 2 M : ℕ) + 1 ≤ M := h
    exact_mod_cast hn
  have hstep : ((Nat.log 2 M : ℝ) + 1) * (k : ℝ) * Real.log 2
      ≤ (M : ℝ) * (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLM (by linarith)) hlog2nn
  have hA24 : (24 : ℕ) ≤ AdoorL M * k :=
    le_trans (le_trans (by norm_num) (AdoorL_ge hM)) (Nat.le_mul_of_pos_right _ (by omega))
  have h64 : (64 : ℕ) ≤ calP (AdoorL M * k) (3072 * M) 1 := by
    have hE : (6 : ℕ) ≤ calE (AdoorL M * k) (3072 * M) 1 := by
      rw [calE_one]; omega
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hcalE2 : calE (AdoorL M * k) (3072 * M) 2 = k * calE (AdoorL M) (3072 * M) 2 := by
    simp only [calE]
    ring
  have hEpos : 0 < calE (AdoorL M) (3072 * M) 2 := by
    rw [calE_doorL_two]
    exact Nat.mul_pos (by norm_num) (Nat.mul_pos hM hM)
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := by omega, one_le_M := hM, G_gateK := by push_cast; linarith,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := hA24,
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · have h4 : ((24 : ℕ) : ℝ) ≤ ((AdoorL M * k : ℕ) : ℝ) := by exact_mod_cast hA24
    push_cast at h4 ⊢
    linarith
  · have hlogsplit : Real.log ((k * calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ)
        = Real.log (k : ℝ) + Real.log ((calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) := by
      have hk0 : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hE0 : ((calE (AdoorL M) (3072 * M) 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hEpos.ne'
      push_cast
      exact Real.log_mul hk0 hE0
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
    have hb1 := log_four_M_door hM
    have hb2 := log_calE_doorL_two hM
    have hp1 : ((k : ℝ) - 1) * 0.6931471803 ≤ ((k : ℝ) - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    have hp2 : (0 : ℝ) ≤ ((k : ℝ) - 1) * Real.log 2 := by nlinarith
    have hp3 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 * ((k : ℝ) - 1) :=
      mul_nonneg hL0' (by linarith)
    have hkey : 16 * ((k : ℝ) - 1) ≤ 24 * (((k : ℝ) - 1) * Real.log 2) := by linarith
    rw [hcalE2, hlogsplit]
    push_cast
    rw [AdoorL_cast]
    exact gate_log_arith_L hl2 hL0' hb1 hb2 hlogk hp2 hp3 hkey hstep
  · calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · have hid : ((((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ))
        = ((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP (AdoorL M * k) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-- **THE `h`-DEPENDENT LINEAR ANCHOR** `A_L(h) := AdoorL M · ⌊L/(M·AdoorL M)⌋`, `M := 8δinv`,
`L := ⌊log₂ h⌋`.  Floor, never ceiling (`Ah_containment_L`), and a multiple of `AdoorL M` so
that the frame rides `calFrameK_satisfiable_scaled_L`. -/
def Ah_L (δinv h : ℕ) : ℕ :=
  AdoorL (8 * δinv) * (Nat.log 2 h / (8 * δinv * AdoorL (8 * δinv)))

/-- `M · A_L(h) ≤ ⌊log₂ h⌋` — the floor-division identity the containment rests on. -/
theorem Ah_mul_le_L (δinv h : ℕ) : 8 * δinv * Ah_L δinv h ≤ Nat.log 2 h := by
  have h1 : 8 * δinv * Ah_L δinv h
      = 8 * δinv * AdoorL (8 * δinv) * (Nat.log 2 h / (8 * δinv * AdoorL (8 * δinv))) := by
    simp only [Ah_L]
    ring
  rw [h1]
  exact Nat.mul_div_le _ _

/-- **`𝒫₁ ≈ h^{δ/8}`, one-sided**, at the linear anchor. -/
theorem Ah_one_sided_L (δinv h : ℕ) (hδ : 1 ≤ δinv) :
    h < 2 ^ (8 * δinv * (Ah_L δinv h + AdoorL (8 * δinv))) := by
  have hBpos : 0 < 8 * δinv * AdoorL (8 * δinv) :=
    Nat.mul_pos (by omega)
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_AdoorL (show 1 ≤ 8 * δinv by omega)))
  have hlt := Nat.lt_mul_div_succ (Nat.log 2 h) hBpos
  have hexp : 8 * δinv * (Ah_L δinv h + AdoorL (8 * δinv))
      = 8 * δinv * AdoorL (8 * δinv) * (Nat.log 2 h / (8 * δinv * AdoorL (8 * δinv)) + 1) := by
    simp only [Ah_L]
    ring
  rw [hexp]
  refine lt_of_lt_of_le (Nat.lt_pow_succ_log_self (b := 2) (by norm_num) h) ?_
  exact Nat.pow_le_pow_right (by norm_num) hlt

/-- **E26-8's containment** `[𝒫₁, 𝒬₁] ⊆ [1, h]` at the `h`-dependent LINEAR anchor. -/
theorem Ah_containment_L (δinv h G : ℕ) (hδ : 1 ≤ δinv) (hh : 1 ≤ h) :
    1 ≤ calP (Ah_L δinv h) G 1
      ∧ calP (Ah_L δinv h) G 1 ≤ calQK (Ah_L δinv h) G (8 * δinv) 1
      ∧ calQK (Ah_L δinv h) G (8 * δinv) 1 ≤ h := by
  refine ⟨Nat.one_le_two_pow, calP_le_calQK (by omega) le_rfl, ?_⟩
  rw [calQK, calE_one]
  calc 2 ^ (1 ^ 2 * (8 * δinv) * Ah_L δinv h) ≤ 2 ^ Nat.log 2 h := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        simpa using Ah_mul_le_L δinv h
    _ ≤ h := Nat.pow_log_le_self 2 (by omega)

/-- **THE FRAME AT THE `h`-DEPENDENT LINEAR ANCHOR** (`calFrameK_satisfiable_Ah_L`). -/
theorem calFrameK_satisfiable_Ah_L (δinv h : ℕ) (hδ : 1 ≤ δinv)
    (hfloor : 8 * δinv * AdoorL (8 * δinv) ≤ Nat.log 2 h) :
    CalFrameK (1 / 12)
      (((calP (Ah_L δinv h) (3072 * (8 * δinv)) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (Ah_L δinv h) (3072 * (8 * δinv)) (8 * δinv) 2
      (calQK (Ah_L δinv h) (3072 * (8 * δinv)) (8 * δinv) 2) := by
  have hBpos : 0 < 8 * δinv * AdoorL (8 * δinv) :=
    Nat.mul_pos (by omega)
      (lt_of_lt_of_le Nat.zero_lt_one (one_le_AdoorL (show 1 ≤ 8 * δinv by omega)))
  have hk1 : 1 ≤ Nat.log 2 h / (8 * δinv * AdoorL (8 * δinv)) :=
    (Nat.one_le_div_iff hBpos).mpr hfloor
  simp only [Ah_L]
  exact calFrameK_satisfiable_scaled_L (by omega) hk1

/-- **The twelve `LevelGates` at the `A_L(h)` family**, free from the frame. -/
theorem levelGates_calibrated_Ah_L (δinv h : ℕ) (hδ : 1 ≤ δinv)
    (hfloor : 8 * δinv * AdoorL (8 * δinv) ≤ Nat.log 2 h) :
    ∀ j ∈ Finset.Icc 2 2,
      LevelGates (calP (Ah_L δinv h) (3072 * (8 * δinv)))
        (calQK (Ah_L δinv h) (3072 * (8 * δinv)) (8 * δinv))
        (calH ((((calP (Ah_L δinv h) (3072 * (8 * δinv)) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))))
        (1 / 12) ((calP (Ah_L δinv h) (3072 * (8 * δinv))) 1)
        (calQK (Ah_L δinv h) (3072 * (8 * δinv)) (8 * δinv) 2) j :=
  levelGates_calibratedK (calFrameK_satisfiable_Ah_L δinv h hδ hfloor)

/-- **The `k`-scaled LINEAR door frame AT THE G-LEVER**, at the WIDE `K`-ceiling. -/
theorem calFrameK_satisfiable_scaled_L_gk (K : ℕ) {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k)
    (hK : K ≤ 170000000 * M) :
    CalFrameK (1 / 12)
      (((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6))
      (AdoorL M * k) (s13GK K M) M 2 (calQK (AdoorL M * k) (s13GK K M) M 2) := by
  have hL0 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) := Nat.cast_nonneg _
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL0' : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 := mul_nonneg hL0 hlog2nn
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hkR
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hKR : (K : ℝ) ≤ 170000000 * (M : ℝ) := by exact_mod_cast hK
  have hKl2 : (K : ℝ) * Real.log 2 ≤ 170000000 * ((M : ℝ) * Real.log 2) := by
    have := mul_le_mul_of_nonneg_right hKR hlog2nn
    linarith [this]
  have hLM : (Nat.log 2 M : ℝ) + 1 ≤ (M : ℝ) := by
    have h : Nat.log 2 M < M := Nat.log_lt_self 2 (by omega)
    have hn : (Nat.log 2 M : ℕ) + 1 ≤ M := h
    exact_mod_cast hn
  have hstep : ((Nat.log 2 M : ℝ) + 1) * (k : ℝ) * Real.log 2
      ≤ (M : ℝ) * (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLM (by linarith)) hlog2nn
  have hstep2 : (M : ℝ) * Real.log 2 ≤ (M : ℝ) * (k : ℝ) * Real.log 2 := by
    have h1 : (M : ℝ) ≤ (M : ℝ) * (k : ℝ) := le_mul_of_one_le_right (by linarith) hkR
    exact mul_le_mul_of_nonneg_right h1 hlog2nn
  have hA24 : (24 : ℕ) ≤ AdoorL M * k :=
    le_trans (le_trans (by norm_num) (AdoorL_ge hM)) (Nat.le_mul_of_pos_right _ (by omega))
  have h64 : (64 : ℕ) ≤ calP (AdoorL M * k) (s13GK K M) 1 := by
    have hE : (6 : ℕ) ≤ calE (AdoorL M * k) (s13GK K M) 1 := by
      rw [calE_gk_one]; omega
    have h6 : (64 : ℕ) = 2 ^ 6 := by norm_num
    rw [calP, h6]
    exact Nat.pow_le_pow_right (by norm_num) hE
  have h64R : (64 : ℝ) ≤ ((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) := by exact_mod_cast h64
  have hP1pos : (0 : ℝ) < ((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) := by linarith
  have hcalE2 : calE (AdoorL M * k) (s13GK K M) 2 = k * calE (AdoorL M) (s13GK K M) 2 := by
    simp only [calE]
    ring
  have hEpos : 0 < calE (AdoorL M) (s13GK K M) 2 := by
    rw [calE_doorL_two_gk]
    exact Nat.mul_pos (Nat.two_pow_pos K) (Nat.mul_pos (by norm_num) (Nat.mul_pos hM hM))
  have hGle : (3072 : ℝ) * (M : ℝ) ≤ ((s13GK K M : ℕ) : ℝ) := by
    have h : 3072 * M ≤ s13GK K M := le_s13GK K M
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this
    linarith
  refine
    { eta_pos := by norm_num, eta_lt := by norm_num, one_le_Jb := by norm_num,
      one_le_G := one_le_s13GK K hM, one_le_M := hM, G_gateK := by push_cast; linarith,
      A_gate_lin := ?_, A_gate_logK := ?_, A_floor := hA24,
      H1_two := ?_, H1_pin := ?_, Q_le_Xd := le_rfl }
  · have h4 : ((24 : ℕ) : ℝ) ≤ ((AdoorL M * k : ℕ) : ℝ) := by exact_mod_cast hA24
    push_cast at h4 ⊢
    linarith
  · have hlogsplit : Real.log ((k * calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ)
        = Real.log (k : ℝ) + Real.log ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) := by
      have hk0 : ((k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hE0 : ((calE (AdoorL M) (s13GK K M) 2 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hEpos.ne'
      push_cast
      exact Real.log_mul hk0 hE0
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) - 1 := Real.log_le_sub_one_of_pos hkpos
    have hb1 := log_four_M_door hM
    have hb2 := log_calE_doorL_two_gk K hM
    have hp1 : ((k : ℝ) - 1) * 0.6931471803 ≤ ((k : ℝ) - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le (by linarith)
    have hp2 : (0 : ℝ) ≤ ((k : ℝ) - 1) * Real.log 2 := by nlinarith
    have hp3 : (0 : ℝ) ≤ (Nat.log 2 M : ℝ) * Real.log 2 * ((k : ℝ) - 1) :=
      mul_nonneg hL0' (by linarith)
    have hkey : 16 * ((k : ℝ) - 1) ≤ 24 * (((k : ℝ) - 1) * Real.log 2) := by linarith
    rw [hcalE2, hlogsplit]
    push_cast
    rw [AdoorL_cast]
    exact gate_log_arith_L_gk hl2 hL0' hb1 hb2 hKl2 hlogk hp2 hp3 hkey hstep hstep2
  · calc (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, ← Real.rpow_natCast 2 6,
            ← Real.rpow_mul (by norm_num)]
          norm_num
      _ ≤ ((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6) :=
          Real.rpow_le_rpow (by norm_num) h64R (by norm_num)
  · have hid : ((((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) ^ (3 : ℕ))
        = ((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast (((calP (AdoorL M * k) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 6)) 3,
        ← Real.rpow_mul hP1pos.le, show (1 : ℝ) / 6 * ((3 : ℕ) : ℝ) = (1 : ℝ) / 2 by norm_num]
    rw [hid]

/-! ## §3 — `M4Residue` at the linear anchor -/

/-- `𝒫₁ = 2^{A_L}` at the linear door. -/
theorem calP_door_one_eq_L (M : ℕ) : calP (AdoorL M) (3072 * M) 1 = 2 ^ AdoorL M := by
  rw [calP, calE_one]

/-- **`𝒫₁ ≥ 2^{262144}`, symbolically**, at the linear anchor.  `AdoorL M = 2^36·M ≥ 2^18`
needs `1 ≤ M` — the one hypothesis the re-cut adds to the dilation gate's chain. -/
theorem two_pow_le_calP_door_one_L {M : ℕ} (hM : 1 ≤ M) :
    (2 : ℝ) ^ (262144 : ℕ) ≤ ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
  have hE : (262144 : ℕ) ≤ AdoorL M := by
    have h := AdoorL_ge_old hM
    rwa [show (2 : ℕ) ^ 18 = 262144 by norm_num] at h
  have hcast : ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) = (2 : ℝ) ^ AdoorL M := by
    rw [calP_door_one_eq_L]
    push_cast
    ring
  rw [hcast]
  exact pow_le_pow_right₀ (by norm_num) hE

/-- **The `W < 𝒫₁` arm** at the linear anchor. -/
theorem lt_calP_door_one_L {M : ℕ} (hM : 1 ≤ M) {W : ℝ} (hW : W < (2 : ℝ) ^ (262144 : ℕ)) :
    W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) :=
  lt_of_lt_of_le hW (two_pow_le_calP_door_one_L hM)

/-- **The `d₀ ≤ q ≤ W < 𝒫₁` chain**, as a ℕ-inequality, at the linear anchor. -/
theorem d_lt_calP_door_one_L {M d q : ℕ} (hM : 1 ≤ M) {W : ℝ} (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ W) (hW : W < (2 : ℝ) ^ (262144 : ℕ)) :
    d < calP (AdoorL M) (3072 * M) 1 := by
  have hd : (d : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact lt_of_le_of_lt (le_trans hdq' hqW) (lt_calP_door_one_L hM hW)
  exact_mod_cast hd

/-- **THE GATE, assembled**, at the linear anchor. -/
theorem door_dilation_gate_L {M d q : ℕ} (hM : 1 ≤ M) {H : ℝ} (h1 : 1 ≤ Real.log H)
    (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    d < calP (AdoorL M) (3072 * M) 1 :=
  d_lt_calP_door_one_L hM hdq hqW (logH_pow_twelve_lt h1 h2)

/-- **THE GATE, `M`-RELATIVE**, at the linear anchor: the ceiling is the door's OWN bottom
block `𝒫₁ = 2^{AdoorL M}`, so no `log H` cap is needed and no `1 ≤ M` either. -/
theorem door_dilation_gate'_L {M d q : ℕ} {W : ℝ} (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < (2 : ℝ) ^ AdoorL M) :
    d < calP (AdoorL M) (3072 * M) 1 := by
  have hcast : ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) = (2 : ℝ) ^ AdoorL M := by
    rw [calP_door_one_eq_L]
    push_cast
    ring
  have hd : (d : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    rw [hcast]
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact lt_of_le_of_lt (le_trans hdq' hqW) hW
  exact_mod_cast hd

/-- The same read at `𝒫₁` itself, at the linear anchor. -/
theorem door_dilation_gate_calP_L {M d q : ℕ} {W : ℝ} (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)) :
    d < calP (AdoorL M) (3072 * M) 1 := by
  have hd : (d : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
    have hdq' : (d : ℝ) ≤ (q : ℝ) := by exact_mod_cast hdq
    exact lt_of_le_of_lt (le_trans hdq' hqW) hW
  exact_mod_cast hd

/-- The linear door `𝒫`-ladder is monotone. -/
theorem calP_door_mono_L {M : ℕ} (hM : 1 ≤ M) : Monotone (calP (AdoorL M) (3072 * M)) := by
  intro i j hij
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact calE_mono (AdoorL M) (by omega) hij

/-- **THE ROW'S CAPSTONE — `𝒮`-transfer at the LINEAR door inhabitant.** -/
theorem memS_dilate_door_L {M J d q m : ℕ} {H : ℝ} (hM : 1 ≤ M) (h1 : 1 ≤ Real.log H)
    (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) (hd : d ≠ 0) (hm : m ≠ 0) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    MemS (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) J (d * m)
      ↔ MemS (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) J m :=
  memS_dilate_of_lt_bot (calP_door_mono_L hM) hd hm
    (door_dilation_gate_L (M := M) hM h1 h2 hdq hqW)

/-- **The residue split at the linear door**, the form M4-3/M4-4 consume. -/
theorem residue_split_dilate_door_L {g : ℕ → ℂ} (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {b q J M : ℕ} {A : Finset ℕ} {H : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (h1 : 1 ≤ Real.log H) (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ))
    (hA : ∀ n ∈ A, Nat.ModEq q n b) (h0 : (0 : ℕ) ∉ A)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    ∑ n ∈ A.filter
        (fun n => MemS (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) J n), g n
      = g (Nat.gcd b q)
        * ∑ m ∈ (A.image (fun n => n / Nat.gcd b q)).filter
            (fun m =>
              MemS (calP (AdoorL M) (3072 * M)) (calQK (AdoorL M) (3072 * M) M) J m), g m := by
  refine residue_split_dilate hg hq hA h0 (fun j hj => ?_)
  have hgate : Nat.gcd b q < calP (AdoorL M) (3072 * M) 1 :=
    door_dilation_gate_L (M := M) hM h1 h2 (Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)) hqW
  exact lt_of_lt_of_le hgate (calP_door_mono_L hM (Finset.mem_Icc.mp hj).1)

/-- The bottom-block gate at the levered linear door (level 1 is K-invariant). -/
theorem door_dilation_gate_L_gk (K : ℕ) {M d q : ℕ} (hM : 1 ≤ M) {H : ℝ}
    (h1 : 1 ≤ Real.log H) (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) (hdq : d ≤ q)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    d < calP (AdoorL M) (s13GK K M) 1 := by
  rw [calP_doorL_one_gk]
  exact door_dilation_gate_L hM h1 h2 hdq hqW

/-- The `M`-relative gate at the levered linear door. -/
theorem door_dilation_gate'_L_gk (K : ℕ) {M d q : ℕ} {W : ℝ} (hdq : d ≤ q) (hqW : (q : ℝ) ≤ W)
    (hW : W < (2 : ℝ) ^ AdoorL M) :
    d < calP (AdoorL M) (s13GK K M) 1 := by
  rw [calP_doorL_one_gk]
  exact door_dilation_gate'_L hdq hqW hW

/-- The linear door `𝒫`-ladder at the lever is monotone. -/
theorem calP_door_mono_L_gk (K : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    Monotone (calP (AdoorL M) (s13GK K M)) := by
  intro i j hij
  refine Nat.pow_le_pow_right (by norm_num) ?_
  exact calE_mono (AdoorL M) (one_le_s13GK K hM) hij

/-- **THE ROW'S CAPSTONE AT THE G-LEVER**, at the linear door. -/
theorem memS_dilate_door_L_gk (K : ℕ) {M J d q m : ℕ} {H : ℝ} (hM : 1 ≤ M)
    (h1 : 1 ≤ Real.log H) (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ)) (hd : d ≠ 0) (hm : m ≠ 0)
    (hdq : d ≤ q) (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    MemS (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) J (d * m)
      ↔ MemS (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) J m :=
  memS_dilate_of_lt_bot (calP_door_mono_L_gk K hM) hd hm
    (door_dilation_gate_L_gk K (M := M) hM h1 h2 hdq hqW)

/-- **The residue split at the levered linear door**, the form M4-3/M4-4 consume. -/
theorem residue_split_dilate_door_L_gk (K : ℕ) {g : ℕ → ℂ}
    (hg : ∀ a b : ℕ, g (a * b) = g a * g b)
    {b q J M : ℕ} {A : Finset ℕ} {H : ℝ} (hM : 1 ≤ M) (hq : 0 < q)
    (h1 : 1 ≤ Real.log H) (h2 : Real.log H ≤ (2 : ℝ) ^ (21845 : ℕ))
    (hA : ∀ n ∈ A, Nat.ModEq q n b) (h0 : (0 : ℕ) ∉ A)
    (hqW : (q : ℝ) ≤ Real.log H ^ (12 : ℕ)) :
    ∑ n ∈ A.filter
        (fun n => MemS (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) J n), g n
      = g (Nat.gcd b q)
        * ∑ m ∈ (A.image (fun n => n / Nat.gcd b q)).filter
            (fun m =>
              MemS (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M) J m), g m := by
  refine residue_split_dilate hg hq hA h0 (fun j hj => ?_)
  have hgate : Nat.gcd b q < calP (AdoorL M) (s13GK K M) 1 :=
    door_dilation_gate_L_gk K (M := M) hM h1 h2 (Nat.le_of_dvd hq (Nat.gcd_dvd_right b q)) hqW
  exact lt_of_lt_of_le hgate (calP_door_mono_L_gk K hM (Finset.mem_Icc.mp hj).1)

end Salt.MR

end
