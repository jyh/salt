/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ArithPageLinear

/-!
# `S15SelLinear` — THE `M`-SELECTION REGISTER AT THE LINEAR DOOR, AND ITS FLAT WITNESS

⟦LINEAR-PAGE, the register half⟧  `S15Compose` §10's `S15Sel''` is the eleven-line register
the capstone fires on.  Four of its lines read the door — `gRows`, `half`, `anchor`, `lvl`
(plus `x0M` and `blk` through `doorRowFloor`/`s13BlockExp`) — and at the LANDED anchor
`Adoor M = 2^36·(⌊log₂M⌋+1)` those four are mutually **unsatisfiable at the flat width**:
`half` caps `⌊log₂M⌋ + 1` at `≈ 1.4427·λ₋` while `anchor` demands
`3.9·10⁹·(⌊log₂M⌋+1) ≥ 14·λ₊`, and the flat road's `λ₊` is `e^{λ₋/2}` (⟦H1-ANCHOR⟧ `p3`,
kernelized: no fixed point at any `λ₋ ≥ 50`; `p5`: no numeral repairs it).

This file states the register at `AdoorL M = 2^36·M` and **discharges all eleven lines at the
flat road's own design point**, symbolically in the design constant `A`:

```
λ₋ = 3.2·A        (the flat design law, `ChowlaRegimeFlat.hflat`)
λ₊ ≤ e^{λ₋/2}     (the flat width export, `TowerFlatExport`)
M  = ⌊e^{λ₋/2}/310301⌋      (`flatDoorM A` — the largest `M` the `half` line admits)
```

⟦THE ACCOUNTING, LINE BY LINE, AT THAT POINT⟧ (`A ≥ 26`, so `e^{1.6A} ≥ 10^{17}`)

| line | spends | against | margin |
|---|---|---|---|
| `half` | `0.49959·e^{3.2A} + 108` | `e^{3.2A}/2` | `8.3·10^{-4}` relative |
| `gRows` | `242·e^{1.6A}` | `2.2146·10⁵·e^{1.6A}` | `915×` |
| `anchor` | `14·e^{1.6A} + 69` | `1.2569·10⁴·e^{1.6A}` | `898×` |
| `gP1` | `14·e^{1.6A} + 79` | `1.535·10⁵·e^{1.6A}` | `10⁴×` |
| `lvl` | `14·e^{1.6A} + 62 + ⅔·log e^{1.6A}` | `1.279·10⁴·e^{1.6A}` | `913×` |
| `blk` | `≤ 19·e^{9.6A}` | `2^{-16}·e^{e^{3.2A}}` | astronomic |
| `x0M` | `e^{3.2A}/10` | `0.1236·e^{3.2A}` | `1.24×` |

The `half` line is the binding one — as it must be, since `M` is chosen AT its ceiling — and
the `anchor`/`gRows`/`lvl` triple, which at the landed door misses by a factor `~2·10⁶` at
this same point (⟦H1-ANCHOR⟧ `p8`), now clears with three orders to spare **uniformly in
`A`** (⟦H1-ANCHOR⟧ `p9`).  Nothing here caps `A` from above: that is the whole content of
⟦H2-CONSTANTS⟧'s synthesis — the `86.65` window was a frozen-witness artifact, and the flat
road pins its own floor.

⟦WHERE THIS STOPS⟧ at the register.  The compose (`logChowla2_conditional_sharp2` and its
levered/flat descendants re-fired on `S15Sel''_L`) is the next wave; this file's job is to
prove the register HOSTS the flat width, which is what ⟦H1-ANCHOR⟧'s repair is.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — the block-scale exponent at the linear door -/

/-- `S13FramesA.s13BlockExp` at the linear anchor.  The third summand is quadratic in
`A·G·M`, so the re-cut takes it from `(2^36·log₂M·3072M·M)²` to `(3·2^46·M³)²`. -/
def s13BlockExp_L (M : ℕ) : ℕ :=
  14427 + (64 + 8 * (Nat.log 2 M + 1)) + 400 * (AdoorL M * (3072 * M) * M) ^ 2

/-- `S13FramesA.s13BlockExp_gk` at the linear anchor. -/
def s13BlockExp_L_gk (K M : ℕ) : ℕ :=
  14427 + (64 + 8 * (Nat.log 2 M + 1)) + 400 * (AdoorL M * s13GK K M * M) ^ 2

/-- The block exponent's head, in closed form: `400·(A_L·3072M·M)² = 3600·2^{92}·M⁶`. -/
theorem s13BlockExp_L_head (M : ℕ) :
    400 * (AdoorL M * (3072 * M) * M) ^ 2 = 3600 * 2 ^ 92 * M ^ 6 := by
  simp only [AdoorL]
  ring

/-- **THE BLOCK EXPONENT'S SIZE** — `s13BlockExp_L M ≤ 2^{104}·M⁶` for every `M ≥ 1`
(`3600 ≤ 2^{12}`, and the two `G`-free summands hide inside the remaining `496·2^{92}`). -/
theorem s13BlockExp_L_le {M : ℕ} (hM : 1 ≤ M) : s13BlockExp_L M ≤ 2 ^ 104 * M ^ 6 := by
  have hlog : Nat.log 2 M ≤ M := Nat.log_le_self 2 M
  have h6 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hM6 : M ≤ M ^ 6 := Nat.le_self_pow (by norm_num) M
  have hhead : 14427 + (64 + 8 * (Nat.log 2 M + 1)) ≤ 496 * 2 ^ 92 * M ^ 6 := by
    have h1 : 14427 + (64 + 8 * (Nat.log 2 M + 1)) ≤ 14507 * M ^ 6 := by
      have : 8 * (Nat.log 2 M + 1) ≤ 8 * M ^ 6 + 8 * M ^ 6 := by omega
      nlinarith [h6, hM6, hlog]
    exact le_trans h1 (Nat.mul_le_mul_right _ (by norm_num))
  have hsplit : (2 : ℕ) ^ 104 * M ^ 6 = 3600 * 2 ^ 92 * M ^ 6 + 496 * 2 ^ 92 * M ^ 6 := by
    ring
  rw [s13BlockExp_L, s13BlockExp_L_head, hsplit]
  omega

/-! ## §2 — ⟦THE `M`-SELECTION REGISTER AT THE LINEAR DOOR⟧ -/

/-- **⟦THE `M`-SELECTION REGISTER, AT THE LINEAR DOOR⟧**
(`S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M`) — `S15Compose.S15Sel''` with every door read re-cut to
`AdoorL M = 2^36·M`: `gRows`/`gP1`/`lvl` at `A_L(M)`, `half`/`x0M` at
`doorRowFloorL M = 2^36·M²`, `blk` at `s13BlockExp_L M`, and — the repair itself — `anchor`
at `3.9·10⁹·M` in place of `3.9·10⁹·(⌊log₂M⌋+1)`.  The other five lines are `S15Sel''`'s
byte for byte. -/
structure S15Sel''_L (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) (M : ℕ) : Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 0⟧ the graded twin's own `ℕ`-floor. -/
  mfloor : Mfl ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'.bfloor` = `M4DoorGates.hMδ`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'.gRows`, at the LINEAR anchor. -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦RESTORED⟧ the opaque threshold at the LINEAR row floor. -/
  x0M : x₀ ≤ 2 ^ doorRowFloorL M
  /-- ⟦`M`-UPPER 1⟧ `MSelect'.blockCeil` AND ⟦F3⟧'s `block`, at the LINEAR block exponent. -/
  blk : ((s13BlockExp_L M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the LINEAR half-window floor. -/
  half : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- the clearing charge — `ρ ≥ e^{−10^{14}}`. -/
  rho : -Real.log ρ ≤ 100000000000000
  /-- ⟦THE REPAIR⟧ the `ρ`-frame's ⟦C1⟧ anchor at `DoorArithFrameRho_L.anchor`'s OWN right
  side `3.9·10⁹·M` — LINEAR in the door's parameter, hence exponential in `λ₋`. -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * (M : ℝ)
  /-- the `𝒯`-leg budget at `constPool`, at the LINEAR anchor. -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `level1` budget — the const-pool line, at the LINEAR anchor. -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2

/-- `S15Sel''_L` at the lever.  As at the landed anchor exactly two lines move — `blk` at
`s13BlockExp_L_gk K M` and `lvl`'s `𝒬₁` at `s13GK K M` (a level-1 read, hence in fact
`K`-invariant, `calQK_gk_one_eq`) — and the `anchor` line is `G`-free. -/
structure S15Sel''_L_gk (K : ℕ) (Cg δ₀ Ct ρ : ℝ) (x₀ Mfl : ℕ) (R : ChowlaRegime) (M : ℕ) :
    Prop where
  /-- the door's parameter is a modulus. -/
  hM : 1 ≤ M
  /-- ⟦`M`-LOWER 0⟧ the graded twin's own `ℕ`-floor. -/
  mfloor : Mfl ≤ M
  /-- ⟦`M`-LOWER 1⟧ `MSelect'_gk K.bfloor`. -/
  bfloor : 24 * Cg / δ₀ ≤ (M : ℝ)
  /-- ⟦`M`-LOWER 2⟧ `MSelect'_gk K.gRows`, at the LINEAR anchor. -/
  gRows : 242 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ ((AdoorL M : ℕ) : ℝ)
  /-- ⟦RESTORED⟧ the opaque threshold at the LINEAR row floor. -/
  x0M : x₀ ≤ 2 ^ doorRowFloorL M
  /-- ⟦`M`-UPPER 1⟧ the block ceiling at the levered LINEAR block exponent. -/
  blk : ((s13BlockExp_L_gk K M : ℕ) : ℝ) + 1 + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)
  /-- ⟦`M`-UPPER 2⟧ THE WINDOW GATE at the LINEAR half-window floor. -/
  half : (7 / 10 : ℝ) * ((doorRowFloorL M : ℕ) : ℝ) + 3 * Real.log (1 / ρ)
    ≤ Real.log ((R.Hlo : ℕ) : ℝ) / 2
  /-- the clearing charge. -/
  rho : -Real.log ρ ≤ 100000000000000
  /-- ⟦THE REPAIR⟧ the ⟦C1⟧ anchor at `3.9·10⁹·M`. -/
  anchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * (M : ℝ)
  /-- the `𝒯`-leg budget at `constPool`, at the LINEAR anchor. -/
  gP1 : 29 + Real.log Ct + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
    ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ
  /-- the `level1` budget at the LINEAR anchor. -/
  lvl : 26 + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ))
      + (-Real.log ρ)
    ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2

/-- `S15Sel''.head` at the linear door. -/
theorem S15Sel''_L.head {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp_L M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp_L M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-- `S15Sel''_L.head` at the lever. -/
theorem S15Sel''_L_gk.head {K : ℕ} {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime} {M : ℕ}
    (hsel : S15Sel''_L_gk K Cg δ₀ Ct ρ x₀ Mfl R M)
    (hΛ : 0 ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) :
    s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ + 1 := by
  have h := hsel.blk
  have hR : ((s13BlockExp_L_gk K M : ℕ) : ℝ) ≤ ((4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    push_cast; linarith
  have : s13BlockExp_L_gk K M ≤ 4 * ⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ := by exact_mod_cast hR
  omega

/-! ## §3 — THE FLAT DESIGN POINT

`M := ⌊e^{λ₋/2}/310301⌋` at `λ₋ = 3.2·A` — the LARGEST modulus the `half` line admits at the
linear door, because `0.7·2^36·M² ≤ e^{λ₋}/2` reads `M ≤ e^{λ₋/2}/310300.6…`.  Choosing `M`
there is what makes every `M`-LOWER line clear at once: at the landed door the same choice is
unavailable, since `half` bounds `⌊log₂M⌋` rather than `M`. -/

/-- **THE FLAT DESIGN POINT'S DOOR MODULUS** `M(A) = ⌊e^{1.6A}/310301⌋`. -/
def flatDoorM (A : ℝ) : ℕ := ⌊Real.exp (3.2 * A / 2) / 310301⌋₊

/-- `e^{1.6A} ≥ 10^{17}` at the flat design floor `A ≥ 26` (`e^{41.6} ≥ 2.7^{41}`). -/
theorem flat_exp_half_ge {A : ℝ} (hA : 26 ≤ A) : (10 : ℝ) ^ 17 ≤ Real.exp (3.2 * A / 2) := by
  have he : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hp : (2.7 : ℝ) ^ (41 : ℕ) ≤ (Real.exp 1) ^ (41 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) he.le 41
  have hE : (Real.exp 1) ^ (41 : ℕ) = Real.exp 41 := by rw [← Real.exp_nat_mul]; norm_num
  have hn : (10 : ℝ) ^ 17 ≤ (2.7 : ℝ) ^ (41 : ℕ) := by norm_num
  have hmono : Real.exp 41 ≤ Real.exp (3.2 * A / 2) := Real.exp_le_exp.mpr (by linarith)
  rw [hE] at hp
  linarith

/-- `e^{3.2A} = (e^{1.6A})²` — the design point's two scales. -/
theorem flat_exp_sq (A : ℝ) : Real.exp (3.2 * A / 2) ^ 2 = Real.exp (3.2 * A) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- `y⁴/256 ≤ e^{y}` for `y ≥ 0` (`USetResiduals.exp_ge_quartic` in the `/4`-shape).  The
`blk` line's only analytic input: it converts the doubly-exponential `H₊` into a polynomial
comparison. -/
theorem flat_exp_ge_quartic {y : ℝ} (hy : 0 ≤ y) : y ^ 4 / 256 ≤ Real.exp y := by
  have h := exp_ge_quartic hy
  have hid : (y / 4) ^ (4 : ℕ) = y ^ 4 / 256 := by ring
  rw [hid] at h
  exact h

theorem flatDoorM_le (A : ℝ) : ((flatDoorM A : ℕ) : ℝ) ≤ Real.exp (3.2 * A / 2) / 310301 :=
  Nat.floor_le (by positivity)

theorem flatDoorM_ge (A : ℝ) :
    Real.exp (3.2 * A / 2) / 310301 - 1 ≤ ((flatDoorM A : ℕ) : ℝ) := by
  have := Nat.lt_floor_add_one (Real.exp (3.2 * A / 2) / 310301)
  simp only [flatDoorM]
  linarith

theorem flatDoorM_one_le {A : ℝ} (hA : 26 ≤ A) : 1 ≤ flatDoorM A := by
  refine Nat.le_floor ?_
  have h := flat_exp_half_ge hA
  rw [Nat.cast_one, le_div_iff₀ (by norm_num)]
  linarith

/-! ## §4 — ⟦THE ACCEPTANCE⟧ THE REGISTER LIVES AT THE FLAT WIDTH -/

set_option maxHeartbeats 1600000 in
-- eleven register lines at a SYMBOLIC design point: `blk` alone carries a `y⁴`-vs-`e^y`
-- comparison at `y = e^{3.2A}` and `x0M` an `exp∘exp` chain, as in the landed `M = 2^355`
-- witness; the default budget is exhausted well before `lvl`
/-- **⟦THE REGISTER AT THE FLAT DESIGN POINT⟧** (`s15_sel''_L_witness_flat`).

Every one of `S15Sel''_L`'s eleven lines, discharged at the FLAT road's own design point —
`λ₋ = 3.2·A`, `λ₊ ≤ e^{λ₋/2}`, `M = ⌊e^{λ₋/2}/310301⌋` — **symbolically in `A ≥ 26`**.  This
is ⟦H1-ANCHOR⟧'s repair, kernelized: the four door lines that are jointly unsatisfiable at the
landed anchor (`p3`) all clear at the linear one, with `~900×` on `anchor`/`gRows`/`lvl` and
`1.24×` on `x0M`, UNIFORMLY IN `A` (`p7`, `p9`).

⟦THE THREE REGIME INPUTS⟧ `hlo` is the flat DESIGN LAW `3.2·A ≤ λ₋` read as
`log H₋ ≥ e^{3.2A}` (`ChowlaRegimeFlat.hflat`); `hhi` is the flat WIDTH EXPORT
`λ₊ ≤ e^{λ₋/2}` at that point (`TowerFlatExport`); `heps` is the landed witness's own
`ε ≥ 2^{-9}`.

⟦THE ONE UNDISCHARGEABLE HYPOTHESIS⟧ `hx0win`, exactly as in the landed witness: `x₀` is
Siegel-ineffective, so no theorem places it in any window.  Here the window is
`x₀ ≤ e^{e^{3.2A}/10}` against the row floor's own `e^{0.1236·e^{3.2A}}`.

⟦WHAT DOES **NOT** APPEAR⟧ any upper bound on `A`.  Nothing in the register caps the design
constant — ⟦H2-CONSTANTS⟧'s synthesis, kernelized. -/
theorem s15_sel''_L_witness_flat {A : ℝ} (hA : 26 ≤ A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 10 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 20)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 20)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ Real.exp (3.2 * A / 2)) :
    S15Sel''_L Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R (flatDoorM A) := by
  set E : ℝ := Real.exp (3.2 * A / 2) with hEdef
  set Mr : ℝ := ((flatDoorM A : ℕ) : ℝ) with hMrdef
  have hE17 : (10 : ℝ) ^ 17 ≤ E := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < E := by positivity
  have hY : E ^ 2 = Real.exp (3.2 * A) := flat_exp_sq A
  have hMle : Mr ≤ E / 310301 := flatDoorM_le A
  have hMge : E / 310301 - 1 ≤ Mr := flatDoorM_ge A
  have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
  have hM1 : (1 : ℝ) ≤ Mr := by rw [hMrdef]; exact_mod_cast hM1N
  have hM0 : (0 : ℝ) ≤ Mr := by linarith
  have hE1 : (1 : ℝ) ≤ E := by linarith [hE17]
  have hE6 : E ≤ E ^ (6 : ℕ) := le_self_pow₀ hE1 (by norm_num)
  have hE61 : (1 : ℝ) ≤ E ^ (6 : ℕ) := one_le_pow₀ hE1
  have hE2 : (10 : ℝ) ^ 34 ≤ E ^ 2 := by nlinarith [hE17, hE0]
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hρlog : -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) ≤ 36 :=
    s15w_neglog_rho_le hδ hK hδb hKb
  have hinv : Real.log (1 / doorRhoOfDelta (s12DeltaSock δ₀ K))
      = -Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by rw [one_div, Real.log_inv]
  have hAd : ((AdoorL (flatDoorM A) : ℕ) : ℝ) = 68719476736 * Mr := AdoorL_cast _
  have hrow : ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) = 68719476736 * Mr ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  -- ⟦the anchor/`gRows` scale: `2^36·M ≥ 221460·E − 6.9·10^{10}` (`2^36/310301 = 221460.7`)⟧
  have hAdlo : 221460 * E - 68719476737 ≤ 68719476736 * Mr := by linarith [hMge]
  -- ⟦the `A_L(M)·log 2` scale, once: `221460·0.69314718 = 153483.9`⟧
  have hAdlog : 153000 * E ≤ 68719476736 * Mr * Real.log 2 := by
    have hpos : (0 : ℝ) ≤ 221460 * E - 68719476737 := by linarith [hE17]
    have h1 : (221460 * E - 68719476737) * Real.log 2 ≤ 68719476736 * Mr * Real.log 2 :=
      mul_le_mul_of_nonneg_right hAdlo (by linarith)
    nlinarith [hpos, hlog2lo, hE17]
  refine
    { hM := hM1N
      mfloor := hMfl
      bfloor := hbfl
      gRows := ?_
      x0M := ?_
      blk := ?_
      half := ?_
      rho := ?_
      anchor := ?_
      gP1 := ?_
      lvl := ?_ }
  · -- ⟦`M`-LOWER 2⟧ `242·λ₊ ≤ A_L(M)`: `242·E` against `2.2146·10⁵·E`
    rw [hAd]
    linarith [hhi, hAdlo, hE17]
  · -- ⟦RESTORED⟧ `x₀ ≤ 2^{doorRowFloorL M}`, through `2^36·M²·log 2 ≥ 0.1236·E²`
    have hMhalf : E / 620602 ≤ Mr := by linarith [hMge, hE17]
    have hsq : (E / 620602) ^ 2 ≤ Mr ^ 2 := by
      have h1 : (0 : ℝ) ≤ Mr - E / 620602 := by linarith
      have h2 : (0 : ℝ) ≤ Mr + E / 620602 := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hkey : Real.exp (3.2 * A) / 10
        ≤ ((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2 := by
      rw [hrow, ← hY]
      have hE2pos : (0 : ℝ) ≤ E ^ 2 := sq_nonneg E
      have hl2 : (0 : ℝ) ≤ Real.log 2 := by linarith
      have hd : (0 : ℝ) ≤ Mr ^ 2 - (E / 620602) ^ 2 := by linarith [hsq]
      have hstep : (68719476736 : ℝ) * (E / 620602) ^ 2 * Real.log 2
          ≤ 68719476736 * Mr ^ 2 * Real.log 2 := by nlinarith [mul_nonneg hl2 hd]
      have hfin : E ^ 2 / 10 ≤ 68719476736 * (E / 620602) ^ 2 * Real.log 2 := by
        nlinarith [mul_nonneg hE2pos (show (0 : ℝ) ≤ Real.log 2 - 0.6931471803 by linarith)]
      linarith [hstep, hfin]
    have hpowid : ((2 : ℝ) ^ (doorRowFloorL (flatDoorM A) : ℕ))
        = Real.exp (((doorRowFloorL (flatDoorM A) : ℕ) : ℝ) * Real.log 2) := by
      rw [← Real.log_pow]
      exact (Real.exp_log (by positivity)).symm
    have hfin : (x₀ : ℝ) ≤ (2 : ℝ) ^ (doorRowFloorL (flatDoorM A) : ℕ) := by
      rw [hpowid]
      exact le_trans hx0win (Real.exp_le_exp.mpr hkey)
    exact_mod_cast hfin
  · -- ⟦`M`-UPPER 1⟧ the block ceiling: `≤ 19·E⁶` against `2^{-16}·e^{E²}`
    have hbeN : s13BlockExp_L (flatDoorM A) ≤ 2 ^ 104 * (flatDoorM A) ^ 6 :=
      s13BlockExp_L_le hM1N
    have hbeR : ((s13BlockExp_L (flatDoorM A) : ℕ) : ℝ) ≤ 2 ^ 104 * Mr ^ 6 := by
      have h : ((s13BlockExp_L (flatDoorM A) : ℕ) : ℝ)
          ≤ ((2 ^ 104 * (flatDoorM A) ^ 6 : ℕ) : ℝ) := by exact_mod_cast hbeN
      push_cast at h
      linarith
    -- `M·2^18 ≤ E`, so `M⁶·2^108 ≤ E⁶`
    have h218 : ((2 : ℝ) ^ (18 : ℕ)) = 262144 := by norm_num
    have hM18 : Mr * 2 ^ (18 : ℕ) ≤ E := by
      have h : Mr * 310301 ≤ E := by
        have hd := hMle
        rw [le_div_iff₀ (by norm_num)] at hd
        linarith
      rw [h218]
      linarith [h, hM0]
    have hM18' : (Mr * 2 ^ (18 : ℕ)) ^ (6 : ℕ) ≤ E ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hM18 6
    have hid6 : (Mr * 2 ^ (18 : ℕ)) ^ (6 : ℕ) = Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) := by
      rw [mul_pow, ← pow_mul]
    have hM6 : Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) ≤ E ^ (6 : ℕ) := by rw [← hid6]; exact hM18'
    have h108 : ((2 : ℝ) ^ (108 : ℕ)) = 16 * (2 : ℝ) ^ (104 : ℕ) := by
      rw [show (108 : ℕ) = 4 + 104 by norm_num, pow_add]; norm_num
    have hlhs : ((s13BlockExp_L (flatDoorM A) : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ 19 * E ^ (6 : ℕ) := by
      have h1 : (2 : ℝ) ^ (104 : ℕ) * Mr ^ (6 : ℕ) ≤ E ^ (6 : ℕ) / 16 := by
        rw [h108] at hM6
        linarith [hM6]
      linarith [hbeR, hhi, hE6, h1, hE61, hE1]
    -- the window side
    have hHlopos : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
      have h := R.hHlo_floor
      have : (0 : ℕ) < R.Hlo := by omega
      exact_mod_cast this
    have hHloge : Real.exp (E ^ 2) ≤ ((R.Hlo : ℕ) : ℝ) := by
      have h := Real.exp_le_exp.mpr (hY ▸ hlo)
      rwa [Real.exp_log hHlopos] at h
    have hHhige : Real.exp (E ^ 2) ≤ ((R.Hhi : ℕ) : ℝ) := by
      have : ((R.Hlo : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast R.hHlohi
      linarith
    have hepsR : (1 : ℝ) / 512 ≤ (R.eps : ℝ) := by
      have hq : ((1 : ℚ) / 512 : ℚ) ≤ R.eps := by
        have := heps; norm_num at this ⊢; linarith
      have hc := (Rat.cast_le (K := ℝ)).mpr hq
      push_cast at hc
      linarith
    have hepssq : (1 : ℝ) / 262144 ≤ (R.eps : ℝ) ^ 2 := by nlinarith [hepsR]
    have hfloorR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1
        ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (R.eps ^ 2 * (R.Hhi : ℚ))
      have h' : ((R.eps ^ 2 * (R.Hhi : ℚ) : ℚ) : ℝ)
          < ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
      push_cast at h'
      linarith
    have hprod : (1 : ℝ) / 262144 * Real.exp (E ^ 2) ≤ (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
      mul_le_mul hepssq hHhige (Real.exp_pos _).le (by positivity)
    -- `e^{E²} ≥ E⁸/256`, so `2^{-18}·e^{E²} ≥ E⁸/2^{26} ≥ 6·E⁶` at `E ≥ 10^{17}`
    have hquart : (E ^ 2) ^ 4 / 256 ≤ Real.exp (E ^ 2) := flat_exp_ge_quartic (by positivity)
    have hbig : 6 * E ^ (6 : ℕ) ≤ 1 / 262144 * Real.exp (E ^ 2) := by
      have h2 : (1 : ℝ) / 262144 * ((E ^ 2) ^ 4 / 256)
          = E ^ (6 : ℕ) * E ^ (2 : ℕ) / 67108864 := by ring
      have h3 : (6 : ℝ) * E ^ (6 : ℕ) ≤ E ^ (6 : ℕ) * E ^ (2 : ℕ) / 67108864 := by
        have hEsq : (402653184 : ℝ) ≤ E ^ (2 : ℕ) := by nlinarith [hE17, hE0]
        have hE60 : (0 : ℝ) ≤ E ^ (6 : ℕ) := by positivity
        nlinarith [mul_nonneg hE60 (show (0 : ℝ) ≤ E ^ (2 : ℕ) - 402653184 by linarith)]
      have h1 : (1 : ℝ) / 262144 * ((E ^ 2) ^ 4 / 256) ≤ 1 / 262144 * Real.exp (E ^ 2) := by
        linarith [hquart]
      linarith [h1, h2, h3]
    linarith [hlhs, hfloorR, hprod, hbig, hE61]
  · -- ⟦`M`-UPPER 2⟧ the window gate: `0.49959·E² + 108` against `E²/2`
    rw [hinv, hrow]
    have hsq : Mr ^ 2 ≤ E ^ 2 / 96286710601 := by
      have h1 : (0 : ℝ) ≤ E / 310301 - Mr := by linarith
      have h2 : (0 : ℝ) ≤ E / 310301 + Mr := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hlogH : E ^ 2 ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by rw [hY]; exact hlo
    linarith [hsq, hlogH, hρlog, hE2]
  · -- the clearing charge
    linarith [hρlog]
  · -- ⟦THE REPAIR⟧ the anchor at `3.9·10⁹·M`: `14·E + 69` against `1.2568·10⁴·E`
    rw [hinv]
    have hlo39 : (12568 : ℝ) * E - 3900000001 ≤ 39 * 10 ^ 8 * Mr := by
      linarith [hMge, hE0]
    linarith [hhi, hρlog, hlo39, hE17]
  · -- the `𝒯`-leg budget: `14·E + 79` against `1.53·10⁵·E`
    rw [hAd]
    have hCtl : Real.log Ct ≤ 20 * Real.log 2 := by
      have h := Real.log_le_log hCt hCtb
      rwa [Real.log_pow] at h
    have hρ' : -(36 : ℝ) ≤ Real.log (doorRhoOfDelta (s12DeltaSock δ₀ K)) := by linarith [hρlog]
    linarith [hAdlog, hhi, hCtl, hρ', hlog2hi, hE17]
  · -- the `level1` budget: `14·E + 62 + ⅔·log E` against `1.279·10⁴·E`
    rw [hAd, s15_log_calQK_L_one, hrow]
    have hQpos : (0 : ℝ) < 68719476736 * Mr ^ 2 * Real.log 2 := by
      have : (0 : ℝ) < Real.log 2 := by linarith
      positivity
    have hsq : Mr ^ 2 ≤ E ^ 2 / 96286710601 := by
      have h1 : (0 : ℝ) ≤ E / 310301 - Mr := by linarith
      have h2 : (0 : ℝ) ≤ E / 310301 + Mr := by positivity
      nlinarith [mul_nonneg h1 h2]
    have hQle : 68719476736 * Mr ^ 2 * Real.log 2 ≤ E ^ 2 := by
      nlinarith [hsq, hlog2hi, sq_nonneg E, hM0, sq_nonneg Mr]
    have hlogQ : Real.log (68719476736 * Mr ^ 2 * Real.log 2) ≤ 2 * Real.log E := by
      have h := Real.log_le_log hQpos hQle
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    have hlogE : Real.log E ≤ E - 1 := Real.log_le_sub_one_of_pos hE0
    have hbud : 12750 * E ≤ 1 / 12 * (68719476736 * Mr) * Real.log 2 := by
      linarith [hAdlog]
    linarith [hhi, hρlog, hlogQ, hlogE, hbud, hE17]

/-! ## §5 — THE LEVER

Exactly one register line moves under the G-lever: `blk`, through
`s13BlockExp_L_gk K M = … + 400·(A_L·s13GK K M·M)² = … + 3600·2^{92}·4^K·M⁶`.  `lvl`'s `𝒬₁`
is a LEVEL-1 read and is therefore `K`-invariant (`calQK_gk_one_eq`), and the `anchor` line is
`G`-free — so the levered register is the ungraded one plus one inequality. -/

/-- The levered block exponent's head: `400·(A_L·s13GK K M·M)² = 3600·2^{92}·4^K·M⁶`. -/
theorem s13BlockExp_L_gk_head (K M : ℕ) :
    400 * (AdoorL M * s13GK K M * M) ^ 2 = 3600 * 2 ^ 92 * 4 ^ K * M ^ 6 := by
  have h4 : (4 : ℕ) ^ K = 2 ^ K * 2 ^ K := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
  simp only [AdoorL, s13GK, h4]
  ring

/-- **THE LEVERED BLOCK EXPONENT'S SIZE** — `s13BlockExp_L_gk K M ≤ 2^{104}·4^K·M⁶`. -/
theorem s13BlockExp_L_gk_le {K M : ℕ} (hM : 1 ≤ M) :
    s13BlockExp_L_gk K M ≤ 2 ^ 104 * 4 ^ K * M ^ 6 := by
  have hlog : Nat.log 2 M ≤ M := Nat.log_le_self 2 M
  have h6 : 1 ≤ M ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hM6 : M ≤ M ^ 6 := Nat.le_self_pow (by norm_num) M
  have h4 : 1 ≤ (4 : ℕ) ^ K := Nat.one_le_pow _ _ (by norm_num)
  have hhead : 14427 + (64 + 8 * (Nat.log 2 M + 1)) ≤ 496 * 2 ^ 92 * 4 ^ K * M ^ 6 := by
    have h1 : 14427 + (64 + 8 * (Nat.log 2 M + 1)) ≤ 14507 * M ^ 6 := by
      have : 8 * (Nat.log 2 M + 1) ≤ 8 * M ^ 6 + 8 * M ^ 6 := by omega
      nlinarith [h6, hM6, hlog]
    have h2 : 14507 * M ^ 6 ≤ 496 * 2 ^ 92 * 4 ^ K * M ^ 6 :=
      Nat.mul_le_mul_right _ (by nlinarith [h4])
    omega
  have hsplit : (2 : ℕ) ^ 104 * 4 ^ K * M ^ 6
      = 3600 * 2 ^ 92 * 4 ^ K * M ^ 6 + 496 * 2 ^ 92 * 4 ^ K * M ^ 6 := by ring
  rw [s13BlockExp_L_gk, s13BlockExp_L_gk_head, hsplit]
  omega

/-- **⟦THE LEVERED REGISTER FROM THE UNGRADED ONE⟧** (`s15_sel''_L_gk_of_L`) — ten of the
eleven lines transport verbatim; `lvl` transports through the level-1 `K`-invariance, and
`blk` is supplied. -/
theorem s15_sel''_L_gk_of_L (Klev : ℕ) {Cg δ₀ Ct ρ : ℝ} {x₀ Mfl : ℕ} {R : ChowlaRegime}
    {M : ℕ} (hsel : S15Sel''_L Cg δ₀ Ct ρ x₀ Mfl R M)
    (hblk : ((s13BlockExp_L_gk Klev M : ℕ) : ℝ) + 1
        + 18 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ))
      ≤ 4 * ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct ρ x₀ Mfl R M where
  hM := hsel.hM
  mfloor := hsel.mfloor
  bfloor := hsel.bfloor
  gRows := hsel.gRows
  x0M := hsel.x0M
  blk := hblk
  half := hsel.half
  rho := hsel.rho
  anchor := hsel.anchor
  gP1 := hsel.gP1
  lvl := by rw [calQK_gk_one_eq]; exact hsel.lvl

set_option maxHeartbeats 1600000 in
-- the levered `blk` line carries `4^K` against `e^{e^{3.2A}}` at a SYMBOLIC design point
/-- **⟦THE LEVERED REGISTER AT THE FLAT DESIGN POINT⟧** (`s15_sel''_L_gk_witness_flat`) —
`s15_sel''_L_witness_flat` at the G-lever, with `Klev` at the LINEAR door's own ceiling
`K ≤ 1.7·10⁸·M` (`DoorLinear.calFrameK_satisfiable_doorL_gk`).  The lever costs
`4^K ≤ e^{760·e^{1.6A}}` on the `blk` line's left, against `e^{e^{3.2A}}` on its right — and
`e^{3.2A} = (e^{1.6A})²` dwarfs `766·e^{1.6A}` by the factor `e^{1.6A} ≥ 10^{17}` itself.  So
the flat register hosts the lever at the door's full `K`-budget. -/
theorem s15_sel''_L_gk_witness_flat {A : ℝ} (hA : 26 ≤ A) (Klev : ℕ)
    (hKle : Klev ≤ 170000000 * flatDoorM A) {Cg δ₀ Ct K : ℝ} {x₀ Mfl : ℕ}
    {R : ChowlaRegime}
    (hδ : 0 < δ₀) (hδb : 1 / 2 ^ 10 ≤ δ₀)
    (hK : 0 < K) (hKb : K ≤ 2 ^ 20)
    (hCt : 0 < Ct) (hCtb : Ct ≤ 2 ^ 20)
    (hbfl : 24 * Cg / δ₀ ≤ ((flatDoorM A : ℕ) : ℝ))
    (hMfl : Mfl ≤ flatDoorM A)
    (hx0win : (x₀ : ℝ) ≤ Real.exp (Real.exp (3.2 * A) / 10))
    (heps : (1 : ℚ) / 2 ^ 9 ≤ R.eps)
    (hlo : Real.exp (3.2 * A) ≤ Real.log ((R.Hlo : ℕ) : ℝ))
    (hhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ Real.exp (3.2 * A / 2)) :
    S15Sel''_L_gk Klev Cg δ₀ Ct (doorRhoOfDelta (s12DeltaSock δ₀ K)) x₀ Mfl R
      (flatDoorM A) := by
  refine s15_sel''_L_gk_of_L Klev
    (s15_sel''_L_witness_flat hA hδ hδb hK hKb hCt hCtb hbfl hMfl hx0win heps hlo hhi) ?_
  set E : ℝ := Real.exp (3.2 * A / 2) with hEdef
  set Mr : ℝ := ((flatDoorM A : ℕ) : ℝ) with hMrdef
  have hE17 : (10 : ℝ) ^ 17 ≤ E := flat_exp_half_ge hA
  have hE0 : (0 : ℝ) < E := by positivity
  have hE1 : (1 : ℝ) ≤ E := by linarith [hE17]
  have hY : E ^ 2 = Real.exp (3.2 * A) := flat_exp_sq A
  have hMle : Mr ≤ E / 310301 := flatDoorM_le A
  have hM1N : 1 ≤ flatDoorM A := flatDoorM_one_le hA
  have hM0 : (0 : ℝ) ≤ Mr := Nat.cast_nonneg _
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- ⟦THE LEFT SIDE⟧ `2^104·4^K·M⁶ ≤ e^{766E}/16`
  have hbeN : s13BlockExp_L_gk Klev (flatDoorM A) ≤ 2 ^ 104 * 4 ^ Klev * (flatDoorM A) ^ 6 :=
    s13BlockExp_L_gk_le hM1N
  have hbeR : ((s13BlockExp_L_gk Klev (flatDoorM A) : ℕ) : ℝ)
      ≤ 2 ^ (104 : ℕ) * 4 ^ Klev * Mr ^ (6 : ℕ) := by
    have h : ((s13BlockExp_L_gk Klev (flatDoorM A) : ℕ) : ℝ)
        ≤ ((2 ^ 104 * 4 ^ Klev * (flatDoorM A) ^ 6 : ℕ) : ℝ) := by exact_mod_cast hbeN
    push_cast at h
    linarith
  -- `M⁶·2^108 ≤ E⁶`
  have h218 : ((2 : ℝ) ^ (18 : ℕ)) = 262144 := by norm_num
  have hM18 : Mr * 2 ^ (18 : ℕ) ≤ E := by
    have h : Mr * 310301 ≤ E := by
      have hd := hMle
      rw [le_div_iff₀ (by norm_num)] at hd
      linarith
    rw [h218]; linarith [h, hM0]
  have hid6 : (Mr * 2 ^ (18 : ℕ)) ^ (6 : ℕ) = Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) := by
    rw [mul_pow, ← pow_mul]
  have hM6 : Mr ^ (6 : ℕ) * 2 ^ (108 : ℕ) ≤ E ^ (6 : ℕ) := by
    rw [← hid6]; exact pow_le_pow_left₀ (by positivity) hM18 6
  have h108 : ((2 : ℝ) ^ (108 : ℕ)) = 16 * (2 : ℝ) ^ (104 : ℕ) := by
    rw [show (108 : ℕ) = 4 + 104 by norm_num, pow_add]; norm_num
  have hpow104 : (2 : ℝ) ^ (104 : ℕ) * Mr ^ (6 : ℕ) ≤ E ^ (6 : ℕ) / 16 := by
    rw [h108] at hM6; linarith [hM6]
  -- `E⁶ ≤ e^{6E}` and `4^{Klev} ≤ e^{760E}`
  have hE6exp : E ^ (6 : ℕ) ≤ Real.exp (6 * E) := by
    have h : Real.log (E ^ (6 : ℕ)) ≤ 6 * E := by
      rw [Real.log_pow]
      push_cast
      linarith [Real.log_le_sub_one_of_pos hE0]
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_log (by positivity)] at h2
  have hKR : (Klev : ℝ) ≤ 170000000 * Mr := by rw [hMrdef]; exact_mod_cast hKle
  have hMr310 : Mr * 310301 ≤ E := by
    have hd := hMle
    rw [le_div_iff₀ (by norm_num)] at hd
    linarith
  have hK0 : (0 : ℝ) ≤ (Klev : ℝ) := Nat.cast_nonneg _
  have h4K : (4 : ℝ) ^ Klev ≤ Real.exp (760 * E) := by
    have hlog4 : Real.log ((4 : ℝ) ^ Klev) = (Klev : ℝ) * Real.log 4 := by
      rw [Real.log_pow]
    have hlog4v : Real.log 4 ≤ 1.3862943616 := by
      have h : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
      rw [h]; linarith [hlog2hi]
    have hKE : (Klev : ℝ) ≤ 548 * E := by linarith [hKR, hMr310, hM0]
    have hbound : Real.log ((4 : ℝ) ^ Klev) ≤ 760 * E := by
      rw [hlog4]
      have h1 : (Klev : ℝ) * Real.log 4 ≤ (Klev : ℝ) * 1.3862943616 :=
        mul_le_mul_of_nonneg_left hlog4v hK0
      nlinarith [h1, hKE]
    have h2 := Real.exp_le_exp.mpr hbound
    rwa [Real.exp_log (by positivity)] at h2
  have hprodL : (2 : ℝ) ^ (104 : ℕ) * 4 ^ Klev * Mr ^ (6 : ℕ)
      ≤ Real.exp (766 * E) / 16 := by
    have h4K0 : (0 : ℝ) < (4 : ℝ) ^ Klev := by positivity
    have hstep : (2 : ℝ) ^ (104 : ℕ) * 4 ^ Klev * Mr ^ (6 : ℕ)
        ≤ (E ^ (6 : ℕ) / 16) * (4 : ℝ) ^ Klev := by
      have h := mul_le_mul_of_nonneg_right hpow104 h4K0.le
      linarith [h]
    have hstep2 : (E ^ (6 : ℕ) / 16) * (4 : ℝ) ^ Klev
        ≤ (Real.exp (6 * E) / 16) * Real.exp (760 * E) :=
      mul_le_mul (by linarith [hE6exp]) h4K (by positivity) (by positivity)
    have hid : (Real.exp (6 * E) / 16) * Real.exp (760 * E) = Real.exp (766 * E) / 16 := by
      rw [show (766 : ℝ) * E = 6 * E + 760 * E by ring, Real.exp_add]
      ring
    linarith [hstep, hstep2, hid]
  -- ⟦THE RIGHT SIDE⟧ `H₊ ≥ e^{E²}` and `E² ≥ 766E + 40`
  have hHlopos : (0 : ℝ) < ((R.Hlo : ℕ) : ℝ) := by
    have h := R.hHlo_floor
    have : (0 : ℕ) < R.Hlo := by omega
    exact_mod_cast this
  have hHhige : Real.exp (E ^ 2) ≤ ((R.Hhi : ℕ) : ℝ) := by
    have h := Real.exp_le_exp.mpr (hY ▸ hlo)
    rw [Real.exp_log hHlopos] at h
    have h2 : ((R.Hlo : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast R.hHlohi
    linarith
  have hepsR : (1 : ℝ) / 512 ≤ (R.eps : ℝ) := by
    have hq : ((1 : ℚ) / 512 : ℚ) ≤ R.eps := by
      have := heps; norm_num at this ⊢; linarith
    have hc := (Rat.cast_le (K := ℝ)).mpr hq
    push_cast at hc
    linarith
  have hepssq : (1 : ℝ) / 262144 ≤ (R.eps : ℝ) ^ 2 := by nlinarith [hepsR]
  have hfloorR : (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) - 1
      ≤ ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (R.eps ^ 2 * (R.Hhi : ℚ))
    have h' : ((R.eps ^ 2 * (R.Hhi : ℚ) : ℚ) : ℝ)
        < ((⌊R.eps ^ 2 * (R.Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    push_cast at h'
    linarith
  have hprod : (1 : ℝ) / 262144 * Real.exp (E ^ 2) ≤ (R.eps : ℝ) ^ 2 * ((R.Hhi : ℕ) : ℝ) :=
    mul_le_mul hepssq hHhige (Real.exp_pos _).le (by positivity)
  have hE2big : 766 * E + 40 ≤ E ^ 2 := by
    have hmul : (10 : ℝ) ^ 17 * E ≤ E * E := by nlinarith [hE17, hE0]
    nlinarith [hmul, hE17, hE0]
  have hexpmono : Real.exp (766 * E + 40) ≤ Real.exp (E ^ 2) := Real.exp_le_exp.mpr hE2big
  have hexp40 : (10 : ℝ) ^ 17 ≤ Real.exp 40 := by
    have he : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    have hp : (2.7 : ℝ) ^ (40 : ℕ) ≤ (Real.exp 1) ^ (40 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) he.le 40
    have hE : (Real.exp 1) ^ (40 : ℕ) = Real.exp 40 := by rw [← Real.exp_nat_mul]; norm_num
    have hn : (10 : ℝ) ^ 17 ≤ (2.7 : ℝ) ^ (40 : ℕ) := by norm_num
    rw [hE] at hp
    linarith
  have hsplit40 : Real.exp (766 * E + 40) = Real.exp (766 * E) * Real.exp 40 := by
    rw [← Real.exp_add]
  have hbig : 2 * Real.exp (766 * E) ≤ 1 / 262144 * Real.exp (E ^ 2) := by
    have hexpp : (0 : ℝ) < Real.exp (766 * E) := Real.exp_pos _
    nlinarith [hexpmono, hsplit40, hexp40, hexpp]
  have hEle : (18 : ℝ) * E + 5 ≤ Real.exp (766 * E) := by
    have h1 : (1 : ℝ) + 766 * E ≤ Real.exp (766 * E) := by
      linarith [Real.add_one_le_exp (766 * E)]
    linarith [hE17]
  linarith [hbeR, hprodL, hhi, hfloorR, hprod, hbig, hEle]

end Salt.MR

end
