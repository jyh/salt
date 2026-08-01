/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FlatConsumers
import Salt.MR.M4ArithPool
import Salt.MR.M4ArithPrime

/-!
# `ArithPageLinear` — THE ARITHMETIC PAGE at the LINEAR door (`AdoorL M = 2^36·M`)

⟦LINEAR-PAGE, the unfinished half of the ratified `Adoor`-linear re-cut⟧  `W0`
(`Salt.MR.DoorLinear`) cut the DOOR linear and stopped at its §7.  This page carries the
`_L` twin family the rest of the way through the ARITHMETIC objects that hardwire the landed
anchor:

```
a2Level1  →  a2RowsSum(')  →  a2Mrow  →  a2DoorGrade  →  DoorArithFrameRho
```

⟦WHY IT IS MANDATORY⟧ ⟦H1-ANCHOR⟧ established that the `3.9·10⁹` of
`M4ArithRho.DoorArithFrameRho.anchor` is **not a frame constant**: it is `(1/12)·A(M)·log 2`
rounded down 1.78 %, i.e. the `lvl` line's own rate written at the door's anchor.  At the
LOGARITHMIC door its right side is `3.9·10⁹·(⌊log₂M⌋+1)`, which the register's `half` line
caps at `≈ 1.4427·λ₋` — LINEAR in `λ₋` — while the flat width demands `λ₊ ≈ e^{λ₋/2}`.  No
numeral repairs that (⟦H1-ANCHOR⟧ `p5`: the shape, not the constant, is the knob).  At the
LINEAR door the same line reads `3.9·10⁹·M` with `M ≈ e^{λ₋/2}/310301`, and it hosts the full
flat width with `> 900×` of margin (`p7`), UNIFORMLY IN the design constant `A` (`p9`).

⟦WHAT IS ADDITIVE, AND WHY NOTHING LANDED MOVES⟧

* **The frame twin is IMPLIED by the landed frame** (`DoorArithFrameRho_L.of_landed`): the
  linear anchor is WEAKER than the logarithmic one (`⌊log₂M⌋ + 1 ≤ M`,
  `anchorL_of_anchor`), so every existing supplier of `DoorArithFrameRho` supplies
  `DoorArithFrameRho_L` for free.  The re-cut costs the supply side NOTHING; what it buys is
  a frame whose anchor field a FLAT-width register can actually meet.
* **The level-1 grade re-derives, it does not transport.**  `a2Level1 M` reads `Adoor M` in
  both the numerator (`log 𝒬₁`) and the denominator (`𝒫₁^{1/12}`), and the re-cut moves both:
  `log 𝒬₁ = 2^36·M²·log 2` (QUADRATIC, was `M·log M`-shaped) against
  `log 𝒫₁ = 2^36·M·log 2`.  §3's `doorGrade_summand2_priced_rho_L` is where that trade is
  paid, and it is paid with room: the anchor spends `3.9·10⁹·M` against a budget
  `(1/12)·2^36·M·log 2 = 3.9694·10⁹·M`, and the residue `6.94·10⁷·M` swallows the
  quadratic `(1/3)·log(2^36 M²·log 2) ≤ 8.32 + (2/3)(M−1)` with everything to spare.
* **The row sums are anchor-symbolic.**  `a2RowsSum`/`a2RowsSum'` read the anchor only
  through `𝒫ⱼ` and `H₁`, so their `_L` twins are the landed texts at `AdoorL`; the `p²`-slot
  ordering (`a2RowsSum'_L_le_a2RowsSum_L`) is the landed proof verbatim.

Source pins: `docs/blueprints/flags.md` ⟦H1-ANCHOR⟧ (`p6`/`p7`/`p9`), ⟦H2-CONSTANTS⟧'s
synthesis (the face dissolves by unfreezing), ⟦FLAT-REF⟧ amendment 0.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — the linear door's level-1 reads

`log 𝒫₁ = A_L(M)·log 2 = 2^36·M·log 2` and `log 𝒬₁ = doorRowFloorL M·log 2 = 2^36·M²·log 2`.
Both are `DoorLinear` identities; what is added here is the positivity/floor scaffolding the
grade needs. -/

/-- `log 𝒬₁ = doorRowFloorL M · log 2` at the linear door family (`S15Compose`'s
`s15_log_calQK_one` twin). -/
theorem s15_log_calQK_L_one (M : ℕ) :
    Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)
      = ((doorRowFloorL M : ℕ) : ℝ) * Real.log 2 := by
  rw [log_calQK, calE_one, doorRowFloorL]
  push_cast; ring

/-- `2^36 ≤ doorRowFloorL M` (`s15_doorRowFloor_ge` twin). -/
theorem s15_doorRowFloorL_ge {M : ℕ} (hM : 1 ≤ M) : (2 : ℕ) ^ 36 ≤ doorRowFloorL M := by
  rw [doorRowFloorL]
  calc (2 : ℕ) ^ 36 ≤ AdoorL M := AdoorL_ge hM
    _ = 1 * AdoorL M := (one_mul _).symm
    _ ≤ M * AdoorL M := Nat.mul_le_mul_right _ hM

theorem s15_log_calQK_L_one_pos {M : ℕ} (hM : 1 ≤ M) :
    (0 : ℝ) < Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ) := by
  rw [s15_log_calQK_L_one]
  have h1 : (1 : ℕ) ≤ doorRowFloorL M := le_trans (by norm_num) (s15_doorRowFloorL_ge hM)
  have h1R : (1 : ℝ) ≤ ((doorRowFloorL M : ℕ) : ℝ) := by exact_mod_cast h1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem s15_loglogQ1_L_nonneg {M : ℕ} (hM : 1 ≤ M) :
    (0 : ℝ) ≤ Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) := by
  refine Real.log_nonneg ?_
  rw [s15_log_calQK_L_one]
  have h : (2 : ℕ) ^ 36 ≤ doorRowFloorL M := s15_doorRowFloorL_ge hM
  have hR : (2 : ℝ) ^ 36 ≤ ((doorRowFloorL M : ℕ) : ℝ) := by exact_mod_cast h
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  nlinarith

theorem s15_calP_L_one_pos (M : ℕ) : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := by
  have h : 0 < calP (AdoorL M) (3072 * M) 1 := by rw [calP]; exact Nat.two_pow_pos _
  exact_mod_cast h

/-- `𝒫₁ ≤ 𝒫₂` at the linear door (`s15_calP_one_le_two` twin) — `e₁ = A ≤ A·G·4 = e₂`. -/
theorem s15_calP_L_one_le_two {M : ℕ} (hM : 1 ≤ M) :
    calP (AdoorL M) (3072 * M) 1 ≤ calP (AdoorL M) (3072 * M) 2 := by
  have hE : calE (AdoorL M) (3072 * M) 1 ≤ calE (AdoorL M) (3072 * M) 2 := by
    have h1 : calE (AdoorL M) (3072 * M) 1 = AdoorL M := calE_one _ _
    have h2 : calE (AdoorL M) (3072 * M) 2 = AdoorL M * (3072 * M) * 4 := by
      simp [calE, Nat.factorial]
    rw [h1, h2]
    calc AdoorL M = AdoorL M * 1 * 1 := by ring
      _ ≤ AdoorL M * (3072 * M) * 4 := by
          have : 1 ≤ 3072 * M := by omega
          exact Nat.mul_le_mul (Nat.mul_le_mul_left _ this) (by omega)
  rw [calP, calP]
  exact Nat.pow_le_pow_right (by norm_num) hE

/-! ## §1 — `a2Level1` and `H1door` at the linear anchor -/

/-- **THE §8.1 LEVEL-1 GRADE AT THE LINEAR DOOR** (`ThmA2.a2Level1` twin):
`(log 𝒬₁)^{1/3}/𝒫₁^{1/12}` read at `A_L(M) = 2^36·M`.  The numerator's exponent is
`2^36·M²` (quadratic), the denominator's `2^36·M` — the whole trade the re-cut makes. -/
def a2Level1_L (M : ℕ) : ℝ :=
  (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
    / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)

/-- `DoorFrameH1.H1door` at the linear anchor — the seam's `H₁` slot, `= 1/a2Level1_L M`. -/
def H1doorL (M : ℕ) : ℝ :=
  ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)
    / (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)

theorem a2Level1_L_pos {M : ℕ} (hM : 1 ≤ M) : 0 < a2Level1_L M := by
  rw [a2Level1_L]
  exact div_pos (Real.rpow_pos_of_pos (s15_log_calQK_L_one_pos hM) _)
    (Real.rpow_pos_of_pos (s15_calP_L_one_pos M) _)

theorem a2Level1_L_nonneg {M : ℕ} (hM : 1 ≤ M) : 0 ≤ a2Level1_L M := (a2Level1_L_pos hM).le

/-- **THE LEVEL-1 GRADE IS K-INVARIANT AT THE LINEAR DOOR** (`a2Level1_gk_eq` twin): level 1
does not see the lever (`GLever.calE_gk_one`). -/
theorem a2Level1_L_gk_eq (K M : ℕ) :
    (Real.log ((calQK (AdoorL M) (s13GK K M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3)
        / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12)
      = a2Level1_L M := by
  rw [calP_gk_one_eq, calQK_gk_one_eq, a2Level1_L]

/-- **⟦`a2Level1_L` IN CLOSED FORM⟧** — `a2Level1_L M = exp(⅓·loglog 𝒬₁ − (1/12)·A_L(M)·log 2)`
(`S15Compose.s15_a2Level1_exp` twin). -/
theorem s15_a2Level1_L_exp {M : ℕ} (hM : 1 ≤ M) :
    a2Level1_L M = Real.exp ((1 / 3) * Real.log (Real.log
        ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
      - (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2) := by
  have hP1pos : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := s15_calP_L_one_pos M
  have hLQ := s15_log_calQK_L_one_pos hM
  rw [a2Level1_L, Real.rpow_def_of_pos hLQ, Real.rpow_def_of_pos hP1pos,
    s11_log_calP_doorL_one M, ← Real.exp_sub]
  ring_nf

/-! ## §2 — the Lemma-12 row sums at the linear anchor

`a2RowsSum`/`a2RowsSum'` read the door only through `𝒫ⱼ` and `H₁`.  Their `_L` twins are the
landed texts at `AdoorL`/`H1doorL`, and the ⟦R1⟧ ordering carries verbatim. -/

/-- `ThmA2.a2RowsSum` at the linear door family. -/
def a2RowsSum_L (M Xd : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 2,
    ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
        * (Real.exp 1 / (Xd : ℝ) ^ 2))
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
      + 1 / (Xd : ℝ))

/-- ⟦R1⟧'s `X_d`-free row sum at the linear door family (`ThmA2.a2RowsSum'` twin). -/
def a2RowsSum'_L (M Xd : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 2,
    ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
        * (Real.exp 1 / (Xd : ℝ) ^ 2))
      + 24 / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
      + 1 / (Xd : ℝ))

/-- **THE TWIN IS SMALLER, AT THE LINEAR DOOR** (`a2RowsSum'_le_a2RowsSum` twin). -/
theorem a2RowsSum'_L_le_a2RowsSum_L {M Xd : ℕ} (hXd : 2 ≤ Xd) :
    a2RowsSum'_L M Xd ≤ a2RowsSum_L M Xd := by
  have hXd2 : (2 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast hXd
  have hXd0 : (0 : ℝ) < (Xd : ℝ) := by linarith
  have hlogb : (3 / 2 : ℝ) ≤ Real.logb 2 (2 * (Xd : ℝ)) := by
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlt2 := Real.log_two_lt_d9
    have hgt2 := Real.log_two_gt_d9
    have hlogXd : Real.log 2 ≤ Real.log (Xd : ℝ) := Real.log_le_log (by norm_num) hXd2
    have hmul : Real.log (2 * (Xd : ℝ)) = Real.log 2 + Real.log (Xd : ℝ) :=
      Real.log_mul (by norm_num) (ne_of_gt hXd0)
    rw [Real.logb, le_div_iff₀ hl2, hmul]
    linarith
  rw [a2RowsSum'_L, a2RowsSum_L]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) := by
    have : 0 < calP (AdoorL M) (3072 * M) j := by rw [calP]; positivity
    exact_mod_cast this
  have hterm : (24 : ℝ) / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
      ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) := by
    gcongr
    linarith
  linarith

/-- `ThmA2.a2Mrow` at the linear door family — the weighted seam row's bound. -/
def a2Mrow_L (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) : ℝ :=
  47520 * a2Level1_L M
    + 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ))
    + 5760 * (a2RowsSum_L M Xd + C * (2 / (M : ℝ)))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-- `ThmA2.a2RowsSum_gk` at the linear door family. -/
def a2RowsSum_L_gk (K M Xd : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 2,
    ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
        * (Real.exp 1 / (Xd : ℝ) ^ 2))
      + 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
      + 1 / (Xd : ℝ))

/-- `ThmA2.a2RowsSum'_gk` at the linear door family. -/
def a2RowsSum'_L_gk (K M Xd : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 2,
    ((Xd : ℝ) * ((2 * Real.exp 1 * (Xd : ℝ) / calH (H1doorL M) j + 1)
        * (Real.exp 1 / (Xd : ℝ) ^ 2))
      + 24 / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
      + 1 / (Xd : ℝ))

/-- **THE LEVER SHRINKS THE ROW SUM, AT THE LINEAR DOOR** (`a2RowsSum_gk_le` twin):
`3072M ≤ s13GK K M` grows `𝒫ⱼ`, hence shrinks the `p²` slot. -/
theorem a2RowsSum_L_gk_le (K M Xd : ℕ) : a2RowsSum_L_gk K M Xd ≤ a2RowsSum_L M Xd := by
  rw [a2RowsSum_L_gk, a2RowsSum_L]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hP : calP (AdoorL M) (3072 * M) j ≤ calP (AdoorL M) (s13GK K M) j := by
    rw [calP, calP]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [calE, calE]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_s13GK K M) _))
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) := by
    have : 0 < calP (AdoorL M) (3072 * M) j := by rw [calP]; positivity
    exact_mod_cast this
  have hPR : ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
      ≤ ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ) := by exact_mod_cast hP
  have hlogb0 : (0 : ℝ) ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) := by
    rcases Nat.eq_zero_or_pos Xd with h | h
    · subst h; simp [Real.logb]
    · have h1 : (1 : ℝ) ≤ (Xd : ℝ) := by exact_mod_cast h
      have h2 : (1 : ℝ) ≤ 2 * (Xd : ℝ) := by linarith
      have := Real.logb_nonneg (b := 2) (by norm_num) h2
      linarith
  have hterm : 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
      ≤ 16 * Real.logb 2 (2 * (Xd : ℝ)) / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left hlogb0 hP0 hPR
  linarith

/-- ⟦R1⟧'s row sum at the lever, linear door (`a2RowsSum'_gk_le` twin). -/
theorem a2RowsSum'_L_gk_le (K M Xd : ℕ) : a2RowsSum'_L_gk K M Xd ≤ a2RowsSum'_L M Xd := by
  rw [a2RowsSum'_L_gk, a2RowsSum'_L]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hP : calP (AdoorL M) (3072 * M) j ≤ calP (AdoorL M) (s13GK K M) j := by
    rw [calP, calP]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    rw [calE, calE]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (le_s13GK K M) _))
  have hP0 : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) := by
    have : 0 < calP (AdoorL M) (3072 * M) j := by rw [calP]; positivity
    exact_mod_cast this
  have hPR : ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ)
      ≤ ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ) := by exact_mod_cast hP
  have hterm : (24 : ℝ) / ((calP (AdoorL M) (s13GK K M) j : ℕ) : ℝ)
      ≤ 24 / ((calP (AdoorL M) (3072 * M) j : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hP0 hPR
  linarith

/-- `ThmA2.a2Mrow_gk` at the linear door family. -/
def a2Mrow_L_gk (K : ℕ) (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) : ℝ :=
  47520 * a2Level1_L M
    + 374784 * Cs * Real.exp 3 * (1 / ((calP (AdoorL M) (s13GK K M) 1 : ℕ) : ℝ))
    + 5760 * (a2RowsSum_L_gk K M Xd + C * (2 / (M : ℝ)))
    + 3 * (Real.log X) ^ (-theta293 + ε)

/-- **THE LEVER SHRINKS THE ROW NUMBER, AT THE LINEAR DOOR** (`a2Mrow_gk_le` twin): the
level-1 slots are K-invariant, the row-sum slot shrinks, the rest is `G`-free. -/
theorem a2Mrow_L_gk_le (K : ℕ) (Cs C : ℝ) (M Xd : ℕ) (X ε : ℝ) :
    a2Mrow_L_gk K Cs C M Xd X ε ≤ a2Mrow_L Cs C M Xd X ε := by
  rw [a2Mrow_L_gk, a2Mrow_L, calP_gk_one_eq]
  have h := a2RowsSum_L_gk_le K M Xd
  linarith

/-! ## §3 — ⟦THE ARITHMETIC FRAME AT THE LINEAR ANCHOR⟧

`M4ArithRho.DoorArithFrameRho` with its ONE door-reading field — `anchor` — restated at
`3.9·10⁹·M`.  Everything else is the landed text: the arm, the `M₀` window, the `j`-floor and
the four positivity fields never mention the anchor. -/

/-- **⟦THE LINEAR ANCHOR IS WEAKER⟧** (`p6_linear_weaker`) — `3.9·10⁹·(⌊log₂M⌋+1) ≤ 3.9·10⁹·M`
for every `M ≥ 1` (`Nat.log_lt_self`, with `M = 1` the boundary case). -/
theorem anchorL_of_anchor {M : ℕ} (hM : 1 ≤ M) :
    (39 * 10 ^ 8 : ℝ) * ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ 39 * 10 ^ 8 * (M : ℝ) := by
  have h : Nat.log 2 M + 1 ≤ M ∨ M = 1 := by
    rcases Nat.lt_or_ge M 2 with h1 | _
    · right; omega
    · left
      have := Nat.log_lt_self 2 (show M ≠ 0 by omega)
      omega
  rcases h with h | h
  · have : ((Nat.log 2 M + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
    linarith
  · subst h; simp

/-- **⟦THE RATIFIED ARITHMETIC FRAME, AT THE LINEAR DOOR⟧**
(`DoorArithFrameRho_L M H j X C₁ M₀ K ρ`) — `M4ArithRho.DoorArithFrameRho` with the ⟦C1⟧
anchor read at `3.9·10⁹·M` in place of `3.9·10⁹·(⌊log₂M⌋+1)`.  That single field is
⟦H1-ANCHOR⟧'s whole repair: the right side is `(1/12)·A_L(M)·log 2` rounded down 1.78 %, so
the anchor line is the `lvl` line of the LINEAR door, and it grows with `M` rather than with
`log M`. -/
structure DoorArithFrameRho_L (M H j : ℕ) (X C₁ M₀ K ρ : ℝ) : Prop where
  /-- the door's parameter. -/
  Mpos : 1 ≤ M
  /-- `0 ≤ log X` — free at a natural base. -/
  logX_nonneg : 0 ≤ Real.log X
  /-- `0 ≤ log H` — free at a natural width. -/
  logH_nonneg : 0 ≤ Real.log (H : ℝ)
  /-- **the `H`-floor** `loglog H ≥ 50`. -/
  Hfloor : 50 ≤ Real.log (Real.log (H : ℝ))
  /-- `K ≥ 0` — the margined floor constant is a floor. -/
  Knonneg : 0 ≤ K
  /-- **the clearing parameter is positive**. -/
  rho_pos : 0 < ρ
  /-- **the clearing parameter is a budget** `ρ ≤ 1`. -/
  rho_le_one : ρ ≤ 1
  /-- **⟦C4 — THE ARM, AT `ρ`⟧** `loglog X ≥ 7000·loglog H + 500·log(1/ρ) + 6600 + 36K`. -/
  arm : 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600 + 36 * K
    ≤ Real.log (Real.log X)
  /-- **⟦C1 — THE 12× ANCHOR, AT THE LINEAR DOOR⟧**
  `14·loglog H + log(1/ρ) + 33 ≤ 3.9·10⁹·M`. -/
  anchor : 14 * Real.log (Real.log (H : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * (M : ℝ)
  /-- the band constant is a constant. -/
  C1_nonneg : 0 ≤ C₁
  /-- **⟦C4 — THE `M₀` WINDOW, LOWER ENDPOINT, AT `ρ`⟧**. -/
  M0_window : Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12) ≤ M₀
  /-- **the window index floor, at `ρ`** `j ≥ 21·loglog H + 2·log(1/ρ) + 28`. -/
  jfloor : 21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28 ≤ (j : ℝ)

namespace DoorArithFrameRho_L

variable {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}

theorem logInvRho_nonneg (h : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) :
    0 ≤ Real.log (1 / ρ) :=
  log_one_div_nonneg h.rho_pos h.rho_le_one

theorem one_lt_logH (h : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) : 1 < Real.log (H : ℝ) :=
  one_lt_log_of_loglog_ge h.logH_nonneg (by norm_num) h.Hfloor

theorem armWeak (h : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) :
    7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log X) := by
  have := h.arm
  have := h.Knonneg
  linarith

theorem loglogX_ge (h : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) :
    356600 ≤ Real.log (Real.log X) := by
  have h1 := h.armWeak
  have h2 := h.Hfloor
  have h3 := h.logInvRho_nonneg
  linarith

theorem one_lt_logX (h : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) : 1 < Real.log X :=
  one_lt_log_of_loglog_ge h.logX_nonneg (show (0:ℝ) < 356600 by norm_num) h.loglogX_ge

end DoorArithFrameRho_L

/-- **⟦THE RE-CUT IS FREE ON THE SUPPLY SIDE⟧** — the LANDED frame implies the LINEAR frame.
Only `anchor` differs, and `anchorL_of_anchor` weakens it.  So every existing supplier of
`DoorArithFrameRho` — `m4_arith_anchor_of_C1_rho` and the whole `s15_doorArithFrameRho_*`
family — supplies `DoorArithFrameRho_L` with NO new obligation.  ⟦H1-ANCHOR⟧'s `p6`. -/
theorem DoorArithFrameRho_L.of_landed {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}
    (h : DoorArithFrameRho M H j X C₁ M₀ K ρ) : DoorArithFrameRho_L M H j X C₁ M₀ K ρ where
  Mpos := h.Mpos
  logX_nonneg := h.logX_nonneg
  logH_nonneg := h.logH_nonneg
  Hfloor := h.Hfloor
  Knonneg := h.Knonneg
  rho_pos := h.rho_pos
  rho_le_one := h.rho_le_one
  arm := h.arm
  anchor := le_trans h.anchor (anchorL_of_anchor h.Mpos)
  C1_nonneg := h.C1_nonneg
  M0_window := h.M0_window
  jfloor := h.jfloor

/-- **⟦C1'S ANCHOR AT THE LINEAR DOOR⟧** (`m4_arith_anchor_of_C1_rho_L`) — ⟦H1-ANCHOR⟧'s `p6`:
the landed supplier's OWN hypothesis (`⌊log₂M⌋ + 1 ≥ 2484`) discharges the LINEAR anchor too,
with `2^2483/2484` more room.  Stated so the landed register's suppliers transport VERBATIM. -/
theorem m4_arith_anchor_of_C1_rho_L {M H : ℕ} {ρ : ℝ} (hM : 2484 ≤ Nat.log 2 M + 1)
    (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11)
    (hρcap : Real.log (1 / ρ) ≤ 10 ^ 11) :
    14 * Real.log (Real.log (H : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * (M : ℝ) := by
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp [Nat.log_zero_right] at hM
    · exact h
  exact le_trans (m4_arith_anchor_of_C1_rho (M := M) (H := H) (ρ := ρ) hM hHcap hρcap)
    (anchorL_of_anchor hM1)

/-- **⟦THE WINDOW-INDEX FLOOR AT THE LINEAR DOOR⟧** (`m4_arith_jfloor_of_anchor_rho` twin) —
the linear row floor `doorRowFloorL M = 2^36·M² ≥ 2^36` already dwarfs
`21·loglog H + 2·log(1/ρ) + 28` on the whole register, so the `j`-floor no longer needs the
`2484`-bit hypothesis at all: `M ≥ 65536` suffices. -/
theorem m4_arith_jfloorL_of_row {M H j : ℕ} (hM : 65536 ≤ M) (hj : doorRowFloorL M ≤ j)
    (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11)
    (hρcap : Real.log (1 / ρ) ≤ 10 ^ 11) :
    21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28 ≤ (j : ℝ) := by
  have hrow : 65536 * (2 ^ 36 * 65536) ≤ doorRowFloorL M := by
    rw [doorRowFloorL, AdoorL]
    exact Nat.mul_le_mul hM (Nat.mul_le_mul_left _ hM)
  have hjN : (281474976710656 : ℕ) ≤ j := le_trans (by norm_num) (le_trans hrow hj)
  have hjR : (281474976710656 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjN
  linarith

/-! ## §4 — ⟦THE PRICING⟧ the level-1 summand at the linear anchor

This is the one summand of `M4Assembly.a2DoorGrade` that reads the door, and the whole
content of the re-cut's arithmetic half.  The trade, exactly:

* the LEVEL-1 GRADE's numerator is now `log 𝒬₁ = 2^36·M²·log 2` — QUADRATIC in `M`, so its
  cube root costs `(1/3)·(36·log 2 + 2·log M + log log 2) ≤ 8.32 + (2/3)(M − 1)`;
* the denominator is `𝒫₁^{1/12} = 2^{2^36·M/12}`, i.e. a budget `(1/12)·2^36·M·log 2
  ≥ 3.9694·10⁹·M`;
* the anchor spends `3.9·10⁹·M` of it, leaving `6.94·10⁷·M` — and
  `log 1787702400 + 8.32 + (2/3)(M−1) + 3·log 2 − 33 ≤ (2/3)·M` fits inside that residue
  with eight orders to spare.

At the LOGARITHMIC door the same accounting has `m = ⌊log₂M⌋ + 1` on the right and `M` inside
the numerator's log, which is what forces the landed proof's `M < 2^m` ladder. -/

/-- **SUMMAND 2 AT `ρ/8`, AT THE LINEAR DOOR** (`doorGrade_summand2_priced_rho` twin).
`1787702400·a2Level1_L M` clears `ρ/8` under the LINEAR anchor
`14·loglog H + log(1/ρ) + 33 ≤ 3.9·10⁹·M`. -/
theorem doorGrade_summand2_priced_rho_L {M H : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hM : 1 ≤ M)
    (hanchor : 14 * Real.log (Real.log (H : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * (M : ℝ)) :
    1787702400 * a2Level1_L M * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 8 := by
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlog2lo := Real.log_two_gt_d9
  have hlog2hi := Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hAdR : ((AdoorL M : ℕ) : ℝ) = 68719476736 * (M : ℝ) := AdoorL_cast M
  have hlogQ := s15_log_calQK_L_one M
  have hrowR : ((doorRowFloorL M : ℕ) : ℝ) = 68719476736 * (M : ℝ) ^ 2 := by
    rw [doorRowFloorL, AdoorL]; push_cast; ring
  have hlogQpos := s15_log_calQK_L_one_pos hM
  have hPpos : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) := s15_calP_L_one_pos M
  have hlogP := s11_log_calP_doorL_one M
  have hnum : (0 : ℝ)
      < (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlogQpos _
  have hden : (0 : ℝ) < ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hPpos _
  have hlvlpos : (0 : ℝ) < a2Level1_L M := by rw [a2Level1_L]; exact div_pos hnum hden
  refine le_of_log_le' (by positivity) (div_pos hρ (by norm_num)) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hlvlpos.ne', Real.log_exp, a2Level1_L,
    Real.log_div hnum.ne' hden.ne', Real.log_rpow hlogQpos, Real.log_rpow hPpos,
    hlogQ, hlogP, hrowR, hAdR, Real.log_div hρ.ne' (by norm_num : (8 : ℝ) ≠ 0), log_eight_eq]
  -- ⟦the numerator: `2^36·M²·log 2 ≤ 2^36·M²`, so `log ≤ 36·log 2 + 2·(M − 1)`⟧
  have hlogM : Real.log (M : ℝ) ≤ (M : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hhead : (68719476736 : ℝ) * (M : ℝ) ^ 2 * Real.log 2
      ≤ 68719476736 * (M : ℝ) ^ 2 := by nlinarith [sq_nonneg (M : ℝ)]
  have hloghead : Real.log ((68719476736 : ℝ) * (M : ℝ) ^ 2 * Real.log 2)
      ≤ Real.log 68719476736 + 2 * ((M : ℝ) - 1) := by
    have hpos : (0 : ℝ) < 68719476736 * (M : ℝ) ^ 2 * Real.log 2 := by positivity
    have hstep : Real.log ((68719476736 : ℝ) * (M : ℝ) ^ 2 * Real.log 2)
        ≤ Real.log ((68719476736 : ℝ) * (M : ℝ) ^ 2) := Real.log_le_log hpos hhead
    have hsplit : Real.log ((68719476736 : ℝ) * (M : ℝ) ^ 2)
        = Real.log 68719476736 + 2 * Real.log (M : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    rw [hsplit] at hstep
    linarith
  have hlog687 : Real.log 68719476736 ≤ 26 := by
    have := log_le_of_le_pow27 (c := (68719476736 : ℝ)) (by norm_num) 26 (r := 0) (by norm_num)
      (by norm_num)
    norm_num at this ⊢
    linarith
  have h1787 := log_1787702400_le
  have hLinv : Real.log (1 / ρ) = -Real.log ρ := log_one_div_eq_neg ρ
  -- ⟦the budget: `(1/12)·2^36·M·log 2 ≥ 3.9694·10⁹·M`, the anchor spends `3.9·10⁹·M`⟧
  have hbud : (3969390000 : ℝ) * (M : ℝ)
      ≤ 1 / 12 * (68719476736 * (M : ℝ)) * Real.log 2 := by
    have h : (0.6931471803 : ℝ) * (M : ℝ) ≤ Real.log 2 * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hlog2lo.le (by linarith)
    nlinarith [h]
  linarith

/-! ## §5 — the door grade at the linear anchor, priced -/

/-- `M4Assembly.a2DoorGrade` at the linear door — one summand moves (`a2Level1_L`). -/
def a2DoorGrade_L (M : ℕ) (X h C₁ M₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1_L M
    + 188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

theorem a2DoorGrade_L_nonneg {M : ℕ} (hM : 1 ≤ M) {X h C₁ M₀ : ℝ} (hX : 0 ≤ Real.log X)
    (hh : 0 < h) : 0 ≤ a2DoorGrade_L M X h C₁ M₀ := by
  have hlvl := a2Level1_L_nonneg hM
  have h1 : (0 : ℝ) ≤ 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
  have h3 : (0 : ℝ) ≤ 188133 * (Real.log X) ^ (-(1 : ℝ) / 500) := by positivity
  have h4 : (0 : ℝ) ≤ 304128 * ballSupC ^ 2
      * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
  have h5 : (0 : ℝ) ≤ 6315000 / h := by positivity
  rw [a2DoorGrade_L]
  linarith

/-- **⟦THE PRICING AT `ρ`, AT THE LINEAR DOOR — THE PAGE'S CORE⟧**
(`M4ArithRho.a2DoorGrade_priced_rho` twin).  At the `ρ`-parametric LINEAR frame the
`φ(q)`-debited door grade sits under the `ρ`-envelope:

  `arcDen 12 H · a2DoorGrade_L M X 2^j C₁ M₀  ≤  RSanDoorRho ρ H`.

Summands 1, 3, 4, 5 are `M4ArithRho`'s VERBATIM (they never read the door); summand 2 is §4's
linear stone.  The budget `ρ/2 + 4·(ρ/8) = ρ` closes exactly, as at the landed anchor. -/
theorem a2DoorGrade_L_priced_rho {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) :
    arcDen 12 H * a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ ≤ RSanDoorRho ρ H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hLrho : 0 ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by
    rw [hstr]; have := hfr.Hfloor; linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
    refine a2DoorGrade_L_nonneg hfr.Mpos (by linarith) ?_
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have hwt := arcDen_mul_strataResidual_sq_le hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoorRho, le_div_iff₀ (pow_pos hstrpos 2)]
  have hkey : arcDen 12 H * a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ * strataResidual H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
    have hid : arcDen 12 H * a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ * strataResidual H ^ 2
        = (arcDen 12 H * strataResidual H ^ 2)
            * a2DoorGrade_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  have h1 := doorGrade_summand1_priced_rho (H := H) hfr.rho_pos hfr.C1_nonneg hfr.logX_nonneg
    hLX hfr.M0_window
  have h2 := doorGrade_summand2_priced_rho_L (H := H) hfr.rho_pos hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_rho (H := H) hfr.rho_pos hLX hfr.armWeak
  have h4 := doorGrade_summand4_priced_rho (H := H) hfr.rho_pos hLrho hLX hfr.Hfloor hfr.armWeak
  have h5 := doorGrade_summand5_priced_rho (H := H) (j := j) hfr.rho_pos hLrho hfr.Hfloor
    hfr.jfloor
  rw [a2DoorGrade_L]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-! ## §6 — the register's `constPool` budget lines, ANCHOR-GENERIC

`S15Compose`'s four budget stones (`s15_p2_of_budget`, `s15_level1_of_budget`,
`s15_gP1_of_budget`, `s15_endpt_at_constPool`) read the door ONLY through
`log 𝒫₁ = A·log 2` and `log 𝒬₁ = M·A·log 2`.  Stating them at a SYMBOLIC anchor `A` retires
the `Adoor`-vs-`AdoorL` question at the source: the landed instances are `A := Adoor M`, the
linear ones `A := AdoorL M`, and no proof is duplicated. -/

/-- `log 𝒫₁ = A·log 2` at an arbitrary anchor (`s13_band_log_calP_one`, anchor-generic). -/
theorem log_calP_one_gen (A G : ℕ) :
    Real.log ((calP A G 1 : ℕ) : ℝ) = (A : ℝ) * Real.log 2 := by
  rw [calP, calE_one]
  push_cast
  rw [Real.log_pow]

/-- **⟦THE `𝒯`-LEG GATE AT `constPool`, ANCHOR-GENERIC⟧** (`s15_gP1_of_budget` at a symbolic
anchor).  Instantiating at `A := AdoorL M`, `G := 3072M` gives the linear door's `gP1`. -/
theorem s15_gP1_of_budget_gen {A G Hhi : ℕ} {Cs ρ : ℝ} (hCs : 0 < Cs) (hρ : 0 < ρ)
    (hbudget : 29 + Real.log Cs + 14 * Real.log (Real.log (Hhi : ℝ))
      ≤ (A : ℝ) * Real.log 2 + Real.log ρ) :
    374784 * Cs * Real.exp 3 * (1 / ((calP A G 1 : ℕ) : ℝ)) ≤ constPool ρ Hhi := by
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have h : 0 < calP A G 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  set L : ℝ := Real.log (Real.log (Hhi : ℝ)) with hL
  set E : ℝ := Real.exp (14 * L) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : constPool ρ Hhi = ρ / (376266 * E) := by rw [constPool_def, hE, hL]
  rw [hpool, show (374784 : ℝ) * Cs * Real.exp 3 * (1 / ((calP A G 1 : ℕ) : ℝ))
      = (374784 * Cs * Real.exp 3) / ((calP A G 1 : ℕ) : ℝ) by ring,
    div_le_div_iff₀ hP1pos (by positivity)]
  have hP1exp : ((calP A G 1 : ℕ) : ℝ) = Real.exp ((A : ℝ) * Real.log 2) := by
    rw [← log_calP_one_gen A G, Real.exp_log hP1pos]
  have hρexp : ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
  have hprod : Real.exp (29 + Real.log Cs + 14 * L) = Real.exp 26 * Real.exp 3 * Cs * E := by
    rw [hE, show (29 : ℝ) + Real.log Cs + 14 * L = 26 + (3 + (Real.log Cs + 14 * L)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hCs]
    ring
  calc 374784 * Cs * Real.exp 3 * (376266 * E)
      = 141018476544 * Real.exp 3 * Cs * E := by ring
    _ ≤ Real.exp 26 * Real.exp 3 * Cs * E := by
        have := s15_exp26
        have hp : (0 : ℝ) < Real.exp 3 * Cs * E := by positivity
        nlinarith
    _ = Real.exp (29 + Real.log Cs + 14 * L) := hprod.symm
    _ ≤ Real.exp (Real.log ρ + (A : ℝ) * Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = ρ * ((calP A G 1 : ℕ) : ℝ) := by rw [Real.exp_add, hP1exp, ← hρexp]

/-- **⟦THE `p²` SLOT AT `constPool`, ANCHOR-GENERIC⟧** (`s15_p2_of_budget` at a symbolic
anchor).  The one extra demand is `𝒫₁ ≤ 𝒫₂`, i.e. `e₁ ≤ e₂` at the family in hand. -/
theorem s15_p2_of_budget_gen {A G Hhi : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (hP12 : calP A G 1 ≤ calP A G 2)
    (hbudget : 27 + 14 * Real.log (Real.log (Hhi : ℝ)) ≤ (A : ℝ) * Real.log 2 + Real.log ρ) :
    138240 * (1 / ((calP A G 1 : ℕ) : ℝ) + 1 / ((calP A G 2 : ℕ) : ℝ))
      ≤ 1 / 4 * constPool ρ Hhi := by
  have hP1pos : (0 : ℝ) < ((calP A G 1 : ℕ) : ℝ) := by
    have h : 0 < calP A G 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hP12R : ((calP A G 1 : ℕ) : ℝ) ≤ ((calP A G 2 : ℕ) : ℝ) := by exact_mod_cast hP12
  have hinv : 1 / ((calP A G 2 : ℕ) : ℝ) ≤ 1 / ((calP A G 1 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hP1pos hP12R
  set E : ℝ := Real.exp (14 * Real.log (Real.log (Hhi : ℝ))) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : (1 : ℝ) / 4 * constPool ρ Hhi = ρ / (1505064 * E) := by
    rw [constPool_def, hE]; field_simp; ring
  have hkey : 416120094720 * E ≤ ρ * ((calP A G 1 : ℕ) : ℝ) := by
    have hmul : ρ * ((calP A G 1 : ℕ) : ℝ)
        = Real.exp (Real.log ρ + Real.log ((calP A G 1 : ℕ) : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hρ, Real.exp_log hP1pos]
    calc 416120094720 * E ≤ Real.exp 27 * E := by nlinarith [s15_exp27, hEpos]
      _ = Real.exp (27 + 14 * Real.log (Real.log (Hhi : ℝ))) := by rw [hE, ← Real.exp_add]
      _ ≤ Real.exp (Real.log ρ + Real.log ((calP A G 1 : ℕ) : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [log_calP_one_gen A G]; linarith
      _ = ρ * ((calP A G 1 : ℕ) : ℝ) := hmul.symm
  have hhalf : 276480 * (1 / ((calP A G 1 : ℕ) : ℝ)) ≤ 1 / 4 * constPool ρ Hhi := by
    rw [hpool, show (276480 : ℝ) * (1 / ((calP A G 1 : ℕ) : ℝ))
        = 276480 / ((calP A G 1 : ℕ) : ℝ) by ring,
      div_le_div_iff₀ hP1pos (by positivity)]
    nlinarith [hkey]
  nlinarith [hinv, hhalf, hP1pos]

/-- **⟦THE `level1` SLOT AT `constPool`, AT THE LINEAR DOOR⟧** (`s15_level1_of_budget` twin) —
the register's binding line, read at `A_L(M)`. -/
theorem s15_level1_L_of_budget {M Hhi : ℕ} {ρ : ℝ} (hM : 1 ≤ M) (hρ : 0 < ρ)
    (hbudget : 26 + 14 * Real.log (Real.log (Hhi : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ) :
    14400 * Real.exp 1 ^ 2 * a2Level1_L M ≤ 1 / 4 * constPool ρ Hhi := by
  set L : ℝ := Real.log (Real.log (Hhi : ℝ)) with hL
  set Q : ℝ := Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ)) with hQ
  set D : ℝ := (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 with hD
  set E : ℝ := Real.exp (14 * L) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hpool : (1 : ℝ) / 4 * constPool ρ Hhi = ρ / (1505064 * E) := by
    rw [constPool_def, hE, hL]; field_simp; ring
  rw [s15_a2Level1_L_exp hM, hpool, le_div_iff₀ (by positivity)]
  have hid : 14400 * Real.exp 1 ^ 2 * Real.exp ((1 / 3) * Q - D) * (1505064 * E)
      = 21672921600 * Real.exp (2 + (1 / 3) * Q - D + 14 * L) := by
    rw [hE, show Real.exp 1 ^ 2 = Real.exp 2 by rw [← Real.exp_nat_mul]; norm_num]
    rw [show (2 : ℝ) + (1 / 3) * Q - D + 14 * L = 2 + ((1 / 3) * Q - D) + 14 * L by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hid]
  have hρexp : ρ = Real.exp (Real.log ρ) := (Real.exp_log hρ).symm
  calc 21672921600 * Real.exp (2 + (1 / 3) * Q - D + 14 * L)
      ≤ Real.exp 24 * Real.exp (2 + (1 / 3) * Q - D + 14 * L) := by
        nlinarith [s15_exp24, Real.exp_pos (2 + (1 / 3) * Q - D + 14 * L)]
    _ = Real.exp (26 + (1 / 3) * Q - D + 14 * L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.mpr (by linarith)
    _ = ρ := hρexp.symm

/-! ## §7 — THE SOCKET AT THE LINEAR ROW FLOOR

`M4Assembly.SocketBase` bakes the door in through ONE conjunct, `doorRowFloor M ≤ j`.  The
linear socket asks for `doorRowFloorL M ≤ j`, and since `doorRowFloor M ≤ doorRowFloorL M`
(`⌊log₂M⌋ + 1 ≤ M` again) the linear socket is STRICTLY STRONGER.  So — the mirror image of
§3's supply-side freeness — every landed socket CONSUMER is available at the linear socket
with no re-derivation. -/

/-- `doorRowFloor M ≤ doorRowFloorL M` — the row floor grows under the re-cut. -/
theorem doorRowFloor_le_doorRowFloorL {M : ℕ} (hM : 1 ≤ M) :
    doorRowFloor M ≤ doorRowFloorL M := by
  rw [doorRowFloor, doorRowFloorL]
  exact Nat.mul_le_mul_left _ (Adoor_le_AdoorL hM)

/-- **THE SOCKET BASE AT THE LINEAR DOOR** — `M4Assembly.SocketBase` with the window index
floor at the LINEAR row `doorRowFloorL M = 2^36·M²`. -/
def SocketBaseL (R : ChowlaRegime) (M H L q j A s : ℕ) : Prop :=
  R.Hlo ≤ H ∧ H ≤ R.Hhi ∧ L ≤ H ∧ 0 < q ∧ (q : ℝ) ≤ arcDen 12 H ∧ j ≤ Nat.log 2 L ∧
    doorRowFloorL M ≤ j ∧ 0 < A ∧ 2 ^ j ≤ A ∧ Real.sqrt (H : ℝ) ≤ (A : ℝ) ∧
    (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) ∧ (A : ℝ) ≤ 2 * (R.x : ℝ) ∧ s ≤ L

/-- **⟦THE LINEAR SOCKET IS THE LANDED SOCKET, STRENGTHENED⟧** — every landed socket consumer
applies at the linear socket verbatim. -/
theorem socketBase_of_socketBaseL {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (h : SocketBaseL R M H L q j A s) : SocketBase R M H L q j A s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, le_trans (doorRowFloor_le_doorRowFloorL hM) h7, h8⟩

/-! ## §8 — the `ρ`-frame family at the linear socket

`S15Compose.s15_doorArithFrameRho_at_socket''` at the LINEAR anchor.  Only two lines differ
from the landed proof, and both improve:

* `anchor` is a direct read of the register's own `3.9·10⁹·M`;
* `jfloor` is paid off the LINEAR row floor's own `M` factor
  (`A_L(M) = 2^36·M ≤ doorRowFloorL M ≤ j`) against the anchor bracket — `17.6×` the
  demand, exactly as at the landed cut, but now with `M` where `⌊log₂M⌋+1` stood. -/

/-- **⟦THE `ρ`-FRAME AT THE LINEAR SOCKET⟧** (`s15_doorArithFrameRho_L_at_socket''`). -/
theorem s15_doorArithFrameRho_L_at_socket'' {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    {C₁ : ℕ → ℝ} (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * (M : ℝ))
    (hHreg : 0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : 0 ≤ C₁ (A + s))
    (hb : SocketBaseL R M H L q j A s) :
    DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
      (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hjd : doorRowFloorL M ≤ j := hb.2.2.2.2.2.2.1
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hAx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) := hb.2.2.2.2.2.2.2.2.2.2.1
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  have hlrho : (0 : ℝ) ≤ Real.log (1 / ρ) := log_one_div_nonneg hρ0 hρ1
  have hllH : Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    s13_loglog_le_of_range (R := R) hlo hhi
  have harmA := m4_arith_arm_of_gArmRho hω hHreg.1 hHreg.2 hg hAx
  have hmuA : (356600 : ℝ) ≤ Real.log (Real.log (A : ℝ)) := by
    have := hHreg.2; linarith
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hlogA : (1 : ℝ) < Real.log (A : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hmuA
  have harm := m4_arith_arm_of_shift hApos (by linarith) hAX harmA
  have hlogH0 : (0 : ℝ) < Real.log ((H : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hHreg.1 (by norm_num) hHreg.2).le
  -- ⟦the window index floor, off the LINEAR row floor's OWN `M` factor⟧
  have hjn : (68719476736 : ℝ) * (M : ℝ) ≤ (j : ℝ) := by
    have h1 : AdoorL M ≤ doorRowFloorL M := by
      rw [doorRowFloorL]; exact Nat.le_mul_of_pos_left _ hM
    have h2 : 2 ^ 36 * M ≤ j := le_trans h1 (le_trans (le_of_eq rfl) hjd)
    have h3 : ((2 ^ 36 * M : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h2
    push_cast at h3 ⊢
    linarith
  have hn0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  exact
    { Mpos := hM
      logX_nonneg := log_natCast_nonneg' (A + s)
      logH_nonneg := hHreg.1
      Hfloor := hHreg.2
      Knonneg := le_rfl
      rho_pos := hρ0
      rho_le_one := hρ1
      arm := harm
      anchor := by linarith [hanchor, hllH]
      C1_nonneg := hC1
      M0_window := s13BandM0_window (R := R) (ρ := ρ) (C₁ := C₁) hhi hlogH0
      jfloor := by linarith [hanchor, hllH, hjn, hlrho, hn0, hHreg.2] }

/-- **⟦THE FAMILY FORM, AT THE LINEAR ANCHOR⟧** (`s15_doorArithFrameRho_L_family''`) — the
form `S15Sel''_L.anchor` feeds directly. -/
theorem s15_doorArithFrameRho_L_family'' {R : ChowlaRegime} {M : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hanchor : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * (M : ℝ))
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi → gArmDoorRho 0 0 (R.ω : ℝ) ρ H ≤ (R.x : ℝ))
    (hC1 : ∀ n : ℕ, 0 ≤ C₁ n) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) 0 ρ := by
  intro H L q j A s hb
  exact s15_doorArithFrameRho_L_at_socket'' hM hρ0 hρ1 hanchor (hHreg H hb.1 hb.2.1)
    (hg H hb.1 hb.2.1) (hC1 (A + s)) hb

/-! ## §9 — the pooled grade at the linear door, and the socket's `henv` -/

/-- `M4AssemblyPool.a2DoorGrade_pool` at the linear door. -/
def a2DoorGrade_pool_L (M : ℕ) (X h C₁ M₀ π₀ : ℝ) : ℝ :=
  8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
    + 1787702400 * a2Level1_L M
    + 188133 * π₀
    + 304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
    + 6315000 / h

/-- At `π₀ := (log X)^{−1/500}` the pooled linear grade IS `a2DoorGrade_L` — definitional. -/
theorem a2DoorGrade_pool_L_at_decay (M : ℕ) (X h C₁ M₀ : ℝ) :
    a2DoorGrade_pool_L M X h C₁ M₀ ((Real.log X) ^ (-(1 : ℝ) / 500))
      = a2DoorGrade_L M X h C₁ M₀ := rfl

theorem a2DoorGrade_pool_L_nonneg {M : ℕ} (hM : 1 ≤ M) {X h C₁ M₀ π₀ : ℝ}
    (hX : 0 ≤ Real.log X) (hh : 0 < h) (hπ : 0 ≤ π₀) :
    0 ≤ a2DoorGrade_pool_L M X h C₁ M₀ π₀ := by
  have hlvl := a2Level1_L_nonneg hM
  have h1 : (0 : ℝ) ≤ 8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀) := by positivity
  have h4 : (0 : ℝ) ≤ 304128 * ballSupC ^ 2
      * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2) := by positivity
  have h5 : (0 : ℝ) ≤ 6315000 / h := by positivity
  rw [a2DoorGrade_pool_L]
  linarith

/-- **⟦THE PRICING AT THE POOL, AT `ρ`, AT THE LINEAR DOOR⟧**
(`M4ArithPool.a2DoorGrade_pool_priced_rho` twin).  Budget `ρ/2 + 4·(ρ/8) = ρ`, unchanged. -/
theorem a2DoorGrade_pool_L_priced_rho {M H j : ℕ} {X C₁ M₀ K ρ π₀ : ℝ}
    (hfr : DoorArithFrameRho_L M H j X C₁ M₀ K ρ) (hpool : 0 ≤ π₀)
    (hprice : 188133 * π₀ * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2) :
    arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ ≤ RSanDoorRho ρ H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hLrho : 0 ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by
    rw [hstr]; have := hfr.Hfloor; linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    refine a2DoorGrade_pool_L_nonneg hfr.Mpos (by linarith) ?_ hpool
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have hwt := arcDen_mul_strataResidual_sq_le hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoorRho, le_div_iff₀ (pow_pos hstrpos 2)]
  have hkey : arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
        * strataResidual H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by
    have hid : arcDen 12 H * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀
          * strataResidual H ^ 2
        = (arcDen 12 H * strataResidual H ^ 2)
            * a2DoorGrade_pool_L M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ π₀ := by ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  have h1 := doorGrade_summand1_priced_rho (H := H) hfr.rho_pos hfr.C1_nonneg hfr.logX_nonneg
    hLX hfr.M0_window
  have h2 := doorGrade_summand2_priced_rho_L (H := H) hfr.rho_pos hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_rho_pool (H := H) hprice
  have h4 := doorGrade_summand4_priced_rho (H := H) hfr.rho_pos hLrho hLX hfr.Hfloor
    hfr.armWeak
  have h5 := doorGrade_summand5_priced_rho (H := H) (j := j) hfr.rho_pos hLrho hfr.Hfloor
    hfr.jfloor
  rw [a2DoorGrade_pool_L]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-- **⟦THE ARITHMETIC GATE, DISCHARGED AT `ρ`, AT THE LINEAR DOOR⟧** (`m4_arith_henv_rho_L`) —
`henv` at `RSbig j H := RSanDoorRho ρ H`, under the LINEAR frame at every base the LINEAR
socket reaches. -/
theorem m4_arith_henv_rho_L {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      DoorArithFrameRho_L M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
      arcDen 12 H * a2DoorGrade_L M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSanDoorRho ρ H :=
  fun H L q j A s hb => a2DoorGrade_L_priced_rho (harith H L q j A s hb)

/-! ## §10 — the const-pool gate at the linear door

`M4ClosureRepair.GRowsZeroGate'''` — the four-slot gate the register's `lvl`/`gP1` lines pay —
at `AdoorL`.  §6's anchor-generic budget stones discharge three of the four slots and
`s15_dens_at_zero` the fourth, so the whole gate reduces to the register's own two budget
lines plus the endpoint. -/

/-- `M4ClosureRepair.GRowsZeroGate'''` at the linear door. -/
structure GRowsZeroGate'''_L (M Xd : ℕ) (Ccc π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free, at the linear grade. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1_L M ≤ 1 / 4 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 4 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE, at the linear ladder. -/
  p2 : 138240 * (1 / ((calP (AdoorL M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (AdoorL M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 4 * π₀
  /-- **⟦THE DENSITY SLOT — D3⟧** the debit pinned to `0`. -/
  dens : 5760 * Ccc * (2 / (M : ℝ)) ≤ 1 / 4 * π₀

/-- **⟦THE CONST-POOL GATE AT THE LINEAR DOOR, FROM THE REGISTER'S OWN LINES⟧**
(`gRowsZeroGate'''_L_of_budget`).  `level1` is the register's `lvl` line, `p2` is `lvl`'s
`𝒫`-side weakening (`27 + 14λ₊ ≤ A_L(M)·log 2 + log ρ`, implied by `gP1` at `Ct ≥ 1`),
`endpt` is the base-lower line, `dens` is free at `C_cc = 0`. -/
theorem gRowsZeroGate'''_L_of_budget {M Xd Hhi : ℕ} {ρ : ℝ} (hM : 1 ≤ M) (hXd : 0 < Xd)
    (hρ : 0 < ρ)
    (hlvl : 26 + 14 * Real.log (Real.log (Hhi : ℝ))
        + (1 / 3) * Real.log (Real.log ((calQK (AdoorL M) (3072 * M) M 1 : ℕ) : ℝ))
      ≤ (1 / 12) * ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ)
    (hp2 : 27 + 14 * Real.log (Real.log (Hhi : ℝ))
      ≤ ((AdoorL M : ℕ) : ℝ) * Real.log 2 + Real.log ρ)
    (hend : 26 + 14 * Real.log (Real.log ((Hhi : ℕ) : ℝ)) + (-Real.log ρ)
      ≤ Real.log ((Xd : ℕ) : ℝ)) :
    GRowsZeroGate'''_L M Xd 0 (constPool ρ Hhi) where
  level1 := s15_level1_L_of_budget hM hρ hlvl
  endpt := s15_endpt_at_constPool hXd hρ hend
  p2 := s15_p2_of_budget_gen hρ (s15_calP_L_one_le_two hM) hp2
  dens := s15_dens_at_zero hρ.le

end Salt.MR

end
