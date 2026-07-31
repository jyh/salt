/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithZero
import Salt.MR.M4AssemblyPrime

/-!
# ⟦R3-A — THE LAST `μ/500` GONE⟧ (`M4ArithPrime`)

`M4ArithZero` §5 discharges the `gRows` gate at ⟦R1⟧'s row sum against the DECAYING target
`(log X_d)^{−1/500}`; that target is why `GRowsZeroGate'`'s three fields still carry a
`μ/500` on the left (`μ = loglog X_d`).  ⟦R2⟧ replaces the target by a FREE pool `π₀`.  At
the join, the `μ` has nothing left to pay for:

  landed `GRowsZeroGate`   `p2 : μ·(1 + 1/500) + 15 ≤ (log 2)·Adoor M`
  ⟦R1⟧   `GRowsZeroGate'`  `p2 : μ/500          + 15 ≤ (log 2)·Adoor M`
  ⟦JOIN⟧ `GRowsZeroGate''` `p2 : 138240·(1/𝒫₁ + 1/𝒫₂) ≤ π₀/3`   — **no `μ` at all**

R1 removed the `μ`-coefficient `1` (the `log₂(2X_d)` numerator); R2 removes the residual
`1/500` (the decaying right-hand side).  Neither alone suffices — this is the K4-CENSUS's
"R1+R2 alone close nothing" at one concrete field.

## ⟦THE FINAL GATE TABLE⟧

`GRowsZeroGate''` is stated DIRECTLY, not in log form: with the target a free constant there
is no exponential to take logs against, so the three slots are the three summands of
`a2RowsSum'_door_decomp` against `π₀/3`, and two of the three are BASE-FREE:

| slot | statement | reads the base? |
|---|---|---|
| `level1` | `14400·e²·a2Level1 M ≤ π₀/3` | **no** |
| `endpt` | `5760·(2e+2)/X_d ≤ π₀/3` | yes — a base-LOWER demand |
| `p2` | `138240·(1/𝒫₁ + 1/𝒫₂) ≤ π₀/3` | **no** |

`endpt` is the honest residue `M4ArithZero.gRows_at_socketBase` already carries at the base;
it is a demand that `X_d` be LARGE, never a cap.

## Contents

* §1 `GRowsZeroGate''` + `gRows_zero_of_gate''` — the `μ`-free discharge;
* §2 `DoorBaseFrame` + `doorFuseFrame_pool'_of_gates` — the ten-field frame from the six
  base-side fields and four `μ`-free gates;
* §3 `m4_chiSummedFreeRow_of_doorAssembly_join` — **THE EXIT AT THE μ-FREE FORMS**.

Additive: no landed declaration is touched.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE `gRows` GATE WITH NO `μ` IN IT -/

/-- **⟦THE `gRows` GATE AT THE JOIN⟧** (`GRowsZeroGate''`) — what `DoorFuseFrame_pool'.gRows`
asks at `C_p = 0`, once ⟦R1⟧ has made the `p²` slot `X_d`-free and ⟦R2⟧ has made the target a
free pool.  Three slots, `1/3` of the pool each, and **no `loglog X_d` anywhere**.

* `level1` — `14400·e²·a2Level1 M ≤ π₀/3`.  Base-free: `a2Level1 M = (log Q₁)^{1/3}/𝒫₁^{1/12}`
  is an `M`-object.  Met by taking `Adoor M` large (the same axis as ⟦gate 8⟧);
* `endpt` — `5760·(2e+2)/X_d ≤ π₀/3`.  The one base-reading slot, and it reads it in the
  SAFE direction: `1/X_d → 0`;
* `p2` — `138240·(1/𝒫₁ + 1/𝒫₂) ≤ π₀/3`.  Base-free — **this is ⟦R1⟧'s whole content**: the
  landed slot was `92160·log₂(2X_d)·(1/𝒫₁ + 1/𝒫₂)`, which GREW with the base. -/
structure GRowsZeroGate'' (M Xd : ℕ) (π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1 M ≤ 1 / 3 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 3 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE. -/
  p2 : 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
        + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * π₀

/-- **⟦THE RESIDUAL, PRICED AT THE JOIN⟧** (`gRows_zero_of_gate''`):

  `5760·(a2RowsSum' M X_d + 0·(2/M)) ≤ π₀`

from `GRowsZeroGate''` alone — one application of `M4ArithZero.a2RowsSum'_door_decomp` and
the three slots summed.  No `slot_of_log_gate`, no `rpow`, no `μ`: with the target a free
constant the whole log-form apparatus of §4/§5 evaporates. -/
theorem gRows_zero_of_gate'' {M Xd : ℕ} {π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate'' M Xd π₀) :
    5760 * (a2RowsSum' M Xd + (0 : ℝ) * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1 M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1 M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2]

/-! ## §2 — THE TEN-FIELD FRAME FROM THE `μ`-FREE GATES -/

/-- **THE SIX BASE-SIDE FRAME FIELDS** (`DoorBaseFrame`) — the grade-blind half of
`DoorFuseFrame_pool'`, bundled so the discharge below states only the FOUR gates that carry
mathematical content.  Every field is `M4Assembly.DoorFuseFrame`'s verbatim. -/
structure DoorBaseFrame (Xd j : ℕ) : Prop where
  /-- `e ≤ X_d`. -/
  X_exp : Real.exp 1 ≤ ((Xd : ℕ) : ℝ)
  /-- `3 ≤ X_d`. -/
  X_three : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)
  /-- `4 ≤ 2^j`. -/
  h_four : (4 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ)
  /-- Lemma 14's window frame. -/
  h_window : ((2 ^ j : ℕ) : ℝ)
    ≤ ((Xd : ℕ) : ℝ) * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 / 5 : ℝ))
  /-- The annulus gate at the family's bottom height. -/
  tann : TannGate ((Xd : ℕ) : ℝ) (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ)))
  /-- The `h`-ceiling. -/
  ceil5 : 5 ≤ Real.log (Real.log (2 * (((Xd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ))))

/-- `3 ≤ X_d` gives `1 ≤ log X_d` — the one arithmetic step the two pool-side fields need. -/
private lemma a3_one_le_log_of_three_le {Xd : ℕ} (h : (3 : ℝ) ≤ ((Xd : ℕ) : ℝ)) :
    (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := by
  have h3 : Real.log 3 ≤ Real.log ((Xd : ℕ) : ℝ) := Real.log_le_log (by norm_num) h
  have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ (3 : ℝ))
    rwa [Real.log_exp] at this
  linarith

/-- **⟦THE FRAME AT THE JOIN, FROM FOUR GATES⟧** (`doorFuseFrame_pool'_of_gates`).  The ten
fields of `DoorFuseFrame_pool'` at `C_p = 0`, from the six base-side fields plus:

* `hgP1` — `374784·C_s·e³/𝒫₁ ≤ π₀`.  **Base-free** (at the pool the landed decaying cap, and
  with it `M4SocketDischarge.gP1_of_le`'s antitone collapse, is no longer needed);
* `hg` — `GRowsZeroGate''`, i.e. the `μ`-free `gRows` of §1;
* `hone` — `1 ≤ π₀`, which with `hε : ε ≤ θ₂₉₃` discharges `eps_pool`
  (`(log X_d)^{−θ₂₉₃+ε} ≤ 1` at `1 ≤ log X_d`, a nonpositive exponent);
* `hL4096` — `4096 ≤ (log X_d)^{1−1/250}`, which with `hone` discharges `band_pool` through
  the landed absorption `4096·(log X_d)^{−1+1/500} ≤ (log X_d)^{−1/500} ≤ 1`.

⟦THE READING⟧ every remaining demand is either base-free or a base-LOWER threshold.  No
field caps the base, so the frame is satisfiable on the socket's whole capped range without
any antitone collapse. -/
theorem doorFuseFrame_pool'_of_gates {M Xd j : ℕ} {Cs ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate'' M Xd π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool' M Xd j Cs 0 ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate'' hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := a3_one_le_log_of_three_le hb.X_three
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := a3_one_le_log_of_three_le hb.X_three
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-! ## §3 — THE EXIT AT THE `μ`-FREE FORMS -/

/-- **⟦THE JOINED CHAIN FEEDS THE FRAMES⟧** (`m4_chiSummedFreeRow_of_doorAssembly_join`) —
⟦item 11⟧ of `m4_second_road` from gates that read the base only from BELOW.

THE COMPLETE GATE LIST, per socket base:

* `hbase` — the six base-side frame fields (`DoorBaseFrame`);
* `hgP1` — `374784·C_s(X_d)·e³/𝒫₁ ≤ π₀(X_d)`, base-free;
* `hgRows` — `GRowsZeroGate''`, the `μ`-free `gRows` (§1);
* `hone` — `1 ≤ π₀`;
* `heps` — `ε ≤ θ₂₉₃` (the `𝒰`-leg exponent, otherwise FREE — ⟦R2⟧'s gift);
* `hL4096` — `4096 ≤ (log X_d)^{1−1/250}`, a base-LOWER threshold;
* `hrows` — the row family at `ThmA2Prime.a2Mrow'`, supplied by
  `A3Middle.a2Rows_of_capfree3_end'`;
* `hband` — `M4Assembly`'s own band supplier, unchanged;
* `henv` — the door arithmetic against `M4AssemblyPool.a2DoorGrade_pool`.

The density constant is pinned at `C_p = 0` (⟦M4ArithZero⟧'s zero-density reading), which is
what makes `gRows` base-free; every other slot is `M4AssemblyPrime`'s exit verbatim. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join {R : ChowlaRegime} {M : ℕ}
    {Cs C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate'' M (A + s) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow' (Cs (A + s)) 0 M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool' (Cs := Cs) (Ccc := fun _ => 0) (C₁ := C₁)
    (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband (fun A => le_trans zero_le_one (hone A))
    henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

/-! ## §GK — the G-lever twin

The `μ`-free join at `G := s13GK K M` (`GLever`), `(K : ℕ)` first.

⟦K-INVARIANT, KEEPS ITS LANDED NAME⟧ `DoorBaseFrame` (:109) reads no door ladder — six purely
base-side fields — and `a3_one_le_log_of_three_le` is generic; both are reused VERBATIM.
`a2Level1 M` is level 1, so `GRowsZeroGate''`'s `level1` and `endpt` fields do not move either;
only its `p2` field, which reads `𝒫₁` and `𝒫₂` directly, is rewritten at the levered base. -/

/-- `GRowsZeroGate''` (:71), at the lever.  `level1` and `endpt` are byte-identical; `p2` moves
with `𝒫₂` (and `𝒫₁`, which is LEVEL 1 and therefore the same symbol). -/
structure GRowsZeroGate''_gk (K : ℕ) (M Xd : ℕ) (π₀ : ℝ) : Prop where
  /-- ⟦THE LEVEL-1 SLOT⟧ base-free. -/
  level1 : 14400 * Real.exp 1 ^ 2 * a2Level1 M ≤ 1 / 3 * π₀
  /-- ⟦THE ENDPOINT SLOT⟧ the only base-reading slot, and base-LOWER. -/
  endpt : 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ)) ≤ 1 / 3 * π₀
  /-- ⟦THE `p²` SLOT, R1⟧ `X_d`-FREE, at the levered ladder. -/
  p2 : 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
        + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
      ≤ 1 / 3 * π₀

/-- `gRows_zero_of_gate''` (:88), at the lever — `M4ArithZero.a2RowsSum'_door_decomp_gk` and
the three slots summed, exactly as landed. -/
theorem gRows_zero_of_gate''_gk (K : ℕ) {M Xd : ℕ} {π₀ : ℝ} (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hg : GRowsZeroGate''_gk K M Xd π₀) :
    5760 * (a2RowsSum'_gk K M Xd + (0 : ℝ) * (2 / (M : ℝ))) ≤ π₀ := by
  rw [a2RowsSum'_door_decomp_gk K hM hXd]
  have hid : 5760 * (5 / 2 * Real.exp 1 ^ 2 * a2Level1 M
        + (2 * Real.exp 1 + 2) / (Xd : ℝ)
        + 24 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ))
        + (0 : ℝ) * (2 / (M : ℝ)))
      = 14400 * Real.exp 1 ^ 2 * a2Level1 M
        + 5760 * ((2 * Real.exp 1 + 2) / (Xd : ℝ))
        + 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)
              + 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ)) := by ring
  rw [hid]
  linarith [hg.level1, hg.endpt, hg.p2]

/-- `doorFuseFrame_pool'_of_gates` (:148), at the lever. -/
theorem doorFuseFrame_pool'_of_gates_gk (K : ℕ) {M Xd j : ℕ} {Cs ε π₀ : ℝ}
    (hb : DoorBaseFrame Xd j)
    (hgP1 : 374784 * Cs * Real.exp 3 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀)
    (hg : GRowsZeroGate''_gk K M Xd π₀)
    (hone : (1 : ℝ) ≤ π₀)
    (hε : ε ≤ theta293)
    (hM : 1 ≤ M) (hXd : 1 ≤ Xd)
    (hL4096 : (4096 : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)) :
    DoorFuseFrame_pool'_gk K M Xd j Cs 0 ε π₀ where
  X_exp := hb.X_exp
  X_three := hb.X_three
  h_four := hb.h_four
  h_window := hb.h_window
  tann := hb.tann
  ceil5 := hb.ceil5
  gP1 := hgP1
  gRows := gRows_zero_of_gate''_gk K hM hXd hg
  eps_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := a3_one_le_log_of_three_le hb.X_three
    have hle : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-theta293 + ε)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      simpa using this
    linarith
  band_pool := by
    have hL1 : (1 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ) := a3_one_le_log_of_three_le hb.X_three
    have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
    have habs : 4096 * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500)
        ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) := by
      have hsp : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          = (Real.log ((Xd : ℕ) : ℝ)) ^ (1 - (1 : ℝ) / 250)
            * (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) + 1 / 500) := by
        rw [← Real.rpow_add hL0]; norm_num
      rw [hsp]
      exact mul_le_mul_of_nonneg_right hL4096 (le_of_lt (Real.rpow_pos_of_pos hL0 _))
    have hone' : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500) ≤ 1 := by
      have : (Real.log ((Xd : ℕ) : ℝ)) ^ (-(1 : ℝ) / 500)
          ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      simpa using this
    linarith

/-- `m4_chiSummedFreeRow_of_doorAssembly_join` (:211), at the lever. -/
theorem m4_chiSummedFreeRow_of_doorAssembly_join_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ}
    {Cs C₁ M₀ ε π₀ : ℕ → ℝ} {RSbig : ℕ → ℕ → ℝ}
    (hM : 1 ≤ M)
    (hbase : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → DoorBaseFrame (A + s) j)
    (hgP1 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      374784 * Cs (A + s) * Real.exp 3
          * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) ≤ π₀ (A + s))
    (hgRows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate''_gk K M (A + s) (π₀ (A + s)))
    (hone : ∀ A : ℕ, (1 : ℝ) ≤ π₀ A)
    (heps : ∀ A : ℕ, ε A ≤ theta293)
    (hL4096 : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      (4096 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - (1 : ℝ) / 250))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff_gk K χ M)) t‖ ^ 2)
          ≤ a2Mrow'_gk K (Cs (A + s)) 0 M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (henv : ∀ H j A s : ℕ, doorRowFloor M ≤ j →
      arcDen 12 H * a2DoorGrade_pool_gk K M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s)) (π₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRow_gk K R M (m4ChiRowGraded M RSbig) := by
  refine m4_chiSummedFreeRow_of_doorAssembly_pool'_gk K (Cs := Cs) (Ccc := fun _ => 0)
    (C₁ := C₁) (M₀ := M₀) (ε := ε) (π₀ := π₀) hM ?_ hrows hband
    (fun A => le_trans zero_le_one (hone A)) henv
  intro H L q j A s hb
  have hXd : 1 ≤ A + s := by
    have hA : 0 < A := hb.2.2.2.2.2.2.2.1
    omega
  exact doorFuseFrame_pool'_of_gates_gk K (hbase H L q j A s hb) (hgP1 H L q j A s hb)
    (hgRows H L q j A s hb) (hone (A + s)) (heps (A + s)) hM hXd (hL4096 H L q j A s hb)

end Salt.MR

-- #audit (temporary)
