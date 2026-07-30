/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4SocketFused
import Salt.MR.M4Assembly
import Salt.MR.RbdSupply
import Salt.MR.USetPrice
import Salt.MR.HybridMoments

/-!
# ⟦THE hcap WIRE — the A3 capstone family instantiated at the door pin⟧ (`M4CapWire`)

Design provenance: **REF-SOCKET-2's 16-item S11 checklist, item 14** (flags, 2026-07-30) —
the LAST analytic wave before the S11 compose.  `M4SocketFused.m4_socket_discharged_fused`
carries exactly one un-instantiated analytic binder, `hcap`: the A3 capstone family
(`M4RowsChi.m4_rowChi_capstone`) read at the door pin `t₁ ≡ 0`, `S ≡ 0`.  This file
instantiates it.

**PURELY ADDITIVE.**  No landed declaration is touched; the file is a leaf.

## ⟦THE PIN — how the capstone is read at the door⟧

`m4_rowChi_capstone`'s conclusion is the `hcap` binder's conclusion at

| capstone slot | door value |
|---|---|
| `X` | `((A + s : ℕ) : ℝ)` (the socket's base) |
| `Tann` | `2 * T` (the `hcap` slot's own height) |
| `N` | `2 * (A + s)` |
| `a` | `winCutH (A + s) (doorCoeffU M)` — the UNTWISTED door row datum |
| `c` | `cU` (the fused terminal's own coefficient binder) |
| `Pseq`, `Qseq` | `calP (Adoor M) (3072M)`, `calQK (Adoor M) (3072M) M` |
| `Hseq`, `αseq`, `J` | `calH (H1door M)`, `mrAlpha (1/12)`, `2` |
| `t₁` | `fun _ => 0` (the door pin) |
| `S` | `fun _ => 0` (`M4Assembly.m4_hSup_door_at_zero`) |
| `εr` | `ε (A + s)` |

The datum identification is `M4Assembly.chiBarCoeff_doorRowDatum`:
`chiBarCoeff q χ (winCutH X_d (doorCoeffU M)) = winCutH X_d (doorChiCoeff χ M)`, which is what
turns the capstone's `spoly N (χ̄a)` into the door's
`spoly (2(A+s)) (winCutH (A+s) (doorChiCoeff χ M))`.

⟦FOUR LOG SCALES, KEPT APART⟧ the capstone speaks `(q, 2T)` (its razor/floor family) and
`X = A + s` (its `H₈₃`/`P₈₃`/`Q₈₃` frame); the SOCKET speaks `H` (the regime's length) and
`arcDen 12 H` (the modulus ledger).  Nothing here identifies them: `H` and `arcDen 12 H` enter
only through `SocketBase`, and the capstone's `H83 ((A+s : ℕ) : ℝ) theta293` is a `log(A+s)`
object.  Likewise the CHARACTER DEBIT exponent `εd` (`q^{2α} ≤ X^{εd}`) and the REMAINDER
absorption exponent `εr = ε (A+s)` are separate fields and are never identified.

## ⟦WHAT IS DISCHARGED HERE, AND WHAT IS CARRIED⟧

DISCHARGED in-file (six of the capstone's binders):

* `hc1` — from the fused terminal's own `∀ p, ‖cU p‖ ≤ 1`;
* `hTgate` — from the `hcap` slot's own `TannGate (A+s) (2T)` antecedent;
* `hXN`, `hN2` — the pins `X ≤ N = 2(A+s) ≤ 2X`, arithmetic;
* `hsupp` — `∀ n ≤ X, a n = 0`, from `M4DoorRow.winCutH_supp0`;
* `hSup` — the ball leg at `S ≡ 0`, from `M4Assembly.m4_hSup_door_at_zero` (needs
  `1 < log X`, supplied by the bundle's `logX_four`).

CARRIED as the named bundle `DoorCapBase` (§2), one structure the S11 spine instantiates
alongside the existing five (`DoorFuseFrame`, `DoorRowZeroBase`, `DoorBandBase`,
`DoorArithFrameRho`, `SocketBase`).

## ⟦THE THREE OPEN SUPPLY OBJECTS — the wires and the ONE mismatch⟧

* **(a) `Rbd`** — WIRED (§4a).  `RbdSupply.rbd_binder_of_doorSocket_free` at
  `Pseq/Qseq/J := calP (Adoor M) (3072M) / calQK (Adoor M) (3072M) M / 2` produces the
  capstone's `hR` binder VERBATIM at `b := doorCoeffU M`, the only edits being the
  `(χ, j)` quantifier swap and the pair-set-to-fibre read.  Its own gates ride:
  the `∀χ` door socket at the `_vt` floor (`RbdSupply.m4_supplier_all_chi`, whose `K` is a
  `cffKVt`-genre symbolic constant — **NOT** `DoorArithFrameRho`'s `K`; the two coincide
  nowhere and are kept apart), and `Rrad + T ≤ |t₁|` which is free at the socket's free `t₁`.
* **(b) `KS`** — WIRED (§4b).  `USetPrice.KS_priced` at `δ' := (log X)^{−100}` gives the
  capstone's `hKS` binder at the explicit budget `KS = 20512·(log X)^{−200}·(1 + log 2T)`,
  under the co-factor-length gates `2 ≤ m₀ j ≤ ramRbot`, `ramRrange ⊆ [1, Mr]`,
  `Mr ≤ 4(m₀ j − 1)`.  The remaining `KS_gate`
  (`32(log X)^{2+2θ}·KS ≤ (log X)^{−θ}`) is arithmetic on the spine's own scale and stays a
  bundle field.
* **(c) `E`** — **NOT WIRED; the mismatch is reported, not massaged.**  The brief named
  `HybridMoments.lemma12_meansq_all_chi` (`:712`); that theorem bounds
  `∑_χ ∫ ‖spoly N (χ̄a)‖²`, NOT the capstone's `∑_χ ∫ ‖ramErr …‖²`.  The shape-correct
  supplier is `HybridMoments.ramErr_meanSq_all_chi` (`:604`), and §4c wires it — but it asks
  the **GLOBAL** block factorization `hcoef : ∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬p∣m →
  a (p·m) = b m · cf p`, which is precisely the contract
  `M4Assembly.doorRows_global_hcoef_kills_block` shows is fatal at a WINDOW-CUT datum — and
  the door's `a = winCutH (A+s) (doorCoeffU M)` is window-cut.  So §4c is stated
  CONDITIONALLY on `hcoef` and `E_binder` stays a carried field of the bundle.  This is the
  same wall `M4Assembly`'s header records for `hrowsSum`, met a second time one level down.

## ⟦THE COMPOSITE⟧

`m4_socket_discharged_capwired` is `m4_socket_discharged_fused` with `hcap` GONE, replaced by
the `DoorCapBase` family and with `t₁` pinned to `fun _ _ => 0` (the door pin — `t₁` occurs
nowhere else in the fused statement, so the binder simply leaves).  Five constants join `Ct`
in the leading existential: `Cq, cs, T₀, Kq, Ks`, the capstone's own, because four bundle
fields mention them (`Cq_gate`, `gate`, `T₀_Tann`, `floor3`, `floor4`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE DOOR'S UNTWISTED ROW DATUM, AND ITS PINS

`M4Assembly.doorCoeffU` is the untwisted door coefficient; the capstone's datum slot `a` is
its half-open dyadic cut.  Three of the capstone's binders are facts about it. -/

/-- `doorCoeffU` unfolded — the shape `RbdSupply.rbd_binder_of_doorSocket_free` produces. -/
theorem doorCoeffU_eq (M : ℕ) :
    doorCoeffU M
      = memSCoeff (calP (Adoor M) (3072 * M)) (calQK (Adoor M) (3072 * M) M) 2 liouvilleC :=
  rfl

/-- The untwisted door coefficient is `1`-bounded (`memSCoeff` only deletes terms). -/
theorem norm_doorCoeffU_le_one (M n : ℕ) : ‖doorCoeffU M n‖ ≤ 1 :=
  norm_memSCoeff_le_one liouvilleC_norm_le_one _ _ 2 n

/-- The capstone's `hsupp` at the door row datum (untwisted). -/
theorem doorRowDatumU_supp0 (M Nd : ℕ) {n : ℕ} (h : (n : ℝ) ≤ ((Nd : ℕ) : ℝ)) :
    winCutH Nd (doorCoeffU M) n = 0 :=
  winCutH_supp0 _ h

/-- The door row datum is `1`-bounded. -/
theorem norm_doorRowDatumU_le_one (M Nd n : ℕ) : ‖winCutH Nd (doorCoeffU M) n‖ ≤ 1 :=
  norm_winCutH_le (norm_doorCoeffU_le_one M) n

/-- The capstone's `hXN` at the door pin `N = 2X_d`. -/
theorem doorCap_hXN (Nd : ℕ) : ((Nd : ℕ) : ℝ) ≤ (((2 * Nd : ℕ)) : ℝ) := by
  push_cast
  have : (0 : ℝ) ≤ (Nd : ℝ) := Nat.cast_nonneg Nd
  linarith

/-- The capstone's `hN2` at the door pin `N = 2X_d` (an equality, read as `≤`). -/
theorem doorCap_hN2 (Nd : ℕ) : (((2 * Nd : ℕ)) : ℝ) ≤ 2 * ((Nd : ℕ) : ℝ) := by
  push_cast
  exact le_rfl

/-! ## §2 — ⟦THE RESIDUE BUNDLE⟧ `DoorCapBase`

Every binder of `M4RowsChi.m4_rowChi_capstone` that §3 does NOT discharge, at the door pin,
as ONE per-base structure.  The parameters are the capstone's own free objects at that pin:

* `Cq cs T₀ Kq Ks` — the capstone's five existential constants (exported by §3);
* `M` — the door parameter; `Nd` — the socket's base `A + s` (so `X = (Nd : ℝ)`,
  `N = 2·Nd`, and the datum is `winCutH Nd (doorCoeffU M)`);
* `q` — the modulus; `Xd P Q Mr Jb` — the ram-block data (dyadic parameter, block window,
  co-factor range cap, the razor's designated level);
* `b cf` — the co-factor and Lemma-12 coefficient sequences (`b := doorCoeffU M` at the
  wired supply side, §4a/§4b);
* `Tann` — the annulus height (`= 2T` at the slot); `VJ V Lr η` — the razor's four reals;
* `εd` — the CHARACTER DEBIT exponent; `εr` — the REMAINDER absorption exponent
  (`= ε (A+s)` at the slot).  **They are never identified.**
* `Rbd CR KS E EP2` — the three open supply objects and their two companions.

⟦THE FIELD LIST — 58 fields in six groups (21 + 9 + 3 + 13 + 4 + 8)⟧

* **(A) the razor family at `(q, Tann)`** — `Jb_lo`, `Jb_hi`, `Hseq_two`, `alpha_nonneg`,
  `Tann_one`, `qTann_one`, `P_three`, `PQ`, `QTann`, `kappa30Q`, `loglog5`, `VJ_bound`,
  `alpha_eta`, `eta_half`, `Tann_X`, `X_pos`, `debit`, `logX_pos`, `q_logX`, `V_one`,
  `V_inv` (21);
* **(B) the socket floor at `(q, Tann)`** — `T0_Tann`, `floor1`, `floor2`, `floor3`,
  `floor4`, `logqT_one`, `logqT_L`, `L_exp`, `logV_L` (9);
* **(C) the `X`-side frame** — `H83_two`, `logX_exp`, `logX_four` (3);
* **(D) the ram-block frame** — `cf_one`, `P_low`, `Q_pos`, `Q_high`, `range`, `budget`,
  `Hj`, `B3`, `BT`, `kappa30`, `BT10`, `WL`, `gate` (13);
* **(E) the co-factor bound and its grade** — `Rbd_nonneg`, `Rbd_grade`, `Cq_gate`,
  `Rbd_binder` (4) — supplier §4a;
* **(F) the `𝒯_S` budget and Lemma 12's error row** — `KS_nonneg`, `KS_binder`, `KS_gate`
  (supplier §4b), `epsr_nonneg`, `abs8640`, `EP2_gate`, `E_row`, `E_binder` (supplier §4c,
  conditional — see the header's mismatch report) (8). -/
structure DoorCapBase (Cq cs T₀ Kq Ks : ℝ) (M Nd q Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
    (Tann VJ V Lr η εd εr Rbd CR KS E EP2 : ℝ) : Prop where
  -- ⟦(A) THE GRADED RAZOR FAMILY AT `(q, Tann)`⟧
  /-- `1 ≤ Jb` — the razor's designated level is a level. -/
  Jb_lo : 1 ≤ Jb
  /-- `Jb ≤ J = 2` — the door's partition has two levels. -/
  Jb_hi : Jb ≤ 2
  /-- `2 ≤ H_Jb` at the door's calibrated `H`-family. -/
  Hseq_two : 2 ≤ calH (H1door M) Jb
  /-- `0 ≤ α_Jb` at the door's `mrAlpha (1/12)`. -/
  alpha_nonneg : 0 ≤ mrAlpha (1 / 12) Jb
  /-- `1 ≤ T_ann`. -/
  Tann_one : 1 ≤ Tann
  /-- `1 < q·T_ann` — the razor's modulus-height scale. -/
  qTann_one : 1 < (q : ℝ) * Tann
  /-- `3 ≤ P_Jb`. -/
  P_three : 3 ≤ calP (Adoor M) (3072 * M) Jb
  /-- `P_Jb ≤ Q_Jb`. -/
  PQ : calP (Adoor M) (3072 * M) Jb ≤ calQK (Adoor M) (3072 * M) M Jb
  /-- `Q_Jb ≤ q·T_ann` — the block top under the razor's scale. -/
  QTann : ((calQK (Adoor M) (3072 * M) M Jb : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- `30 ≤ log(q·T_ann)/log Q_Jb` — ⟦MR (21)⟧'s κ-gate at the designated level. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (Adoor M) (3072 * M) M Jb : ℕ) : ℝ)
  /-- `5 ≤ loglog(q·T_ann)`. -/
  loglog5 : 5 ≤ Real.log (Real.log ((q : ℝ) * Tann))
  /-- The razor's `V_J` cap over the designated block's `H·log p` grid. -/
  VJ_bound : ∀ v ∈ ramI (calH (H1door M) Jb) (calP (Adoor M) (3072 * M) Jb)
      (calQK (Adoor M) (3072 * M) M Jb),
    Real.exp (mrAlpha (1 / 12) Jb * (v : ℝ) / calH (H1door M) Jb) ≤ VJ
  /-- `α_Jb ≤ 1/4 − η` — the razor's exponent room. -/
  alpha_eta : mrAlpha (1 / 12) Jb ≤ 1 / 4 - η
  /-- `2η ≤ 1`. -/
  eta_half : 2 * η ≤ 1
  /-- `T_ann ≤ X` — the annulus sits under the base. -/
  Tann_X : Tann ≤ ((Nd : ℕ) : ℝ)
  /-- `0 < X`. -/
  X_pos : (0 : ℝ) < ((Nd : ℕ) : ℝ)
  /-- ⟦THE CHARACTER DEBIT⟧ `q^{2α_Jb} ≤ X^{εd}` — spent inside the razor's budget. -/
  debit : (q : ℝ) ^ (2 * mrAlpha (1 / 12) Jb) ≤ ((Nd : ℕ) : ℝ) ^ εd
  /-- `0 < log X`. -/
  logX_pos : 0 < Real.log ((Nd : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — the modulus gate the `φ(q)` repayment is charged to. -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  /-- `1 ≤ V`. -/
  V_one : 1 ≤ V
  /-- `V⁻¹ ≤ (log X)^{−106}` — the level pin. -/
  V_inv : V⁻¹ ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-106 : ℝ)
  -- ⟦(B) THE PER-`(q, T)` SOCKET FLOOR⟧
  /-- `T₀ ≤ T_ann` — the capstone's own height floor. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1 — the VK strip constant against `loglog(5T+1)`. -/
  floor1 : 8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 2. -/
  floor2 : 8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
    ≤ Real.log (Real.log (5 * Tann + 1))
  /-- Floor gate 3 — the `Kq` arm. -/
  floor3 : Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
    ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)
  /-- Floor gate 4 — the `Ks` arm. -/
  floor4 : (q : ℝ) ^ ((1 : ℝ) / 16)
    ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
  /-- `1 ≤ log(q·T_ann)`. -/
  logqT_one : 1 ≤ Real.log ((q : ℝ) * Tann)
  /-- `log(q·T_ann) ≤ L`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ Lr
  /-- `e ≤ L`. -/
  L_exp : Real.exp 1 ≤ Lr
  /-- `log V ≤ 100·log L`. -/
  logV_L : Real.log V ≤ 100 * Real.log Lr
  -- ⟦(C) THE `X`-SIDE FRAME⟧
  /-- `2 ≤ H₈₃ X θ₂₉₃`. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  /-- `e ≤ log X`. -/
  logX_exp : Real.exp 1 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `4 ≤ log X`. -/
  logX_four : 4 ≤ Real.log ((Nd : ℕ) : ℝ)
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `‖cf n‖ ≤ 1` — Lemma 12's prime-side coefficient. -/
  cf_one : ∀ n : ℕ, ‖cf n‖ ≤ 1
  /-- `P₈₃ X θ₂₉₃ ≤ P`. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- The co-factor range sits in `[1, Mr]` at every block. -/
  range : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd j ⊆ Finset.Icc 1 Mr
  /-- ⟦THE GRADED BUDGET⟧ `thinBundleGChi(q·T_ann)·X^{1−2η+εd} ≤ Mr`. -/
  budget : thinBundleGChi ((q : ℝ) * Tann) VJ (calH (H1door M) Jb)
      (calP (Adoor M) (3072 * M) Jb) (calQK (Adoor M) (3072 * M) M Jb)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * η + εd) ≤ (Mr : ℝ)
  /-- `H₈₃ ≤ j` on the grid. -/
  Hj : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ (j : ℝ)
  /-- `3 ≤ Q_base` on the grid. -/
  B3 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    3 ≤ ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j
  /-- `Q_base ≤ q·T_ann` on the grid. -/
  BT : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ (q : ℝ) * Tann
  /-- The κ-gate on the grid. -/
  kappa30 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)
  /-- `Q_base ≤ T_ann^{10}` on the grid. -/
  BT10 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j : ℝ) ≤ Tann ^ 10
  /-- `log Q_base ≤ L` on the grid. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ Lr
  /-- The `cs`-gate on the grid. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * Lr * Lr ^ ((3 : ℝ) / 4) * (Real.log Lr) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧ (supplier §4a)
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧ `Rbd ≤ CR·(log X)^{−ρ₂₉₃}`. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧ `1728·Cq·CR² ≤ (log X)^{2θ₂₉₃}`. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` BINDER⟧ the co-factor polynomial is `≤ Rbd` off the door ball. -/
  Rbd_binder : ∀ χ : DirichletCharacter ℂ q,
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ∀ t ∈ seamAnn ((Nd : ℕ) : ℝ) Tann \ seamBall ((Nd : ℕ) : ℝ) 0,
      ‖ramR (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j (chiBarCoeff q χ b) t‖ ≤ Rbd
  -- ⟦(F) THE `𝒯_S` BUDGET AND LEMMA 12's ERROR ROW⟧ (suppliers §4b, §4c)
  /-- `0 ≤ KS`. -/
  KS_nonneg : 0 ≤ KS
  /-- ⟦THE `𝒯_S` BUDGET BINDER⟧ (supplier `USetPrice.KS_priced`, §4b). -/
  KS_binder : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    5128 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (Mr : ℝ) * (1 + Real.log (2 * Tann))
        * (∑ m ∈ Finset.Icc 1 Mr,
            ‖ramRcoeff (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j b m‖ ^ 2 / (m : ℝ) ^ 2)
      ≤ KS
  /-- ⟦THE `𝒯_S` GRADE GATE⟧ `32(log X)^{2+2θ}·KS ≤ (log X)^{−θ}`. -/
  KS_gate : 32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * KS
    ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
  /-- `0 ≤ εr` — the remainder absorption exponent. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}` — the absorption. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- Lemma 12's three rows collected into `E`. -/
  E_row : E ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293 + EP2)
  /-- ⟦LEMMA 12's `χ`-SUMMED ERROR ROW⟧ (conditional supplier §4c — see the header). -/
  E_binder : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
      ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
        (chiBarCoeff q χ (winCutH Nd (doorCoeffU M))) (chiBarCoeff q χ b)
        (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E

/-! ## §3 — ⟦THE WIRE⟧ `m4_hcap_at_door`

`M4RowsChi.m4_rowChi_capstone` at the door pin, with the six discharged binders in and the
rest read off the `DoorCapBase` bundle.  The conclusion is `m4_socket_discharged_fused`'s
`hcap` binder BYTE-FOR-BYTE at `t₁ := fun _ _ => 0`. -/

set_option maxHeartbeats 1000000 in
-- The capstone is a ~45-binder theorem; one application elaborates its whole hypothesis list
-- against the door pin's instantiation (same cause as `M4RowsChi` §5/§7).
/-- **⟦THE hcap WIRE⟧** (`m4_hcap_at_door`).  For the capstone's five constants, and for any
door parameters carrying the per-base residue bundle `DoorCapBase`, the fused terminal's
`hcap` binder holds at the door pin `t₁ ≡ 0`, `S ≡ 0`.

⟦THE ONE PIN THE STATEMENT MAKES⟧ `t₁` is `0`, not free: the ball leg is discharged by
EMPTINESS (`M4Assembly.m4_hSup_door_at_zero` via `CapFreeArm.ball_leg_vacuous_at_zero`), which
is the only route to `S ≡ 0`, and `8·S²` is hard-coded to `8·0²` in the `hcap` shape. -/
theorem m4_hcap_at_door :
    ∃ Cq cs T₀ Kq Ks : ℝ, 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (R : ChowlaRegime) (M : ℕ) (cU : ℕ → ℂ) (ε : ℕ → ℝ),
        (∀ p : ℕ, ‖cU p‖ ≤ 1) →
        (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
            5 ≤ Real.log (Real.log (2 * T)) →
            ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ) (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
              DoorCapBase Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T) VJ V Lr η εd
                (ε (A + s)) Rbd CR KS E EP2) →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
            (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
            TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
            (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
              ≤ 8 * (0 : ℝ) ^ 2
                + (∫ t in (seamAnn (((A + s : ℕ)) : ℝ) (2 * T)
                      \ seamBall (((A + s : ℕ)) : ℝ) 0)
                    ∩ seamTtotG (chiBarCoeff q χ cU) (calP (Adoor M) (3072 * M))
                        (calQK (Adoor M) (3072 * M) M) (calH (H1door M))
                        (mrAlpha (1 / 12)) 2,
                    ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
                + 2 * ((2 * T / (((A + s : ℕ)) : ℝ) + 1)
                    * (Real.log (((A + s : ℕ)) : ℝ)) ^ (-theta293 + ε (A + s))) := by
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hcapstone⟩ := m4_rowChi_capstone
  refine ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro R M cU ε hcU hfam H L q j A s hb χ T hTlo hThi hTgate hTll
  obtain ⟨Xd, P, Q, Mr, Jb, b, cf, VJ, V, Lr, η, εd, Rbd, CR, KS, E, EP2, hd⟩ :=
    hfam H L q j A s hb T hTlo hThi hTgate hTll
  haveI : NeZero q := ⟨hb.2.2.2.1.ne'⟩
  have hlogX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := hd.logX_four
    linarith
  have hres := hcapstone q cU hcU (calP (Adoor M) (3072 * M))
    (calQK (Adoor M) (3072 * M) M) (calH (H1door M)) (mrAlpha (1 / 12)) 2 Jb
    hd.Jb_lo hd.Jb_hi hd.Hseq_two hd.alpha_nonneg
    (2 * T) VJ V Lr (((A + s : ℕ)) : ℝ) hd.Tann_one hd.qTann_one hd.P_three hd.PQ hd.QTann
    hd.kappa30Q hd.loglog5 hd.VJ_bound η εd hd.alpha_eta hd.eta_half hd.Tann_X hd.X_pos
    hd.debit hd.logX_pos hd.q_logX hd.V_one hd.V_inv hd.T0_Tann hd.floor1 hd.floor2
    hd.floor3 hd.floor4 hd.logqT_one hd.logqT_L hd.L_exp hd.logV_L
    hd.H83_two hd.logX_exp hd.logX_four hTgate
    (2 * (A + s)) Xd P Q Mr (winCutH (A + s) (doorCoeffU M)) b cf hd.cf_one hd.P_low
    hd.Q_pos hd.Q_high hd.range hd.budget hd.Hj hd.B3 hd.BT hd.kappa30 hd.BT10 hd.WL hd.gate
    Rbd CR hd.Rbd_nonneg hd.Rbd_grade hd.Cq_gate
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ)) hd.Rbd_binder
    KS hd.KS_nonneg hd.KS_binder hd.KS_gate E EP2 (ε (A + s)) hd.epsr_nonneg hd.abs8640
    hd.EP2_gate hd.E_row hd.E_binder (doorCap_hXN (A + s)) (doorCap_hN2 (A + s))
    (fun n hn => doorRowDatumU_supp0 M (A + s) hn)
    (fun _ : DirichletCharacter ℂ q => (0 : ℝ))
    (m4_hSup_door_at_zero q (winCutH (A + s) (doorCoeffU M)) (2 * (A + s)) hlogX1) χ
  rw [chiBarCoeff_doorRowDatum] at hres
  simpa using hres

/-! ## §4 — THE THREE SUPPLY-SIDE WIRES

§4a and §4b DISCHARGE two of the three open supply objects at the door; §4c states the third
CONDITIONALLY on the contract the door datum refutes — see the header's mismatch report. -/

/-- **§4a — ⟦THE `Rbd` BINDER, WIRED⟧** (`m4_capRbd_at_door`).
`RbdSupply.rbd_binder_of_doorSocket_free` read at the door's own K-family and at the door
pin's centre `t₁ = 0`, delivering `DoorCapBase.Rbd_binder` at `b := doorCoeffU M`.

⟦THE TWO EDITS, BOTH FREE⟧ the `(χ, j)` quantifier order (the supplier is pair-native, the
capstone is `χ`-first — a pure reassociation) and the domain read (`A ⊆ Icc (−T_ann) T_ann`
from `SeamSplit.seamAnn_subset_Icc`, at `T := T_ann` so `hT` is `le_rfl`).

⟦THE SOCKET'S OWN GATES RIDE⟧ `hs` is `RbdSupply.m4_supplier_all_chi`'s conclusion at
`Ps := 1`, with `t₁` FREE — which is why the radial side condition costs nothing.  Its own
threshold constant is the `_vt` floor's `K` (a `cffKVt`-genre symbolic constant): **it is not
`DoorArithFrameRho`'s `K`**, and the two are never identified. -/
theorem m4_capRbd_at_door {q M Nd Xd P Q : ℕ} {Tann Rrad Rbd : ℝ}
    (hs : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
      CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q Tann Rrad t₁ Rbd
        (doorCofactor0 χ (calP (Adoor M) (3072 * M))
          (calQK (Adoor M) (3072 * M) M) 2 1)) :
    ∀ χ : DirichletCharacter ℂ q,
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ∀ t ∈ seamAnn ((Nd : ℕ) : ℝ) Tann \ seamBall ((Nd : ℕ) : ℝ) 0,
      ‖ramR (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j
        (chiBarCoeff q χ (doorCoeffU M)) t‖ ≤ Rbd := by
  have hA : (seamAnn ((Nd : ℕ) : ℝ) Tann \ seamBall ((Nd : ℕ) : ℝ) 0)
      ⊆ Set.Icc (-Tann) Tann :=
    fun _ ht => seamAnn_subset_Icc ((Nd : ℕ) : ℝ) Tann ht.1
  have hbind := rbd_binder_of_doorSocket_free (Rrad := Rrad) hA (le_refl Tann) hs
  intro χ j hj t ht
  exact hbind j hj (χ, t) ht

/-- **§4b — ⟦THE `𝒯_S` BUDGET, WIRED⟧** (`m4_capKS_at_door`).  `USetPrice.KS_priced` read at
the pinned level `δ' := (log X)^{−100}` (so `δ'² = (log X)^{−200}`, the exponent the capstone's
`hKS` slot carries) and at the constant range cap `Ms ≡ Mr`, delivering
`DoorCapBase.KS_binder` at the explicit budget

  `KS = 20512·(log X)^{−200}·(1 + log 2T_ann)`.

⟦THE GATES⟧ the co-factor-length family `m₀`: `2 ≤ m₀ j`, `m₀ j ≤ ramRbot H X_d j` (⟦V4a⟧'s
sharp lower length) and the sharpness gate `Mr ≤ 4(m₀ j − 1)`, plus the range containment the
bundle already carries (`range`) and `1 ≤ T_ann`.  Nothing else. -/
theorem m4_capKS_at_door {M Nd Xd P Q Mr : ℕ} {Tann : ℝ} (m₀ : ℕ → ℕ)
    (hlogX : 0 ≤ Real.log ((Nd : ℕ) : ℝ)) (hT : 1 ≤ Tann)
    (hm₀2 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 ≤ m₀ j)
    (hm₀ : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Xd j)
    (hMs : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd j ⊆ Finset.Icc 1 Mr)
    (hMs4 : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ((Mr : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)) :
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      5128 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (Mr : ℝ) * (1 + Real.log (2 * Tann))
          * (∑ m ∈ Finset.Icc 1 Mr,
              ‖ramRcoeff (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j
                (doorCoeffU M) m‖ ^ 2 / (m : ℝ) ^ 2)
        ≤ 20512 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (1 + Real.log (2 * Tann)) := by
  have hsq : ((Real.log ((Nd : ℕ) : ℝ)) ^ (-100 : ℝ)) ^ 2
      = (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) := by
    rw [← Real.rpow_natCast ((Real.log ((Nd : ℕ) : ℝ)) ^ (-100 : ℝ)) 2,
      ← Real.rpow_mul hlogX]
    norm_num
  intro j hj
  have hbase := KS_priced (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q j (doorCoeffU M)
    (norm_doorCoeffU_le_one M) (m₀ j) Mr (hm₀2 j hj) (hm₀ j hj) (hMs j hj) (hMs4 j hj)
    Tann ((Real.log ((Nd : ℕ) : ℝ)) ^ (-100 : ℝ)) hT
  rwa [hsq] at hbase

/-- **§4c — ⟦LEMMA 12's `χ`-SUMMED ERROR ROW — THE CONDITIONAL WIRE⟧**
(`m4_capE_at_door_of_hcoef`).  `HybridMoments.ramErr_meanSq_all_chi` at the door datum,
delivering `DoorCapBase.E_binder` at the explicit `E`.

⟦THE MISMATCH, REPORTED NOT MASSAGED⟧ the supplier asks the **GLOBAL** block factorization
`hcoef` — `∀ p m, p.Prime → P ≤ p → p ≤ Q → ¬p∣m → a(p·m) = b m · cf p` — for the datum
`a = winCutH Nd (doorCoeffU M)`, which is WINDOW-CUT.
`M4Assembly.doorRows_global_hcoef_kills_block`
(itself `ThmA2Spine.seam_coef_contract_forces_vanishing`) shows that pair forces `a(p₁·m) = 0`
for every `m` coprime to `p₁` as soon as one product is live and one block prime pushes off the
window.  So this theorem is stated CONDITIONALLY on `hcoef`, `E_binder` remains a carried field
of `DoorCapBase`, and the honest repair — the STRICT relativized pair law
(`SeamRowWindowed.SeamCoefWS`, the shape the `q = 1` supplier `ThmA2Rows.a2Rows_of_capfree3_end`
carries) re-cut through `ramErr_moment_split` — is a design question, not an executor's edit.

Note also: the brief's named supplier `HybridMoments.lemma12_meansq_all_chi` (`:712`) does NOT
fit this slot at all — its left-hand side is `∑_χ ∫ ‖spoly N (χ̄a)‖²`, not the capstone's
`∑_χ ∫ ‖ramErr …‖²`.  `ramErr_meanSq_all_chi` (`:604`) is the shape-correct one. -/
theorem m4_capE_at_door_of_hcoef {q M Nd Xd P Q : ℕ} [NeZero q] {b cf : ℕ → ℂ} {Tann : ℝ}
    (hH : 0 < H83 ((Nd : ℕ) : ℝ) theta293) (hP : 1 ≤ P) (hT : 0 ≤ Tann)
    (hcoef : ∀ p m : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ m →
      winCutH Nd (doorCoeffU M) (p * m) = b m * cf p) :
    (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU M))) (chiBarCoeff q χ b)
          (chiBarCoeff q χ cf) t‖ ^ 2)
      ≤ 3 * ((q.totient : ℝ)
            * (2 * Tann * (windowMass (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P Q b cf) ^ 2)
          + (2 * (q.totient : ℝ) * Tann
                + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
              * (∑ n ∈ Finset.Icc 1 (2 * Nd),
                  ‖ramP2coeff (2 * Nd) P Q (winCutH Nd (doorCoeffU M)) b cf n‖ ^ 2
                    / (n : ℝ) ^ 2)
          + (2 * (q.totient : ℝ) * Tann
                + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
              * (∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
                  ‖winCutH Nd (doorCoeffU M) n‖ ^ 2 / (n : ℝ) ^ 2)) :=
  ramErr_meanSq_all_chi q (H83 ((Nd : ℕ) : ℝ) theta293) hH (2 * Nd) Xd P Q hP
    (winCutH Nd (doorCoeffU M)) b cf hcoef Tann hT

/-! ## §5 — ⟦THE COMPOSITE⟧ `m4_socket_discharged_capwired`

`M4SocketFused.m4_socket_discharged_fused` with `hcap` GONE — replaced by §2's bundle family —
and `t₁` pinned to `fun _ _ => 0`.  Everything else is byte-identical to the fused terminal,
including the three conjuncts and the five other carried binder groups. -/

set_option maxHeartbeats 1000000 in
-- The statement re-elaborates the fused terminal's full binder list with the `DoorCapBase`
-- family in place of `hcap` (same cause as `M4SocketFused`).
/-- **⟦THE CAP-WIRED TERMINAL⟧** (`m4_socket_discharged_capwired`).  `m4_second_road`'s three
demands (⟦item 11⟧ at the `ρ`-grade, ⟦gate 4⟧, the ceiling) at a hypothesis set in which the
LAST analytic binder `hcap` has been replaced by the named per-base residue bundle
`DoorCapBase`.  The δ₀ side is still `0 < δ₀` alone.

⟦WHAT CHANGED FROM THE FUSED TERMINAL⟧
* the leading existential gains the capstone's five constants `Cq, cs, T₀, Kq, Ks`;
* the `t₁` binder is GONE (pinned to `fun _ _ => 0`, the door pin — it occurred only in
  `hcap`);
* `hcap` is replaced by `hcapbase`, the `DoorCapBase` family over the socket's bases and the
  slot's heights.

⟦THE S11 LAW, UNCHANGED⟧ `harith`'s `anchor`/`jfloor` fields are met DIRECTLY at the chosen
anchor numeral (`log₂M + 1 ≥ 14728`, working point 20000) — NOT through
`M4ArithRho.m4_arith_anchor_of_C1_rho` / `m4_arith_jfloor_of_anchor_rho`. -/
theorem m4_socket_discharged_capwired (hMmu : MmuChiRate) (Aexp : ℝ) (hAexp : 0 < Aexp) :
    ∃ Ct Cq cs T₀ Kq Ks : ℝ,
      0 < Ct ∧ 0 < Cq ∧ 0 < cs ∧ 3 ≤ T₀ ∧ 0 < Kq ∧ 0 < Ks ∧
      ∀ (Cp : ℝ), 0 ≤ Cp →
      ∀ (R : ChowlaRegime) (M : ℕ) (C₁ M₀ : ℕ → ℝ), 1 ≤ M →
        ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
          ∀ (ε : ℕ → ℝ) (cU : ℕ → ℂ) (bU : ℕ → ℕ → ℂ) (K δ₀ : ℝ),
            0 < δ₀ →
            (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
              0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ))) →
            (∀ i m : ℕ, ‖bU i m‖ ≤ 1) → (∀ p : ℕ, ‖cU p‖ ≤ 1) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorFuseFrame M (A + s) j Ct Cp (ε (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorRowZeroBase M (A + s) j cU bU) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
                2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
                5 ≤ Real.log (Real.log (2 * T)) →
                ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ) (VJ V Lr η εd Rbd CR KS E EP2 : ℝ),
                  DoorCapBase Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T) VJ V Lr η
                    εd (ε (A + s)) Rbd CR KS E EP2) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))) →
            (∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
              DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
                (doorRhoOfDelta δ₀)) →
            M4ChiSummedFreeRow R M
                (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
              ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
                  m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
                    ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
              ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
                  96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
                      * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
                    ≤ δ₀ ^ 2) := by
  obtain ⟨Ct, hCt, hfused⟩ := m4_socket_discharged_fused hMmu Aexp hAexp
  obtain ⟨Cq, cs, T₀, Kq, Ks, hCq, hcs, hT₀, hKq, hKs, hwire⟩ := m4_hcap_at_door
  refine ⟨Ct, Cq, cs, T₀, Kq, Ks, hCt, hCq, hcs, hT₀, hKq, hKs, ?_⟩
  intro Cp hCp R M C₁ M₀ hM
  obtain ⟨C', x₀, hC'pos, hterm⟩ := hfused Cp hCp R M C₁ M₀ hM
  refine ⟨C', x₀, hC'pos, ?_⟩
  intro ε cU bU K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase hcapbase hbandbase harith
  exact hterm ε cU bU (fun _ _ => (0 : ℝ)) K δ₀ hδ₀ hHreg hb1 hc1 hframe hbase
    (hwire R M cU ε hc1 hcapbase) hbandbase harith

end Salt.MR

end
