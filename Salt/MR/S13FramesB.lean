/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12Compose

/-!
# ⟦S13-B⟧ — THE `DoorCapErrWS` → `DoorCapBase` BUNDLE GROUP, INSTANTIATED

`S12Compose.logChowla2_capstone_conditional` carries five frame families.  This file is the
instantiation page for ONE of them: the `hcapWS` slot

```
∀ H L q j A s, SocketBase R M H L q j A s → ∀ T, … →
  ∃ Xd P Q Mr Jb b cf VJ V Lr η εd Rbd CR KS E EP2 Mtail,
    DoorCapErrWS M (A+s) q Xd P Q b cf (2T) E Mtail
      ∧ (E-binder → DoorCapBase Cq cs T₀ Kq Ks M (A+s) q Xd P Q Mr Jb b cf (2T) … )
```

— `RamErrWS.DoorCapErrWS`'s ELEVEN fields and `M4CapWire.DoorCapBase`'s FIFTY-EIGHT, at the
certified working point (`m = 66`, `λ₋ ∈ [74.198, 83.667]`, `δ₀ = c₀ε/4` at `ε = 1/500`,
`ρ = doorRhoOfDelta (√(δ₀/16K))`, the base `X_d = A + s`, `T_ann = 2T`, `Aexp = 1`).

**PURELY ADDITIVE.**  No landed declaration is touched; the file is a leaf.

## ⟦WHAT THIS PAGE DOES⟧ — the existentials are PINNED, the residue is NAMED

The eighteen existential slots of the `hcapWS` body are **closed in the open**:

| slot | value | why |
|---|---|---|
| `Xd` | `Nd = A + s` | forced by `DoorCapErrWS.Xd_eq` (the datum's own window) |
| `Jb` | `2` | the door's partition has two levels (`Jb_hi`) |
| `b` | `doorCoeffU M` | §1's BAND pair law — the co-factor slot IS the datum |
| `cf` | `liouvilleC` | the same law's prime slot |
| `η` | `5/48` | the LARGEST `η` with `alpha_eta` at `Jb = 2` (`= (1/12)(1 + 1/(2·2))`), so the graded `budget`'s exponent `1 − 2η + εd` is smallest |
| `εd` | `2α₂·log q/log X` | makes `debit` an EQUALITY (`q^{2α₂} = X^{εd}`) — no slack is spent on the character debit |
| `VJ` | `Q₂^{α₂}` | the razor's grid cap at its top point `v ≤ H₂·log Q₂` |
| `V` | `(log X)^{106}` | makes `V_inv` an EQUALITY (the level pin, exactly met) |
| `Lr` | `(log X)^{11/10}` | ⟦THE ONE REAL SPINE CHOICE⟧ — see below |
| `KS` | `20512·(log X)^{−200}(1+log 2T_ann)` | `M4CapWire.m4_capKS_at_door`'s own exit at `δ' = (log X)^{−100}` |
| `E` | `3(720(T_ann/X+1)/H₈₃ + EP2)` | makes `E_row` `le_rfl` |
| `Mtail` | the coprime-tail sum itself | makes `DoorCapErrWS.tail` `le_rfl` |
| `P Q Mr Rbd CR EP2` | gate parameters | the ram-block window, the range cap and the three grade constants stay free, priced by the gate |

⟦`Lr`, THE ONE REAL CHOICE⟧  `Lr` is squeezed from BOTH sides: `logV_L` (`log V ≤ 100 log L`)
forces `L ≥ (log X)^{1.06}` once `V_inv` pins `V ≥ (log X)^{106}`, while `DoorCapBase.gate`
(`420·L^{7/4}(log L)^5 ≤ cs(log Q_base)²`, with `log Q_base ≍ (log X)^{1−θ₂₉₃}`) caps
`L ≲ (log X)^{(8/7)(1−θ₂₉₃)} = (log X)^{1.1390…}`.  `11/10` sits inside `[1.06, 1.1390]` with
`4%` of room below and `3.5%` above; it is fixed here as a `def`, and `logV_L` and `L_exp`
are DISCHARGED at it.

## ⟦THE FIELD LEDGER — 69 bundle fields in, 36 named gate lines out⟧

DISCHARGED here, from `SocketBase` / the `T`-antecedents / `1 ≤ M` / the gate's one scale
floor `4 ≤ log X`, or through a landed wire:

* **(A) the razor at `(q, T_ann)`, 21 fields** — **18 DISCHARGED** (`Jb_lo`, `Jb_hi`,
  `Hseq_two`, `alpha_nonneg`, `Tann_one`, `qTann_one`, `P_three`, `PQ`, `loglog5`,
  `VJ_bound`, `alpha_eta`, `eta_half`, `Tann_X`, `X_pos`, `debit`, `logX_pos`, `V_one`,
  `V_inv`), 3 carried (`QTann`, `kappa30Q`, `q_logX`);
* **(B) the socket floor, 9 fields** — **3 DISCHARGED** (`logqT_one`, `L_exp`, `logV_L`),
  6 carried (`T0_Tann`, `floor1`–`floor4`, `logqT_L` at the pinned `Lr`);
* **(C) the `X`-frame, 3 fields** — **1 DISCHARGED** (`logX_exp`), 2 carried (`logX_four`
  — the scale floor itself — and `H83_two`, ONE gate line serving both bundles);
* **(D) the ram-block frame, 13 fields** — **1 DISCHARGED** (`cf_one`), 12 carried (`P_low`,
  `Q_pos`, `Q_high`, `range`, `budget`, `Hj`, `B3`, `BT`, `kappa30`, `BT10`, `WL`, `gate`);
* **(E) the co-factor, 4 fields** — **1 DISCHARGED THROUGH ITS WIRE** (`Rbd_binder`, from
  `M4CapWire.m4_capRbd_at_door` at the gate's `Rbd_socket`), 3 carried;
* **(F) the `𝒯_S` budget + Lemma 12's row, 8 fields** — **3 DISCHARGED** (`KS_nonneg`,
  `KS_binder` THROUGH ITS WIRE `M4CapWire.m4_capKS_at_door`, `E_row` by construction),
  `E_binder` supplied by the implication's OWN ANTECEDENT, 4 carried (`KS_gate`,
  `epsr_nonneg`, `abs8640`, `EP2_gate`);
* **`DoorCapErrWS`, 11 fields** — **9 DISCHARGED** (`Xd_eq`, `Nd_one`, `H83_le`, `P_one`,
  `Tann_nonneg`, `b_one`, `cf_one`, **`coefWS`** — §1's band pair law — and `tail` at
  `le_rfl`), 2 carried (`H83_two` shared with (C), `E_ge`).

So: 27 + 9 = **36 bundle fields discharged**, `E_binder` off the antecedent, and 30 + 1 = 31
bundle fields carried.  The gate's other FIVE lines are the SUPPLY-SIDE inputs the two wires
consume in place of the bundle's two hardest analytic fields: `Rbd_socket` (for
`Rbd_binder`), `m0_two`/`m0_bot`/`Mr_sharp` (for `KS_binder`), and `Q2_reg`
(= `M4RowsChiZero.DoorRowZeroBase.reg`, a field the spine's row bundle ALREADY carries at
this base) for §1's band gate.  Total: **36 gate lines**.

## ⟦§1 — THE UNTWISTED BAND PAIR LAW⟧ (the one genuinely new stone)

`DoorCapErrWS.coefWS` is `SeamCoefWS X_d P Q (winCutH X_d (doorCoeffU M)) b cf` at the
**RAM-BLOCK** window `[P, Q]` — NOT at a door block.  `S11CoefWS`'s witness is the PUNCTURE
law at `P := 𝒫_i`, `Q := 𝒬K_i` and does not fit: `DoorCapBase.P_low` pins `P ≥ P₈₃ X θ₂₉₃`,
which is above every door block top.  The device that DOES fit is `M4Band`'s BAND law — the
one `S11CoefWS`'s header calls "the wrong device" *for its own slot*, and the right one here,
for exactly the reason stated there: the band law is stated at primes ABOVE every block.
§1 transplants `M4Band.memSCoeff_seamCoefWS_band_gen` from `liouChi χ` to `liouvilleC`
(`M4Band.indicator_mul_shift_up` is already general in the completely multiplicative factor),
and the band gate is `M4Band.door_band_gate_of_log` off `P_low` and `log 𝒬K₂ ≤ √(log X)` —
the latter being `M4RowsChiZero.DoorRowZeroBase.reg` VERBATIM, a field the spine's row bundle
already carries at the same base.

## ⚠ ⟦THE BAND-WIDTH TENSION — REPORTED, NOT MASSAGED⟧

The gate below is a faithful reduction, not a satisfiability certificate.  Walking its
fields at the working point exhibits a collision on the ONE axis the two bundles share, the
band width `log Q / log P`:

* `range` puts `Mr ≳ 2X/P` (the co-factor range at the BOTTOM block `j ≈ H₈₃ log P`), and
  then `KS_binder` read at the TOP block (`Σ_m ≍ Q/X`) makes `KS ≳ (log X)^{−199}·Q/P`, so
  `KS_gate` (`KS ≤ (log X)^{−2−3θ}/32`) forces `log Q ≤ log P + O(log log X)` — the band is a
  POINT in the log scale;
* `DoorCapErrWS.E_ge`'s coprime-tail row `(7φ(q)·2N_d/q)·Mtail` is then `≍ φ(q)/q · 7`
  (the block-free density is `≍ log P/log Q ≍ 1`, so `Mtail ≍ 1/(2N_d)`), i.e. `E ≳ 1`,
  while `E_row` + `EP2_gate` cap `E ≤ 3(1440/H₈₃ + (log X)^{−1/500}/12)`, which is `o(1)`.

That is `M4Band`'s own ⟦POINT-vs-BAND WALL⟧ met from the other side: there the point was
refused because the coprime tail's charge is `O(1)` and no `ε`-window absorbs it; here
`KS_gate` is what forces the point.  The two gate fields `KS_gate` and `E_ge` are therefore
flagged as the pair to adjudicate; nothing in this file assumes either is met.

⟦THE FOUR LOG SCALES⟧ stay apart: `log X` (the base), `log(q·T_ann)` (the razor/floor scale,
reaching `Lr`), `log Q_base` (the ram-block scale) and `log H` — which enters ONLY through
`SocketBase` and is never identified with any of them.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — ⟦THE UNTWISTED STRICT BAND PAIR LAW⟧

`M4Band` §3′ at `g := liouvilleC`.  `M4Band.indicator_mul_shift_up` is already general in the
completely multiplicative factor, so the transplant is the landed proof with `liouvilleC_mul`
in place of `liouChi_mul χ`. -/

/-- **THE UNTWISTED STRICT BAND PAIR LAW AT AN ABSTRACT CUT**
(`memSCoeff_seamCoefWS_band_gen_U`) — `M4Band.memSCoeff_seamCoefWS_band_gen` at the untwisted
datum `1_𝒮·λ`. -/
theorem memSCoeff_seamCoefWS_band_gen_U (Pseq Qseq : ℕ → ℕ) (J Xd P Q : ℕ) (a : ℕ → ℂ)
    (hgate : ∀ j ∈ Finset.Icc 1 J, Qseq j < P)
    (haH : ∀ n : ℕ, Xd < n → n ≤ 2 * Xd → a n = memSCoeff Pseq Qseq J liouvilleC n) :
    SeamCoefWS Xd P Q a (memSCoeff Pseq Qseq J liouvilleC) liouvilleC := by
  intro p m hp hPp _ _ hlo hhi
  have hgt : ∀ j ∈ Finset.Icc 1 J, Qseq j < p := fun j hj => lt_of_lt_of_le (hgate j hj) hPp
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exfalso
    have h0 : (0 : ℝ) ≤ (Xd : ℝ) := Nat.cast_nonneg Xd
    rw [Nat.cast_zero, mul_zero] at hlo
    linarith
  · have hloN : Xd < p * m := by
      have h : ((Xd : ℕ) : ℝ) < ((p * m : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    have hhiN : p * m ≤ 2 * Xd := by
      have h : ((p * m : ℕ) : ℝ) ≤ ((2 * Xd : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast h
    rw [haH _ hloN hhiN]
    exact indicator_mul_shift_up liouvilleC_mul hp (by omega) hgt

/-- **⟦THE `DoorCapErrWS.coefWS` WITNESS ON THE RAM-BLOCK BAND⟧**
(`doorCoeffU_seamCoefWS_band_H`).  The half-open door datum, its own UN-cut self as
co-factor, and `λ` as the prime coefficient satisfy the STRICT relativized pair law on the
whole band `[P, Q]`, as soon as every door block top is strictly below `P`.

This is the `b`/`cf` pin of the whole page: `b := doorCoeffU M` is exactly the co-factor slot
`RbdSupply`'s socket and `USetPrice.KS_priced` are wired at (`M4CapWire` §4a/§4b), so the two
supply wires and the pair law all read the SAME sequence. -/
theorem doorCoeffU_seamCoefWS_band_H (M Xd P Q : ℕ)
    (hgate : ∀ i ∈ Finset.Icc 1 2, calQK (Adoor M) (3072 * M) M i < P) :
    SeamCoefWS Xd P Q (winCutH Xd (doorCoeffU M)) (doorCoeffU M) liouvilleC :=
  memSCoeff_seamCoefWS_band_gen_U (calP (Adoor M) (3072 * M))
    (calQK (Adoor M) (3072 * M) M) 2 Xd P Q _ hgate
    (fun _ h1 h2 => winCutH_of_mem _ h1 h2)

/-! ## §2 — ⟦THE SPINE CHOICES⟧, as defs with their derivations -/

/-- ⟦THE DESIGNATED RAZOR LEVEL⟧ `Jb := 2` — the door's partition has exactly two levels, so
`Jb_hi` (`Jb ≤ J = 2`) pins the top and `Jb_lo` the bottom. -/
def s13Jb : ℕ := 2

/-- ⟦THE RAZOR'S EXPONENT ROOM⟧ `η := 5/48`.  `alpha_eta` asks `α_Jb ≤ 1/4 − η`, and
`mrAlpha (1/12) 2 = 1/4 − (1/12)(1 + 1/4) = 1/4 − 5/48`, so `5/48` is the LARGEST admissible
`η` at `Jb = 2` — which is the right choice, because `η` enters the graded `budget` only
through the exponent `1 − 2η + εd` (larger `η`, smaller demand).  `2η = 5/24 ≤ 1`. -/
def s13Eta : ℝ := 5 / 48

/-- ⟦THE CHARACTER DEBIT EXPONENT⟧ `εd := 2α₂·log q/log X` — the value at which
`DoorCapBase.debit` (`q^{2α_Jb} ≤ X^{εd}`) is an EQUALITY.  Nothing is spent on the debit,
so all of the budget's slack is available to the razor's bundle. -/
def s13EpsD (q Nd : ℕ) : ℝ :=
  2 * mrAlpha (1 / 12) 2 * Real.log ((q : ℕ) : ℝ) / Real.log ((Nd : ℕ) : ℝ)

/-- ⟦THE RAZOR'S GRID CAP⟧ `VJ := Q₂^{α₂} = exp(α₂·log 𝒬K₂)`.  `VJ_bound` runs over
`v ∈ ramI H₂ 𝒫₂ 𝒬K₂ = Icc ⌊H₂ log 𝒫₂⌋ ⌊H₂ log 𝒬K₂⌋`, so `v/H₂ ≤ log 𝒬K₂` at the top point
and the cap is exactly the exponential of that. -/
def s13VJ (M : ℕ) : ℝ :=
  Real.exp (mrAlpha (1 / 12) 2 * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ))

/-- ⟦THE LEVEL PIN⟧ `V := (log X)^{106}` — the value at which `V_inv` (`V⁻¹ ≤ (log X)^{−106}`)
is an EQUALITY. -/
def s13V (Nd : ℕ) : ℝ := (Real.log ((Nd : ℕ) : ℝ)) ^ (106 : ℝ)

/-- ⟦THE ONE REAL SPINE CHOICE⟧ `Lr := (log X)^{11/10}`.

`logV_L` (`log V ≤ 100·log L`) with `V = (log X)^{106}` forces `L ≥ (log X)^{1.06}`;
`DoorCapBase.gate` (`420·L^{7/4}(log L)^5 ≤ cs·(log Q_base)²` at `log Q_base ≍
(log X)^{1−θ₂₉₃}`) caps `L ≲ (log X)^{(8/7)(1−θ₂₉₃)} = (log X)^{1.13898…}`.  `11/10` is
interior to `[1.06, 1.13898]`: `3.8%` above the floor, `3.5%` below the ceiling.  `logqT_L`
(`log(q·T_ann) ≤ L`) is the remaining demand and is carried by the gate. -/
def s13Lr (Nd : ℕ) : ℝ := (Real.log ((Nd : ℕ) : ℝ)) ^ ((11 : ℝ) / 10)

/-- ⟦THE `𝒯_S` BUDGET⟧ `KS := 20512·(log X)^{−200}·(1 + log 2T_ann)` — `M4CapWire.m4_capKS_at_door`'s
own exit value, at the pinned level `δ' = (log X)^{−100}`. -/
def s13KS (Nd : ℕ) (Tann : ℝ) : ℝ :=
  20512 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) * (1 + Real.log (2 * Tann))

/-- ⟦LEMMA 12's ROW TOTAL⟧ `E := 3(720(T_ann/X + 1)/H₈₃ + EP2)` — the value at which
`DoorCapBase.E_row` is `le_rfl`. -/
def s13E (Nd : ℕ) (Tann EP2 : ℝ) : ℝ :=
  3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293 + EP2)

/-- ⟦R3a — THE COPRIME-TAIL MASS, PRICED NOT PINNED⟧ `Mtail :=` the sum itself, so
`DoorCapErrWS.tail` is `le_rfl` and every ounce of the tail's real size is visible in the
ONE place it is charged, `E_ge`. -/
def s13Mtail (M Nd P Q : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 (2 * Nd)).filter (fun n => blockOmega P Q n = 0),
    ‖winCutH Nd (doorCoeffU M) n‖ ^ 2 / (n : ℝ) ^ 2

/-! ## §3 — ⟦THE NAMED RESIDUE⟧ `S13CapGate` -/

/-- **⟦THE PER-BASE GATE⟧** (`S13CapGate`).  Exactly the fields of `DoorCapErrWS` and
`DoorCapBase` that survive §2's pins, plus five supply-side inputs — 36 lines, against the
two bundles' 69.

Everything here is stated at the door's own numerals; nothing is absorbed, and every field
is either a bundle field VERBATIM, a strictly weaker reduction of one (`logqT_L` at the
pinned `Lr`; `budget` at the pinned `η`, `εd`, `VJ`; `KS_gate` at the pinned `KS`; `E_ge` at
the pinned `E` and `Mtail`), or one of the FIVE supply-side inputs the wires consume in place
of a harder field (`Rbd_socket` for `Rbd_binder`; `m0_two`/`m0_bot`/`Mr_sharp` for
`KS_binder`; `Q2_reg` — `DoorRowZeroBase.reg`, already carried by the spine's row bundle —
for §1's band gate).

⚠ `KS_gate` and `E_ge` are the pair flagged in the header's ⟦BAND-WIDTH TENSION⟧: they pull
`log Q/log P` in opposite directions.  This structure asserts nothing about their joint
satisfiability. -/
structure S13CapGate (Cq cs T₀ Kq Ks : ℝ) (M Nd q P Q Mr : ℕ) (m₀ : ℕ → ℕ)
    (Tann Rrad Rbd CR EP2 εr : ℝ) : Prop where
  -- ⟦THE SCALE FLOOR — the one line every discharged field reads⟧
  /-- `4 ≤ log X` — `DoorCapBase.logX_four` verbatim; `logX_pos` and `logX_exp` come off it. -/
  logX_four : 4 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `2 ≤ H₈₃ X θ₂₉₃` — `DoorCapBase.H83_two` = `DoorCapErrWS.H83_two`, ONE field for both. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  -- ⟦(A) THE RAZOR — the three that do not reduce⟧
  /-- `𝒬K₂ ≤ q·T_ann` — `DoorCapBase.QTann` at `Jb = 2`. -/
  QTann : ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- ⟦MR (21)⟧'s κ-gate at the designated level — `DoorCapBase.kappa30Q`. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — `DoorCapBase.q_logX`.  (Independent of `DoorBandBase.qfit`'s
  base-side `q ≤ (log X_d)^{10}`; the two are never identified.) -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  -- ⟦(B) THE SOCKET FLOOR AT `(q, T_ann)`⟧
  /-- `T₀ ≤ T_ann` — the capstone's own height floor at its opaque `T₀`. -/
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
  /-- `log(q·T_ann) ≤ Lr` AT THE PINNED `Lr = (log X)^{11/10}` — `DoorCapBase.logqT_L`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ s13Lr Nd
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `P₈₃ X θ₂₉₃ ≤ P` — `DoorCapBase.P_low`; also the band gate §1 reads. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `log 𝒬K₂ ≤ √(log X)` — `M4RowsChiZero.DoorRowZeroBase.reg` VERBATIM (the spine's row
  bundle already carries it at this base); §1's band gate is `door_band_gate_of_log` off it. -/
  Q2_reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
    ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- The co-factor range sits in `[1, Mr]` at every block. -/
  range : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd j ⊆ Finset.Icc 1 Mr
  /-- ⟦THE GRADED BUDGET⟧ at the pinned `VJ`, `η`, `εd`. -/
  budget : thinBundleGChi ((q : ℝ) * Tann) (s13VJ M) (calH (H1door M) 2)
      (calP (Adoor M) (3072 * M) 2) (calQK (Adoor M) (3072 * M) M 2)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ (Mr : ℝ)
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
  /-- `log Q_base ≤ Lr` on the grid, at the pinned `Lr`. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ s13Lr Nd
  /-- The `cs`-gate on the grid, at the pinned `Lr` — the field that CAPS `Lr` from above. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧ `Rbd ≤ CR·(log X)^{−ρ₂₉₃}`. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧ `1728·Cq·CR² ≤ (log X)^{2θ₂₉₃}`. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` SUPPLY⟧ the door's un-phased co-factor socket, at the door pin's FREE centre
  (`RbdSupply.m4_supplier_all_chi`'s own conclusion shape at `Ps := 1`).  `M4CapWire`
  §4a converts it into `DoorCapBase.Rbd_binder`; its threshold constant is the `_vt` floor's
  `K` (a `cffKVt`-genre symbol), **never** `DoorArithFrameRho`'s `K`. -/
  Rbd_socket : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
    CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q Tann Rrad t₁ Rbd
      (doorCofactor0 χ (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 1)
  -- ⟦(F) THE `𝒯_S` BUDGET AND LEMMA 12's ERROR ROW⟧
  /-- ⟦V4a⟧'s co-factor length family, lower pin. -/
  m0_two : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 ≤ m₀ j
  /-- ⟦V4a⟧'s co-factor length family against `ramRbot`. -/
  m0_bot : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ((m₀ j : ℕ) : ℝ) ≤ ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Nd j
  /-- The sharpness gate `Mr ≤ 4(m₀ j − 1)` — with `range`, the pair that pins `Mr ≍ ramRbot`. -/
  Mr_sharp : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    ((Mr : ℕ) : ℝ) ≤ 4 * (((m₀ j : ℕ) : ℝ) - 1)
  /-- ⟦THE `𝒯_S` GRADE GATE⟧ at the pinned `KS`. ⚠ one half of the band-width tension. -/
  KS_gate : 32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * s13KS Nd Tann
    ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)
  /-- `0 ≤ εr`. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}`. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- ⟦`DoorCapErrWS.E_ge`⟧ at the pinned `E` and `Mtail`. ⚠ the other half of the tension. -/
  E_ge : 4 * ((q.totient : ℝ)
        * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
      + (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ))
            + endMass Nd)
      + (2 * (q.totient : ℝ) * Tann + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
          * s13Mtail M Nd P Q) ≤ s13E Nd Tann EP2

/-! ## §4 — THE SCALE STONES

The handful of facts every group reads off the gate's ONE scale line `4 ≤ log X`. -/

/-- `0 < θ₂₉₃` and `θ₂₉₃ ≤ 1` — the exponent that `H83_le` and the `X`-frame spend. -/
theorem theta293_pos_le_one : 0 < theta293 ∧ theta293 ≤ 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hd : (1 : ℝ) ≤ 32 * (3 * Real.exp 1 + 1) := by nlinarith
  have hd0 : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by linarith
  constructor
  · rw [theta293]; positivity
  · rw [theta293, div_le_one hd0]; linarith

/-- `H₈₃ X θ₂₉₃ ≤ X` — `DoorCapErrWS.H83_le`, from `4 ≤ log X` alone. -/
theorem s13_H83_le {Nd : ℕ} (h : 4 ≤ Real.log ((Nd : ℕ) : ℝ)) :
    H83 ((Nd : ℕ) : ℝ) theta293 ≤ ((Nd : ℕ) : ℝ) := by
  obtain ⟨hθ0, hθ1⟩ := theta293_pos_le_one
  have h1 : (1 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hstep : (Real.log ((Nd : ℕ) : ℝ)) ^ theta293
      ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 hθ1
  rw [Real.rpow_one] at hstep
  have hNd : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Nd with h0 | hpos
    · exfalso
      rw [h0] at h
      simp only [Nat.cast_zero, Real.log_zero] at h
      linarith
    · exact_mod_cast hpos
  have hself : Real.log ((Nd : ℕ) : ℝ) ≤ ((Nd : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hNd
  rw [H83]
  linarith

/-! ## §5 — ⟦THE DISCHARGE⟧ the two bundles at the working point -/

/-- **⟦THE ERROR BUNDLE, AT THE WORKING POINT⟧** (`s13_doorCapErrWS`).
`RamErrWS.DoorCapErrWS` at `Xd := N_d`, `b := doorCoeffU M`, `cf := liouvilleC`,
`E := s13E`, `Mtail := s13Mtail` — NINE of its eleven fields discharged, the two carried
ones (`H83_two`, `E_ge`) read straight off the gate.

The analytic field `coefWS` is §1's BAND pair law; its band gate is
`M4Band.door_band_gate_of_log` off `P_low` and `Q2_reg`. -/
theorem s13_doorCapErrWS {Cq cs T₀ Kq Ks : ℝ} {M Nd q P Q Mr : ℕ} {m₀ : ℕ → ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ} (hM : 1 ≤ M) (hNd : 1 ≤ Nd)
    (hg : S13CapGate Cq cs T₀ Kq Ks M Nd q P Q Mr m₀ Tann Rrad Rbd CR EP2 εr)
    (hT1 : 1 ≤ Tann) :
    DoorCapErrWS M Nd q Nd P Q (doorCoeffU M) liouvilleC Tann
      (s13E Nd Tann EP2) (s13Mtail M Nd P Q) := by
  have hlogX1 : (1 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by have := hg.logX_four; linarith
  have hP1 : 1 ≤ P := by
    have hP0 : (0 : ℝ) < P83 ((Nd : ℕ) : ℝ) theta293 := by rw [P83]; exact Real.exp_pos _
    have : (0 : ℝ) < (P : ℝ) := lt_of_lt_of_le hP0 hg.P_low
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
      intro h0
      rw [h0] at this
      simp at this)
  refine
    { Xd_eq := rfl
      Nd_one := hNd
      H83_two := hg.H83_two
      H83_le := s13_H83_le hg.logX_four
      P_one := hP1
      Tann_nonneg := by linarith
      b_one := norm_doorCoeffU_le_one M
      cf_one := liouvilleC_norm_le_one
      coefWS := ?_
      tail := le_rfl
      E_ge := hg.E_ge }
  exact doorCoeffU_seamCoefWS_band_H M Nd P Q
    (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hlogX1 hg.Q2_reg hg.P_low)

/-- **⟦THE CAP BUNDLE, AT THE WORKING POINT⟧** (`s13_doorCapBase`).
`M4CapWire.DoorCapBase`'s fifty-eight fields at §2's pins, from the gate.  Twenty-four are
discharged in this proof; `Rbd_binder` and `KS_binder` come through their wires
(`M4CapWire.m4_capRbd_at_door`, `m4_capKS_at_door`); `E_binder` is the argument `hE`, which
is exactly the antecedent of `S12Compose`'s implication. -/
theorem s13_doorCapBase {Cq cs T₀ Kq Ks : ℝ} {M Nd q P Q Mr : ℕ} {m₀ : ℕ → ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ} (hM : 1 ≤ M) (hNd : 1 ≤ Nd)
    (hg : S13CapGate Cq cs T₀ Kq Ks M Nd q P Q Mr m₀ Tann Rrad Rbd CR EP2 εr)
    (hq : 1 ≤ q) (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ))
    (hTll : 5 ≤ Real.log (Real.log Tann))
    (hE : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU M))) (chiBarCoeff q χ (doorCoeffU M))
          (chiBarCoeff q χ liouvilleC) t‖ ^ 2) ≤ s13E Nd Tann EP2) :
    DoorCapBase Cq cs T₀ Kq Ks M Nd q Nd P Q Mr s13Jb (doorCoeffU M) liouvilleC Tann
      (s13VJ M) (s13V Nd) (s13Lr Nd) s13Eta (s13EpsD q Nd) εr Rbd CR
      (s13KS Nd Tann) (s13E Nd Tann EP2) EP2 := by
  have hLX4 := hg.logX_four
  have hLX1 : (1 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hLX0 : (0 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hNdR : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hNd
    linarith
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  -- ⟦the razor's level and its exponent⟧
  have halpha : mrAlpha (1 / 12) 2 = 7 / 48 := by
    rw [mrAlpha]; norm_num
  have hH1 : (2 : ℝ) ≤ H1door M := H1door_two hM
  have hcalH : calH (H1door M) 2 = 4 * H1door M := by rw [calH]; norm_num
  have hcalH0 : (0 : ℝ) < calH (H1door M) 2 := by rw [hcalH]; linarith
  -- ⟦the height scale⟧
  have hqT1 : (1 : ℝ) < (q : ℝ) * Tann := by nlinarith
  have hlogqT0 : (0 : ℝ) < Real.log ((q : ℝ) * Tann) := Real.log_pos hqT1
  have hloglog5 : (5 : ℝ) ≤ Real.log (Real.log ((q : ℝ) * Tann)) := by
    have hTpos : (0 : ℝ) < Tann := by linarith
    have h1 : Real.log Tann ≤ Real.log ((q : ℝ) * Tann) :=
      Real.log_le_log hTpos (by nlinarith)
    have hlogT0 : (0 : ℝ) < Real.log Tann := Real.log_pos hT1
    exact le_trans hTll (Real.log_le_log hlogT0 h1)
  have hlogqT1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * Tann) := by
    by_cases hc : (1 : ℝ) ≤ Real.log ((q : ℝ) * Tann)
    · exact hc
    · exfalso
      have hlt : Real.log ((q : ℝ) * Tann) < 1 := not_le.mp hc
      have : Real.log (Real.log ((q : ℝ) * Tann)) < 0 := Real.log_neg hlogqT0 hlt
      linarith
  -- ⟦the ladder⟧
  have hA0 : 0 < Adoor M := by
    rw [Adoor]; exact Nat.mul_pos (by norm_num) (Nat.succ_pos _)
  have hE2 : 2 ≤ calE (Adoor M) (3072 * M) 2 := by
    have h : calE (Adoor M) (3072 * M) 2 = Adoor M * (3072 * M) * 4 := by
      rw [calE]; norm_num [Nat.factorial]
    rw [h]
    have h1 : 1 ≤ Adoor M := hA0
    have h2 : 1 ≤ 3072 * M := by omega
    nlinarith
  -- ⟦the pinned `Lr` and `V`⟧
  have hLr : s13Lr Nd = (Real.log ((Nd : ℕ) : ℝ)) ^ ((11 : ℝ) / 10) := rfl
  have hLrge : Real.log ((Nd : ℕ) : ℝ) ≤ s13Lr Nd := by
    rw [hLr]
    have := Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num : (1 : ℝ) ≤ (11 : ℝ) / 10)
    rwa [Real.rpow_one] at this
  have hLrpos : (0 : ℝ) < s13Lr Nd := by linarith
  have hlogLr : Real.log (s13Lr Nd) = (11 / 10 : ℝ) * Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
    rw [hLr, Real.log_rpow hLX0]
  have hlogLXnn : (0 : ℝ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)) := Real.log_nonneg hLX1
  refine
    { Jb_lo := by rw [s13Jb]; norm_num
      Jb_hi := by rw [s13Jb]
      Hseq_two := ?_
      alpha_nonneg := by rw [s13Jb, halpha]; norm_num
      Tann_one := by linarith
      qTann_one := hqT1
      P_three := ?_
      PQ := ?_
      QTann := hg.QTann
      kappa30Q := hg.kappa30Q
      loglog5 := hloglog5
      VJ_bound := ?_
      alpha_eta := by rw [s13Jb, halpha, s13Eta]; norm_num
      eta_half := by rw [s13Eta]; norm_num
      Tann_X := hTX
      X_pos := hNdR
      debit := ?_
      logX_pos := hLX0
      q_logX := hg.q_logX
      V_one := ?_
      V_inv := ?_
      T0_Tann := hg.T0_Tann
      floor1 := hg.floor1
      floor2 := hg.floor2
      floor3 := hg.floor3
      floor4 := hg.floor4
      logqT_one := hlogqT1
      logqT_L := hg.logqT_L
      L_exp := ?_
      logV_L := ?_
      H83_two := hg.H83_two
      logX_exp := ?_
      logX_four := hLX4
      cf_one := liouvilleC_norm_le_one
      P_low := hg.P_low
      Q_pos := hg.Q_pos
      Q_high := hg.Q_high
      range := hg.range
      budget := hg.budget
      Hj := hg.Hj
      B3 := hg.B3
      BT := hg.BT
      kappa30 := hg.kappa30
      BT10 := hg.BT10
      WL := hg.WL
      gate := hg.gate
      Rbd_nonneg := hg.Rbd_nonneg
      Rbd_grade := hg.Rbd_grade
      Cq_gate := hg.Cq_gate
      Rbd_binder := m4_capRbd_at_door hg.Rbd_socket
      KS_nonneg := ?_
      KS_binder := ?_
      KS_gate := hg.KS_gate
      epsr_nonneg := hg.epsr_nonneg
      abs8640 := hg.abs8640
      EP2_gate := hg.EP2_gate
      E_row := le_rfl
      E_binder := hE }
  · -- ⟦`Hseq_two`⟧ `2 ≤ 4·H₁` at `H₁ ≥ 2`
    rw [s13Jb, hcalH]; linarith
  · -- ⟦`P_three`⟧ `𝒫₂ = 2^{e₂}` with `e₂ ≥ 2`
    rw [s13Jb, calP]
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ calE (Adoor M) (3072 * M) 2 := Nat.pow_le_pow_right (by norm_num) hE2
  · -- ⟦`PQ`⟧ `2^{e₂} ≤ 2^{4M·e₂}`
    rw [s13Jb, calP, calQK]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 1 * calE (Adoor M) (3072 * M) 2 ≤ (2 ^ 2 * M) * calE (Adoor M) (3072 * M) 2 :=
      Nat.mul_le_mul_right _ (by omega)
    simpa using this
  · -- ⟦`VJ_bound`⟧ the grid cap at its top point
    intro v hv
    rw [s13VJ, s13Jb]
    refine Real.exp_le_exp.mpr ?_
    rw [halpha]
    have hvle : (v : ℝ) ≤ calH (H1door M) 2
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
      rw [ramI, Finset.mem_Icc] at hv
      have h1 : (v : ℝ) ≤ (⌊calH (H1door M) 2
          * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast hv.2
      have hQ1 : (1 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
        exact_mod_cast one_le_calQK (Adoor M) (3072 * M) M 2
      have h2 : (0 : ℝ) ≤ calH (H1door M) 2
          * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
        have := Real.log_nonneg hQ1
        positivity
      exact le_trans h1 (Nat.floor_le h2)
    rw [div_le_iff₀ hcalH0]
    nlinarith [hvle, hcalH0]
  · -- ⟦`debit`⟧ an EQUALITY at the pinned `εd`
    rw [s13Jb, s13EpsD, halpha]
    have h1 : ((Nd : ℕ) : ℝ) ^ (2 * (7 / 48 : ℝ) * Real.log ((q : ℕ) : ℝ)
        / Real.log ((Nd : ℕ) : ℝ))
        = Real.exp (2 * (7 / 48 : ℝ) * Real.log ((q : ℕ) : ℝ)) := by
      rw [Real.rpow_def_of_pos hNdR]
      congr 1
      field_simp
    have h2 : (q : ℝ) ^ (2 * (7 / 48 : ℝ)) = Real.exp (Real.log ((q : ℕ) : ℝ) * (2 * (7 / 48 : ℝ))) :=
      Real.rpow_def_of_pos hqR0 _
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (le_of_eq (by ring))
  · -- ⟦`V_one`⟧
    rw [s13V]
    have := Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num : (0 : ℝ) ≤ (106 : ℝ))
    rwa [Real.rpow_zero] at this
  · -- ⟦`V_inv`⟧ an EQUALITY at the pinned `V`
    rw [s13V, ← Real.rpow_neg hLX0.le]
  · -- ⟦`L_exp`⟧ `e ≤ log X ≤ Lr`
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · -- ⟦`logV_L`⟧ `106·loglog X ≤ 110·loglog X`
    rw [s13V, Real.log_rpow hLX0, hlogLr]
    linarith
  · -- ⟦`logX_exp`⟧
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · -- ⟦`KS_nonneg`⟧
    rw [s13KS]
    have h1 : (0 : ℝ) < (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) := Real.rpow_pos_of_pos hLX0 _
    have h2 : (0 : ℝ) ≤ Real.log (2 * Tann) := Real.log_nonneg (by linarith)
    positivity
  · -- ⟦`KS_binder`⟧ through `M4CapWire` §4b
    rw [s13KS]
    exact m4_capKS_at_door m₀ hLX0.le (by linarith) hg.m0_two hg.m0_bot hg.range hg.Mr_sharp

/-! ## §6 — ⟦THE COMPOSITE⟧ at `S12Compose`'s exact binder shape -/

/-- **⟦THE BUNDLE GROUP, AT THE WORKING POINT⟧** (`doorCapBundle_at_workingPoint`).
The body of `S12Compose.logChowla2_capstone_conditional`'s `hcapWS` slot, at ONE base and ONE
admissible height, from the gate.  Every existential is closed at §2's pins. -/
theorem doorCapBundle_at_workingPoint {Cq cs T₀ Kq Ks : ℝ} {M Nd q P Q Mr : ℕ} {m₀ : ℕ → ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ} (hM : 1 ≤ M) (hNd : 1 ≤ Nd) (hq : 1 ≤ q)
    (hg : S13CapGate Cq cs T₀ Kq Ks M Nd q P Q Mr m₀ Tann Rrad Rbd CR EP2 εr)
    (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ))
    (hTll : 5 ≤ Real.log (Real.log Tann)) :
    ∃ (Xd P' Q' Mr' Jb : ℕ) (b cf : ℕ → ℂ)
      (VJ V Lr η εd Rbd' CR' KS E EP2' Mtail : ℝ),
      DoorCapErrWS M Nd q Xd P' Q' b cf Tann E Mtail
        ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
              ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P' Q'
                (chiBarCoeff q χ (winCutH Nd (doorCoeffU M)))
                (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
            → DoorCapBase Cq cs T₀ Kq Ks M Nd q Xd P' Q' Mr' Jb b cf Tann
                VJ V Lr η εd εr Rbd' CR' KS E EP2') := by
  refine ⟨Nd, P, Q, Mr, s13Jb, doorCoeffU M, liouvilleC, s13VJ M, s13V Nd, s13Lr Nd,
    s13Eta, s13EpsD q Nd, Rbd, CR, s13KS Nd Tann, s13E Nd Tann EP2, EP2, s13Mtail M Nd P Q,
    s13_doorCapErrWS hM hNd hg (le_of_lt hT1), ?_⟩
  intro hE
  exact s13_doorCapBase hM hNd hg hq hT1 hTX hTll hE

/-! ## §7 — ⟦THE SLOT⟧ `S12Compose`'s `hcapWS` hypothesis, byte for byte -/

/-- **⟦THE `hcapWS` SLOT, DISCHARGED FROM THE GATE FAMILY⟧** (`doorCapBundle_family`).
The statement below is `S12Compose.logChowla2_capstone_conditional`'s `hcapWS` hypothesis
VERBATIM (`Nd := A + s`, `Tann := 2T`, `εr := epsf (A + s)`).  Its own hypothesis is the SAME
quantifier prefix carrying `S13CapGate` instead — i.e. the spine's remaining obligation for
this frame family, 31 lines per base instead of 69, with every existential closed.

`1 < T_ann` is read off the slot's own `TannGate` antecedent against the gate's `4 ≤ log X`;
`1 ≤ q` and `1 ≤ A + s` off `SocketBase`. -/
theorem doorCapBundle_family {Cq cs T₀ Kq Ks : ℝ} {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    {epsf : ℕ → ℝ}
    (hgate : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (P Q Mr : ℕ) (m₀ : ℕ → ℕ) (Rrad Rbd CR EP2 : ℝ),
          S13CapGate Cq cs T₀ Kq Ks M (A + s) q P Q Mr m₀ (2 * T) Rrad Rbd CR EP2
            (epsf (A + s))) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
        2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
        5 ≤ Real.log (Real.log (2 * T)) →
        ∃ (Xd P Q Mr Jb : ℕ) (b cf : ℕ → ℂ)
          (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
          DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
            ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                  ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                    (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                    (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                → DoorCapBase Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                    VJ V Lr η εd (epsf (A + s)) Rbd CR KS E EP2) := by
  intro H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Mr, m₀, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  -- ⟦`1 < T_ann`⟧ off the slot's own `TannGate` against the gate's scale floor
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_four; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint hM hNd hq hg hT1 hThi hTll

/-! ## §8 — ⟦KNOT-1 ARITY SURGERY⟧ THE PER-BLOCK PINS

⟦WHAT THE SURGERY BOUGHT⟧  §3's gate carried `range` and `Mr_sharp` as two independent lines
about ONE scalar `Mr`.  Read at the two ends of the ram band they force `Q ≤ 2P` — the
⟦BAND-WIDTH TENSION⟧ of the header, met from the `KS` side.  KNOT1-SCOPE (flags, 2026-07-30)
identified the scalar as the whole cause; `M4CapWire.DoorCapBasePerBlock` reads `Mr : ℕ → ℕ`
inside the ∀`j` the bundle already carries, and this section PINS it:

| pin | value | what it discharges |
|---|---|---|
| `s13Mr Nd j` | `⌈2·N_d·e^{−j/H₈₃}⌉₊` | `range` — DEFINITIONAL (the window's own top, rounded up) |
| `s13m0 Nd j` | `⌊N_d·e^{−j/H₈₃}⌋₊` | `m0_two`, `m0_bot` — `Nat.floor` facts |
| — | — | `Mr_sharp` at `N_d e^{−j/H} ≥ 9/2`, itself FREE on the grid (§8a) |
| `s13KS` | unchanged | `KS_gate` — DISCHARGED (§8c), `(log X)^{197}`-genre room |
| `s13MtailBand C Nd P Q` | `C(log P/log Q)/N_d + 1/N_d²` | `DoorCapErrWS.tail`, through
  `M4RowSupply.m4_tail_mass_at_band` |

⟦§8a — WHY `Mr_sharp` IS NOW FREE⟧  `range` and `Mr_sharp` are read at the SAME `j`, so the
only demand left is the per-block `N_d e^{−j/H} ≥ 9/2` (from `⌈2B⌉₊ ≤ 2B+1` and
`⌊B⌋₊ > B−1`: `2B+1 ≤ 4(B−2)` ⟺ `B ≥ 9/2`).  On the grid `j ≤ ⌊H log Q⌋₊`, so
`B ≥ N_d/Q`, and `Q ≤ Q₈₃ X = exp(μ/log μ)` against `N_d = e^μ` closes it at `μ ≥ 8` with
room to spare.  **The point-band forcing is gone** — nothing in this section relates `P` and
`Q` beyond `P ≤ Q`.

⟦§8c — THE `KS_gate` DISCHARGE⟧  `32·μ^{2+2θ}·20512·μ^{−200}(1+log 2T_ann) ≤ μ^{−θ}` reduces,
at `T_ann ≤ X`, to `656384(2+μ) ≤ μ^{198−3θ}` — a `μ^{197}`-genre demand against a linear one.
Proved off `8^7 = 2097152 ≥ 1312768`.  **The `KS_gate` half of the header's ⟦BAND-WIDTH
TENSION⟧ is therefore resolved outright**: it never constrained the band; it constrained the
scalar.

⟦§8d — THE `E_ge` LINE, ROW BY ROW⟧  `DoorCapErrWS.E_ge` is discharged from THREE named gate
lines, one per row of `ramErr_meanSq_all_chi_ws_priced`'s bound, each charged to `EP2` (the
`s13E` pin gives the row sum exactly `2160·W + 3·EP2`, so no slack is lost in the split):

* ⟦THE `φ(q)` LINE⟧ `phi_row` — `4·520·φ(q)·W ≤ 2160·W + EP2`, sufficient form
  `4160·φ(q)·μ^{−θ₂₉₃} ≤ EP2` at `W ≤ 2μ^{−θ₂₉₃}`.  **`4·520·φ(q)` against `3·720` fits only
  at `φ(q) ≤ 1.038`; for `φ(q) ≥ 2` the excess exits through `EP2`, and that is a genuine
  `q`-vs-base gate.**  ⟦CORRECTION 3 — ITS HONEST HOME⟧ it does NOT close against the
  capstone's `q ≤ (log X)^{12}` (there both sides are exponential and the `q`-side is bigger
  at every `μ`); it closes ONLY against `SocketBase`'s own H-SIDE modulus ledger
  `q ≤ arcDen 12 H = (log H)^{12}` — carried here as `q_arcDen` — through the `hPHheadroom`
  conversion, in the refuter's form `εr·μ ≥ log 16640 + 12·log log H + log(8Cμ)` with
  `εr ≤ θ₂₉₃ − 1/500`, closing at the floor `μ = 1.41·10³²` by 27 orders.
* `p2_row` — the `p²`-correction and end-mass row against `EP2`;
* `tail_row` — the coprime-tail row at the BAND value of `Mtail`, against `EP2`.

⚠ `epsr_theta` (`εr ≤ θ₂₉₃ − 1/500`), the refuter's companion to the `φ(q)` line, is
**deliberately NOT a field of the gate**: read together with the landed `abs8640`
(`8640 ≤ μ^{εr}`, i.e. `εr ≥ log 8640/log μ ≈ 0.122` at the floor) it is in tension, and a
contradictory field would make the whole gate vacuous — a silent trivialization this file
refuses.  The pair is recorded here as the adjudication owed, exactly as §3's header records
`KS_gate`/`E_ge`.

⟦THE BUDGET's CEILING — RETIRED 7/30 (MUCAP-SCOPE; maestro ruling 6)⟧ this file briefly
carried a `mu_cap` field (`log Nd ≤ (5/48)·log 𝒫₂`), transcribed from the KNOT1-REF freeze
at the `μ = log X_d` reading — 8 minutes after K4-CENSUS had pinned `μ = log H` (the
stale-freeze catch, flags #99).  The field had ZERO readers, and was kernel-refuted from
the gate's own `Q2_reg` at every `M ≥ 1` (probe_mucap_internal_kill).  The honest facts:
the bundle's leg is `exp(2·(log S/log 𝒫₂)·loglog S)` at `S = q·Tann` — its absorption
demand sits verbatim inside the carried `budget` field below; the ×1280 window's own
bookkeeping is `MSelect'.winFit` (`S13MSelect2`); the one-more-log shape
`loglog X_d ≤ (5/48)·log 𝒫₂` is kernel-verified satisfiable at the block floor
(scratch probe_mucap_repaired_at_floor) if a documented ceiling is ever wanted.

**PURELY ADDITIVE.**  §1–§7 stand unmodified. -/

/-- ⟦THE PER-BLOCK RANGE CAP⟧ `Mr j := ⌈2·N_d·e^{−j/H₈₃}⌉₊` — the ram window's own top at
block `j`, rounded up.  `DoorCapBasePerBlock.range` is then definitional (§8a). -/
def s13Mr (Nd : ℕ) (j : ℕ) : ℕ :=
  ⌈2 * ((Nd : ℕ) : ℝ) * Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293)⌉₊

/-- ⟦V4a's CO-FACTOR LENGTH, PER BLOCK⟧ `m₀ j := ⌊N_d·e^{−j/H₈₃}⌋₊` — the window's own
BOTTOM, rounded down, so `m0_bot` is `Nat.floor_le` and `Mr_sharp` is the two roundings. -/
def s13m0 (Nd : ℕ) (j : ℕ) : ℕ :=
  ⌊((Nd : ℕ) : ℝ) * Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293)⌋₊

/-- ⟦R3a, RE-PINNED TO THE BAND⟧ `Mtail := C·(log P/log Q)/N_d + 1/N_d²` —
`M4RowSupply.m4_tail_mass_at_band`'s own value, in place of §2's `s13Mtail` (the raw sum).
The re-pin is what makes `DoorCapErrWS.tail` a WIRE instead of `le_rfl`, at the price of the
band lemma's two side conditions (`Q_hundred`, `band_product`). -/
noncomputable def s13MtailBand (C : ℝ) (Nd P Q : ℕ) : ℝ :=
  C * (Real.log (P : ℝ) / Real.log (Q : ℝ)) / ((Nd : ℕ) : ℝ) + 1 / ((Nd : ℕ) : ℝ) ^ 2

/-! ### §8a — the grid stones -/

/-- `e² < 8` — the numeral behind `2 ≤ log μ` at `μ ≥ 8`. -/
theorem s13_exp_two_lt_eight : Real.exp 2 < 8 := by
  have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h1 := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  nlinarith

/-- `0 < N_d` off the scale floor. -/
theorem s13_Nd_pos {Nd : ℕ} (h8 : 8 ≤ Real.log ((Nd : ℕ) : ℝ)) : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos Nd with h0 | hpos
  · exfalso
    rw [h0] at h8
    simp only [Nat.cast_zero, Real.log_zero] at h8
    linarith
  · exact_mod_cast hpos

/-- **⟦THE GRID FLOOR⟧** (`s13_ramRbot_ge`).  On the ram grid the co-factor window's bottom is
at least `9/2`: `j ≤ ⌊H·log Q⌋₊` gives `N_d e^{−j/H} ≥ N_d/Q`, and `Q ≤ Q₈₃ X = e^{μ/log μ}`
against `N_d = e^μ` closes it at `μ ≥ 8` (`log μ ≥ 2`, so `μ/log μ ≤ μ/2`, and
`e^{μ/2} ≥ μ/2 + 1 ≥ 5`).  This ONE line is what `Mr_sharp` costs after the arity repair. -/
theorem s13_ramRbot_ge {Nd P Q j : ℕ} (h8 : 8 ≤ Real.log ((Nd : ℕ) : ℝ))
    (hQ0 : 0 < Q) (hQhigh : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ))
    (hj : j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q) :
    (9 : ℝ) / 2 ≤ ((Nd : ℕ) : ℝ) * Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293) := by
  obtain ⟨hθ0, hθ1⟩ := theta293_pos_le_one
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := s13_Nd_pos h8
  have hμ0 : (0 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hH0 : (0 : ℝ) < H83 ((Nd : ℕ) : ℝ) theta293 := by
    rw [H83]; exact Real.rpow_pos_of_pos hμ0 _
  have hQ0R : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ0
  have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ0
  have hlogQ0 : (0 : ℝ) ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1R
  -- ⟦the grid top⟧
  have hjtop : j ≤ ⌊H83 ((Nd : ℕ) : ℝ) theta293 * Real.log (Q : ℝ)⌋₊ := by
    rw [ramI, Finset.mem_Icc] at hj
    exact hj.2
  have hjR : (j : ℝ) ≤ H83 ((Nd : ℕ) : ℝ) theta293 * Real.log (Q : ℝ) := by
    refine le_trans ?_ (Nat.floor_le (by positivity))
    exact_mod_cast hjtop
  have hdiv : (j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293 ≤ Real.log (Q : ℝ) :=
    (div_le_iff₀ hH0).mpr (by linarith [hjR])
  have hexp : (Q : ℝ)⁻¹ ≤ Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293) := by
    have h1 : Real.exp (-Real.log (Q : ℝ))
        ≤ Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293) := by
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div]
      linarith
    rwa [Real.exp_neg, Real.exp_log hQ0R] at h1
  -- ⟦the numeral: `9Q/2 ≤ N_d`⟧
  have hlogμ2 : (2 : ℝ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
    rw [Real.le_log_iff_exp_le hμ0]
    linarith [s13_exp_two_lt_eight]
  have hQ83 : (Q : ℝ) ≤ Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) := by
    refine le_trans hQhigh ?_
    rw [Q83]
    refine Real.exp_le_exp.mpr ?_
    exact div_le_div_of_nonneg_left hμ0.le (by norm_num) hlogμ2
  have hhalf : (9 : ℝ) / 2 ≤ Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) := by
    have h := Real.add_one_le_exp (Real.log ((Nd : ℕ) : ℝ) / 2)
    linarith
  have hNdexp : ((Nd : ℕ) : ℝ)
      = Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) * Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) := by
    rw [← Real.exp_add]
    have : Real.log ((Nd : ℕ) : ℝ) / 2 + Real.log ((Nd : ℕ) : ℝ) / 2
        = Real.log ((Nd : ℕ) : ℝ) := by ring
    rw [this, Real.exp_log hNd0]
  have hQNd : (9 : ℝ) / 2 * (Q : ℝ) ≤ ((Nd : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) := Real.exp_pos _
    calc (9 : ℝ) / 2 * (Q : ℝ)
        ≤ 9 / 2 * Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) := by linarith
      _ ≤ Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2)
            * Real.exp (Real.log ((Nd : ℕ) : ℝ) / 2) := by nlinarith
      _ = ((Nd : ℕ) : ℝ) := hNdexp.symm
  -- ⟦assemble⟧
  have hstep : ((Nd : ℕ) : ℝ) * (Q : ℝ)⁻¹
      ≤ ((Nd : ℕ) : ℝ) * Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293) :=
    mul_le_mul_of_nonneg_left hexp hNd0.le
  have hfrac : (9 : ℝ) / 2 ≤ ((Nd : ℕ) : ℝ) * (Q : ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hQ0R]
    linarith [hQNd]
  linarith

/-- **⟦`range`, DEFINITIONAL⟧** (`s13_range_perBlock`).  Every member of the block-`j` window
is `≤ ⌈2N_d e^{−j/H}⌉₊` by the window's own top, and `≥ 1` by the ambient `Icc 1 N`. -/
theorem s13_range_perBlock (Nd P Q : ℕ) :
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ramRrange (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd j ⊆ Finset.Icc 1 (s13Mr Nd j) := by
  intro j _ m hm
  rw [ramRrange, Finset.mem_filter, Finset.mem_Icc] at hm
  obtain ⟨⟨hm1, _⟩, _, hmtop⟩ := hm
  refine Finset.mem_Icc.mpr ⟨hm1, ?_⟩
  have h := Nat.ceil_le_ceil hmtop
  rwa [Nat.ceil_natCast] at h

/-- **⟦`m0_bot`⟧** — `⌊B⌋₊ ≤ B = ramRbot`. -/
theorem s13_m0_bot (Nd P Q : ℕ) :
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ((s13m0 Nd j : ℕ) : ℝ) ≤ ramRbot (H83 ((Nd : ℕ) : ℝ) theta293) Nd j := by
  intro j _
  rw [s13m0, ramRbot]
  exact Nat.floor_le (by positivity)

/-- **⟦`m0_two`⟧** — `2 ≤ ⌊B⌋₊` off the grid floor `B ≥ 9/2`. -/
theorem s13_m0_two {Nd P Q : ℕ} (h8 : 8 ≤ Real.log ((Nd : ℕ) : ℝ)) (hQ0 : 0 < Q)
    (hQhigh : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)) :
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q, 2 ≤ s13m0 Nd j := by
  intro j hj
  have hB := s13_ramRbot_ge h8 hQ0 hQhigh hj
  rw [s13m0]
  refine Nat.le_floor ?_
  push_cast
  linarith

/-- **⟦`Mr_sharp`, DISCHARGED⟧** (`s13_Mr_sharp`).  `⌈2B⌉₊ < 2B + 1` and `B < ⌊B⌋₊ + 1` give
`Mr j ≤ 2B + 1 ≤ 4(B − 2) ≤ 4(⌊B⌋₊ − 1)` as soon as `B ≥ 9/2` — which §8a's grid floor
supplies at every block.  **This is the line that, at a SCALAR `Mr`, collided with `range`
read at the other end of the band and forced `Q ≤ 2P`.** -/
theorem s13_Mr_sharp {Nd P Q : ℕ} (h8 : 8 ≤ Real.log ((Nd : ℕ) : ℝ)) (hQ0 : 0 < Q)
    (hQhigh : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)) :
    ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
      ((s13Mr Nd j : ℕ) : ℝ) ≤ 4 * (((s13m0 Nd j : ℕ) : ℝ) - 1) := by
  intro j hj
  have hB := s13_ramRbot_ge h8 hQ0 hQhigh hj
  have hceil : ((s13Mr Nd j : ℕ) : ℝ)
      < 2 * ((Nd : ℕ) : ℝ) * Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293) + 1 := by
    rw [s13Mr]
    exact Nat.ceil_lt_add_one (by linarith)
  have hfloor : ((Nd : ℕ) : ℝ) * Real.exp (-(j : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293)
      < ((s13m0 Nd j : ℕ) : ℝ) + 1 := by
    rw [s13m0]
    exact Nat.lt_floor_add_one _
  linarith

/-! ### §8c — the `KS_gate` discharge -/

/-- **⟦THE `KS_gate`, DISCHARGED⟧** (`s13_KS_gate`).
`32·μ^{2+2θ}·(20512·μ^{−200}(1+log 2T_ann)) ≤ μ^{−θ}` at `T_ann ≤ X`, `μ = log X ≥ 8`.
The exponent budget is `2+2θ−200 → −θ`, i.e. `198−3θ ≥ 197` powers of `μ` against
`656384(2+μ)`; `8^7 = 2097152 ≥ 1312768` closes it with 190 powers unused. -/
theorem s13_KS_gate {Nd : ℕ} {Tann : ℝ} (h8 : 8 ≤ Real.log ((Nd : ℕ) : ℝ))
    (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ)) :
    32 * (Real.log ((Nd : ℕ) : ℝ)) ^ (2 + 2 * theta293) * s13KS Nd Tann
      ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by
  obtain ⟨hθ0, hθ1⟩ := theta293_pos_le_one
  set μ := Real.log ((Nd : ℕ) : ℝ) with hμdef
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := s13_Nd_pos h8
  have hμ0 : (0 : ℝ) < μ := by rw [hμdef]; linarith
  have hμ1 : (1 : ℝ) ≤ μ := by linarith
  -- ⟦the height leg⟧
  have hS : 1 + Real.log (2 * Tann) ≤ 2 + μ := by
    have h2T : (0 : ℝ) < 2 * Tann := by linarith
    have hle : Real.log (2 * Tann) ≤ Real.log (2 * ((Nd : ℕ) : ℝ)) :=
      Real.log_le_log h2T (by linarith)
    have hsplit : Real.log (2 * ((Nd : ℕ) : ℝ)) = Real.log 2 + μ := by
      rw [Real.log_mul (by norm_num) hNd0.ne', hμdef]
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    linarith
  -- ⟦the exponent room⟧
  have hkey : (1312768 : ℝ) ≤ μ ^ (197 - 3 * theta293 : ℝ) := by
    have h1 : (8 : ℝ) ^ (7 : ℝ) ≤ μ ^ (7 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) (by rw [hμdef]; linarith) (by norm_num)
    have h2 : μ ^ (7 : ℝ) ≤ μ ^ (197 - 3 * theta293 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hμ1 (by linarith)
    have h3 : (8 : ℝ) ^ (7 : ℝ) = 2097152 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hstep : 656384 * (1 + Real.log (2 * Tann))
      ≤ μ ^ (197 - 3 * theta293 : ℝ) * μ := by
    have h1 : 656384 * (1 + Real.log (2 * Tann)) ≤ 656384 * (2 + μ) := by linarith
    have h2 : (656384 : ℝ) * (2 + μ) ≤ 1312768 * μ := by linarith
    have h3 : (1312768 : ℝ) * μ ≤ μ ^ (197 - 3 * theta293 : ℝ) * μ :=
      mul_le_mul_of_nonneg_right hkey hμ0.le
    linarith
  -- ⟦the exponent identity⟧
  have hid : μ ^ (2 + 2 * theta293 : ℝ) * μ ^ (-200 : ℝ)
      * (μ ^ (197 - 3 * theta293 : ℝ) * μ ^ (1 : ℝ)) = μ ^ (-theta293 : ℝ) := by
    rw [← Real.rpow_add hμ0, ← Real.rpow_add hμ0, ← Real.rpow_add hμ0]
    ring_nf
  rw [Real.rpow_one] at hid
  have hApos : (0 : ℝ) < μ ^ (2 + 2 * theta293 : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have hBpos : (0 : ℝ) < μ ^ (-200 : ℝ) := Real.rpow_pos_of_pos hμ0 _
  have hmul := mul_le_mul_of_nonneg_right hstep
    (mul_pos hApos hBpos).le
  rw [s13KS, ← hμdef, ← hid]
  nlinarith [hmul, hApos, hBpos]

/-! ### §8d — ⟦THE PER-BASE GATE, PER-BLOCK⟧ `S13CapGatePerBlock` -/

/-- **⟦THE PER-BASE GATE, PER-BLOCK⟧** (`S13CapGatePerBlock`).  §3's gate at the per-block
pins.  Against `S13CapGate` the changes are:

* GONE (discharged in §8): `range`, `m0_two`, `m0_bot`, `Mr_sharp`, `KS_gate`, and
  `DoorCapErrWS.E_ge` itself;
* NEW: the scale floor is `8 ≤ log X` (was `4`; `logX_four` comes off it) — the strengthening
  §8a's grid floor asks for, free at every base the regime reaches; `P_le_Q`; the tail band's
  two side conditions `Q_hundred` and `band_product`; the three `E_ge` rows `phi_row`,
  `p2_row`, `tail_row`; and the `φ(q)` line's honest modulus home `q_arcDen`;
* `budget` now reads the PER-BLOCK cap `s13Mr Nd j` inside `∀ j ∈ ramI`.

`Hreg` is the regime's own length `H` (the `SocketBase` slot), and enters ONLY through
`q_arcDen` — it is never identified with `log X`, `log(qT_ann)` or `log Q_base`. -/
structure S13CapGatePerBlock (Cq cs T₀ Kq Ks C : ℝ) (M Nd q P Q Hreg : ℕ)
    (Tann Rrad Rbd CR EP2 εr : ℝ) : Prop where
  -- ⟦THE SCALE FLOOR⟧
  /-- `8 ≤ log X` — §3's `logX_four` strengthened by one octave (§8a's grid floor). -/
  logX_eight : 8 ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- `2 ≤ H₈₃ X θ₂₉₃` — ONE field for both bundles. -/
  H83_two : 2 ≤ H83 ((Nd : ℕ) : ℝ) theta293
  -- ⟦(A) THE RAZOR — the three that do not reduce⟧
  /-- `𝒬K₂ ≤ q·T_ann`. -/
  QTann : ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann
  /-- ⟦MR (21)⟧'s κ-gate at the designated level. -/
  kappa30Q : 30 ≤ Real.log ((q : ℝ) * Tann)
    / Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
  /-- `q ≤ (log X)^{12}` — the capstone's base-side modulus gate. -/
  q_logX : (q : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ 12
  -- ⟦(B) THE SOCKET FLOOR AT `(q, T_ann)`⟧
  /-- `T₀ ≤ T_ann`. -/
  T0_Tann : T₀ ≤ Tann
  /-- Floor gate 1. -/
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
  /-- `log(q·T_ann) ≤ Lr` at the pinned `Lr = (log X)^{11/10}`. -/
  logqT_L : Real.log ((q : ℝ) * Tann) ≤ s13Lr Nd
  -- ⟦(D) THE RAM-BLOCK FRAME⟧
  /-- `P₈₃ X θ₂₉₃ ≤ P`. -/
  P_low : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)
  /-- `log 𝒬K₂ ≤ √(log X)` — `DoorRowZeroBase.reg` VERBATIM (§1's band gate). -/
  Q2_reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
    ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))
  /-- `0 < Q`. -/
  Q_pos : 0 < Q
  /-- `Q ≤ Q₈₃ X`. -/
  Q_high : (Q : ℝ) ≤ Q83 ((Nd : ℕ) : ℝ)
  /-- `P ≤ Q` — the band is a band.  ⟦NOTHING relates `P` and `Q` beyond this⟧: the
  point-band forcing of §3's header was the scalar `Mr`'s artifact and is gone. -/
  P_le_Q : P ≤ Q
  /-- ⟦THE GRADED BUDGET, PER-BLOCK⟧ at the pinned `VJ`, `η`, `εd` and the per-block cap. -/
  budget : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    thinBundleGChi ((q : ℝ) * Tann) (s13VJ M) (calH (H1door M) 2)
        (calP (Adoor M) (3072 * M) 2) (calQK (Adoor M) (3072 * M) M 2)
      * ((Nd : ℕ) : ℝ) ^ (1 - 2 * s13Eta + s13EpsD q Nd) ≤ ((s13Mr Nd j : ℕ) : ℝ)
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
  /-- `log Q_base ≤ Lr` on the grid. -/
  WL : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j) ≤ s13Lr Nd
  /-- The `cs`-gate on the grid — the field that CAPS `Lr` from above. -/
  gate : ∀ j ∈ ramI (H83 ((Nd : ℕ) : ℝ) theta293) P Q,
    420 * s13Lr Nd * (s13Lr Nd) ^ ((3 : ℝ) / 4) * (Real.log (s13Lr Nd)) ^ 5
      ≤ cs * (Real.log (ramQbase (H83 ((Nd : ℕ) : ℝ) theta293) P j)) ^ 2
  -- ⟦(E) THE CO-FACTOR BOUND AND ITS GRADE⟧
  /-- `0 ≤ Rbd`. -/
  Rbd_nonneg : 0 ≤ Rbd
  /-- ⟦THE ZENO LINE⟧. -/
  Rbd_grade : Rbd ≤ CR * (Real.log ((Nd : ℕ) : ℝ)) ^ (-rho293)
  /-- ⟦THE `Cq`-GATE⟧. -/
  Cq_gate : 1728 * Cq * CR ^ 2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (2 * theta293)
  /-- ⟦THE `Rbd` SUPPLY⟧ the door's un-phased co-factor socket at the free centre. -/
  Rbd_socket : ∀ (t₁ : ℝ) (χ : DirichletCharacter ℂ q),
    CofactorSocket (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q Tann Rrad t₁ Rbd
      (doorCofactor0 χ (calP (Adoor M) (3072 * M))
        (calQK (Adoor M) (3072 * M) M) 2 1)
  -- ⟦(F) LEMMA 12's ERROR ROW, ROW BY ROW⟧
  /-- `0 ≤ εr`. -/
  epsr_nonneg : 0 ≤ εr
  /-- `8640 ≤ (log X)^{εr}`. -/
  abs8640 : 8640 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ εr
  /-- The `p²`-correction row's absorption. -/
  EP2_gate : 12 * EP2 ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293 + εr)
  /-- ⟦THE `φ(q)` LINE — correction 3's honest home⟧ `q ≤ arcDen 12 H = (log H)^{12}`, the
  H-SIDE modulus ledger `SocketBase` itself carries.  The `φ(q)` row does NOT close against
  the base-side `q_logX`; it closes here. -/
  q_arcDen : (q : ℝ) ≤ arcDen 12 Hreg
  /-- ⟦THE `φ(q)` ROW⟧ `4·520·φ(q)·W ≤ EP2` in the sufficient form `W ≤ 2μ^{−θ₂₉₃}` — the
  `4·520·φ(q)` vs `3·720` excess, charged to `EP2`.  Refuter form:
  `εr·μ ≥ log 16640 + 12·log log H + log(8Cμ)` (27 orders at the floor). -/
  phi_row : 4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) ≤ EP2
  /-- ⟦THE `p²`/END-MASS ROW⟧ against `EP2`. -/
  p2_row : 4 * (2 * (q.totient : ℝ) * Tann
        + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q)
      * (16 * Real.logb 2 (2 * ((Nd : ℕ) : ℝ)) / (((Nd : ℕ) : ℝ) * (P : ℝ)) + endMass Nd)
    ≤ EP2
  /-- ⟦THE COPRIME-TAIL ROW⟧ at the BAND value of `Mtail`, against `EP2`. -/
  tail_row : 4 * (2 * (q.totient : ℝ) * Tann
        + 7 * (q.totient : ℝ) * (((2 * Nd : ℕ)) : ℝ) / q) * s13MtailBand C Nd P Q
    ≤ EP2
  /-- ⟦THE TAIL BAND's SIDE CONDITION 1⟧ `100·log Q ≤ log X_d`. -/
  Q_hundred : 100 * Real.log (Q : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ)
  /-- ⟦THE TAIL BAND's SIDE CONDITION 2⟧ the band product. -/
  band_product : ((Nat.sqrt Nd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
    ≤ ((Nd : ℕ) : ℝ) * (Real.log (P : ℝ) / Real.log (Q : ℝ))

/-! ### §8e — the two bundles at the per-block pins -/

/-- `2 ≤ P` off `P_low` — `P₈₃ = exp((log X)^{1−θ}) ≥ e > 2` at `log X ≥ 1`. -/
theorem s13_P_two {Nd P : ℕ} (h8 : 8 ≤ Real.log ((Nd : ℕ) : ℝ))
    (hPlow : P83 ((Nd : ℕ) : ℝ) theta293 ≤ (P : ℝ)) : 2 ≤ P := by
  obtain ⟨hθ0, hθ1⟩ := theta293_pos_le_one
  have hμ1 : (1 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hone : (1 : ℝ) ≤ (Real.log ((Nd : ℕ) : ℝ)) ^ (1 - theta293) := by
    have := Real.rpow_le_rpow_of_exponent_le hμ1 (by linarith : (0 : ℝ) ≤ 1 - theta293)
    rwa [Real.rpow_zero] at this
  have hP : (2 : ℝ) < (P : ℝ) := by
    have h1 : Real.exp 1 ≤ P83 ((Nd : ℕ) : ℝ) theta293 := by
      rw [P83]
      exact Real.exp_le_exp.mpr hone
    have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 1 < 2) (by exact_mod_cast hP.le)

/-- **⟦THE ERROR BUNDLE, PER-BLOCK PINS⟧** (`s13_doorCapErrWS_perBlock`).
`RamErrWS.DoorCapErrWS` at `Mtail := s13MtailBand C Nd P Q`.  Against §5's version TWO fields
move: `tail` becomes the WIRE `M4RowSupply.m4_tail_mass_at_band` (at the gate's `Q_hundred`
and `band_product`), and `E_ge` is DISCHARGED from the gate's three rows. -/
theorem s13_doorCapErrWS_perBlock {Cq cs T₀ Kq Ks C : ℝ} {M Nd q P Q Hreg : ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ}
    (hband : ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 100 * Real.log Q ≤ Real.log Xd →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
    (hM : 1 ≤ M) (hNd : 1 ≤ Nd)
    (hg : S13CapGatePerBlock Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 εr)
    (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ)) :
    DoorCapErrWS M Nd q Nd P Q (doorCoeffU M) liouvilleC Tann
      (s13E Nd Tann EP2) (s13MtailBand C Nd P Q) := by
  have h8 := hg.logX_eight
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := s13_Nd_pos h8
  have hlogX1 : (1 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hP2 : 2 ≤ P := s13_P_two h8 hg.P_low
  -- ⟦the datum's window pin⟧
  have hasupp : ∀ n : ℕ, winCutH Nd (doorCoeffU M) n ≠ 0 → Nd ≤ n ∧ n ≤ 2 * Nd := by
    intro n hn
    obtain ⟨h1, h2⟩ := winCutH_asupp hn
    exact ⟨h1, h2⟩
  refine
    { Xd_eq := rfl
      Nd_one := hNd
      H83_two := hg.H83_two
      H83_le := s13_H83_le (by linarith)
      P_one := by omega
      Tann_nonneg := by linarith
      b_one := norm_doorCoeffU_le_one M
      cf_one := liouvilleC_norm_le_one
      coefWS := doorCoeffU_seamCoefWS_band_H M Nd P Q
        (door_band_gate_of_log (by omega : 1 ≤ 3072 * M) hlogX1 hg.Q2_reg hg.P_low)
      tail := ?_
      E_ge := ?_ }
  · -- ⟦the tail, WIRED at the band⟧
    exact hband P Q Nd (2 * Nd) (winCutH Nd (doorCoeffU M)) hP2 hg.P_le_Q hNd
      hg.Q_hundred hg.band_product (fun n => norm_doorRowDatumU_le_one M Nd n) hasupp
  · -- ⟦`E_ge`, row by row⟧
    have hH0 : (0 : ℝ) < H83 ((Nd : ℕ) : ℝ) theta293 := by
      rw [H83]; exact Real.rpow_pos_of_pos (by linarith) _
    have hφ0 : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    -- ⟦`W ≤ 2·μ^{−θ}` and `0 ≤ W`⟧
    have hWnn : (0 : ℝ) ≤ (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293 := by
      have : (0 : ℝ) ≤ Tann / ((Nd : ℕ) : ℝ) := by positivity
      positivity
    have hWle : (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293
        ≤ 2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by
      have h2 : Tann / ((Nd : ℕ) : ℝ) + 1 ≤ 2 := by
        have : Tann / ((Nd : ℕ) : ℝ) ≤ 1 := (div_le_one hNd0).mpr hTX
        linarith
      have hHinv : (0 : ℝ) ≤ (H83 ((Nd : ℕ) : ℝ) theta293)⁻¹ := (inv_pos.mpr hH0).le
      have h3 : (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293
          ≤ 2 / H83 ((Nd : ℕ) : ℝ) theta293 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h2 hHinv
      have h4 : (2 : ℝ) / H83 ((Nd : ℕ) : ℝ) theta293
          = 2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by
        rw [H83, Real.rpow_neg (by linarith : (0 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ)),
          div_eq_mul_inv]
      linarith [h3, h4.le, h4.ge]
    -- ⟦row 1 — the `φ(q)` line⟧
    have hrow1 : 4 * ((q.totient : ℝ)
          * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293))
        ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293) + EP2 := by
      have hstep : (q.totient : ℝ)
            * ((Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)
          ≤ (q.totient : ℝ) * (2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293)) :=
        mul_le_mul_of_nonneg_left hWle hφ0
      have hnn : (0 : ℝ) ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1)
          / H83 ((Nd : ℕ) : ℝ) theta293) := by
        have : (0 : ℝ) ≤ Tann / ((Nd : ℕ) : ℝ) := by positivity
        positivity
      calc 4 * ((q.totient : ℝ)
              * (520 * (Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293))
          = 2080 * ((q.totient : ℝ)
              * ((Tann / ((Nd : ℕ) : ℝ) + 1) / H83 ((Nd : ℕ) : ℝ) theta293)) := by
            ring
        _ ≤ 2080 * ((q.totient : ℝ)
              * (2 * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293))) :=
            mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = 4160 * (q.totient : ℝ) * (Real.log ((Nd : ℕ) : ℝ)) ^ (-theta293) := by ring
        _ ≤ EP2 := hg.phi_row
        _ ≤ 3 * (720 * (Tann / ((Nd : ℕ) : ℝ) + 1)
              / H83 ((Nd : ℕ) : ℝ) theta293) + EP2 := by linarith
    -- ⟦rows 2 and 3⟧
    have hrow2 := hg.p2_row
    have hrow3 := hg.tail_row
    rw [s13E]
    linarith [hrow1, hrow2, hrow3]

set_option maxHeartbeats 1000000 in
-- The bundle has fifty-eight fields; one `refine` elaborates the whole list.
/-- **⟦THE CAP BUNDLE, PER-BLOCK PINS⟧** (`s13_doorCapBase_perBlock`).
`M4CapWire.DoorCapBasePerBlock` at §2's pins and §8's per-block cap `s13Mr Nd`.  Against §5's
version FIVE more fields are discharged — `range` (§8a, definitional), `KS_gate` (§8c), and
the `KS` wire's `m0_two`/`m0_bot`/`Mr_sharp` (§8a's grid floor) — and `budget` is read
per-block off the gate. -/
theorem s13_doorCapBase_perBlock {Cq cs T₀ Kq Ks C : ℝ} {M Nd q P Q Hreg : ℕ}
    {Tann Rrad Rbd CR EP2 εr : ℝ} (hM : 1 ≤ M) (hNd : 1 ≤ Nd)
    (hg : S13CapGatePerBlock Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 εr)
    (hq : 1 ≤ q) (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ))
    (hTll : 5 ≤ Real.log (Real.log Tann))
    (hE : (∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
        ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Nd P Q
          (chiBarCoeff q χ (winCutH Nd (doorCoeffU M))) (chiBarCoeff q χ (doorCoeffU M))
          (chiBarCoeff q χ liouvilleC) t‖ ^ 2) ≤ s13E Nd Tann EP2) :
    DoorCapBasePerBlock Cq cs T₀ Kq Ks M Nd q Nd P Q (s13Mr Nd) s13Jb (doorCoeffU M)
      liouvilleC Tann (s13VJ M) (s13V Nd) (s13Lr Nd) s13Eta (s13EpsD q Nd) εr Rbd CR
      (s13KS Nd Tann) (s13E Nd Tann EP2) EP2 := by
  have h8 := hg.logX_eight
  have hLX4 : (4 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hLX1 : (1 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hLX0 : (0 : ℝ) < Real.log ((Nd : ℕ) : ℝ) := by linarith
  have hNdR : (0 : ℝ) < ((Nd : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hNd
    linarith
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith
  -- ⟦the razor's level and its exponent⟧
  have halpha : mrAlpha (1 / 12) 2 = 7 / 48 := by rw [mrAlpha]; norm_num
  have hH1 : (2 : ℝ) ≤ H1door M := H1door_two hM
  have hcalH : calH (H1door M) 2 = 4 * H1door M := by rw [calH]; norm_num
  have hcalH0 : (0 : ℝ) < calH (H1door M) 2 := by rw [hcalH]; linarith
  -- ⟦the height scale⟧
  have hqT1 : (1 : ℝ) < (q : ℝ) * Tann := by nlinarith
  have hlogqT0 : (0 : ℝ) < Real.log ((q : ℝ) * Tann) := Real.log_pos hqT1
  have hloglog5 : (5 : ℝ) ≤ Real.log (Real.log ((q : ℝ) * Tann)) := by
    have hTpos : (0 : ℝ) < Tann := by linarith
    have h1 : Real.log Tann ≤ Real.log ((q : ℝ) * Tann) :=
      Real.log_le_log hTpos (by nlinarith)
    have hlogT0 : (0 : ℝ) < Real.log Tann := Real.log_pos hT1
    exact le_trans hTll (Real.log_le_log hlogT0 h1)
  have hlogqT1 : (1 : ℝ) ≤ Real.log ((q : ℝ) * Tann) := by
    by_cases hc : (1 : ℝ) ≤ Real.log ((q : ℝ) * Tann)
    · exact hc
    · exfalso
      have hlt : Real.log ((q : ℝ) * Tann) < 1 := not_le.mp hc
      have : Real.log (Real.log ((q : ℝ) * Tann)) < 0 := Real.log_neg hlogqT0 hlt
      linarith
  -- ⟦the ladder⟧
  have hA0 : 0 < Adoor M := by
    rw [Adoor]; exact Nat.mul_pos (by norm_num) (Nat.succ_pos _)
  have hE2 : 2 ≤ calE (Adoor M) (3072 * M) 2 := by
    have h : calE (Adoor M) (3072 * M) 2 = Adoor M * (3072 * M) * 4 := by
      rw [calE]; norm_num [Nat.factorial]
    rw [h]
    have h1 : 1 ≤ Adoor M := hA0
    have h2 : 1 ≤ 3072 * M := by omega
    nlinarith
  -- ⟦the pinned `Lr` and `V`⟧
  have hLr : s13Lr Nd = (Real.log ((Nd : ℕ) : ℝ)) ^ ((11 : ℝ) / 10) := rfl
  have hLrge : Real.log ((Nd : ℕ) : ℝ) ≤ s13Lr Nd := by
    rw [hLr]
    have := Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num : (1 : ℝ) ≤ (11 : ℝ) / 10)
    rwa [Real.rpow_one] at this
  have hLrpos : (0 : ℝ) < s13Lr Nd := by linarith
  have hlogLr : Real.log (s13Lr Nd) = (11 / 10 : ℝ) * Real.log (Real.log ((Nd : ℕ) : ℝ)) := by
    rw [hLr, Real.log_rpow hLX0]
  have hlogLXnn : (0 : ℝ) ≤ Real.log (Real.log ((Nd : ℕ) : ℝ)) := Real.log_nonneg hLX1
  refine
    { Jb_lo := by rw [s13Jb]; norm_num
      Jb_hi := by rw [s13Jb]
      Hseq_two := ?_
      alpha_nonneg := by rw [s13Jb, halpha]; norm_num
      Tann_one := by linarith
      qTann_one := hqT1
      P_three := ?_
      PQ := ?_
      QTann := hg.QTann
      kappa30Q := hg.kappa30Q
      loglog5 := hloglog5
      VJ_bound := ?_
      alpha_eta := by rw [s13Jb, halpha, s13Eta]; norm_num
      eta_half := by rw [s13Eta]; norm_num
      Tann_X := hTX
      X_pos := hNdR
      debit := ?_
      logX_pos := hLX0
      q_logX := hg.q_logX
      V_one := ?_
      V_inv := ?_
      T0_Tann := hg.T0_Tann
      floor1 := hg.floor1
      floor2 := hg.floor2
      floor3 := hg.floor3
      floor4 := hg.floor4
      logqT_one := hlogqT1
      logqT_L := hg.logqT_L
      L_exp := ?_
      logV_L := ?_
      H83_two := hg.H83_two
      logX_exp := ?_
      logX_four := hLX4
      cf_one := liouvilleC_norm_le_one
      P_low := hg.P_low
      Q_pos := hg.Q_pos
      Q_high := hg.Q_high
      range := s13_range_perBlock Nd P Q
      budget := hg.budget
      Hj := hg.Hj
      B3 := hg.B3
      BT := hg.BT
      kappa30 := hg.kappa30
      BT10 := hg.BT10
      WL := hg.WL
      gate := hg.gate
      Rbd_nonneg := hg.Rbd_nonneg
      Rbd_grade := hg.Rbd_grade
      Cq_gate := hg.Cq_gate
      Rbd_binder := m4_capRbd_at_door hg.Rbd_socket
      KS_nonneg := ?_
      KS_binder := ?_
      KS_gate := s13_KS_gate h8 hT1 hTX
      epsr_nonneg := hg.epsr_nonneg
      abs8640 := hg.abs8640
      EP2_gate := hg.EP2_gate
      E_row := le_rfl
      E_binder := hE }
  · -- ⟦`Hseq_two`⟧
    rw [s13Jb, hcalH]; linarith
  · -- ⟦`P_three`⟧
    rw [s13Jb, calP]
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ calE (Adoor M) (3072 * M) 2 := Nat.pow_le_pow_right (by norm_num) hE2
  · -- ⟦`PQ`⟧
    rw [s13Jb, calP, calQK]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have : 1 * calE (Adoor M) (3072 * M) 2 ≤ (2 ^ 2 * M) * calE (Adoor M) (3072 * M) 2 :=
      Nat.mul_le_mul_right _ (by omega)
    simpa using this
  · -- ⟦`VJ_bound`⟧
    intro v hv
    rw [s13VJ, s13Jb]
    refine Real.exp_le_exp.mpr ?_
    rw [halpha]
    have hvle : (v : ℝ) ≤ calH (H1door M) 2
        * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
      rw [ramI, Finset.mem_Icc] at hv
      have h1 : (v : ℝ) ≤ (⌊calH (H1door M) 2
          * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)⌋₊ : ℝ) := by
        exact_mod_cast hv.2
      have hQ1 : (1 : ℝ) ≤ ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
        exact_mod_cast one_le_calQK (Adoor M) (3072 * M) M 2
      have h2 : (0 : ℝ) ≤ calH (H1door M) 2
          * Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
        have := Real.log_nonneg hQ1
        positivity
      exact le_trans h1 (Nat.floor_le h2)
    rw [div_le_iff₀ hcalH0]
    nlinarith [hvle, hcalH0]
  · -- ⟦`debit`⟧ an EQUALITY at the pinned `εd`
    rw [s13Jb, s13EpsD, halpha]
    have h1 : ((Nd : ℕ) : ℝ) ^ (2 * (7 / 48 : ℝ) * Real.log ((q : ℕ) : ℝ)
        / Real.log ((Nd : ℕ) : ℝ))
        = Real.exp (2 * (7 / 48 : ℝ) * Real.log ((q : ℕ) : ℝ)) := by
      rw [Real.rpow_def_of_pos hNdR]
      congr 1
      field_simp
    have h2 : (q : ℝ) ^ (2 * (7 / 48 : ℝ))
        = Real.exp (Real.log ((q : ℕ) : ℝ) * (2 * (7 / 48 : ℝ))) :=
      Real.rpow_def_of_pos hqR0 _
    rw [h1, h2]
    exact Real.exp_le_exp.mpr (le_of_eq (by ring))
  · -- ⟦`V_one`⟧
    rw [s13V]
    have := Real.rpow_le_rpow_of_exponent_le hLX1 (by norm_num : (0 : ℝ) ≤ (106 : ℝ))
    rwa [Real.rpow_zero] at this
  · -- ⟦`V_inv`⟧
    rw [s13V, ← Real.rpow_neg hLX0.le]
  · -- ⟦`L_exp`⟧
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · -- ⟦`logV_L`⟧
    rw [s13V, Real.log_rpow hLX0, hlogLr]
    linarith
  · -- ⟦`logX_exp`⟧
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  · -- ⟦`KS_nonneg`⟧
    rw [s13KS]
    have h1 : (0 : ℝ) < (Real.log ((Nd : ℕ) : ℝ)) ^ (-200 : ℝ) := Real.rpow_pos_of_pos hLX0 _
    have h2 : (0 : ℝ) ≤ Real.log (2 * Tann) := Real.log_nonneg (by linarith)
    positivity
  · -- ⟦`KS_binder`⟧ through `M4CapWire` §6b, at the per-block cap
    rw [s13KS]
    exact m4_capKS_at_door_perBlock (s13m0 Nd) hLX0.le (by linarith)
      (s13_m0_two h8 hg.Q_pos hg.Q_high) (s13_m0_bot Nd P Q) (s13_range_perBlock Nd P Q)
      (s13_Mr_sharp h8 hg.Q_pos hg.Q_high)

/-! ### §8f — ⟦THE COMPOSITE⟧ at `S12Compose` §3's exact binder shape -/

/-- **⟦THE BUNDLE GROUP, PER-BLOCK⟧** (`doorCapBundle_at_workingPoint_perBlock`). -/
theorem doorCapBundle_at_workingPoint_perBlock {Cq cs T₀ Kq Ks C : ℝ}
    {M Nd q P Q Hreg : ℕ} {Tann Rrad Rbd CR EP2 εr : ℝ}
    (hband : ∀ (P Q Xd N : ℕ) (a : ℕ → ℂ),
      2 ≤ P → P ≤ Q → 1 ≤ Xd → 100 * Real.log Q ≤ Real.log Xd →
      ((Nat.sqrt Xd : ℝ) + 1) * ∏ p ∈ primeBand P Q, (1 + 3 / (p : ℝ))
          ≤ (Xd : ℝ) * (Real.log P / Real.log Q) →
      (∀ n, ‖a n‖ ≤ 1) → (∀ n, a n ≠ 0 → Xd ≤ n ∧ n ≤ 2 * Xd) →
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => blockOmega P Q n = 0),
          ‖a n‖ ^ 2 / (n : ℝ) ^ 2
        ≤ C * (Real.log P / Real.log Q) / (Xd : ℝ) + 1 / (Xd : ℝ) ^ 2)
    (hM : 1 ≤ M) (hNd : 1 ≤ Nd) (hq : 1 ≤ q)
    (hg : S13CapGatePerBlock Cq cs T₀ Kq Ks C M Nd q P Q Hreg Tann Rrad Rbd CR EP2 εr)
    (hT1 : 1 < Tann) (hTX : Tann ≤ ((Nd : ℕ) : ℝ))
    (hTll : 5 ≤ Real.log (Real.log Tann)) :
    ∃ (Xd P' Q' : ℕ) (Mr' : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
      (VJ V Lr η εd Rbd' CR' KS E EP2' Mtail : ℝ),
      DoorCapErrWS M Nd q Xd P' Q' b cf Tann E Mtail
        ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-Tann)..Tann,
              ‖ramErr (H83 ((Nd : ℕ) : ℝ) theta293) (2 * Nd) Xd P' Q'
                (chiBarCoeff q χ (winCutH Nd (doorCoeffU M)))
                (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
            → DoorCapBasePerBlock Cq cs T₀ Kq Ks M Nd q Xd P' Q' Mr' Jb b cf Tann
                VJ V Lr η εd εr Rbd' CR' KS E EP2') := by
  refine ⟨Nd, P, Q, s13Mr Nd, s13Jb, doorCoeffU M, liouvilleC, s13VJ M, s13V Nd, s13Lr Nd,
    s13Eta, s13EpsD q Nd, Rbd, CR, s13KS Nd Tann, s13E Nd Tann EP2, EP2,
    s13MtailBand C Nd P Q,
    s13_doorCapErrWS_perBlock hband hM hNd hg hT1 hTX, ?_⟩
  intro hE
  exact s13_doorCapBase_perBlock hM hNd hg hq hT1 hTX hTll hE

/-- **⟦THE `hcapWS` SLOT, PER-BLOCK, DISCHARGED FROM THE GATE FAMILY⟧**
(`doorCapBundle_family_perBlock`).  `S12Compose.logChowla2_capstone_conditional_perBlock`'s
`hcapWS` hypothesis VERBATIM, from the per-block gate family.  `C` is the corpus's own
coprime-tail constant (`M4RowSupply.m4_tail_mass_at_band`), exposed here because the gate's
`tail_row` prices against it. -/
theorem doorCapBundle_family_perBlock {Cq cs T₀ Kq Ks : ℝ} {R : ChowlaRegime} {M : ℕ}
    (hM : 1 ≤ M) {epsf : ℕ → ℝ} :
    ∃ C : ℝ, 0 < C ∧
      ((∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
        ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          ∃ (P Q : ℕ) (Rrad Rbd CR EP2 : ℝ),
            S13CapGatePerBlock Cq cs T₀ Kq Ks C M (A + s) q P Q H (2 * T) Rrad Rbd CR EP2
              (epsf (A + s))) →
      ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
        ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
          2 * T ≤ (((A + s : ℕ)) : ℝ) → TannGate (((A + s : ℕ)) : ℝ) (2 * T) →
          5 ≤ Real.log (Real.log (2 * T)) →
          ∃ (Xd P Q : ℕ) (Mr : ℕ → ℕ) (Jb : ℕ) (b cf : ℕ → ℂ)
            (VJ V Lr η εd Rbd CR KS E EP2 Mtail : ℝ),
            DoorCapErrWS M (A + s) q Xd P Q b cf (2 * T) E Mtail
              ∧ ((∑ χ : DirichletCharacter ℂ q, ∫ t in (-(2 * T))..(2 * T),
                    ‖ramErr (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) Xd P Q
                      (chiBarCoeff q χ (winCutH (A + s) (doorCoeffU M)))
                      (chiBarCoeff q χ b) (chiBarCoeff q χ cf) t‖ ^ 2) ≤ E
                  → DoorCapBasePerBlock Cq cs T₀ Kq Ks M (A + s) q Xd P Q Mr Jb b cf (2 * T)
                      VJ V Lr η εd (epsf (A + s)) Rbd CR KS E EP2)) := by
  obtain ⟨C, hC, hband⟩ := m4_tail_mass_at_band
  refine ⟨C, hC, ?_⟩
  intro hgate H L q j A s hsb T hTlo hThi hTgate hTll
  obtain ⟨P, Q, Rrad, Rbd, CR, EP2, hg⟩ := hgate H L q j A s hsb T hTlo hThi hTgate hTll
  have hq : 1 ≤ q := hsb.2.2.2.1
  have hA : 0 < A := hsb.2.2.2.2.2.2.2.1
  have hNd : 1 ≤ A + s := by omega
  -- ⟦`1 < T_ann`⟧ off the slot's own `TannGate` against the gate's scale floor
  have hlogX0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by have := hg.logX_eight; linarith
  have hpow : (0 : ℝ) < (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hlogX0 _
  have hexp : 30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2) + 1
      ≤ Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) := Real.add_one_le_exp _
  have hgate2 : Real.exp (30 * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((1 : ℝ) / 2)) ≤ 2 * T := hTgate
  have hT1 : (1 : ℝ) < 2 * T := by linarith
  exact doorCapBundle_at_workingPoint_perBlock hband hM hNd hq hg hT1 hThi hTll

end Salt.MR

end
