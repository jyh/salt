/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RegisterSupply

/-!
# `CofactorBulk` — ⟦RULING 9⟧'s CO-FACTOR DEBT, INSTANTIATED AT THE LINEAR ANCHORS

`RegisterSupply` §4 closed the ONLY anchor-reading and the ONLY character-reading binder of
the co-factor supplier (`cofkL_capFreeFloor_at_socket`).  What remained was the BULK: the
ladder bundle `Mt`/`kk`/`Dd`/`Xa` with its ten per-block laws, `TLBlockGates34`, the
`c`/`Cb`/`ShortIntervalDatum` head, and the `S`/`R̄₀`/`C_R` grading register — the ~35 binders
of `CaseAWide.m4_supplier_complete` that read neither `AdoorL` nor `s13GK` nor `χ`
(⟦COFK-L⟧ §4: *"the BULK is anchor-blind and unbuilt at both doors; the L re-cut adds ZERO
to it"*; the precedent is `M4RowLinear.DoorRowCarried_L_gk` (:5799), where this very bundle
is CARRIED and never discharged, at BOTH doors).

This file discharges what is discharge**able** and names the rest exactly.

## §1 — THE LADDER IS DETERMINED, NOT FREE

`FrameWitness`'s witness table supplies `kk`/`Mt` in closed form off the window bottom
`B_j = ramRbot H X_d j`; this file adds the trivial divisor ladder `D(j) = 1` and the anchor
`X_a(j) = B_j`.  At that table **seven of the ten per-block ladder laws are theorems**, all
of them off `TLBlockGates34`'s own C7 gate `ballQuarterThreshold + 1 ≤ B_j`:

| law | at the witness |
|---|---|
| `1 ≤ D(j)` | `rfl` |
| `D(j) ≤ k₀(j)` | `k₀ ≥ B−1 ≥ 4` |
| `√X_a(j) ≤ k₀(j)/D(j)` | `√B ≤ B−1` at `B ≥ 5` |
| `pin2Gate ≤ k₀(j)/D(j)` | `USetGradedPrice.pin2Gate_le_ballQuarterThreshold` |
| `e ≤ X_a(j)` | `B ≥ 5 > e` |
| `M(j) ≤ 2X_a(j)` | `M ≤ 2(B−1)` |
| `2X_a(j) ≤ X` | ⟦THE WINDOW CEILING IS FREE AT THE BAND⟧, below |

Two of the window gates the door register carries are recovered here rather than carried:
`5 ≤ B_j` from C7 (`4 ≤ ballQuarterThreshold`), and **`2·B_j ≤ X`** — every block index of
`ramI H P Q` sits at or above `⌊H·log P⌋₊ > H·log P − 1 ≥ 2H − 1`, so `j/H ≥ 1` and
`B_j = X·e^{−j/H} ≤ X/e < X/2`.  The band's own bottom endpoint pays for the anchor ceiling
and for `TLBlockGates34`'s C15.

The three that are NOT theorems — `X₀ ≤ √X_a(j)` (the supplier's OPAQUE wide threshold),
`0 ≤ cofactorMfl X θ k₀(j)` and the two contour boxes — ride in the register.

## §2 — `TLBlockGates34`: SEVENTEEN CONJUNCTS, AND THE ONE THAT IS FREE HERE

`FrameWitness.tlBlockGates34_at_witness` discharges all seventeen at the band `[P, Q]`.  At
THIS consumer two of its inputs become free rather than carried:

* **C6, the `cq`-gate**, is free — `cq` is a binder of `m4_supplier_complete` that occurs in
  NO other hypothesis and NOT in the conclusion, so the instantiation may choose
  `cq := 420·L·L^{3/4}·(log L)^5` and C6 collapses to `1 ≤ (log P)²`.  (At the M4-5 consumer
  `cq` is the capstone's own opaque `cq₁`, which is why it is carried there and not here.)
* **C4, the `h`-ceiling**, is read at the band top through `Q ≤ Q₈₃ X`: the register carries
  the single clean charge `30·(log X/loglog X) ≤ log(2T)` and the per-block C4 follows from
  `ramQbase ≤ Q`.

## §3 — THE HEAD AND THE GRADE

`c := c_g := 1/e` (so `2c < 1` and `c ≤ 1/e` are numerals), `Cb` comes from
`GradeConst.exists_shortIntervalDatum` ONCE outside every quantifier, `θ := θ₂₉₃`,
`Rrad := seamRad X`, `J := 2`, `Ps := 1`, `N := 2X_d`, `X_d := A+s`,
`P := s13BandP (A+s)`, `Q := s13BandQ (A+s)`, `H := H₈₃(X, θ₂₉₃)`, `Tann := 2T`.
The band floors `3 ≤ P` and `2 ≤ log P` are DERIVED from the socket's own scale
(`P₈₃ X θ ≤ P` and `(log X)^{1−θ} ≥ e^{31/32} ≥ 2`), not carried.

The exit ceiling is `R̄ = 2^J·R̄₀ = 4·R̄₀` and the predicate's `C_R` is `gradeCR2 Cb` — so its
two grading conjuncts are exactly `M4RowLinear`'s own carried pair
(`4·R̄₀ ≤ C_R·(log X)^{−ρ₂₉₃}`, `1728·C_q·C_R² ≤ (log X)^{2θ₂₉₃}`).

## §4 — WHAT IS CARRIED, NAMED EXACTLY (`CofactorBulkL`)

Seventeen conjuncts, every one of them a gate on the Ramaré band geometry (the C7 window
floor, the two contour boxes, the loglog descent charge, the seam radius, the band's
nonemptiness and the `h`-ceiling charge on `T`) or on an OPAQUE constant (`X₀`, `S`, `R̄₀`,
`C_q`, `cofactorMfl`) — **NONE of them reads the door blocks, the anchor `AdoorL`, the lever
`s13GK`, or the character `χ`.**  That is the ⟦COFK-L⟧ §4 verdict ("the BULK is anchor-blind")
at the bytes.

**THE `K_vt` DISPOSITION.**  `K_vt` stays SYMBOLIC (no effective bound exists anywhere in the
corpus).  It is Skolemized here as `Kvt : ℕ → ℕ → ℝ` (lever `K`, modulus cap `Q_m`) and rides
under `RegisterSupply`'s single explicit cushion `32·K_vt + 32·D ≤ log H₊/4` at the modulus
cap `Q_m := ⌈arcDen 12 R.H₊⌉₊`, which the socket's own `q ≤ arcDen 12 H ≤ arcDen 12 R.H₊`
supplies.  At the terminal's regime the cushion admits `K_vt ≤ e^{518}/128 ≈ 10^{222}`.

**PURELY ADDITIVE.**  No landed declaration is touched.
-/

noncomputable section

namespace Salt.MR

open Salt.Entropy.Chowla
open scoped BigOperators

/-! ## §0 — two numerals off the quartic bracket -/

/-- `2 ≤ e^{31/32}` — the quartic bracket at `u = 31/32` gives `(159/128)^4 = 2.38…`.  This
is the numeral behind `2 ≤ log P₈₃` at every scale with `e ≤ log X`. -/
theorem cofk_two_le_exp_31_32 : (2 : ℝ) ≤ Real.exp (31 / 32) := by
  have h := cofk_exp_quartic (u := (31 / 32 : ℝ)) (by norm_num)
  have hn : (2 : ℝ) ≤ (1 + (31 / 32 : ℝ) / 4) ^ 4 := by norm_num
  linarith

/-! ## §1 — THE LADDER LAWS AT THE WITNESS TABLE

`kk := witKk H X_d`, `Mt := witMt H X_d`, `Dd := 1`, `Xa := ramRbot H X_d`.  Everything below
comes from the single window floor `5 ≤ B_j`. -/

/-- `B_j − 1 ≤ k₀(j)` — `FrameWitness.witKk_cut`'s upper half. -/
theorem cofkL_ramRbot_le_kk {H : ℝ} {Xd j : ℕ} (hW : (5 : ℝ) ≤ ramRbot H Xd j) :
    ramRbot H Xd j - 1 ≤ ((witKk H Xd j : ℕ) : ℝ) := by
  have h := (witKk_cut (H := H) (Xd := Xd) (j := j) (by linarith)).2
  linarith

/-- `1 ≤ k₀(j)` — the trivial divisor ladder `D(j) = 1` fits under the cut. -/
theorem cofkL_one_le_kk {H : ℝ} {Xd j : ℕ} (hW : (5 : ℝ) ≤ ramRbot H Xd j) :
    1 ≤ witKk H Xd j := by
  have h := cofkL_ramRbot_le_kk hW
  have h1 : (1 : ℝ) ≤ ((witKk H Xd j : ℕ) : ℝ) := by linarith
  exact_mod_cast h1

/-- `√B_j ≤ k₀(j)` — `√B ≤ B − 1` holds from `B ≥ 5` (it needs only `B² − 3B + 1 ≥ 0`). -/
theorem cofkL_sqrt_le_kk {H : ℝ} {Xd j : ℕ} (hW : (5 : ℝ) ≤ ramRbot H Xd j) :
    Real.sqrt (ramRbot H Xd j) ≤ ((witKk H Xd j : ℕ) : ℝ) := by
  have hk := cofkL_ramRbot_le_kk hW
  have hle : Real.sqrt (ramRbot H Xd j) ≤ ramRbot H Xd j - 1 := by
    have h1 : Real.sqrt (ramRbot H Xd j) ≤ Real.sqrt ((ramRbot H Xd j - 1) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  linarith

/-- **THE PIN-2 GATE FROM THE BALL-QUARTER GATE** (`cofkL_pin2_le_kk`). -/
theorem cofkL_pin2_le_kk {H : ℝ} {Xd j : ℕ} (hW : (5 : ℝ) ≤ ramRbot H Xd j)
    (hkth : ballQuarterThreshold + 1 ≤ ramRbot H Xd j) :
    pin2Gate ≤ ((witKk H Xd j : ℕ) : ℝ) := by
  have hk := cofkL_ramRbot_le_kk hW
  have h := pin2Gate_le_ballQuarterThreshold
  linarith

/-- `M(j) ≤ 2B_j` — the sharp Abel length sits inside twice the window bottom. -/
theorem cofkL_Mt_le_two_ramRbot {H : ℝ} {Xd j : ℕ} (hW : (5 : ℝ) ≤ ramRbot H Xd j) :
    ((witMt H Xd j : ℕ) : ℝ) ≤ 2 * ramRbot H Xd j := by
  have h := (witMt_window (H := H) (Xd := Xd) (j := j) (by linarith)).2.1
  linarith

/-- `4 ≤ ballQuarterThreshold` — `e^{e^{165}} ≥ 1 + e^{165} ≥ 167`.  This is what makes the
window floor `5 ≤ B_j` a CONSEQUENCE of `TLBlockGates34`'s own C7 gate rather than a separate
carried conjunct. -/
theorem four_le_ballQuarterThreshold : (4 : ℝ) ≤ ballQuarterThreshold := by
  rw [ballQuarterThreshold]
  have h1 : (1 : ℝ) + 165 ≤ Real.exp 165 := by linarith [Real.add_one_le_exp (165 : ℝ)]
  have h2 : (1 : ℝ) + Real.exp 165 ≤ Real.exp (Real.exp 165) := by
    linarith [Real.add_one_le_exp (Real.exp 165)]
  linarith

/-- **⟦THE WINDOW FLOOR IS FREE ABOVE THE BALL-QUARTER GATE⟧** (`cofkL_five_le_ramRbot`). -/
theorem cofkL_five_le_ramRbot {H : ℝ} {Xd j : ℕ}
    (hkth : ballQuarterThreshold + 1 ≤ ramRbot H Xd j) : (5 : ℝ) ≤ ramRbot H Xd j := by
  linarith [four_le_ballQuarterThreshold]

/-- **⟦THE WINDOW CEILING IS FREE AT THE BAND⟧** (`cofkL_two_ramRbot_le`).  Every block index
of `ramI H P Q` sits at or above `⌊H·log P⌋₊ > H·log P − 1`, so at `2 ≤ log P` and `1 ≤ H`
the block height obeys `j/H ≥ 1`, whence `B_j = X·e^{−j/H} ≤ X/e < X/2`.  The supplier's
anchor ceiling `2·X_a(j) ≤ X` and `TLBlockGates34`'s C15 therefore cost NOTHING at the band —
they are consequences of the band's own bottom endpoint. -/
theorem cofkL_two_ramRbot_le {H : ℝ} {Xd P Q j : ℕ} (hH1 : 1 ≤ H)
    (hlogP2 : (2 : ℝ) ≤ Real.log (P : ℝ)) (hj : j ∈ ramI H P Q) :
    2 * ramRbot H Xd j ≤ (Xd : ℝ) := by
  have hH0 : (0 : ℝ) < H := by linarith
  rw [ramI, Finset.mem_Icc] at hj
  have hjR : ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
  have hfl : H * Real.log (P : ℝ) - 1 < ((⌊H * Real.log (P : ℝ)⌋₊ : ℕ) : ℝ) := by
    linarith [Nat.lt_floor_add_one (H * Real.log (P : ℝ))]
  have hjbig : H * 2 - 1 ≤ (j : ℝ) := by nlinarith
  have hdiv : (1 : ℝ) ≤ (j : ℝ) / H := by
    rw [le_div_iff₀ hH0]; nlinarith
  have hexp : Real.exp (-(j : ℝ) / H) ≤ Real.exp (-1) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div]
    linarith
  have he : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos (by norm_num)]
    linarith
  have hXd0 : (0 : ℝ) ≤ (Xd : ℝ) := Nat.cast_nonneg _
  rw [ramRbot]
  nlinarith [hexp, he, hXd0, Real.exp_pos (-(j : ℝ) / H)]

/-! ## §2 — THE SOCKET'S OWN SCALE FLOORS

`RegisterSupply` §3/§4 derive these inside their proofs; the bulk needs them as an export. -/

/-- **THE TWO SCALE FLOORS AT THE SOCKET** (`cofkL_socket_floors`).  From the terminal's own
design floor `518 ≤ loglog H₋` (i.e. `3.2·A ≤ loglog H₋` at `A ≥ 162`): `H ≥ 4·10⁶` and
`H₊ ≥ 10^{14}`. -/
theorem cofkL_socket_floors {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseL R M H L q j A s)
    (hlo : (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ))) :
    (4000000 : ℝ) ≤ (H : ℝ) ∧ (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ) := by
  have h1 : R.Hlo ≤ H := hb.1
  have h2 : H ≤ R.Hhi := hb.2.1
  have hHlo4 : (4000000 : ℝ) ≤ (R.Hlo : ℝ) := by exact_mod_cast R.hHlo_floor
  have hHloH : (R.Hlo : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hH4 : (4000000 : ℝ) ≤ (H : ℝ) := by linarith
  have hlogHlo : (14 : ℝ) ≤ Real.log (R.Hlo : ℝ) := cofk_log_big hHlo4
  have hexp : Real.exp (518 : ℝ) ≤ Real.log (R.Hlo : ℝ) := by
    have h := Real.exp_le_exp.mpr hlo
    rwa [Real.exp_log (by linarith)] at h
  have hquart : (10 : ℝ) ^ 8 ≤ Real.exp (518 : ℝ) := by
    have h := cofk_exp_quartic (u := (518 : ℝ)) (by norm_num)
    have hnum : (290029400 : ℝ) ≤ (1 + (518 : ℝ) / 4) ^ 4 := by norm_num
    linarith
  have hHhi0 : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hlogmono : Real.log (R.Hlo : ℝ) ≤ Real.log (R.Hhi : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hLH8 : (10 : ℝ) ^ 8 ≤ Real.log (R.Hhi : ℝ) := by linarith
  have hHhi14 : (10 : ℝ) ^ 14 ≤ (R.Hhi : ℝ) := by
    have hlogle : Real.log ((10 : ℝ) ^ 14) ≤ Real.log (R.Hhi : ℝ) := by
      rw [show ((10 : ℝ) ^ 14) = (10 : ℝ) ^ (14 : ℕ) by norm_num, Real.log_pow]
      push_cast
      linarith [cofk_log_ten_le, hLH8]
    have h2' := Real.exp_le_exp.mpr hlogle
    rwa [Real.exp_log (by positivity), Real.exp_log hHhi0] at h2'
  exact ⟨hH4, hHhi14⟩

/-- **THE MODULUS CAP AT THE REGIME'S ENDPOINT** (`cofkL_q_le_arcCap`).  The socket's own
`q ≤ arcDen 12 H` and `H ≤ H₊` put every socket modulus under ONE cap
`Q_m = ⌈arcDen 12 H₊⌉₊`, which is what lets the `_vt` floor's `Q_m`-indexed constant be
Skolemized outside the socket quantifier. -/
theorem cofkL_q_le_arcCap {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBaseL R M H L q j A s) (hH : (4000000 : ℝ) ≤ (H : ℝ)) :
    q ≤ ⌈arcDen 12 R.Hhi⌉₊ := by
  have h2 : H ≤ R.Hhi := hb.2.1
  have harc : (q : ℝ) ≤ arcDen 12 H := hb.2.2.2.2.1
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hlogH : (14 : ℝ) ≤ Real.log (H : ℝ) := cofk_log_big hH
  have hHHhi : (H : ℝ) ≤ (R.Hhi : ℝ) := by exact_mod_cast h2
  have hlogmono : Real.log (H : ℝ) ≤ Real.log (R.Hhi : ℝ) := Real.log_le_log hH0 hHHhi
  have hmono : arcDen 12 H ≤ arcDen 12 R.Hhi := by
    rw [arcDen, arcDen]
    exact Real.rpow_le_rpow (by linarith) hlogmono (by norm_num)
  have hceil : arcDen 12 R.Hhi ≤ ((⌈arcDen 12 R.Hhi⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hqR : (q : ℝ) ≤ ((⌈arcDen 12 R.Hhi⌉₊ : ℕ) : ℝ) := by linarith
  exact_mod_cast hqR

/-! ## §3 — ⟦THE CARRIED REGISTER⟧ `CofactorBulkL`

Seventeen conjuncts.  Each one is a gate on the Ramaré band geometry (the C7 window floor,
the two contour boxes, the `h`-ceiling charge), on an OPAQUE constant (`X₀`, `S`, `R̄₀`,
`C_q`), or on the `θ₂₉₃`/`ρ₂₉₃` grading — and none of them mentions `AdoorL`, `s13GK`,
or `χ`. -/

/-- **⟦THE CO-FACTOR BULK, CARRIED⟧** (`CofactorBulkL`).  The residual binder list of
`CaseAWide.m4_supplier_complete` at the LINEAR socket's instantiation, after the ladder table
of §1 and the band floors of §4 have been discharged.

`Cq` is the predicate's own co-factor constant, `Xsk` the supplier's opaque wide threshold,
`Cb` the short-interval datum's constant; `Xd = A+s` is the block scale and `T` the socket's
height. -/
def CofactorBulkL (Cq Xsk Cb : ℝ) (Xd : ℕ) (T : ℝ) : Prop :=
  ∃ S Rbar0 : ℝ,
    -- ⟦the §8.3 band: nonempty, under the height, and the `h`-ceiling charge⟧
    (s13BandP Xd ≤ s13BandQ Xd) ∧
    ((s13BandQ Xd : ℝ) ≤ 2 * T) ∧
    (30 * (Real.log (Xd : ℝ) / Real.log (Real.log (Xd : ℝ))) ≤ Real.log (2 * T)) ∧
    -- ⟦the window floors, per block⟧ (`5 ≤ B_j` and `2·B_j ≤ X` are NOT here — §1 derives
    -- them from this gate and from the band's own bottom endpoint)
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      ballQuarterThreshold + 1 ≤ ramRbot (H83 (Xd : ℝ) theta293) Xd v) ∧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      18 + Real.log (Real.log (Xd : ℝ))
          - Real.log (Real.log (ramRbot (H83 (Xd : ℝ) theta293) Xd v - 1))
        ≤ 32 * theta293 * Real.log (Real.log (Xd : ℝ))) ∧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      seamRad (Xd : ℝ) ≤ Real.sqrt 2 * ramRbot (H83 (Xd : ℝ) theta293) Xd v) ∧
    -- ⟦the supplier's OPAQUE wide threshold⟧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      Xsk ≤ Real.sqrt (ramRbot (H83 (Xd : ℝ) theta293) Xd v)) ∧
    -- ⟦the CASE-A window floor's own value⟧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      (0 : ℝ) ≤ cofactorMfl (Xd : ℝ) theta293
        ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)) ∧
    -- ⟦the two contour boxes⟧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd), ∀ t : ℝ, |t| ≤ 2 * T →
      |t| + Tstar2 ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Real.log ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)) ≤ 3 * (Xd : ℝ)) ∧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd), ∀ t : ℝ, |t| ≤ 2 * T →
      ∀ i : ℕ, ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ) ≤ (i : ℝ) →
        (i : ℝ) ≤ 2 * ramRbot (H83 (Xd : ℝ) theta293) Xd v →
          |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * (Xd : ℝ)) ∧
    -- ⟦the CASE-A exit constant⟧
    ((0 : ℝ) ≤ S) ∧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cSq * caseASwide (1 / Real.exp 1) Cb
          (cofactorMfl (Xd : ℝ) theta293 ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ))
          ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
          (ramRbot (H83 (Xd : ℝ) theta293) Xd v)
        + cSq ≤ S) ∧
    -- ⟦the endpoint charge and the ceiling⟧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      2 / ramRbot (H83 (Xd : ℝ) theta293) Xd v
        ≤ cofactorRbdGen S ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
            ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Tstar2 ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
              (Real.log ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)))
            (seamRad (Xd : ℝ)) / 3) ∧
    (∀ v ∈ ramI (H83 (Xd : ℝ) theta293) (s13BandP Xd) (s13BandQ Xd),
      cofactorRbdGen S ((witKk (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
          ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
          (Tstar2 ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)
            (Real.log ((witMt (H83 (Xd : ℝ) theta293) Xd v : ℕ) : ℝ)))
          (seamRad (Xd : ℝ)) ≤ Rbar0) ∧
    -- ⟦THE GRADING REGISTER⟧ (`ρ₂₉₃`/`θ₂₉₃`)
    ((0 : ℝ) ≤ Rbar0) ∧
    (4 * Rbar0 ≤ gradeCR2 Cb * (Real.log (Xd : ℝ)) ^ (-rho293)) ∧
    (1728 * Cq * (gradeCR2 Cb) ^ 2 ≤ (Real.log (Xd : ℝ)) ^ (2 * theta293))

/-! ## §4 — ⟦THE INSTANTIATION⟧ -/

set_option maxHeartbeats 2000000 in
-- the ~35-binder instantiation of `m4_supplier_complete` plus the 19-conjunct register
-- destructuring elaborate in one `exact`-shaped context; no tactic search happens here
/-- **⟦THE CO-FACTOR SUPPLY AT THE LINEAR DOOR AND THE LINEAR SOCKET⟧**
(`cofkL_cofactorSupply_L_gk_of_bulk`).  ⟦RULING 9⟧'s debt, instantiated end-to-end.

The three Skolem constants are hoisted ONCE, outside every quantifier: `Xsk` is
`CaseAWide.m4_supplier_complete`'s opaque wide threshold, `Kvt K Qm` is
`RegisterSupply.cofkL_capFreeFloor_at_socket`'s `_vt` floor constant (symbolic — no effective
bound exists in the corpus, and it rides under the ONE explicit cushion), and `Cb` is
`GradeConst.exists_shortIntervalDatum`'s short-interval constant at `Cb = 250`.

Everything the theorem consumes beyond the register is the terminal's OWN export list
(`1 ≤ M`, `ε ≥ 1/500`, `518 ≤ loglog H₋`, the cushion) — exactly `RegisterSupply` §4's inputs.

⟦WHAT IS DISCHARGED HERE⟧ the ladder bundle and its ten per-block laws (§1), the band floors
`3 ≤ P`, `2 ≤ log P`, `1 ≤ Q`, `P₈₃ ≤ P`, `Q ≤ Q₈₃`, `log Q ≤ log X`, all seventeen
`TLBlockGates34` conjuncts (through `FrameWitness.tlBlockGates34_at_witness`, with C6 FREE at
this consumer's own `cq`), the head `c = c_g = 1/e`, `θ = θ₂₉₃`, `Rrad = seamRad X`, and the
per-piece cap-free floor (arm 1's `cofkL_capFreeFloor_at_socket`, the only anchor- and
character-reading binder).

⟦WHAT IS CARRIED⟧ `CofactorBulkL`'s seventeen. -/
theorem cofkL_cofactorSupply_L_gk_of_bulk :
    ∃ (Xsk : ℝ) (Kvt : ℕ → ℕ → ℝ) (Cb : ℝ),
      0 < Xsk ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧ 0 ≤ Cb ∧
      ∀ (K : ℕ) (Cq : ℝ) (R : ChowlaRegime) (M : ℕ), 1 ≤ M →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        (518 : ℝ) ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt K ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log (M : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        (∀ H L q j A s : ℕ, SocketBaseL R M H L q j A s →
          ∀ T : ℝ, (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((A + s : ℕ)) : ℝ) → CofactorBulkL Cq Xsk Cb (A + s) T) →
        S16CofactorSupply_L_gk K Cq R M := by
  obtain ⟨Xsk, hXsk0, hsup⟩ := m4_supplier_complete
  choose Kvt hKvt0 hKvt using cofkL_capFreeFloor_at_socket
  obtain ⟨Cb, hCb0, hCbound⟩ := exists_shortIntervalDatum
  refine ⟨Xsk, Kvt, Cb, hXsk0, hKvt0, hCb0, ?_⟩
  intro K Cq R M hM hε hlo hcush hbulk H L q j A s hb T hTlo hThi
  -- ⟦the socket's own arithmetic⟧
  have hq0 : 0 < q := hb.2.2.2.1
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨hH4, hHhi14⟩ := cofkL_socket_floors hb hlo
  have hqQm : q ≤ ⌈arcDen 12 R.Hhi⌉₊ := cofkL_q_le_arcCap hb hH4
  -- ⟦THE BLOCK SCALE⟧
  have hXee : Real.exp (Real.exp 1) ≤ (((A + s : ℕ)) : ℝ) :=
    cofkL_X_ge_expexp hb hε hHhi14 hH4
  have hLX : Real.exp 1 ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hXee
    rwa [Real.log_exp] at h
  have he1 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hLs0 : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by linarith
  have hX0 : (0 : ℝ) < (((A + s : ℕ)) : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos (Real.exp 1)) hXee
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLX
    rwa [Real.log_exp] at h
  -- ⟦THE PER-PIECE CAP-FREE FLOOR⟧ — arm 1's exit, verbatim
  have hfloorχ : ∀ χ : DirichletCharacter ℂ q, ∀ 𝒥 ∈ (Finset.Icc 1 2).powerset,
      CapFreeFloor3 (pieceDatum χ 𝒥 (calP (AdoorL M) (s13GK K M))
        (calQK (AdoorL M) (s13GK K M) M)) (((A + s : ℕ)) : ℝ) :=
    fun χ => hKvt K ⌈arcDen 12 R.Hhi⌉₊ χ hb hM hqQm hε hlo hcush
  -- ⟦THE REGISTER⟧
  obtain ⟨S, Rbar0, hPQ, hQT, h30g, hkth, hC16, hRradW, hXskj, hMfl0r,
    hboxr, hboxwr, hS0, hSbdr, hendGenr, hRbdUr, hRbar00, hRgrade, hCqgate⟩ :=
    hbulk H L q j A s hb T hTlo hThi
  have hW5 : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)), (5 : ℝ) ≤ ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v :=
    fun v hv => cofkL_five_le_ramRbot (hkth v hv)
  -- ⟦THE BAND FLOORS, DERIVED FROM THE SCALE⟧
  have hθ0 : (0 : ℝ) < theta293 := theta293_pos
  have hθ32 : theta293 ≤ 1 / 32 := theta293_lt_one_div_32.le
  have hPexp : (2 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - theta293) := by
    have h1 : (Real.exp 1) ^ (1 - theta293)
        ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - theta293) :=
      Real.rpow_le_rpow (Real.exp_pos 1).le hLX (by linarith)
    have h2 : (Real.exp 1) ^ (31 / 32 : ℝ) ≤ (Real.exp 1) ^ (1 - theta293) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h3 : (Real.exp 1) ^ (31 / 32 : ℝ) = Real.exp (31 / 32) := Real.exp_one_rpow _
    have h4 := cofk_two_le_exp_31_32
    rw [h3] at h2
    linarith
  have hP83log : Real.log (P83 (((A + s : ℕ)) : ℝ) theta293)
      = (Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - theta293) := by
    rw [P83, Real.log_exp]
  have hP83pos : (0 : ℝ) < P83 (((A + s : ℕ)) : ℝ) theta293 := by
    rw [P83]; exact Real.exp_pos _
  have hP83ge : (3 : ℝ) ≤ P83 (((A + s : ℕ)) : ℝ) theta293 := by
    rw [P83]
    have h1 : Real.exp 2 ≤ Real.exp ((Real.log (((A + s : ℕ)) : ℝ)) ^ (1 - theta293)) :=
      Real.exp_le_exp.mpr hPexp
    have h2 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have hPlow : P83 (((A + s : ℕ)) : ℝ) theta293 ≤ ((s13BandP (A + s) : ℕ) : ℝ) := by
    rw [s13BandP]; exact Nat.le_ceil _
  have hP3R : (3 : ℝ) ≤ ((s13BandP (A + s) : ℕ) : ℝ) := by linarith
  have hP3 : 3 ≤ s13BandP (A + s) := by exact_mod_cast hP3R
  have hP1 : 1 ≤ s13BandP (A + s) := by omega
  have hlogP2 : (2 : ℝ) ≤ Real.log ((s13BandP (A + s) : ℕ) : ℝ) := by
    have h := Real.log_le_log hP83pos hPlow
    rw [hP83log] at h
    linarith
  have hQ1 : 1 ≤ s13BandQ (A + s) := by omega
  have hQhigh : ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Q83 (((A + s : ℕ)) : ℝ) := by
    rw [s13BandQ]
    exact Nat.floor_le (by rw [Q83]; exact (Real.exp_pos _).le)
  have hQlog : Real.log ((s13BandQ (A + s) : ℕ) : ℝ)
      ≤ Real.log (((A + s : ℕ)) : ℝ) / Real.log (Real.log (((A + s : ℕ)) : ℝ)) :=
    log_le_of_le_Q83 hQ1 hQhigh
  have hQL : Real.log ((s13BandQ (A + s) : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
    have hdiv : Real.log (((A + s : ℕ)) : ℝ) / Real.log (Real.log (((A + s : ℕ)) : ℝ))
        ≤ Real.log (((A + s : ℕ)) : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- ⟦THE WIDTH AND THE RADIUS⟧
  have hH1 : (1 : ℝ) ≤ H83 (((A + s : ℕ)) : ℝ) theta293 := by
    rw [H83]; exact Real.one_le_rpow (by linarith) hθ0.le
  have hH0 : (0 : ℝ) < H83 (((A + s : ℕ)) : ℝ) theta293 := by linarith
  have hRrad0 : (0 : ℝ) < seamRad (((A + s : ℕ)) : ℝ) := by
    rw [seamRad]; exact Real.rpow_pos_of_pos hLs0 _
  -- ⟦THE WINDOW CEILING IS FREE AT THE BAND⟧ — §1, off the band's own bottom endpoint
  have hMtX : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      2 * ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v ≤ (((A + s : ℕ)) : ℝ) :=
    fun v hv => cofkL_two_ramRbot_le hH1 hlogP2 hv
  -- ⟦THE `cq` GATE IS FREE AT THIS CONSUMER⟧
  have hlogLs0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hrp : (0 : ℝ) ≤ (Real.log (((A + s : ℕ)) : ℝ)) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg hLs0.le _
  have hp5 : (0 : ℝ) ≤ (Real.log (Real.log (((A + s : ℕ)) : ℝ))) ^ 5 :=
    pow_nonneg hlogLs0 5
  have hcq0 : (0 : ℝ) ≤ 420 * Real.log (((A + s : ℕ)) : ℝ)
      * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (((A + s : ℕ)) : ℝ))) ^ 5 := by
    have h1 : (0 : ℝ) ≤ 420 * Real.log (((A + s : ℕ)) : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg h1 hrp) hp5
  have hcqgate : 420 * Real.log (((A + s : ℕ)) : ℝ)
        * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (((A + s : ℕ)) : ℝ))) ^ 5
      ≤ (420 * Real.log (((A + s : ℕ)) : ℝ)
          * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (((A + s : ℕ)) : ℝ))) ^ 5)
        * (Real.log ((s13BandP (A + s) : ℕ) : ℝ)) ^ 2 := by
    have hsq : (1 : ℝ) ≤ (Real.log ((s13BandP (A + s) : ℕ) : ℝ)) ^ 2 := by nlinarith
    nlinarith [hcq0, hsq]
  -- ⟦`TLBlockGates34` AT THE WITNESS, PER BLOCK⟧
  have hblk : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      TLBlockGates34 (420 * Real.log (((A + s : ℕ)) : ℝ)
          * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((3 : ℝ) / 4)
          * (Real.log (Real.log (((A + s : ℕ)) : ℝ))) ^ 5)
        (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) (2 * (A + s)) (A + s)
        (witMt (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s))
        (witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s))
        (2 * T) (Real.log (((A + s : ℕ)) : ℝ)) (1 / Real.exp 1) Cb
        (((A + s : ℕ)) : ℝ) theta293 (seamRad (((A + s : ℕ)) : ℝ)) v := by
    intro v hv
    have hbaseQ : ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) v
        ≤ s13BandQ (A + s) := ramQbase_le_top hH0 hQ1 hPQ hv
    have hbase3 : 3 ≤ ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) v :=
      le_trans hP3 (ramQbase_ge_bot _ _ _)
    have hb3R : (3 : ℝ)
        ≤ ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) v : ℕ) : ℝ) := by
      exact_mod_cast hbase3
    have hblog0 : (0 : ℝ)
        < Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) v : ℕ)
            : ℝ) := Real.log_pos (by linarith)
    have hbQ : Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) v
          : ℕ) : ℝ) ≤ Real.log ((s13BandQ (A + s) : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast hbaseQ)
    have h30 : (30 : ℝ) ≤ Real.log (2 * T)
        / Real.log ((ramQbase (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s)) v : ℕ)
            : ℝ) := by
      rw [le_div_iff₀ hblog0]
      linarith
    exact tlBlockGates34_at_witness hH1 hP3 hlogP2 hQ1 hPQ hcq0 hv hQT h30 hQL hcqgate
      (by linarith [hW5 v hv]) (hkth v hv) le_rfl (hMtX v hv) (hC16 v hv) hRrad0 (hRradW v hv)
  -- ⟦THE TEN PER-BLOCK LADDER LAWS⟧
  have hD1 : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)), 1 ≤ (fun _ : ℕ => 1) v := fun _ _ => le_refl 1
  have hDk : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      (fun _ : ℕ => 1) v ≤ witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v :=
    fun v hv => cofkL_one_le_kk (hW5 v hv)
  have hX₀j : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      Xsk ≤ Real.sqrt (ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v) := hXskj
  have hsqXa : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      Real.sqrt (ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v)
        ≤ ((witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v
            / (fun _ : ℕ => 1) v : ℕ) : ℝ) := by
    intro v hv
    simp only [Nat.div_one]
    exact cofkL_sqrt_le_kk (hW5 v hv)
  have hpin : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      pin2Gate ≤ ((witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v
        / (fun _ : ℕ => 1) v : ℕ) : ℝ) := by
    intro v hv
    simp only [Nat.div_one]
    exact cofkL_pin2_le_kk (hW5 v hv) (hkth v hv)
  have hXae : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      Real.exp 1 ≤ ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v := by
    intro v hv
    have h := hW5 v hv
    linarith [Real.exp_one_lt_d9]
  have hMXa : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      ((witMt (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v : ℕ) : ℝ)
        ≤ 2 * ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v :=
    fun v hv => cofkL_Mt_le_two_ramRbot (hW5 v hv)
  have hMfl0 : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      (0 : ℝ) ≤ cofactorMfl (((A + s : ℕ)) : ℝ) theta293
        ((witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v
          / (fun _ : ℕ => 1) v : ℕ) : ℝ) := by
    intro v hv
    simp only [Nat.div_one]
    exact hMfl0r v hv
  have hboxw : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)), ∀ t : ℝ, |t| ≤ 2 * T → ∀ i : ℕ,
      ((witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v
        / (fun _ : ℕ => 1) v : ℕ) : ℝ) ≤ (i : ℝ) →
        (i : ℝ) ≤ 2 * ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v →
          |t| + Tstar2 (i : ℝ) (Real.log (i : ℝ)) ≤ 3 * (((A + s : ℕ)) : ℝ) := by
    intro v hv t ht i hi1 hi2
    simp only [Nat.div_one] at hi1
    exact hboxwr v hv t ht i hi1 hi2
  have hSbd : ∀ v ∈ ramI (H83 (((A + s : ℕ)) : ℝ) theta293) (s13BandP (A + s))
      (s13BandQ (A + s)),
      cSq * caseASwide (1 / Real.exp 1) Cb
          (cofactorMfl (((A + s : ℕ)) : ℝ) theta293
            ((witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v
              / (fun _ : ℕ => 1) v : ℕ) : ℝ))
          ((witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v
            / (fun _ : ℕ => 1) v : ℕ) : ℝ)
          (ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s) v)
        + cSq * (((fun _ : ℕ => 1) v : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) ≤ S := by
    intro v hv
    simp only [Nat.div_one, Nat.cast_one, Real.one_rpow, mul_one]
    exact hSbdr v hv
  -- ⟦THE HEAD⟧
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hce : (1 : ℝ) / Real.exp 1 ≤ 1 / Real.exp 1 := le_refl _
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  -- ⟦THE EXIT⟧
  refine ⟨seamRad (((A + s : ℕ)) : ℝ), 4 * Rbar0, gradeCR2 Cb, by linarith, hRgrade,
    hCqgate, ?_⟩
  intro t₁ χ
  have hs := hsup q χ (calP (AdoorL M) (s13GK K M)) (calQK (AdoorL M) (s13GK K M) M)
    (H83 (((A + s : ℕ)) : ℝ) theta293) (2 * (A + s)) (A + s) (s13BandP (A + s))
    (s13BandQ (A + s)) 2 1
    (witMt (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s))
    (witKk (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s)) (fun _ : ℕ => 1)
    (ramRbot (H83 (((A + s : ℕ)) : ℝ) theta293) (A + s))
    (420 * Real.log (((A + s : ℕ)) : ℝ)
      * (Real.log (((A + s : ℕ)) : ℝ)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (((A + s : ℕ)) : ℝ))) ^ 5)
    (Real.log (((A + s : ℕ)) : ℝ)) (1 / Real.exp 1) Cb (((A + s : ℕ)) : ℝ) theta293
    (seamRad (((A + s : ℕ)) : ℝ)) (2 * T) t₁ Rbar0 (1 / Real.exp 1) S
    hc0 hce hc1 hCb0 hCbound hP1 (le_refl 1) hRrad0 hθ0 hθ32 hLX hPlow hQhigh hPQ
    (hfloorχ χ) hblk hboxr hD1 hDk hX₀j hsqXa hpin hXae hMXa hMtX hMfl0 hboxw hS0 hSbd
    hendGenr hRbdUr
  have he : (2 : ℝ) ^ (2 : ℕ) * Rbar0 = 4 * Rbar0 := by norm_num
  rwa [he] at hs

/-! ## §5 — ⟦THE PREDICATE AT THE TERMINAL'S LEVER AND ANCHOR⟧ -/

/-- **⟦THE CO-FACTOR DEBT AT THE FLAT DOOR⟧** (`cofkL_cofactorSupply_L_gk_flat`).  §4
specialized to the terminal's own numerals: the lever `K = 32000000`, the anchor
`M = flatDoorM A` at `162 ≤ A`, and the regime exports `1/500 ≤ ε`, `3.2·A ≤ loglog H₋`.
The design floor `518 ≤ loglog H₋` is `3.2·162 = 518.4`, read off `A ≥ 162`.

This is the shape `S13CapGateLinear.s16_capGate_supply_L_gk`'s `hcof` slot demands. -/
theorem cofkL_cofactorSupply_L_gk_flat :
    ∃ (Xsk : ℝ) (Kvt : ℕ → ℕ → ℝ) (Cb : ℝ),
      0 < Xsk ∧ (∀ K Qm : ℕ, 0 ≤ Kvt K Qm) ∧ 0 ≤ Cb ∧
      ∀ (Cq A : ℝ) (R : ChowlaRegime), (162 : ℝ) ≤ A →
        1 ≤ flatDoorM A →
        (1 : ℝ) / 500 ≤ (R.eps : ℝ) →
        3.2 * A ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        32 * Kvt 32000000 ⌈arcDen 12 R.Hhi⌉₊
            + 32 * (2 * Real.log ((flatDoorM A : ℕ) : ℝ) + Real.log 4 + 50)
          ≤ Real.log (R.Hhi : ℝ) / 4 →
        (∀ H L q j Aw s : ℕ, SocketBaseL R (flatDoorM A) H L q j Aw s →
          ∀ T : ℝ, (((Aw + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T →
            2 * T ≤ (((Aw + s : ℕ)) : ℝ) → CofactorBulkL Cq Xsk Cb (Aw + s) T) →
        S16CofactorSupply_L_gk 32000000 Cq R (flatDoorM A) := by
  obtain ⟨Xsk, Kvt, Cb, hXsk0, hKvt0, hCb0, hmain⟩ := cofkL_cofactorSupply_L_gk_of_bulk
  refine ⟨Xsk, Kvt, Cb, hXsk0, hKvt0, hCb0, ?_⟩
  intro Cq A R hA hM hε hAlo hcush hbulk
  refine hmain 32000000 Cq R (flatDoorM A) hM hε ?_ hcush hbulk
  linarith

end Salt.MR

end
