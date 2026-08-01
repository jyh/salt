/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13FramesA
import Salt.MR.M4ArithRho
import Salt.MR.M4SocketDischarge

/-!
# ⟦S13-BAND⟧ — THE `DoorBandBase` SUPPLIER (`S13BandBase`)

PURELY ADDITIVE: no landed declaration is touched anywhere in this file.

`M4SocketDischarge.DoorBandBase` is the nine-field per-base gate bundle of the `T₀`-band
supplier, asked at eighteen consumer sites in the byte-identical shape

    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorBandBase x₀ C' Aexp M (A + s) q (C₁ (A + s)) (M₀ (A + s))

and it was — until this file — a hypothesis in six modules and a theorem in none.  §5's
`doorBandBase_family` is that theorem: ONE supplier, at that shape, off

* the ARITHMETIC FRAME FAMILY (`M4ArithRho.DoorArithFrameRho`, the terminal's own `harith`
  binder), which is what pays for `qfit` and every scale floor the analytic trio needs; and
* `S13BandGate` — FIVE named gate lines, listed in §5, that no page below can pay.

⟦THE THREE RULINGS THIS FILE IMPLEMENTS⟧ (maestro, 2026-07-30, on `BANDBASE-SCOPE`)

* **F1** — the saving parameter is PINNED, `s13Aexp := 3`.  The trio (`gHalf`, `gO1`,
  `gWin`) closes `M`-uniformly at that value off the arith frame's arm alone; `Aexp = 1` is
  not attempted, and no Lean object below reads the prose pin.
* **F2** — `s13BandM0` (§1) is EXPORTED as THE shared `M₀` pin: the arithmetic window's
  LOWER endpoint, read at the window's top `H₊ = R.Hhi`.  Both unbuilt suppliers consume the
  same object, so the two `M₀`-readers cannot drift apart (the incompatibility fence).  The
  `err` discharge (§4) is EXACT there: `M₀`'s `e` cancels `hErr`'s `1/(2e)` on the nose, and
  what survives is the numeral residue line `err_res`.
* **F3** — `s13BlockFloor M ≤ X_d` rides as a NAMED GATE LINE (`S13BandGate.block`).  It is
  NOT socket-implied (the socket's own `j`-floor is linear in `M·Adoor M`, the block floor
  quadratic), and no landed statement is amended to make it so.

⟦WHAT IS FREE AND WHAT IS NOT⟧  Seven of the nine fields are discharged here.  The two that
are not — `x₀_le` and `grade` — read `MmuChiRate`'s OPAQUE existential witnesses `x₀` and
`C'`, so nothing below the compose can bound them; both are reduced as far as the base
allows (to `x₀ ≤ 2^{doorRowFloor M}` and to a floor at `log 2 · doorRowFloor M`, i.e. to
`M`-only lines, through the base-floor bridge §2) and then named.  `C₁_one` is free the
moment the caller pins `C₁ ≡ 1`, which it may: the only other reader of `C₁` is
`DoorArithFrameRho.C1_nonneg`.

⟦NO TOWER IS EVER FORMED⟧  `2^{doorRowFloor M} = 2^{M·Adoor M}` and `s13BlockFloor M` are
astronomically large naturals.  Every step through them goes by the base-floor bridge
`s13_band_baseFloor` (`log 2 · doorRowFloor M ≤ log X_d`, from `2^j ≤ A` and the socket's
`j`-floor) or by `Adoor_ge` in the exponent; `2^{2^36}` is never evaluated.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE TWO PINS (`s13Aexp`, `s13BandM0`)

⟦F1⟧ and ⟦F2⟧, as Lean objects. -/

/-- **⟦F1 — THE SAVING PARAMETER, PINNED⟧** (`s13Aexp`).  `DoorBandBase`'s `Aexp` at the
door: `3`.  The trio closes `M`-uniformly here off the arith frame's arm; the pin costs
nothing, since `Aexp` enters the closure only through the three trio fields and `grade`. -/
def s13Aexp : ℝ := 3

/-- The pin is positive — `m4_hband_at_door_slot`'s `hAexp`. -/
theorem s13Aexp_pos : 0 < s13Aexp := by rw [s13Aexp]; norm_num

/-- **⟦F2 — THE SHARED `M₀` PIN⟧** (`s13BandM0`).  `DoorArithFrameRho.M0_window`'s LOWER
endpoint, read at the window's TOP `H₊ = R.Hhi` so that it is `H`-free across the whole
socket family:

  `M₀(n) = e·(loglog n / 45 + 14·loglog H₊ + 2·log(C₁ n + 1) + log(1/ρ) + 12)`.

Both unbuilt suppliers (this file's band family and the `DoorArithFrameRho` family) consume
THIS object, which is what makes them compatible: §4's `err` needs the pin from ABOVE (the
`e`-cancellation), the arith frame needs it from BELOW (`M0_window`), and
`s13BandM0_window` below is the bridge between the two readings. -/
def s13BandM0 (R : ChowlaRegime) (ρ : ℝ) (C₁ : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp 1 * (Real.log (Real.log ((n : ℕ) : ℝ)) / 45
    + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 2 * Real.log (C₁ n + 1)
    + Real.log (1 / ρ) + 12)

/-- **THE PIN MEETS `M0_window` AT EVERY `H` IN THE WINDOW** (`s13BandM0_window`) — the
`DoorArithFrameRho.M0_window` field at `M₀ := s13BandM0 R ρ C₁`, for any width `H ≤ H₊`.
Exported for the arith-frame family: reading the pin at the TOP of the window is what makes
one `M₀` serve every `H`. -/
theorem s13BandM0_window {R : ChowlaRegime} {ρ : ℝ} {C₁ : ℕ → ℝ} {H n : ℕ}
    (hH : H ≤ R.Hhi) (hlogH : 0 < Real.log ((H : ℕ) : ℝ)) :
    Real.exp 1 * (Real.log (Real.log ((n : ℕ) : ℝ)) / 45
        + 14 * Real.log (Real.log ((H : ℕ) : ℝ)) + 2 * Real.log (C₁ n + 1)
        + Real.log (1 / ρ) + 12)
      ≤ s13BandM0 R ρ C₁ n := by
  have hH0 : (0 : ℝ) < ((H : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hz | hz
    · rw [hz] at hlogH; norm_num at hlogH
    · exact_mod_cast hz
  have hcast : ((H : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hH
  have hlog : Real.log ((H : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) :=
    Real.log_le_log hH0 hcast
  have hll : Real.log (Real.log ((H : ℕ) : ℝ)) ≤ Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) :=
    Real.log_le_log hlogH hlog
  rw [s13BandM0]
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  refine mul_le_mul_of_nonneg_left ?_ he.le
  linarith

/-! ## §2 — THE SOCKET-SIDE FLOORS

`X400` and the base-floor bridge come from `SocketBase` ALONE (no frame, no analysis).  The
scale floors — `log X_d ≥ 356601`, `48(Λ+1) ≤ log X_d`, `24(Λ+1) ≤ √(log X_d)` — come from
the arith frame's `loglogX_ge` (`Λ := loglog X_d ≥ 356600`) through one two-step square-root
argument.  The `𝒫₁`/`𝒬₂` floors are `M`-only, off `Adoor_ge`. -/

/-- **⟦THE BASE FLOOR⟧** (`s13_band_X400`) — `DoorBandBase.X400`, free from the socket's own
`j`-floor: `j ≥ doorRowFloor M ≥ 2^36 ≥ 9`, so `A ≥ 2^9 = 512 ≥ 400`. -/
theorem s13_band_X400 {R : ChowlaRegime} {M H L q j A s : ℕ} (hM : 1 ≤ M)
    (hb : SocketBase R M H L q j A s) : (400 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
  have hj : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
  have h9 : 9 ≤ j := by
    have h36 : 2 ^ 36 ≤ Adoor M := Adoor_ge M
    have : 2 ^ 36 ≤ doorRowFloor M := by
      rw [doorRowFloor]
      calc (2 : ℕ) ^ 36 = 1 * 2 ^ 36 := by ring
        _ ≤ M * Adoor M := Nat.mul_le_mul hM h36
    have h2 : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
    omega
  have h512 : (512 : ℕ) ≤ A := by
    calc (512 : ℕ) = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h9
      _ ≤ A := hAj
  have : (512 : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    have : (512 : ℕ) ≤ A + s := by omega
    exact_mod_cast this
  linarith

/-- **⟦THE BASE-FLOOR BRIDGE⟧** (`s13_band_baseFloor`) — `log 2 · doorRowFloor M ≤ log X_d`,
from `2^j ≤ A` and the socket's `j`-floor.  This is the ONLY road from the `M`-side floors
into the base: no `2^{2^36}` is ever formed, because the tower stays inside `Real.log_pow`. -/
theorem s13_band_baseFloor {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) :
    Real.log 2 * ((doorRowFloor M : ℕ) : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by
  have hj : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
  have hpow : (2 : ℕ) ^ doorRowFloor M ≤ A + s := by
    have : (2 : ℕ) ^ doorRowFloor M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  have hR : ((2 : ℝ)) ^ (doorRowFloor M) ≤ (((A + s : ℕ)) : ℝ) := by
    have h : ((2 ^ doorRowFloor M : ℕ) : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by exact_mod_cast hpow
    simpa using h
  have h0 : (0 : ℝ) < ((2 : ℝ)) ^ (doorRowFloor M) := by positivity
  have := Real.log_le_log h0 hR
  rwa [Real.log_pow, mul_comm] at this

/-- `1 + log t / 2 ≤ √t` — `log √t ≤ √t − 1` read through `Real.log_sqrt`.  Applied ONCE it
gives `t ≥ (1 + log t/2)²`; applied to `√t` it gives `√t ≥ (1 + log t/4)²`.  That is the
whole content of §2's scale floors. -/
theorem s13_band_sqrt_ge {t : ℝ} (ht : 0 < t) : 1 + Real.log t / 2 ≤ Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt ht.le] at h
  linarith

/-- **⟦THE SCALE FLOORS AT THE ARM⟧** (`s13_band_floors`) — everything the analytic trio asks
of the base scale, from the arith frame's `Λ := loglog X_d ≥ 356600` alone (`t := log X_d`):

* `t ≥ 356601` (so `2 ≤ t`, and `12 ≤ Λ`);
* `48(Λ + 1) ≤ t` — `gHalf`'s room, from `t ≥ (1 + Λ/2)²`;
* `24(Λ + 1) ≤ √t` — `gO1`'s room, from `√t ≥ (1 + Λ/4)²`. -/
theorem s13_band_floors {t : ℝ} (ht : 0 < t) (hL : (356600 : ℝ) ≤ Real.log t) :
    356601 ≤ t ∧ 48 * (Real.log t + 1) ≤ t ∧ 24 * (Real.log t + 1) ≤ Real.sqrt t := by
  have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hsqge : 1 + Real.log t / 2 ≤ Real.sqrt t := s13_band_sqrt_ge ht
  have hsq4 : Real.sqrt (Real.sqrt t) * Real.sqrt (Real.sqrt t) = Real.sqrt t :=
    Real.mul_self_sqrt hs.le
  have h4ge : 1 + Real.log (Real.sqrt t) / 2 ≤ Real.sqrt (Real.sqrt t) := s13_band_sqrt_ge hs
  have hlogsqrt : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt ht.le
  rw [hlogsqrt] at h4ge
  refine ⟨by linarith, ?_, ?_⟩
  · nlinarith [hsqge, hsq, hL]
  · nlinarith [h4ge, hsq4, hL, Real.sqrt_nonneg (Real.sqrt t)]

/-- `log 𝒫₁ = Adoor M · log 2` at the door family (`calE A G 1 = A`). -/
theorem s13_band_log_calP_one (M : ℕ) :
    Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  rw [calP, calE_one]
  push_cast
  rw [Real.log_pow]

/-- `log 𝒬₂ = 16·A·G·M · log 2` at the door family (`s13_calQK_door_two`). -/
theorem s13_band_log_calQK_two (M : ℕ) :
    Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      = ((16 * (Adoor M * (3072 * M) * M) : ℕ) : ℝ) * Real.log 2 := by
  rw [s13_calQK_door_two]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- `log(log 2) ≥ −0.3725`, by `(1 + 0.3725/16)^16 ≤ exp 0.3725` and `Real.log_two_gt_d9`.
The ONE tight numeral of this file: `gWin`'s `𝒫₁`-floor `24.58` has `0.0008` of room. -/
theorem s13_band_loglog_two : (-(3725 : ℝ) / 10000) ≤ Real.log (Real.log 2) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2pos : (0 : ℝ) < Real.log 2 := by linarith
  rw [Real.le_log_iff_exp_le h2pos]
  have hx : (1 : ℝ) + (3725 / 10000) / 16 ≤ Real.exp ((3725 / 10000) / 16) := by
    have := Real.add_one_le_exp ((3725 / 10000 : ℝ) / 16)
    linarith
  have hpow : ((1 : ℝ) + (3725 / 10000) / 16) ^ (16 : ℕ)
      ≤ (Real.exp ((3725 / 10000) / 16)) ^ (16 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hx 16
  have hexp16 : (Real.exp ((3725 / 10000 : ℝ) / 16)) ^ (16 : ℕ)
      = Real.exp ((3725 / 10000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hnum : (14427 / 10000 : ℝ) ≤ ((1 : ℝ) + (3725 / 10000) / 16) ^ (16 : ℕ) := by
    norm_num
  have hbig : (14427 / 10000 : ℝ) ≤ Real.exp ((3725 / 10000 : ℝ)) := by
    rw [← hexp16]; linarith
  have hepos : (0 : ℝ) < Real.exp ((3725 / 10000 : ℝ)) := Real.exp_pos _
  have hneg : Real.exp (-(3725 : ℝ) / 10000) = 1 / Real.exp ((3725 / 10000 : ℝ)) := by
    rw [show (-(3725 : ℝ) / 10000) = -((3725 : ℝ) / 10000) by ring, Real.exp_neg]
    simp
  rw [hneg, div_le_iff₀ hepos]
  nlinarith [hbig, hlo]

/-- **⟦THE `𝒫₁` FLOOR⟧** (`s13_band_loglog_calP_one`) — `loglog 𝒫₁ ≥ 24.58`, uniformly in
`M`: `loglog 𝒫₁ = log(Adoor M) + log(log 2) ≥ 36·log 2 − 0.3725 = 24.5808`.  This is exactly
`gWin`'s covering-window budget `25 − 24.58 = 0.42`. -/
theorem s13_band_loglog_calP_one (M : ℕ) :
    (2458 / 100 : ℝ) ≤ Real.log (Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hll : (-(3725 : ℝ) / 10000) ≤ Real.log (Real.log 2) := s13_band_loglog_two
  have hA : ((2 ^ 36 : ℕ) : ℝ) ≤ ((Adoor M : ℕ) : ℝ) := by exact_mod_cast Adoor_ge M
  have hApos : (0 : ℝ) < ((Adoor M : ℕ) : ℝ) := by
    have h2 : ((2 : ℝ)) ^ (36 : ℕ) ≤ ((Adoor M : ℕ) : ℝ) := by push_cast at hA ⊢; linarith
    nlinarith [h2]
  have hlogA : (36 : ℝ) * Real.log 2 ≤ Real.log ((Adoor M : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((2 ^ 36 : ℕ) : ℝ)) hA
    rw [show ((2 ^ 36 : ℕ) : ℝ) = (2 : ℝ) ^ (36 : ℕ) by push_cast; ring, Real.log_pow] at h
    push_cast at h
    linarith
  rw [s13_band_log_calP_one, Real.log_mul (ne_of_gt hApos) (by linarith)]
  linarith

/-- **⟦THE `𝒬₂` FLOOR⟧** (`s13_band_log_calQK_two_ge`) — `log 𝒬₂ ≥ 1`, uniformly in `M`,
since `16·A·G·M ≥ 16`.  `gO1` needs `≥ 0` and `gWin` needs `> 0`; both ride this. -/
theorem s13_band_log_calQK_two_ge (M : ℕ) (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : 1 ≤ Adoor M * (3072 * M) * M := by
    have hA := one_le_Adoor M
    have h2 : 1 ≤ 3072 * M := by omega
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ Adoor M * (3072 * M) * M := Nat.mul_le_mul (Nat.mul_le_mul hA h2) hM
  have h16 : (16 : ℕ) ≤ 16 * (Adoor M * (3072 * M) * M) := by omega
  have h16R : (16 : ℝ) ≤ ((16 * (Adoor M * (3072 * M) * M) : ℕ) : ℝ) := by exact_mod_cast h16
  rw [s13_band_log_calQK_two]
  nlinarith [h16R, hlo]

/-! ## §3 — THE CONDUCTOR GATE AND THE ANALYTIC TRIO

`qfit` is the `12`-vs-`10` conductor mismatch, and it goes off `DoorArithFrameRho.arm`
(`7000·λ_H ≤ Λ`), NOT off `SocketBase`'s own `q`-field: the socket bounds `q` by
`arcDen 12 H = (log H)^{12}`, an `H`-side object, and the band asks for `(log X_d)^{10}`, an
`X_d`-side object.  The arm converts one into the other with a factor `5833` to spare.

The trio is `M`-uniform at `Aexp = 3` (⟦F1⟧): every hypothesis is a scale floor of §2. -/

/-- **⟦`qfit`⟧** (`s13_band_qfit`) — `q ≤ (log X_d)^{10}` from `q ≤ (log H)^{12}` and the
arm.  `12·λ_H ≤ 10·Λ` is `7000·λ_H ≤ Λ` with `5833×` of margin. -/
theorem s13_band_qfit {q H Xd : ℕ}
    (hq : (q : ℝ) ≤ arcDen 12 H)
    (hH : (0 : ℝ) < Real.log ((H : ℕ) : ℝ)) (hX : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hHfl : (0 : ℝ) ≤ Real.log (Real.log ((H : ℕ) : ℝ)))
    (harm : 7000 * Real.log (Real.log ((H : ℕ) : ℝ))
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ))) :
    (q : ℝ) ≤ (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ) := by
  refine le_trans hq ?_
  have hA : arcDen 12 H = Real.exp (12 * Real.log (Real.log ((H : ℕ) : ℝ))) := by
    rw [arcDen, Real.rpow_def_of_pos hH]; ring_nf
  have hB : (Real.log ((Xd : ℕ) : ℝ)) ^ (10 : ℕ)
      = Real.exp (10 * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [← Real.rpow_natCast (Real.log ((Xd : ℕ) : ℝ)) 10, Real.rpow_def_of_pos hX]
    push_cast; ring_nf
  rw [hA, hB]
  exact Real.exp_le_exp.mpr (by linarith)

/-- **⟦`gHalf` AT `Aexp = 3`⟧** (`s13_band_gHalf`) — the half-range mass gate on
`[X_d, 2X_d]`.  The `k`-transport is `log k ≥ log X_d` and `loglog k ≤ loglog X_d + 1`. -/
theorem s13_band_gHalf {Xd : ℕ} (hX : (2 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ))
    (hg : 48 * (Real.log (Real.log ((Xd : ℕ) : ℝ)) + 1) ≤ Real.log ((Xd : ℕ) : ℝ)) :
    ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
      16 * (3 : ℝ) * Real.log (Real.log ((k : ℕ) : ℝ)) ≤ Real.log ((k : ℕ) : ℝ) := by
  intro k hk1 hk2
  have hXd0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Xd with hz | hz
    · rw [hz] at hX; norm_num at hX
    · exact_mod_cast hz
  have hkX : ((Xd : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk1
  have hk2X : ((k : ℕ) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by exact_mod_cast hk2
  have hlk : Real.log ((Xd : ℕ) : ℝ) ≤ Real.log ((k : ℕ) : ℝ) := Real.log_le_log hXd0 hkX
  have hlk2 : Real.log ((k : ℕ) : ℝ) ≤ Real.log 2 + Real.log ((Xd : ℕ) : ℝ) := by
    have := Real.log_le_log (by linarith) hk2X
    rwa [Real.log_mul (by norm_num) (ne_of_gt hXd0)] at this
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hll : Real.log (Real.log ((k : ℕ) : ℝ))
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) + 1 := by
    have hstep : Real.log ((k : ℕ) : ℝ) ≤ 2 * Real.log ((Xd : ℕ) : ℝ) := by linarith
    have := Real.log_le_log (by linarith) hstep
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    linarith
  linarith

/-- **⟦`gO1` AT `Aexp = 3`⟧** (`s13_band_gO1`) — the `O(1)`-range Rankin gate at the door's
upper cutoff `𝒬₂`, off `DoorRowZeroBase.reg` (`log 𝒬₂ ≤ √log X_d`) and §2's `√`-floor. -/
theorem s13_band_gO1 {Xd Q : ℕ} (hX : (2 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ))
    (hQ0 : (0 : ℝ) ≤ Real.log ((Q : ℕ) : ℝ))
    (hreg : Real.log ((Q : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Xd : ℕ) : ℝ)))
    (hg : 24 * (Real.log (Real.log ((Xd : ℕ) : ℝ)) + 1)
      ≤ Real.sqrt (Real.log ((Xd : ℕ) : ℝ))) :
    ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
      8 * (3 : ℝ) * Real.log (Real.log ((k : ℕ) : ℝ)) * Real.log ((Q : ℕ) : ℝ)
        ≤ Real.log ((k : ℕ) : ℝ) := by
  intro k hk1 hk2
  have hXd0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Xd with hz | hz
    · rw [hz] at hX; norm_num at hX
    · exact_mod_cast hz
  have hkX : ((Xd : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk1
  have hk2X : ((k : ℕ) : ℝ) ≤ 2 * ((Xd : ℕ) : ℝ) := by exact_mod_cast hk2
  have hlk : Real.log ((Xd : ℕ) : ℝ) ≤ Real.log ((k : ℕ) : ℝ) := Real.log_le_log hXd0 hkX
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlk2 : Real.log ((k : ℕ) : ℝ) ≤ Real.log 2 + Real.log ((Xd : ℕ) : ℝ) := by
    have := Real.log_le_log (by linarith) hk2X
    rwa [Real.log_mul (by norm_num) (ne_of_gt hXd0)] at this
  have hll : Real.log (Real.log ((k : ℕ) : ℝ))
      ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) + 1 := by
    have hstep : Real.log ((k : ℕ) : ℝ) ≤ 2 * Real.log ((Xd : ℕ) : ℝ) := by linarith
    have := Real.log_le_log (by linarith) hstep
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    linarith
  have hsq : Real.sqrt (Real.log ((Xd : ℕ) : ℝ)) * Real.sqrt (Real.log ((Xd : ℕ) : ℝ))
      = Real.log ((Xd : ℕ) : ℝ) := Real.mul_self_sqrt (by linarith)
  have hllpos : (0 : ℝ) ≤ Real.log (Real.log ((k : ℕ) : ℝ)) := by
    refine Real.log_nonneg ?_
    linarith
  calc 8 * (3 : ℝ) * Real.log (Real.log ((k : ℕ) : ℝ)) * Real.log ((Q : ℕ) : ℝ)
      ≤ (24 * (Real.log (Real.log ((Xd : ℕ) : ℝ)) + 1))
          * Real.sqrt (Real.log ((Xd : ℕ) : ℝ)) := by
        refine mul_le_mul (by linarith) hreg hQ0 ?_
        have : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
          refine Real.log_nonneg ?_; linarith
        linarith
    _ ≤ Real.sqrt (Real.log ((Xd : ℕ) : ℝ)) * Real.sqrt (Real.log ((Xd : ℕ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_right hg (Real.sqrt_nonneg _)
    _ = Real.log ((Xd : ℕ) : ℝ) := hsq
    _ ≤ Real.log ((k : ℕ) : ℝ) := hlk

/-- **⟦`gWin` AT `Aexp = 3`⟧** (`s13_band_gWin`) — the covering-window gate at `[𝒫₁, 𝒬₂]`.
`loglog 𝒬₂ ≤ ½·loglog X_d` is `reg` read through `Real.log_sqrt`; the surviving constant is
`2e·(25 − loglog 𝒫₁) ≤ 2e·0.42`, which the `12 ≤ loglog X_d` floor absorbs against `3 − e`. -/
theorem s13_band_gWin {Xd P Q : ℕ}
    (hX : (12 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)))
    (hX2 : (2 : ℝ) ≤ Real.log ((Xd : ℕ) : ℝ))
    (hP : (2458 / 100 : ℝ) ≤ Real.log (Real.log ((P : ℕ) : ℝ)))
    (hQ1 : (1 : ℝ) ≤ Real.log ((Q : ℕ) : ℝ))
    (hreg : Real.log ((Q : ℕ) : ℝ) ≤ Real.sqrt (Real.log ((Xd : ℕ) : ℝ))) :
    ∀ k : ℕ, Xd ≤ k → k ≤ 2 * Xd →
      Real.exp (2 * Real.exp 1
          * (Real.log (Real.log ((Q : ℕ) : ℝ)) - Real.log (Real.log ((P : ℕ) : ℝ)) + 25))
        ≤ (Real.log ((k : ℕ) : ℝ)) ^ (3 : ℝ) := by
  intro k hk1 hk2
  have hXd0 : (0 : ℝ) < ((Xd : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos Xd with hz | hz
    · rw [hz] at hX2; norm_num at hX2
    · exact_mod_cast hz
  have hkX : ((Xd : ℕ) : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk1
  have hlk : Real.log ((Xd : ℕ) : ℝ) ≤ Real.log ((k : ℕ) : ℝ) := Real.log_le_log hXd0 hkX
  have hlkpos : (0 : ℝ) < Real.log ((k : ℕ) : ℝ) := by linarith
  have hllk : Real.log (Real.log ((Xd : ℕ) : ℝ)) ≤ Real.log (Real.log ((k : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith) hlk
  have hRHS : (Real.log ((k : ℕ) : ℝ)) ^ (3 : ℝ)
      = Real.exp (3 * Real.log (Real.log ((k : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hlkpos]; ring_nf
  rw [hRHS]
  refine Real.exp_le_exp.mpr ?_
  have hlQ : Real.log (Real.log ((Q : ℕ) : ℝ))
      ≤ (1 / 2) * Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
    have h1 : Real.log (Real.log ((Q : ℕ) : ℝ))
        ≤ Real.log (Real.sqrt (Real.log ((Xd : ℕ) : ℝ))) :=
      Real.log_le_log (by linarith) hreg
    have h2 : Real.log (Real.sqrt (Real.log ((Xd : ℕ) : ℝ)))
        = (1 / 2) * Real.log (Real.log ((Xd : ℕ) : ℝ)) := by
      rw [Real.log_sqrt (by linarith)]; ring
    linarith
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hLk12 : (12 : ℝ) ≤ Real.log (Real.log ((k : ℕ) : ℝ)) := le_trans hX hllk
  have hstep : 2 * Real.exp 1
        * (Real.log (Real.log ((Q : ℕ) : ℝ)) - Real.log (Real.log ((P : ℕ) : ℝ)) + 25)
      ≤ 2 * Real.exp 1 * ((1 / 2) * Real.log (Real.log ((k : ℕ) : ℝ)) + 42 / 100) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have hprod : Real.exp 1 * Real.log (Real.log ((k : ℕ) : ℝ))
      ≤ 2.7182818286 * Real.log (Real.log ((k : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right he.le (by linarith)
  have hexpand : 2 * Real.exp 1 * ((1 / 2) * Real.log (Real.log ((k : ℕ) : ℝ)) + 42 / 100)
      = Real.exp 1 * Real.log (Real.log ((k : ℕ) : ℝ)) + (84 / 100) * Real.exp 1 := by
    ring
  linarith [hstep, hprod, hexpand.le, hexpand.ge]

/-! ## §4 — `err` AT THE PIN

⟦F2's payoff⟧ `hErr` asks `4·(log X_d)^{−1/2+1/1000} ≤ exp(−M₀/(2e))`, and the pin carries a
factor `e` in front.  So `−(1/(2e))·M₀` is EXACTLY `−½·(loglog X_d/45 + 14λ₊ + 2log(C₁+1) +
log(1/ρ) + 12)` — the `e` cancels on the nose, no inequality spent — and the whole field
reduces to comparing `log 4 + (−½ + 1/1000)·Λ` with that.  What survives is one linear
residue line in `Λ`, discharged in §5 from `Λ ≥ 356600` and `S13BandGate.err_res`. -/

/-- **⟦`err` AT THE `s13BandM0` PIN⟧** (`s13_band_err_at_pin`) — `DoorBandBase.err`, under
ONE residue line.  `1/45 − 1/1000 ≥ 0.9757/45` is where the `0.9757` comes from. -/
theorem s13_band_err_at_pin {R : ChowlaRegime} {Xd : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hμ : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hΛ : (0 : ℝ) ≤ Real.log (Real.log ((Xd : ℕ) : ℝ)))
    (hgate : 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 2 * Real.log (C₁ Xd + 1)
        + Real.log (1 / ρ) + 15
      ≤ (9757 / 10000) * Real.log (Real.log ((Xd : ℕ) : ℝ))) :
    4 * Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * s13BandM0 R ρ C₁ Xd) := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hrw : Real.log ((Xd : ℕ) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
      = Real.exp ((-(1 : ℝ) / 2 + 1 / 1000) * Real.log (Real.log ((Xd : ℕ) : ℝ))) := by
    rw [Real.rpow_def_of_pos hμ]; ring_nf
  have h4 : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
  rw [hrw, h4, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hcancel : -(1 / (2 * Real.exp 1)) * s13BandM0 R ρ C₁ Xd
      = -(1 / 2) * (Real.log (Real.log ((Xd : ℕ) : ℝ)) / 45
        + 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 2 * Real.log (C₁ Xd + 1)
        + Real.log (1 / ρ) + 12) := by
    rw [s13BandM0]; field_simp
  rw [hcancel]
  have hlog4 : Real.log 4 < 1.3863 := by
    have h4e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith
  linarith

/-! ## §5 — THE GATE STRUCTURE AND THE SUPPLIER

⟦THE FIVE GATE LINES⟧ (`S13BandGate`), and what each one is:

1. `x0_le` — `x₀ ≤ 2^{doorRowFloor M}`.  IRREDUCIBLE: `x₀` is `MmuChiRate`'s opaque
   threshold witness, quantified AFTER `M` at every consumer.  Reduced from the raw
   `x₀ ≤ X_d` to an `M`-only line by the socket's `j`-floor.
2. `C1_one` — `1 ≤ C₁ n`.  FREE at the caller's `C₁ ≡ 1` (`DoorArithFrameRho.C1_nonneg` is
   the only other reader of `C₁`).
3. `grade` — `8C' ≤ (log 2 · doorRowFloor M)^{5/2 + 1/1000}`.  IRREDUCIBLE for the same
   reason as (1); reduced to an `M`-only line through the base-floor bridge.
4. `err_res` — `14·loglog H₊ + 2·log(C₁ n + 1) + log(1/ρ) + 15 ≤ 347900`.  The `T₀`-band
   residue, AFTER the `e`-cancellation; it is a numeral line because the arm already pins
   `Λ ≥ 356600` and `0.9757·356600 = 347934.6`.  At `C₁ ≡ 1`, `λ₊ ≤ 289` and
   `ρ = doorRhoOfDelta …` this reads `≈ 4300 ≤ 347900`.
5. `block` — `s13BlockFloor M ≤ A + s` at every socket base.  ⟦F3⟧: NOT socket-implied (the
   socket's floor is `2^{M·Adoor M}`, the block floor `2^{400(A·G·M)²}`), and the landed
   `MSelect`/`blockCeil` statements are not amended to make it so. -/

/-- **THE BAND GATE BUNDLE** (`S13BandGate`) — the five lines `doorBandBase_family` cannot
pay from the socket and the arith frame.  Everything else in `DoorBandBase` is discharged. -/
structure S13BandGate (R : ChowlaRegime) (M x₀ : ℕ) (C' ρ : ℝ) (C₁ : ℕ → ℝ) : Prop where
  /-- ⟦1⟧ the opaque threshold, floored at the socket's own `j`-floor. -/
  x0_le : x₀ ≤ 2 ^ doorRowFloor M
  /-- ⟦2⟧ the band constant's normalisation (free at `C₁ ≡ 1`). -/
  C1_one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n
  /-- ⟦3⟧ the grade fit, at the `M`-only floor `log 2 · doorRowFloor M`. -/
  grade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- ⟦4⟧ the `T₀`-band residue line at the pin, after the `e`-cancellation. -/
  err_res : ∀ n : ℕ, 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 2 * Real.log (C₁ n + 1)
    + Real.log (1 / ρ) + 15 ≤ 347900
  /-- ⟦5⟧ ⟦F3⟧ the block-scale floor at every socket base. -/
  block : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor M ≤ A + s

/-- **⟦THE `DoorBandBase` SUPPLIER⟧** (`doorBandBase_family`) — the closure's last unbuilt
object.  At the eighteen consumer sites' binder shape, with `Aexp := s13Aexp` (⟦F1⟧) and
`M₀ := s13BandM0 R ρ C₁` (⟦F2⟧):

* `X400`, `x₀_le` — the socket's `j`-floor (`§2`);
* `C₁_one`, `grade`, `err`'s residue — `S13BandGate`;
* `qfit` — the arith frame's ARM (`§3`), not the socket's `q`-field;
* `gHalf`, `gO1`, `gWin` — the trio at `Aexp = 3`, `M`-uniform, off `DoorRowZeroBase.reg`
  (i.e. off the block-floor line) and the arm's `Λ ≥ 356600`;
* `err` — the exact `e`-cancellation at the pin (`§4`).

The arith-frame family is the SAME `harith` hypothesis the terminal already carries, at the
same `M₀` — that identity is ⟦F2⟧'s incompatibility fence, and it is what lets one `M₀`
serve the band and the arithmetic page at once. -/
theorem doorBandBase_family {R : ChowlaRegime} {M x₀ : ℕ} {C' K ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) K ρ)
    (hgate : S13BandGate R M x₀ C' ρ C₁) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorBandBase x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (s13BandM0 R ρ C₁ (A + s)) := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  -- ⟦the arm's two consequences⟧
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the row-zero bundle at this base — the block-floor line⟧
  have hjfl : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five hM (hgate.block H L q j A s hb) hjfl
  have hreg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400 hM hb
      C₁_one := hgate.C1_one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · -- ⟦`x₀_le`⟧ the gate line, transported by `2^{doorRowFloor M} ≤ 2^j ≤ A`
    have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloor M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hgate.x0_le (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · -- ⟦`qfit`⟧ off the ARM
    refine s13_band_qfit hb.2.2.2.2.1 (lt_trans (by norm_num) hfr.one_lt_logH) hμ ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · -- ⟦`gHalf`⟧
    intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gO1`⟧
    intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge M hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gWin`⟧
    intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one M)
      (s13_band_log_calQK_two_ge M hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · -- ⟦`grade`⟧ the gate line, transported by the base-floor bridge
    refine le_trans hgate.grade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor hb) ?_
    rw [s13Aexp]; norm_num
  · -- ⟦`err`⟧ the exact cancellation at the pin, under the residue line
    refine s13_band_err_at_pin hμ hΛ0 ?_
    have := hgate.err_res (A + s)
    linarith

open MeasureTheory in
/-- **⟦THE BYTE-FIT, CERTIFIED⟧** (`s13_hband_at_door_of_gate`) — `S11Hoist`'s landed band
slot `m4_hband_at_door_slot_hoisted`, with its `DoorBandBase` binder DISCHARGED by
`doorBandBase_family`.  The compile IS the certificate that the supplier's conclusion is the
consumer binder byte for byte, at `Aexp := s13Aexp` and `M₀ := s13BandM0 R ρ C₁`; the same
term serves the other seventeen sites, which quantify the identical binder.

What is left in the open is exactly: the landed slot `MmuChiRate`, the arith-frame family at
the shared pin, and the five lines of `S13BandGate`. -/
theorem s13_hband_at_door_of_gate (hMmu : MmuChiRate) (R : ChowlaRegime) (M : ℕ) (hM : 1 ≤ M)
    (K ρ : ℝ) (C₁ : ℕ → ℝ)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) K ρ) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      (S13BandGate R M x₀ C' ρ C₁ →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (s13BandM0 R ρ C₁ (A + s))) := by
  obtain ⟨C', x₀, hC'pos, hband⟩ :=
    m4_hband_at_door_slot_hoisted hMmu s13Aexp s13Aexp_pos M hM
  exact ⟨C', x₀, hC'pos, fun hgate => hband R C₁ (s13BandM0 R ρ C₁)
    (doorBandBase_family hM harith hgate)⟩

/-! ## §6 — ⟦ERR-REPAIR⟧ THE SHARP ARM AT THE WINDOW TOP, AND `err` FOR FREE

PURELY ADDITIVE: §5's `S13BandGate` and `doorBandBase_family` are untouched; this section
builds a PARALLEL gate with one fewer line.

⟦WHY⟧ `S13BandGate.err_res` is a NUMERAL line (`14·λ₊ + … ≤ 347900`), obtained by spending
the arm's floor `Λ ≥ 356600` and throwing the rest of `loglog X_d` away.  Read as a cap on
the window top it says `λ₊ ≤ 24849`; the refuter's kernel probe (`ERR-REF`, flags 2026-07-30
23:38) then showed that against WIDTH-SCOPE's forced tower `λ₊ ≥ λ₋³ ≥ 125000` the whole
selection register is EMPTY at every regime the spine can build.  No numeral can repair it:
`λ₊` has no upper bound on the register.  The line is DELETED here, not re-numeraled.

⟦THE ROUTE⟧ the compose pins `R.x` by its own `g`-arm read AT THE WINDOW TOP `H₊` — not at
the per-base `H` that `DoorArithFrameRho.arm` records — and `SocketBase`'s x-scale field caps
`R.x` by `16·ω·arcDen 12 H·A` at that base's `H ≤ H₊`.  `arcDen 12` is monotone in `H`, so
the `H₊`-form of the arm survives at EVERY base (`s13_band_arm_at_top`), and the residue line
closes on its CONSTANT term alone: `0.9757·(7000λ₊ + 500·log(1/ρ) + 6600)` beats
`14λ₊ + 2log(C₁+1) + log(1/ρ) + 15` with `6439.62` against `17` before a single `λ₊` is
spent.  The `err` leg therefore carries NO width law at all — it is priced against the OUTER
scale `x`, where ⟦B4⟧'s crossing bound is a `λ₊`-`λ₋` law through `M`.

Constants `7000 / 500 / 6600 / 0.9757` are unchanged, and `DoorArithFrameRho` is not read
differently: the arm at `H₊` is derived directly from `m4_arith_arm_of_gArmRho`, the frame's
own supplier lemma, at the socket's own antecedent. -/

/-- **⟦THE ARM, READ AT THE WINDOW TOP⟧** (`s13_band_arm_at_top`) — from the `g`-arm floor at
`H₊` and `SocketBase`'s x-scale field at the base's own `H ≤ H₊`, the `H₊`-form
`loglog A ≥ 7000·loglog H₊ + 500·log(1/ρ) + 6600` at EVERY socket base.  Monotonicity of
`arcDen 12` is the only inequality spent beyond `m4_arith_arm_of_gArmRho`. -/
theorem s13_band_arm_at_top {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ}
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ R.Hhi ≤ (R.x : ℝ))
    (hb : SocketBase R M H L q j A s) :
    7000 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log ((A : ℕ) : ℝ)) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hhi : H ≤ R.Hhi := hb.2.1
  have hAx : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 H * (A : ℝ) :=
    hb.2.2.2.2.2.2.2.2.2.2.1
  have hω : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast R.hω
    linarith
  obtain ⟨hlogH0, hlamH⟩ := hHreg H hlo hhi
  obtain ⟨hlogT0, hlamT⟩ := hHreg R.Hhi (le_trans hlo hhi) le_rfl
  -- ⟦`arcDen 12 H ≤ arcDen 12 H₊`⟧
  have hHpos : (0 : ℝ) < Real.log ((H : ℕ) : ℝ) :=
    lt_of_lt_of_le (by norm_num) (one_lt_log_of_loglog_ge hlogH0 (by norm_num) hlamH).le
  have hH0 : (0 : ℝ) < ((H : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos H with hz | hz
    · rw [hz] at hHpos; norm_num at hHpos
    · exact_mod_cast hz
  have hcast : ((H : ℕ) : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hhi
  have hlogmono : Real.log ((H : ℕ) : ℝ) ≤ Real.log ((R.Hhi : ℕ) : ℝ) :=
    Real.log_le_log hH0 hcast
  have harc : arcDen 12 H ≤ arcDen 12 R.Hhi := by
    rw [arcDen, arcDen]; exact Real.rpow_le_rpow hHpos.le hlogmono (by norm_num)
  have hApos : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hsock : (R.x : ℝ) ≤ 16 * (R.ω : ℝ) * arcDen 12 R.Hhi * (A : ℝ) := by
    refine le_trans hAx ?_
    have h1 : 16 * (R.ω : ℝ) * arcDen 12 H ≤ 16 * (R.ω : ℝ) * arcDen 12 R.Hhi := by
      nlinarith [harc, hω]
    nlinarith [h1, hApos]
  have := m4_arith_arm_of_gArmRho (x₀ := 0) (K := 0) hω hlogT0 hlamT hg hsock
  linarith [this]

/-- **⟦THE `err` LEG IS FREE⟧** (`s13_band_err_free`) — `DoorBandBase.err` at the ⟦F2⟧ pin,
discharged at EVERY socket base off the `H₊`-form arm alone, with NO upper constraint on
`λ₊ = loglog H₊` of any kind.  The residue line is paid with a factor `6829.9/14 = 487.85`
of slack in `λ₊`, `487.85` in `log(1/ρ)`, and `6439.62` against `17` in the constant. -/
theorem s13_band_err_free {R : ChowlaRegime} {M H L q j A s : ℕ} {ρ : ℝ} {C₁ : ℕ → ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hC1lo : (1 : ℝ) ≤ C₁ (A + s)) (hC1hi : C₁ (A + s) ≤ 1)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ R.Hhi ≤ (R.x : ℝ))
    (hb : SocketBase R M H L q j A s) :
    4 * Real.log (((A + s : ℕ)) : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)
      ≤ Real.exp (-(1 / (2 * Real.exp 1)) * s13BandM0 R ρ C₁ (A + s)) := by
  have harm := s13_band_arm_at_top hHreg hg hb
  obtain ⟨hlogT0, hlamT⟩ := hHreg R.Hhi (le_trans hb.1 hb.2.1) le_rfl
  have hlρ : (0 : ℝ) ≤ Real.log (1 / ρ) := by
    rw [one_div, Real.log_inv]
    have : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
    linarith
  -- ⟦the arm's floor transports from `A` to the shifted base `A + s`⟧
  have hA356 : (356600 : ℝ) ≤ Real.log (Real.log ((A : ℕ) : ℝ)) := by linarith
  have hlogA1 : (1 : ℝ) < Real.log ((A : ℕ) : ℝ) :=
    one_lt_log_of_loglog_ge (log_natCast_nonneg' A) (by norm_num) hA356
  have hApos : (0 : ℝ) < ((A : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos A with hz | hz
    · rw [hz] at hlogA1; norm_num at hlogA1
    · exact_mod_cast hz
  have hAX : ((A : ℕ) : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hshift := m4_arith_arm_of_shift hApos (by linarith) hAX harm
  -- ⟦the two side pins on the shifted base⟧
  have hΛ : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) :=
    lt_trans (by norm_num)
      (one_lt_log_of_loglog_ge (log_natCast_nonneg' (A + s)) (show (0:ℝ) < 356600 by norm_num)
        (by linarith))
  refine s13_band_err_at_pin (R := R) (Xd := A + s) (ρ := ρ) (C₁ := C₁) hμ hΛ ?_
  -- ⟦THE RESIDUE LINE, SHARP⟧ `14λ₊ + 2·log(C₁+1) + log(1/ρ) + 15 ≤ 0.9757·loglog X_d`
  have hc : Real.log (C₁ (A + s) + 1) ≤ 1 := by
    have h2 : Real.log (C₁ (A + s) + 1) ≤ Real.log 2 :=
      Real.log_le_log (by linarith) (by linarith)
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  -- `0.9757·(7000λ₊ + 500·log(1/ρ) + 6600) = 6829.9λ₊ + 487.85·log(1/ρ) + 6439.62`
  set X : ℝ := Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) with hXdef
  set Y : ℝ := Real.log (Real.log (((A + s : ℕ)) : ℝ)) with hYdef
  set L : ℝ := Real.log (1 / ρ) with hLdef
  set c : ℝ := Real.log (C₁ (A + s) + 1) with hcdef
  linarith [hshift, hlamT, hlρ, hc]

/-- **THE SHARP BAND GATE BUNDLE** (`S13BandGate'`) — §5's `S13BandGate` with the `err_res`
line DELETED and NOTHING added.  Four lines survive, and `ρ` is no longer a parameter: it
appeared only in `err_res`.

⟦1⟧ `x0_le`, ⟦2⟧ `C1_one`, ⟦3⟧ `grade`, ⟦4⟧ `block` — verbatim from §5. -/
structure S13BandGate' (R : ChowlaRegime) (M x₀ : ℕ) (C' : ℝ) (C₁ : ℕ → ℝ) : Prop where
  /-- ⟦1⟧ the opaque threshold, floored at the socket's own `j`-floor. -/
  x0_le : x₀ ≤ 2 ^ doorRowFloor M
  /-- ⟦2⟧ the band constant's normalisation (free at `C₁ ≡ 1`). -/
  C1_one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n
  /-- ⟦3⟧ the grade fit, at the `M`-only floor `log 2 · doorRowFloor M`. -/
  grade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- ⟦4⟧ ⟦F3⟧ the block-scale floor at every socket base. -/
  block : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor M ≤ A + s

/-- **⟦THE SHARP `DoorBandBase` SUPPLIER⟧** (`doorBandBase_family'`) — §5's
`doorBandBase_family` with `err` paid by the arm at the window top instead of by the numeral
residue line.  The conclusion is BYTE-IDENTICAL to §5's, so every consumer of the landed
supplier accepts this one unchanged.

Two hypotheses replace `S13BandGate.err_res`, and both are already carried at the compose:
`hHreg` (the register's `H`-floor, `regime_Hfloor_of_loglogFloor50`) and `hg` (the `g`-arm at
`H₊`, the compose's own `hgarm` at `H := R.Hhi`).  `hC1hi` is `le_rfl` at the caller's
`C₁ ≡ 1`, the same pin `C1_one` is free at. -/
theorem doorBandBase_family' {R : ChowlaRegime} {M x₀ : ℕ} {C' K ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hC1hi : ∀ n : ℕ, C₁ n ≤ 1)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ R.Hhi ≤ (R.x : ℝ))
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) K ρ)
    (hgate : S13BandGate' R M x₀ C' C₁) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorBandBase x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (s13BandM0 R ρ C₁ (A + s)) := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  -- ⟦the arm's two consequences⟧
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the row-zero bundle at this base — the block-floor line⟧
  have hjfl : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five hM (hgate.block H L q j A s hb) hjfl
  have hreg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400 hM hb
      C₁_one := hgate.C1_one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · -- ⟦`x₀_le`⟧ the gate line, transported by `2^{doorRowFloor M} ≤ 2^j ≤ A`
    have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloor M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hgate.x0_le (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · -- ⟦`qfit`⟧ off the ARM
    refine s13_band_qfit hb.2.2.2.2.1 (lt_trans (by norm_num) hfr.one_lt_logH) hμ ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · -- ⟦`gHalf`⟧
    intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gO1`⟧
    intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge M hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gWin`⟧
    intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one M)
      (s13_band_log_calQK_two_ge M hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · -- ⟦`grade`⟧ the gate line, transported by the base-floor bridge
    refine le_trans hgate.grade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor hb) ?_
    rw [s13Aexp]; norm_num
  · -- ⟦`err`⟧ THE ARM AT THE TOP — no `λ₊` cap anywhere
    exact s13_band_err_free hρ0 hρ1 (hgate.C1_one (A + s)) (hC1hi (A + s)) hHreg hg hb

/-! ## §GK — the G-lever twin -/

/-- `s13_band_log_calP_one` (:194) TRANSPORTED to the lever.  LEVEL 1 is K-INVARIANT
(`calP_gk_one_eq`), so this is the landed numeral re-read at the levered symbol, not a twin. -/
theorem s13_band_log_calP_one_gk (K M : ℕ) :
    Real.log ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) = ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  rw [calP_gk_one_eq]
  exact s13_band_log_calP_one M

/-- `s13_band_loglog_calP_one` (:239) TRANSPORTED to the lever — the `𝒫₁` floor `24.58` is
LEVEL 1 and therefore does not move. -/
theorem s13_band_loglog_calP_one_gk (K M : ℕ) :
    (2458 / 100 : ℝ) ≤ Real.log (Real.log ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ)) := by
  rw [calP_gk_one_eq]
  exact s13_band_loglog_calP_one M

/-- `s13_band_log_calQK_two (:201)` at the lever.  RE-DERIVED: the `16·(A·G·M)`
form now carries the lever's `2^K` inside `G`. -/
theorem s13_band_log_calQK_two_gk (K : ℕ) (M : ℕ) :
    Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
      = ((16 * (Adoor M * (s13GK K M) * M) : ℕ) : ℝ) * Real.log 2 := by
  rw [s13_calQK_door_two_gk K]
  push_cast
  rw [Real.log_pow]
  push_cast
  ring

/-- `s13_band_log_calQK_two_ge (:257)` at the lever. -/
theorem s13_band_log_calQK_two_ge_gk (K : ℕ) (M : ℕ) (hM : 1 ≤ M) :
    (1 : ℝ) ≤ Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) := by
  have hlo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h1 : 1 ≤ Adoor M * (s13GK K M) * M := by
    have hA := one_le_Adoor M
    have h2 : 1 ≤ s13GK K M := one_le_s13GK K hM
    calc 1 = 1 * 1 * 1 := by ring
      _ ≤ Adoor M * (s13GK K M) * M := Nat.mul_le_mul (Nat.mul_le_mul hA h2) hM
  have h16 : (16 : ℕ) ≤ 16 * (Adoor M * (s13GK K M) * M) := by omega
  have h16R : (16 : ℝ) ≤ ((16 * (Adoor M * (s13GK K M) * M) : ℕ) : ℝ) := by exact_mod_cast h16
  rw [s13_band_log_calQK_two_gk K]
  nlinarith [h16R, hlo]

/-! ## §3 — THE CONDUCTOR GATE AND THE ANALYTIC TRIO

`qfit` is the `12`-vs-`10` conductor mismatch, and it goes off `DoorArithFrameRho.arm`
(`7000·λ_H ≤ Λ`), NOT off `SocketBase`'s own `q`-field: the socket bounds `q` by
`arcDen 12 H = (log H)^{12}`, an `H`-side object, and the band asks for `(log X_d)^{10}`, an
`X_d`-side object.  The arm converts one into the other with a factor `5833` to spare.

The trio is `M`-uniform at `Aexp = 3` (⟦F1⟧): every hypothesis is a scale floor of §2. -/

/-- `S13BandGate (:481)` at the lever. Only `block` moves (to the levered floor). -/
structure S13BandGate_gk (K : ℕ) (R : ChowlaRegime) (M x₀ : ℕ) (C' ρ : ℝ) (C₁ : ℕ → ℝ) : Prop where
  /-- ⟦1⟧ the opaque threshold, floored at the socket's own `j`-floor. -/
  x0_le : x₀ ≤ 2 ^ doorRowFloor M
  /-- ⟦2⟧ the band constant's normalisation (free at `C₁ ≡ 1`). -/
  C1_one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n
  /-- ⟦3⟧ the grade fit, at the `M`-only floor `log 2 · doorRowFloor M`. -/
  grade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- ⟦4⟧ the `T₀`-band residue line at the pin, after the `e`-cancellation. -/
  err_res : ∀ n : ℕ, 14 * Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) + 2 * Real.log (C₁ n + 1)
    + Real.log (1 / ρ) + 15 ≤ 347900
  /-- ⟦5⟧ ⟦F3⟧ the block-scale floor at every socket base. -/
  block : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s

/-- `doorBandBase_family (:509)` at the lever. -/
theorem doorBandBase_family_gk (K : ℕ) {R : ChowlaRegime} {M x₀ : ℕ} {C' Kar ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) Kar ρ)
    (hgate : S13BandGate_gk K R M x₀ C' ρ C₁) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorBandBase_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (s13BandM0 R ρ C₁ (A + s)) := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  -- ⟦the arm's two consequences⟧
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the row-zero bundle at this base — the block-floor line⟧
  have hjfl : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five_gk K hM (hgate.block H L q j A s hb) hjfl
  have hreg : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400 hM hb
      C₁_one := hgate.C1_one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · -- ⟦`x₀_le`⟧ the gate line, transported by `2^{doorRowFloor M} ≤ 2^j ≤ A`
    have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloor M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hgate.x0_le (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · -- ⟦`qfit`⟧ off the ARM
    refine s13_band_qfit hb.2.2.2.2.1 (lt_trans (by norm_num) hfr.one_lt_logH) hμ ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · -- ⟦`gHalf`⟧
    intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gO1`⟧
    intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge_gk K M hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gWin`⟧
    intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one_gk K M)
      (s13_band_log_calQK_two_ge_gk K M hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · -- ⟦`grade`⟧ the gate line, transported by the base-floor bridge
    refine le_trans hgate.grade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor hb) ?_
    rw [s13Aexp]; norm_num
  · -- ⟦`err`⟧ the exact cancellation at the pin, under the residue line
    refine s13_band_err_at_pin hμ hΛ0 ?_
    have := hgate.err_res (A + s)
    linarith

open MeasureTheory in
/-- `s13_hband_at_door_of_gate (:585)` at the lever. -/
theorem s13_hband_at_door_of_gate_gk (K : ℕ) (hMmu : MmuChiRate) (R : ChowlaRegime)
    (M : ℕ) (hM : 1 ≤ M)
    (Kar ρ : ℝ) (C₁ : ℕ → ℝ)
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) Kar ρ) :
    ∃ (C' : ℝ) (x₀ : ℕ), 0 < C' ∧
      (S13BandGate_gk K R M x₀ C' ρ C₁ →
        ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
          ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
              ‖dpolyA (winCutH (A + s) (doorChiCoeff_gk K χ M))
                (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
              ≤ t0BandB (((A + s : ℕ)) : ℝ)
                  (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (s13BandM0 R ρ C₁ (A + s))) := by
  obtain ⟨C', x₀, hC'pos, hband⟩ :=
    m4_hband_at_door_slot_hoisted_gk K hMmu s13Aexp s13Aexp_pos M hM
  exact ⟨C', x₀, hC'pos, fun hgate => hband R C₁ (s13BandM0 R ρ C₁)
    (doorBandBase_family_gk K hM harith hgate)⟩

/-! ## §6 — ⟦ERR-REPAIR⟧ THE SHARP ARM AT THE WINDOW TOP, AND `err` FOR FREE

PURELY ADDITIVE: §5's `S13BandGate_gk K` and `doorBandBase_family_gk K` are untouched; this section
builds a PARALLEL gate with one fewer line.

⟦WHY⟧ `S13BandGate_gk K.err_res` is a NUMERAL line (`14·λ₊ + … ≤ 347900`), obtained by spending
the arm's floor `Λ ≥ 356600` and throwing the rest of `loglog X_d` away.  Read as a cap on
the window top it says `λ₊ ≤ 24849`; the refuter's kernel probe (`ERR-REF`, flags 2026-07-30
23:38) then showed that against WIDTH-SCOPE's forced tower `λ₊ ≥ λ₋³ ≥ 125000` the whole
selection register is EMPTY at every regime the spine can build.  No numeral can repair it:
`λ₊` has no upper bound on the register.  The line is DELETED here, not re-numeraled.

⟦THE ROUTE⟧ the compose pins `R.x` by its own `g`-arm read AT THE WINDOW TOP `H₊` — not at
the per-base `H` that `DoorArithFrameRho.arm` records — and `SocketBase`'s x-scale field caps
`R.x` by `16·ω·arcDen 12 H·A` at that base's `H ≤ H₊`.  `arcDen 12` is monotone in `H`, so
the `H₊`-form of the arm survives at EVERY base (`s13_band_arm_at_top`), and the residue line
closes on its CONSTANT term alone: `0.9757·(7000λ₊ + 500·log(1/ρ) + 6600)` beats
`14λ₊ + 2log(C₁+1) + log(1/ρ) + 15` with `6439.62` against `17` before a single `λ₊` is
spent.  The `err` leg therefore carries NO width law at all — it is priced against the OUTER
scale `x`, where ⟦B4⟧'s crossing bound is a `λ₊`-`λ₋` law through `M`.

Constants `7000 / 500 / 6600 / 0.9757` are unchanged, and `DoorArithFrameRho` is not read
differently: the arm at `H₊` is derived directly from `m4_arith_arm_of_gArmRho`, the frame's
own supplier lemma, at the socket's own antecedent. -/

/-- `S13BandGate' (:725)` at the lever. -/
structure S13BandGate'_gk (K : ℕ) (R : ChowlaRegime) (M x₀ : ℕ) (C' : ℝ) (C₁ : ℕ → ℝ) : Prop where
  /-- ⟦1⟧ the opaque threshold, floored at the socket's own `j`-floor. -/
  x0_le : x₀ ≤ 2 ^ doorRowFloor M
  /-- ⟦2⟧ the band constant's normalisation (free at `C₁ ≡ 1`). -/
  C1_one : ∀ n : ℕ, (1 : ℝ) ≤ C₁ n
  /-- ⟦3⟧ the grade fit, at the `M`-only floor `log 2 · doorRowFloor M`. -/
  grade : 8 * C' ≤ (Real.log 2 * ((doorRowFloor M : ℕ) : ℝ))
    ^ (s13Aexp + (-(1 : ℝ) / 2 + 1 / 1000))
  /-- ⟦4⟧ ⟦F3⟧ the block-scale floor at every socket base. -/
  block : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s → s13BlockFloor_gk K M ≤ A + s

/-- `doorBandBase_family' (:745)` at the lever. -/
theorem doorBandBase_family'_gk (K : ℕ) {R : ChowlaRegime} {M x₀ : ℕ} {C' Kar ρ : ℝ} {C₁ : ℕ → ℝ}
    (hM : 1 ≤ M) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hC1hi : ∀ n : ℕ, C₁ n ≤ 1)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho 0 0 (R.ω : ℝ) ρ R.Hhi ≤ (R.x : ℝ))
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s))
        (s13BandM0 R ρ C₁ (A + s)) Kar ρ)
    (hgate : S13BandGate'_gk K R M x₀ C' C₁) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorBandBase_gk K x₀ C' s13Aexp M (A + s) q (C₁ (A + s)) (s13BandM0 R ρ C₁ (A + s)) := by
  intro H L q j A s hb
  have hfr := harith H L q j A s hb
  -- ⟦the arm's two consequences⟧
  have hΛ : (356600 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := hfr.loglogX_ge
  have hμ : (0 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := lt_trans (by norm_num) hfr.one_lt_logX
  obtain ⟨hbig, h48, h24⟩ := s13_band_floors hμ hΛ
  have hΛ0 : (0 : ℝ) ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by linarith
  have hX2 : (2 : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := by linarith
  -- ⟦the row-zero bundle at this base — the block-floor line⟧
  have hjfl : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have hfive := s13_doorRowZeroBase_five_gk K hM (hgate.block H L q j A s hb) hjfl
  have hreg : Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log (((A + s : ℕ)) : ℝ)) := hfive.2.1
  refine
    { X400 := s13_band_X400 hM hb
      C₁_one := hgate.C1_one (A + s)
      x₀_le := ?_
      qfit := ?_
      gHalf := ?_
      gO1 := ?_
      gWin := ?_
      grade := ?_
      err := ?_ }
  · -- ⟦`x₀_le`⟧ the gate line, transported by `2^{doorRowFloor M} ≤ 2^j ≤ A`
    have hAj : 2 ^ j ≤ A := hb.2.2.2.2.2.2.2.2.1
    have hpow : (2 : ℕ) ^ doorRowFloor M ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hjfl
    exact le_trans hgate.x0_le (le_trans hpow (le_trans hAj (Nat.le_add_right A s)))
  · -- ⟦`qfit`⟧ off the ARM
    refine s13_band_qfit hb.2.2.2.2.1 (lt_trans (by norm_num) hfr.one_lt_logH) hμ ?_ ?_
    · linarith [hfr.Hfloor]
    · have := hfr.armWeak
      have := hfr.logInvRho_nonneg
      linarith
  · -- ⟦`gHalf`⟧
    intro k hk1 hk2
    have h := s13_band_gHalf hX2 h48 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gO1`⟧
    intro k hk1 hk2
    have hQ0 : (0 : ℝ) ≤ Real.log ((calQK (Adoor M) (s13GK K M) M 2 : ℕ) : ℝ) := by
      linarith [s13_band_log_calQK_two_ge_gk K M hM]
    have h := s13_band_gO1 hX2 hQ0 hreg h24 k hk1 hk2
    simp only [s13Aexp]
    linarith
  · -- ⟦`gWin`⟧
    intro k hk1 hk2
    have h := s13_band_gWin (by linarith) hX2 (s13_band_loglog_calP_one_gk K M)
      (s13_band_log_calQK_two_ge_gk K M hM) hreg k hk1 hk2
    simpa only [s13Aexp] using h
  · -- ⟦`grade`⟧ the gate line, transported by the base-floor bridge
    refine le_trans hgate.grade ?_
    refine Real.rpow_le_rpow (by positivity) (s13_band_baseFloor hb) ?_
    rw [s13Aexp]; norm_num
  · -- ⟦`err`⟧ THE ARM AT THE TOP — no `λ₊` cap anywhere
    exact s13_band_err_free hρ0 hρ1 (hgate.C1_one (A + s)) (hC1hi (A + s)) hHreg hg hb


end Salt.MR

end
