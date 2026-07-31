/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S12FuseCompose
import Salt.MR.S13BandBase
import Salt.MR.S13MSelect2
import Salt.MR.M4AssemblyFrames

/-!
# ⟦S14-COMPOSE⟧ — THE FINAL COMPOSE, AND WHERE IT STOPS

PURELY ADDITIVE: no landed declaration is touched anywhere in this file.

This file was opened to fire `S12FuseCompose.logChowla2_capstone_final_rawcap'` at a working
point and land the witnessed-scale theorem.  It does not.  §3 is a kernel proof that the
compose road's ⟦B1'-3⟧ binder — `GRowsZeroGate''' M (A+s) Cp (decayPool (A+s))` at every
socket base — is **FALSE at every `M` and every regime the road reaches**, and §4 exhibits the
socket base at which it fails.  What is landed here is therefore the STOP, with the exact
frontier, plus the target statement (§5) written down and named.

## ⟦THE COMPOSE LEDGER⟧ — the instantiation table as designed, and its fate

The maestro's table (dispatch of 2026-07-30) instantiated the twin
(`S12FuseCompose.lean:530`) as follows; the right column is the state at the STOP.

| slot | choice | source | fate |
|---|---|---|---|
| `Aexp` | `s13Aexp = 3` | `S13BandBase.lean:71` (⟦F1⟧) | fixed, unused below the stop |
| `Cp` | `0` (the twin binds `0 ≤ Cp`) | — | kills `GRowsZeroGate'''.dens` |
| `C₁` | `fun _ => 1` | ⟦F2⟧'s `C1_one` free | fine |
| `M₀` | `s13BandM0 R ρ C₁` | `S13BandBase.lean:86` | ⟦F2⟧'s fence; `s13BandM0_window` |
| `epsf` | inert | — | fine |
| `epsrf` | `0` | ruling 7 (⟦B2⟧ holds at `0`) | fine |
| `Kf` | `0` | `DoorArithFrameRho.Knonneg` | fine |
| `k` | `doorCount R.ω` | `s13_doorGates_of_MSelect'` | fine |
| `ρ` | `doorRhoOfDelta (s12DeltaSock δ₀ K)` | the twin's own | fine |
| `U1floor` | `≥ Hcap` (the pin) | `HloExportMR.lean:187` | fine |
| `g` | `max` of `s13GArm' δ₀`, `gArmDoorRho`, `gArmEge` | `M4AssemblyFrames.lean:529` | fine |
| `M` | the ceiling of the floors read after `R` | ⟦EDGE 8⟧ | **REFUTED** — §3 |

⟦THE `M`-SELECTION SYSTEM IS EMPTY⟧ the `M`-floors were to be absorbed after `R`; but the
road also carries `M`-UPPERS, and §3 shows the two families do not merely fail to separate —
one single pool slot contradicts the socket at EVERY `M`:

* `MSelect'.winFit` (`S13MSelect2.lean:370`), the true window gate that supplies ⟦A5⟧, forces
  `(7/10)·doorRowFloor M ≤ log H₋`, i.e. `2^{doorRowFloor M} ≤ R.Hlo` (`e^{0.7} > 2`);
* so the socket family at `(R, M)` is INHABITED (§4's certificate, at the explicit tuple);
* at any socket base `SocketBase`'s x-scale field and the regime's `hPHheadroom` give
  `loglog X_d ≥ ½·log H` (`S13MSelect2.s13_socketBase_loglogA_sharp`, landed), while the
  socket's own `j`-floor gives `log H ≥ log 2 · doorRowFloor M`;
* `GRowsZeroGate'''.p2` reads `138240/𝒫₁ ≤ ¼·(log X_d)^{−θ₂₉₃}`, i.e.
  `log 552960 + θ₂₉₃·loglog X_d ≤ Adoor M·log 2` — an UPPER cap on `loglog X_d` linear in
  `Adoor M`.

Two readings of that cap collide.  Reading it against the `j`-floor gives
`θ₂₉₃·½·log 2·M·Adoor M ≤ Adoor M·log 2`, i.e. **`M ≤ 2/θ₂₉₃ = 586`**.  Reading it against
the capstone's own absorbed `loglogFloor50` (`log H ≥ e^{50} ≥ 10^{21}`) gives
`Adoor M ≥ 10^{12}`, i.e. `Nat.log 2 M + 1 ≥ 15`, i.e. `M ≥ 2^{14}`.  `586 < 2^{14}`.

This is `Salt/MR/All.lean`'s banked ⚠ ⟦THE `X_d`-SCALE COLLISION, flagged not closed⟧ (the
`S13-A` block), at the DECAY pool and in closed form: it is not an unmet numeral that a larger
`M` would meet — it is a refutation, uniform in `M`, and it needs no opaque constant
(`Cp`, `Ct`, `Cg`, `δ₀`, `x₀`, `C'` all drop out of the `p²` slot).

## ⟦THE OTHER SURVIVORS, NAMED⟧ (not reached, recorded for the frontier)

* ⟦B5 `grade`⟧ `S13BandGate.grade` asks `8·C' ≤ (log 2 · doorRowFloor M)^{5/2+1/1000}`, and in
  every landed export (`LambdaChiMask.MlamGrChiMask_rate_split` → … →
  `S11Hoist.m4_hband_at_door_slot_split`) the band constant `C'` is quantified AFTER `M`
  (`C' = C·4^{Aexp}·windowMassConst 𝒫₁ 𝒬₂ + 1`, `M`-reading through the window).  So the gate
  line cannot be absorbed into an `M`-floor: `M` is chosen before `C'` is revealed.  Closing
  it needs one new split-hoist link exposing `C` (the `Aexp`-only constant) before the mass —
  the same move `MlamGrChiMask_rate_split` made for `x₀`, one level lower.  INDEPENDENT of §3.
* ⟦B4 raw⟧ the crossing bound at `εr = 0` is carried; `M4AssemblyFrames` §9's ledger calls it
  "spine-witnessed; carried" and no landed theorem discharges it.
* ⟦B5 `x0_le`⟧ absorbable (`x₀` is in the twin's top block, before `M`).
* the four ⟦M-SIDE NUMERALS⟧ of `M4AssemblyFrames` §3/§4 at `X_d = 3·R.x`: `dens` is free at
  `Cp := 0`; `p2` is §3's refuted slot; `gP1` and `level1` are the same genre with the opaque
  `Ct` / `a2Level1 M` in them.

## Contents

* §1 the socket-side scale lemmas (`s14_two_pow_j_le_H`, `s14_logH_ge_of_socket`,
  `s14_loglogX_ge_of_socket`);
* §2 the `p²` slot in logs (`s14_p2_in_logs`);
* §3 ⟦THE KILL⟧ `s14_gRows_kill`, `s14_socket_empty_of_gRows`;
* §4 ⟦THE INHABITATION CERTIFICATE⟧ `s14_socketBase_witness`, the window floor
  `s14_window_floor_of_winFit`, and the STOP `s14_compose_stops_of_MSelect'`;
* §5 the target statement `LogChowla2WitnessedScale` — NAMED, NOT DERIVED.
-/

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §1 — THE SOCKET-SIDE SCALE

Three readings of `SocketBase`, all landed-fact only: the window index sits under the width,
the door's `j`-floor is a `log H` floor, and the base's `loglog` is half the width's `log`. -/

/-- **⟦THE WINDOW INDEX UNDER THE WIDTH⟧** (`s14_two_pow_j_le_H`) — `2^j ≤ H` at every socket
base, from `j ≤ log₂ L`, `L ≤ H` (and the regime's own `H`-floor at `L = 0`). -/
theorem s14_two_pow_j_le_H {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) : (2 : ℕ) ^ j ≤ H := by
  obtain ⟨hlo, hhi, hLH, hqp, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  have hH : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    rw [Nat.log_zero_right] at hjL
    have hj : j = 0 := by omega
    subst hj
    simpa using (by omega : 1 ≤ H)
  · have h1 : (2 : ℕ) ^ j ≤ 2 ^ (Nat.log 2 L) := Nat.pow_le_pow_right (by norm_num) hjL
    have h2 : (2 : ℕ) ^ (Nat.log 2 L) ≤ L := Nat.pow_log_le_self 2 (by omega)
    omega

/-- **⟦THE DOOR'S `j`-FLOOR, IN LOGS⟧** (`s14_logH_ge_of_socket`) — `log 2 · doorRowFloor M ≤
log H`.  No tower is formed: `2^{doorRowFloor M}` stays inside `Real.log_pow`. -/
theorem s14_logH_ge_of_socket {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) :
    Real.log 2 * ((doorRowFloor M : ℕ) : ℝ) ≤ Real.log (H : ℝ) := by
  have hjfl : doorRowFloor M ≤ j := hb.2.2.2.2.2.2.1
  have h2j := s14_two_pow_j_le_H hb
  have hpow : (2 : ℕ) ^ doorRowFloor M ≤ H :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hjfl) h2j
  have hR : ((2 : ℝ)) ^ (doorRowFloor M) ≤ (H : ℝ) := by
    have h : ((2 ^ doorRowFloor M : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hpow
    simpa using h
  have h0 : (0 : ℝ) < ((2 : ℝ)) ^ (doorRowFloor M) := by positivity
  have h := Real.log_le_log h0 hR
  rw [Real.log_pow] at h
  linarith

/-- **⟦THE BASE'S `loglog`, AT THE WIRE'S `X_d`⟧** (`s14_loglogX_ge_of_socket`) —
`½·log H ≤ loglog (A+s)`.  `S13MSelect2.s13_socketBase_loglogA_sharp` (the ⟦D2⟧ correction's
x-scale figure) transported from `A` to the wire's base `X_d = A + s`. -/
theorem s14_loglogX_ge_of_socket {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) :
    Real.log (H : ℝ) / 2 ≤ Real.log (Real.log (((A + s : ℕ)) : ℝ)) := by
  have hsharp := s13_socketBase_loglogA_sharp hfl hb
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hmono : Real.log (A : ℝ) ≤ Real.log (((A + s : ℕ)) : ℝ) := Real.log_le_log hA0 hAX
  have h := Real.log_le_log (by linarith : (0 : ℝ) < Real.log (A : ℝ)) hmono
  linarith

/-! ## §2 — THE `p²` SLOT IN LOGS

`GRowsZeroGate'''.p2` at the decay pool is `138240·(1/𝒫₁ + 1/𝒫₂) ≤ ¼·(log X_d)^{−θ₂₉₃}`.
Dropping the (positive) `𝒫₂` summand and taking logs turns it into ONE linear inequality —
an UPPER cap on `loglog X_d`, with the pool's exponent as the coefficient and `log 𝒫₁ =
Adoor M · log 2` (`S13BandBase.s13_band_log_calP_one`) on the right.  No constant of the
compose survives the step: `Cp` never enters `p2`. -/

/-- **⟦THE `p²` CAP, IN LOGS⟧** (`s14_p2_in_logs`) —
`log 552960 + θ₂₉₃·loglog X_d ≤ Adoor M · log 2`. -/
theorem s14_p2_in_logs {M Xd : ℕ} {Cp : ℝ} (hX1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hg : GRowsZeroGate''' M Xd Cp (decayPool Xd)) :
    Real.log 552960 + theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))
      ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  have hp2 := hg.p2
  have hP1pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (3072 * M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hP2pos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (3072 * M) 2 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hpool : decayPool Xd
      = Real.exp (-(theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))) := by
    rw [decayPool_def, Real.rpow_def_of_pos hL0]; ring_nf
  have hstep : 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      ≤ 1 / 4 * decayPool Xd := by
    have hpos : (0 : ℝ) < 1 / ((calP (Adoor M) (3072 * M) 2 : ℕ) : ℝ) :=
      one_div_pos.mpr hP2pos
    linarith
  rw [hpool] at hstep
  have hE : (0 : ℝ) < Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))) :=
    Real.exp_pos _
  have hrw1 : 138240 * (1 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ))
      = 138240 / ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by ring
  have hrw2 : (1 : ℝ) / 4 * (Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))))⁻¹
      = 1 / (4 * Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))) := by
    field_simp
  rw [Real.exp_neg, hrw1, hrw2, div_le_div_iff₀ hP1pos (by positivity)] at hstep
  have hkey : 552960 * Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))
      ≤ ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by linarith
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
    s13_band_log_calP_one M] at hlog
  linarith

/-! ## §3 — ⟦THE KILL⟧

The `p²` cap, read twice against the same socket base, contradicts itself.

* AGAINST THE `j`-FLOOR (§1): `loglog X_d ≥ ½·log 2·M·Adoor M`, so the cap forces
  `θ₂₉₃·½·log 2·M·Adoor M ≤ Adoor M·log 2`, i.e. `M ≤ 2/θ₂₉₃ ≤ 589` — hence
  `Nat.log 2 M ≤ 9` and `Adoor M ≤ 2^{36}·10 = 6.872·10^{11}`.
* AGAINST `loglogFloor50` (the capstone's own absorbed floor): `log H ≥ e^{50} ≥ 10^{21}`, so
  `loglog X_d ≥ ½·10^{21}` and the cap forces `Adoor M ≥ 10^{12}`.

`6.872·10^{11} < 10^{12}`.  The margin is deliberately coarse: the true figures are
`Adoor M ≥ 1.27·10^{19}` against `Adoor M ≤ 6.87·10^{11}`, seven orders. -/

/-- `10^{21} ≤ exp 50` (true value `5.18·10^{21}`), via `2.7^{50} ≥ 10^{21}`. -/
theorem s14_exp50_ge : (10 : ℝ) ^ 21 ≤ Real.exp 50 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h50 : Real.exp 50 = (Real.exp 1) ^ (50 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (50 : ℕ) ≤ (Real.exp 1) ^ (50 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1.le 50
  have hn : (10 : ℝ) ^ 21 ≤ (2.7 : ℝ) ^ (50 : ℕ) := by norm_num
  rw [h50]; linarith

/-- **⟦THE KILL⟧** (`s14_gRows_kill`) — at any regime carrying the capstone's absorbed
`loglogFloor50` floor, `GRowsZeroGate''' M X_d Cp (decayPool X_d)` is FALSE at every socket
base, for every `M` and every `Cp`.

This is the compose road's ⟦B1'-3⟧ binder (`S12FuseCompose.lean:560`), refuted.  Nothing
opaque enters: the `p²` slot carries only numerals and `𝒫₁`. -/
theorem s14_gRows_kill {R : ChowlaRegime} {M H L q j A s : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hg : GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) : False := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogHpos : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have h := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogHpos] at h
  have hlogHbig : (10 : ℝ) ^ 21 ≤ Real.log (H : ℝ) := le_trans s14_exp50_ge hexp50
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hp2 := s14_p2_in_logs hX1 hg
  have hll := s14_loglogX_ge_of_socket hfl hb
  have hlogHj := s14_logH_ge_of_socket hb
  have hθ : (0.0034 : ℝ) ≤ theta293 := by have := s13_theta293_margin_lo; linarith
  have hlog552960 : (0 : ℝ) ≤ Real.log 552960 := Real.log_nonneg (by norm_num)
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hAd1 : 1 ≤ Adoor M := one_le_Adoor M
  have hAd0 : (0 : ℝ) < ((Adoor M : ℕ) : ℝ) := by exact_mod_cast hAd1
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hdr : ((doorRowFloor M : ℕ) : ℝ) = (M : ℝ) * ((Adoor M : ℕ) : ℝ) := by
    rw [doorRowFloor]; push_cast; ring
  -- ⟦reading 2⟧ the `e^{50}` floor forces `Adoor M ≥ 10^{12}`
  have hAbig : (10 : ℝ) ^ 12 ≤ ((Adoor M : ℕ) : ℝ) := by
    nlinarith [hp2, hll, hlogHbig, hθ, hlog552960, hlog2hi, hlog2lo, hAd0]
  -- ⟦reading 1⟧ the `j`-floor caps `M`
  have hMle : (M : ℝ) ≤ 589 := by
    nlinarith [hp2, hll, hlogHj, hθ, hlog552960, hlog2lo, hAd0, hM0, hdr]
  have hMn : M ≤ 589 := by exact_mod_cast hMle
  have hlogM : Nat.log 2 M ≤ 9 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h]
    · have hlt : M < 2 ^ 10 := by norm_num; omega
      have := Nat.log_lt_of_lt_pow (by omega : M ≠ 0) hlt
      omega
  have hAdle : Adoor M ≤ 687194767360 := by
    have h : Adoor M ≤ 2 ^ 36 * 10 := by
      rw [Adoor]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hAdleR : ((Adoor M : ℕ) : ℝ) ≤ 687194767360 := by exact_mod_cast hAdle
  norm_num at hAbig
  linarith

/-- **⟦THE DICHOTOMY⟧** (`s14_socket_empty_of_gRows`) — the family form: if the compose's
⟦B1'-3⟧ binder holds at `(R, M)` then the socket family at `(R, M)` is EMPTY.

So the twin `logChowla2_capstone_final_rawcap'` can only ever be fired where no socket base
exists — and then EVERY socket-family residue item of it (⟦B1'⟧'s five, ⟦B2⟧, ⟦B3⟧, ⟦B4⟧,
⟦B5⟧, ⟦B6⟧) is vacuously true.  §4 closes that escape. -/
theorem s14_socket_empty_of_gRows {R : ChowlaRegime} {M : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hg : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) :
    ∀ H L q j A s : ℕ, ¬ SocketBase R M H L q j A s :=
  fun H L q j A s hb => s14_gRows_kill hfl hb (hg H L q j A s hb)

/-! ## §4 — ⟦THE INHABITATION CERTIFICATE⟧ AND THE STOP

The summit checklist's sharpest line: exhibit a tuple at which `SocketBase R M H L q j A s`
holds, at the compose's own `(R, M)`.  §4 does, under the ONE side condition
`2^{doorRowFloor M} ≤ R.Hhi` — and then shows that condition is FORCED by the very gate that
supplies the twin's ⟦A5⟧ slot, so the vacuity escape of §3's dichotomy is closed. -/

/-- **⟦THE SOCKET BASE, EXHIBITED⟧** (`s14_socketBase_witness`) — at the tuple

  `H = L = R.Hhi`,  `q = 1`,  `j = doorRowFloor M`,  `A = 2·R.x`,  `s = 0`,

`SocketBase R M H L q j A s` holds as soon as the door's own row floor fits under the window's
top, `2^{doorRowFloor M} ≤ R.Hhi`.  Every other field is a regime field: `hHlohi`, `hheadroom`
(`H₊ ≤ x/ω`), `hx`, `hω`, and `1 ≤ arcDen 12 H` at the regime's `H`-floor. -/
theorem s14_socketBase_witness {R : ChowlaRegime} {M : ℕ}
    (hw : 2 ^ doorRowFloor M ≤ R.Hhi) :
    SocketBase R M R.Hhi R.Hhi 1 (doorRowFloor M) (2 * R.x) 0 := by
  have hHhi0 : 0 < R.Hhi := lt_of_lt_of_le (by omega) (le_trans R.hHlo_floor R.hHlohi)
  have hx2 : 2 ≤ R.x := R.hx
  have hω2 : 2 ≤ R.ω := R.hω
  have hHx : R.Hhi ≤ R.x := le_trans R.hheadroom (Nat.div_le_self _ _)
  have harc : (1 : ℝ) ≤ arcDen 12 R.Hhi := one_le_arcDen_of_regime (R := R) R.hHlohi
  have hxR : (2 : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast hx2
  have hωR : (2 : ℝ) ≤ (R.ω : ℝ) := by exact_mod_cast hω2
  have hHR : (0 : ℝ) ≤ (R.Hhi : ℝ) := Nat.cast_nonneg _
  have hHxR : (R.Hhi : ℝ) ≤ (R.x : ℝ) := by exact_mod_cast hHx
  refine ⟨R.hHlohi, le_rfl, le_rfl, by norm_num, ?_, ?_, le_rfl, by omega, ?_, ?_, ?_, ?_,
    by omega⟩
  · simpa using harc
  · exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr hw
  · omega
  · have h : Real.sqrt (R.Hhi : ℝ) ≤ Real.sqrt (((2 * R.x : ℕ) : ℝ) ^ 2) := by
      refine Real.sqrt_le_sqrt ?_
      push_cast
      nlinarith
    rwa [Real.sqrt_sq (by positivity)] at h
  · have hx0 : (0 : ℝ) < (R.x : ℝ) := by linarith
    have hprod : (2 : ℝ) ≤ (R.ω : ℝ) * arcDen 12 R.Hhi := by nlinarith [harc, hωR]
    have hstep := mul_le_mul_of_nonneg_right hprod hx0.le
    push_cast
    nlinarith [hstep, hx0]
  · push_cast
    linarith

/-- **⟦THE WINDOW FLOOR⟧** (`s14_window_floor_of_winFit`) — `MSelect'.winFit` read at the
window's lower endpoint forces `2^{doorRowFloor M} ≤ R.Hlo`.

The gate is `(7/10)·doorRowFloor M + 3·G ≤ log H` with
`G = log 9 + 84·loglog H + 2·log(strataResidual H) − log ρ`, and every summand of `G` is
nonnegative at `0 < ρ ≤ 1` and the regime's own `H`-floor.  So `log H ≥ 0.7·doorRowFloor M`,
and `e^{0.7} = 2.0138 > 2`. -/
theorem s14_window_floor_of_winFit {R : ChowlaRegime} {M : ℕ} {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hwf : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
        + 3 * (Real.log 9 + 84 * Real.log (Real.log ((R.Hlo : ℕ) : ℝ))
            + 2 * Real.log (strataResidual R.Hlo) - Real.log ρ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ)) :
    2 ^ doorRowFloor M ≤ R.Hlo := by
  have hH4 : 4000000 ≤ R.Hlo := R.hHlo_floor
  have hH0 : (0 : ℝ) < (R.Hlo : ℝ) := by
    have : (0 : ℕ) < R.Hlo := by omega
    exact_mod_cast this
  have hLexp : Real.exp 1 ≤ Real.log ((R.Hlo : ℕ) : ℝ) :=
    exp_one_le_log_of_regime_le R le_rfl
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hL1 : (1 : ℝ) < Real.log ((R.Hlo : ℕ) : ℝ) := by linarith
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log ((R.Hlo : ℕ) : ℝ)) :=
    Real.log_nonneg (by linarith)
  have harc : (1 : ℝ) ≤ arcDen 12 R.Hlo := one_le_arcDen_of_regime (R := R) le_rfl
  have hSR : (1 : ℝ) ≤ strataResidual R.Hlo := by
    have h : (0 : ℝ) ≤ Real.log (arcDen 12 R.Hlo) := Real.log_nonneg harc
    rw [strataResidual]; linarith
  have hlogSR : (0 : ℝ) ≤ Real.log (strataResidual R.Hlo) := Real.log_nonneg hSR
  have hlog9 : (0 : ℝ) ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  have hfloor : (7 / 10 : ℝ) * ((doorRowFloor M : ℕ) : ℝ)
      ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hj0 : (0 : ℝ) ≤ ((doorRowFloor M : ℕ) : ℝ) := Nat.cast_nonneg _
  have hkey : Real.log 2 * ((doorRowFloor M : ℕ) : ℝ) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
    nlinarith [hfloor, hlog2, hj0]
  have hpow : ((2 : ℝ)) ^ (doorRowFloor M) ≤ ((R.Hlo : ℕ) : ℝ) := by
    have h : Real.log (((2 : ℝ)) ^ (doorRowFloor M)) ≤ Real.log ((R.Hlo : ℕ) : ℝ) := by
      rw [Real.log_pow]; linarith
    have h2 : (0 : ℝ) < ((2 : ℝ)) ^ (doorRowFloor M) := by positivity
    exact (Real.log_le_log_iff h2 hH0).mp h
  have hcast : ((2 ^ doorRowFloor M : ℕ) : ℝ) ≤ ((R.Hlo : ℕ) : ℝ) := by
    push_cast; exact hpow
  exact_mod_cast hcast

/-- **⟦THE STOP⟧** (`s14_compose_stops_of_MSelect'`) — the `M`-selection system `MSelect'`
(which supplies the twin's ⟦A1⟧–⟦A5⟧ group) and the twin's ⟦B1'-3⟧ binder are JOINTLY
UNSATISFIABLE, at every `(R, M)` the road reaches.

Read as the compose's obituary: `winFit` puts the whole regime window above the door's own row
floor, that inhabits the socket family (§4's certificate), and §3 refutes the row gate at any
inhabited base.  No choice of `M`, `Cp`, `C₁`, `M₀`, `epsrf`, `Kf`, `k`, `g`, `U1floor` — and
no value of the opaque `Cg`, `δ₀`, `Ct`, `x₀`, `C'` — changes it. -/
theorem s14_compose_stops_of_MSelect' {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hS : MSelect' Cg δ₀ Λ ρ R M)
    (hg : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) :
    False := by
  have hwin : 2 ^ doorRowFloor M ≤ R.Hlo :=
    s14_window_floor_of_winFit hρ0 hρ1 (hS.winFit R.Hlo le_rfl R.hHlohi)
  exact s14_socket_empty_of_gRows hfl hg _ _ _ _ _ _
    (s14_socketBase_witness (le_trans hwin R.hHlohi))

/-- **⟦THE DICHOTOMY, SHARPENED⟧** (`s14_rawcap_forces_empty_window`) — firing the twin's
⟦B1'-3⟧ binder at `(R, M)` forces the regime's ENTIRE window to sit strictly below the door's
own row floor, `R.Hhi < 2^{doorRowFloor M}`.

That is the only shape in which the compose road can be entered, and it is exactly the shape
in which every socket-family residue item of the twin is vacuous — the door assembly would
then be composed over an empty family.  The window gate (`s14_window_floor_of_winFit`) puts
`R.Hlo` ABOVE that floor, so the shape is unreachable on the corpus's own ⟦A5⟧ route. -/
theorem s14_rawcap_forces_empty_window {R : ChowlaRegime} {M : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hg : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate''' M (A + s) Cp (decayPool (A + s))) :
    R.Hhi < 2 ^ doorRowFloor M := by
  by_contra hcon
  exact s14_socket_empty_of_gRows hfl hg _ _ _ _ _ _
    (s14_socketBase_witness (by omega))

/-! ## §5 — THE TARGET, NAMED

HEAD-SCOUT's drafted statement (`docs/blueprints/flags.md`, 2026-07-30 20:25, ⟦E0⟧), written
here so the campaign owns the shape in the kernel.  **THE FINAL NAME IS THE CAPTAIN'S** — the
working name below is a placeholder, and the fences HEAD-SCOUT recorded stand: `ε` is OPAQUE
(not universal), `x` is LOWER-bounded only, and the content is fixed-factor cancellation at
the witnessed scale, not a `∀ε` statement.

⚠ **NOT DERIVED.**  The road that was to derive it — `logChowla2_capstone_final_rawcap'` at the
decay pool — is refuted at ⟦B1'-3⟧ by §3.  It is stated, not proved, and nothing in this file
weakens it. -/

/-- **⟦THE WITNESSED-SCALE STATEMENT⟧** (`LogChowla2WitnessedScale`, working name) — the
log-averaged two-point Chowla bound at a witnessed scale:

  there is a fixed `ε > 0` such that for every floor `U1floor` and every register arm `g`
  there is a regime `R` above that floor, with `x` past the arm, at which
  `logChowla2Fails R.eps R.x R.ω` FAILS.

`R.ω` carries `2 ≤ R.ω ≤ R.x` and `R.Hlo ≥ U1floor` from `ChowlaRegime`'s own fields, so the
`∃ R` payload is exactly the ⟦E0⟧ draft's `(x, ω, floors)` data. -/
def LogChowla2WitnessedScale : Prop :=
  ∃ ε : ℚ, 0 < ε ∧ ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
    ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
      ¬ logChowla2Fails R.eps R.x R.ω

/-- The last mile, written out: the twin's conclusion IS the target's payload, so a fired
capstone at ONE `ε` gives the statement.  (The hypothesis is what §3 refutes on the decay
road; the bridge is recorded so a repaired road has nothing left to invent.) -/
theorem logChowla2_witnessed_scale_of_fired
    (h : ∃ ε : ℚ, 0 < ε ∧ ∀ (U1floor : ℕ) (g : ℕ → ℕ → ℕ),
      ∃ R : ChowlaRegime, R.eps = ε ∧ U1floor ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
        ¬ logChowla2Fails R.eps R.x R.ω) :
    LogChowla2WitnessedScale := h

/-! ## §GK — the G-lever twin -/

/-- `s14_p2_in_logs (:166)` at the lever. `𝒫₁` is LEVEL 1, so the numeral does not move. -/
theorem s14_p2_in_logs_gk (K : ℕ) {M Xd : ℕ} {Cp : ℝ} (hX1 : (1 : ℝ) < Real.log ((Xd : ℕ) : ℝ))
    (hg : GRowsZeroGate'''_gk K M Xd Cp (decayPool Xd)) :
    Real.log 552960 + theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))
      ≤ ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
  have hp2 := hg.p2
  have hP1pos : (0 : ℝ) < ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (s13GK K M) 1 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hP2pos : (0 : ℝ) < ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) := by
    have h : 0 < calP (Adoor M) (s13GK K M) 2 := by rw [calP]; exact Nat.two_pow_pos _
    exact_mod_cast h
  have hL0 : (0 : ℝ) < Real.log ((Xd : ℕ) : ℝ) := by linarith
  have hpool : decayPool Xd
      = Real.exp (-(theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))) := by
    rw [decayPool_def, Real.rpow_def_of_pos hL0]; ring_nf
  have hstep : 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      ≤ 1 / 4 * decayPool Xd := by
    have hpos : (0 : ℝ) < 1 / ((calP (Adoor M) (s13GK K M) 2 : ℕ) : ℝ) :=
      one_div_pos.mpr hP2pos
    linarith
  rw [hpool] at hstep
  have hE : (0 : ℝ) < Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))) :=
    Real.exp_pos _
  have hrw1 : 138240 * (1 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ))
      = 138240 / ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by ring
  have hrw2 : (1 : ℝ) / 4 * (Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ))))⁻¹
      = 1 / (4 * Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))) := by
    field_simp
  rw [Real.exp_neg, hrw1, hrw2, div_le_div_iff₀ hP1pos (by positivity)] at hstep
  have hkey : 552960 * Real.exp (theta293 * Real.log (Real.log ((Xd : ℕ) : ℝ)))
      ≤ ((calP (Adoor M) (s13GK K M) 1 : ℕ) : ℝ) := by linarith
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
    s13_band_log_calP_one_gk K M] at hlog
  linarith

/-! ## §3 — ⟦THE KILL⟧

The `p²` cap, read twice against the same socket base, contradicts itself.

* AGAINST THE `j`-FLOOR (§1): `loglog X_d ≥ ½·log 2·M·Adoor M`, so the cap forces
  `θ₂₉₃·½·log 2·M·Adoor M ≤ Adoor M·log 2`, i.e. `M ≤ 2/θ₂₉₃ ≤ 589` — hence
  `Nat.log 2 M ≤ 9` and `Adoor M ≤ 2^{36}·10 = 6.872·10^{11}`.
* AGAINST `loglogFloor50` (the capstone's own absorbed floor): `log H ≥ e^{50} ≥ 10^{21}`, so
  `loglog X_d ≥ ½·10^{21}` and the cap forces `Adoor M ≥ 10^{12}`.

`6.872·10^{11} < 10^{12}`.  The margin is deliberately coarse: the true figures are
`Adoor M ≥ 1.27·10^{19}` against `Adoor M ≤ 6.87·10^{11}`, seven orders. -/

/-- `s14_gRows_kill (:230)` at the lever. -/
theorem s14_gRows_kill_gk (K : ℕ) {R : ChowlaRegime} {M H L q j A s : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s)
    (hg : GRowsZeroGate'''_gk K M (A + s) Cp (decayPool (A + s))) : False := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogHpos : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have h := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogHpos] at h
  have hlogHbig : (10 : ℝ) ^ 21 ≤ Real.log (H : ℝ) := le_trans s14_exp50_ge hexp50
  obtain ⟨h2000, -⟩ := s13_socketBase_loglogA hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hAX : (A : ℝ) ≤ (((A + s : ℕ)) : ℝ) := by
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]
  have hX1 : (1 : ℝ) < Real.log (((A + s : ℕ)) : ℝ) := by
    have := Real.log_le_log hA0 hAX; linarith
  have hp2 := s14_p2_in_logs_gk K hX1 hg
  have hll := s14_loglogX_ge_of_socket hfl hb
  have hlogHj := s14_logH_ge_of_socket hb
  have hθ : (0.0034 : ℝ) ≤ theta293 := by have := s13_theta293_margin_lo; linarith
  have hlog552960 : (0 : ℝ) ≤ Real.log 552960 := Real.log_nonneg (by norm_num)
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hAd1 : 1 ≤ Adoor M := one_le_Adoor M
  have hAd0 : (0 : ℝ) < ((Adoor M : ℕ) : ℝ) := by exact_mod_cast hAd1
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hdr : ((doorRowFloor M : ℕ) : ℝ) = (M : ℝ) * ((Adoor M : ℕ) : ℝ) := by
    rw [doorRowFloor]; push_cast; ring
  -- ⟦reading 2⟧ the `e^{50}` floor forces `Adoor M ≥ 10^{12}`
  have hAbig : (10 : ℝ) ^ 12 ≤ ((Adoor M : ℕ) : ℝ) := by
    nlinarith [hp2, hll, hlogHbig, hθ, hlog552960, hlog2hi, hlog2lo, hAd0]
  -- ⟦reading 1⟧ the `j`-floor caps `M`
  have hMle : (M : ℝ) ≤ 589 := by
    nlinarith [hp2, hll, hlogHj, hθ, hlog552960, hlog2lo, hAd0, hM0, hdr]
  have hMn : M ≤ 589 := by exact_mod_cast hMle
  have hlogM : Nat.log 2 M ≤ 9 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h]
    · have hlt : M < 2 ^ 10 := by norm_num; omega
      have := Nat.log_lt_of_lt_pow (by omega : M ≠ 0) hlt
      omega
  have hAdle : Adoor M ≤ 687194767360 := by
    have h : Adoor M ≤ 2 ^ 36 * 10 := by
      rw [Adoor]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hAdleR : ((Adoor M : ℕ) : ℝ) ≤ 687194767360 := by exact_mod_cast hAdle
  norm_num at hAbig
  linarith

/-- `s14_socket_empty_of_gRows (:288)` at the lever. -/
theorem s14_socket_empty_of_gRows_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hg : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate'''_gk K M (A + s) Cp (decayPool (A + s))) :
    ∀ H L q j A s : ℕ, ¬ SocketBase R M H L q j A s :=
  fun H L q j A s hb => s14_gRows_kill_gk K hfl hb (hg H L q j A s hb)

/-! ## §4 — ⟦THE INHABITATION CERTIFICATE⟧ AND THE STOP

The summit checklist's sharpest line: exhibit a tuple at which `SocketBase R M H L q j A s`
holds, at the compose's own `(R, M)`.  §4 does, under the ONE side condition
`2^{doorRowFloor M} ≤ R.Hhi` — and then shows that condition is FORCED by the very gate that
supplies the twin's ⟦A5⟧ slot, so the vacuity escape of §3's dichotomy is closed. -/

/-- `s14_compose_stops_of_MSelect' (:393)` at the lever. -/
theorem s14_compose_stops_of_MSelect'_gk (K : ℕ) {Cg δ₀ Λ ρ : ℝ} {R : ChowlaRegime} {M : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hS : MSelect'_gk K Cg δ₀ Λ ρ R M)
    (hg : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate'''_gk K M (A + s) Cp (decayPool (A + s))) :
    False := by
  have hwin : 2 ^ doorRowFloor M ≤ R.Hlo :=
    s14_window_floor_of_winFit hρ0 hρ1 (hS.winFit R.Hlo le_rfl R.hHlohi)
  exact s14_socket_empty_of_gRows_gk K hfl hg _ _ _ _ _ _
    (s14_socketBase_witness (le_trans hwin R.hHlohi))

/-- `s14_rawcap_forces_empty_window (:412)` at the lever. -/
theorem s14_rawcap_forces_empty_window_gk (K : ℕ) {R : ChowlaRegime} {M : ℕ} {Cp : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo)
    (hg : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      GRowsZeroGate'''_gk K M (A + s) Cp (decayPool (A + s))) :
    R.Hhi < 2 ^ doorRowFloor M := by
  by_contra hcon
  exact s14_socket_empty_of_gRows_gk K hfl hg _ _ _ _ _ _
    (s14_socketBase_witness (by omega))

/-! ## §5 — THE TARGET, NAMED

HEAD-SCOUT's drafted statement (`docs/blueprints/flags.md`, 2026-07-30 20:25, ⟦E0⟧), written
here so the campaign owns the shape in the kernel.  **THE FINAL NAME IS THE CAPTAIN'S** — the
working name below is a placeholder, and the fences HEAD-SCOUT recorded stand: `ε` is OPAQUE
(not universal), `x` is LOWER-bounded only, and the content is fixed-factor cancellation at
the witnessed scale, not a `∀ε` statement.

⚠ **NOT DERIVED.**  The road that was to derive it — `logChowla2_capstone_final_rawcap'` at the
decay pool — is refuted at ⟦B1'-3⟧ by §3.  It is stated, not proved, and nothing in this file
weakens it. -/

-- #audit (temporary)

end Salt.MR

end
