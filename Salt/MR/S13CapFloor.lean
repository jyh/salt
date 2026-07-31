/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.S13MSelect2
import Salt.MR.S13FramesB

/-!
# ⟦W-FLOOR⟧ — `S13CapGatePerBlock`'s RAZOR PAIR AND SOCKET FLOOR, SUPPLIED

**PURELY ADDITIVE.**  No landed declaration is touched; the file is a leaf (the maestro adds
the `All.lean` import at the seal).

This page supplies EIGHT of `S13FramesB.S13CapGatePerBlock`'s thirty-seven fields at the
socket working point:

| field | line | what it is |
|---|---|---|
| `QTann` | `S13FramesB:999` | `𝒬K₂ ≤ q·T_ann` |
| `kappa30Q` | `:1001` | `30 ≤ log(q·T_ann)/log 𝒬K₂` |
| `T0_Tann` | `:1007` | `T₀ ≤ T_ann` |
| `floor1` | `:1009` | `8·log(40000·vkStripConst q) ≤ loglog(5T_ann+1)` |
| `floor2` | `:1011` | the `+8104` companion |
| `floor3` | `:1014` | the `Kq` arm |
| `floor4` | `:1018` | the `Ks` arm |
| `Q2_reg` | `:1027` | passed through (it is the hypothesis the razor pair reads) |

## ⟦THE WORKING POINT⟧

`SocketBase R M H L q j A s` together with the capstone's absorbed `loglogFloor50 ≤ R.Hlo`
(`S13MSelect2` §2) gives, at any base `Nd ≥ A` (in the wire, `Nd = A + s`):

* `log H ≥ e^{50} ≥ 10^{21}` — write `v := log H`;
* `μ_X := log Nd ≥ √H = e^{v/2}` (`s13_socketBase_logA_ge_sqrt`);
* the family's OWN lower binder `hTlo : Nd/2^j ≤ T_ann` (the `hcapWS` slot's `T`-binder at
  `T_ann = 2T`, `S12Compose:317`) plus `2^j ≤ H` (from `SocketBase`'s `j ≤ Nat.log 2 L` and
  `L ≤ H`) gives `log T_ann ≥ log Nd − log H ≥ ½·log Nd ≥ ½·√H`.

⟦THE NEAR-KILL, WALKED BACK⟧ **`TannGate` is NOT the binding `T`-floor** — `hTlo` is.  Every
`T`-floor on this page routes through `hTlo`; `TannGate` is *produced* here (`capfloor_tannGate`)
rather than consumed.  The two derived constants the rest of the page prices against are

  `μ := log(5·T_ann+1) ≥ e^{v/4}` ,   `Λ := loglog(5·T_ann+1) ≥ v/4 ≥ 2.5·10^{20}` .

## ⟦THE CONSTANT REGISTER — stated, not buried⟧

Three of the eight fields mention constants that the port leaves `∃`-bound with only
`3 ≤ T₀`, `0 < Ks` exposed (`PortNonVacuous`'s header names the price).  A supplier CANNOT
discharge them without a numeric handle, so this page carries three explicit register lines:

* `hT₀ : T₀ ≤ exp (exp 100)`  — the height floor sits below `10^{10^{43}}`;
* `hKq : Kq ≤ exp 100`        — `Kq ≤ 2.7·10^{43}`;
* `hKs : exp (-100) ≤ Ks`     — `Ks ≥ 3.7·10^{-44}` (the Siegel constant is not zero-ish).

⟦THE HONEST AFFORDANCE⟧ these numerals are FAR inside what the working point can pay.  The
sharp forms are `T₀ ≤ exp(√H/2)` (proved separately as `capfloor_T0_Tann_sharp`, and
`√H ≥ e^{5·10^{20}}`), `Kq ≤ e^{3v/16}` and `Ks ≥ e^{-3v/16}` with `3v/16 ≥ 1.8·10^{20}`.  The
round `100`s are chosen for legibility, not for tightness.

`Q2_reg` is NOT proved here: it is a genuine `M`-vs-`H` comparison, and it is already supplied
upstream by the `hcapWS`-adjacent slot (`S12Compose:311-312`).  It enters as a hypothesis and
is re-exported by the bundle so the seal gets eight fields from one call.

`PortNonVacuous.gates_jointly_satisfiable:75` is the proof-body MODEL for §3 but is the WRONG
SHAPE to cite: it is existential in `T`, and its witness collides with `logqT_L`'s cap on
`log(q·T_ann)`.  Its body is inlined here AT THE GIVEN `T_ann`.
-/

noncomputable section
open scoped BigOperators
namespace Salt.MR
open Salt.Entropy.Chowla

/-! ### §0 — the numerals and the two elementary majorants -/

/-- `10^{21} ≤ e^{50}` (true value `5.18·10^{21}`). -/
theorem capfloor_ten21_le_exp50 : (10 : ℝ) ^ (21 : ℕ) ≤ Real.exp 50 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h50 : Real.exp 50 = (Real.exp 1) ^ (50 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (50 : ℕ) ≤ (Real.exp 1) ^ (50 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 50
  have hn : (10 : ℝ) ^ (21 : ℕ) ≤ (2.7 : ℝ) ^ (50 : ℕ) := by norm_num
  rw [h50]; linarith

/-- `2·10^8 ≤ e^{20}` — the one numeral floors 1 and 2 spend. -/
theorem capfloor_twoE8_le_exp20 : (300000000 : ℝ) ≤ Real.exp 20 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h20 : Real.exp 20 = (Real.exp 1) ^ (20 : ℕ) := by rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7 : ℝ) ^ (20 : ℕ) ≤ (Real.exp 1) ^ (20 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 20
  have hn : (300000000 : ℝ) ≤ (2.7 : ℝ) ^ (20 : ℕ) := by norm_num
  rw [h20]; linarith

/-- `log v ≤ v/10^{10}` at `v ≥ 10^{21}` — the majorant every `Λ`-side row uses. -/
theorem capfloor_logv_le {v : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v) :
    Real.log v ≤ v / 10 ^ (10 : ℕ) := by
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le h21 hv
  have hs0 : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
  have hlog : Real.log v ≤ 2 * Real.sqrt v := by
    have h := Real.log_le_sub_one_of_pos hs0
    have hs : Real.log (Real.sqrt v) = Real.log v / 2 := Real.log_sqrt hv0.le
    rw [hs] at h; linarith
  have hbig : (2 : ℝ) * 10 ^ (10 : ℕ) ≤ Real.sqrt v := by nlinarith [hsq, hv, hs0]
  nlinarith [hsq, hbig, hs0, hlog, mul_le_mul_of_nonneg_right hbig hs0.le]

/-- `log H ≤ √H/2` at `H ≥ 4·10^6` — the fourth-root majorant (`log H = 4·log H^{1/4}`). -/
theorem capfloor_logH_le_half_sqrt {H : ℝ} (hH : (4000000 : ℝ) ≤ H) :
    Real.log H ≤ Real.sqrt H / 2 := by
  have hH0 : (0 : ℝ) < H := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hH0
  set a : ℝ := Real.sqrt (Real.sqrt H) with ha
  have ha0 : (0 : ℝ) < a := Real.sqrt_pos.mpr hs0
  have ha2 : a * a = Real.sqrt H := Real.mul_self_sqrt hs0.le
  have hloga : Real.log a = Real.log H / 4 := by
    rw [ha, Real.log_sqrt hs0.le, Real.log_sqrt hH0.le]; ring
  have hle : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha0
  have hs2000 : (2000 : ℝ) ≤ Real.sqrt H := by
    nlinarith [Real.mul_self_sqrt hH0.le, hs0]
  have ha40 : (40 : ℝ) ≤ a := by nlinarith [ha2, ha0, hs2000]
  nlinarith [hloga, hle, ha2, ha40, ha0]

/-- `√H = e^{(log H)/2}` at `H > 0`. -/
theorem capfloor_sqrt_eq_exp {H : ℝ} (hH : (0 : ℝ) < H) :
    Real.sqrt H = Real.exp (Real.log H / 2) := by
  have hs0 : (0 : ℝ) < Real.sqrt H := Real.sqrt_pos.mpr hH
  have h : Real.log (Real.sqrt H) = Real.log H / 2 := Real.log_sqrt hH.le
  rw [← h, Real.exp_log hs0]

/-! ### §1 — the socket's `T`-floor: `2^j ≤ H`, and the `μ`/`Λ` pair -/

/-- ⟦THE `T`-FLOOR STONE, PORTED (CAPGATE-SCOPE probe `capgate_twoj_le_H`)⟧ `2^j ≤ H` from
`SocketBase`'s window fields `j ≤ Nat.log 2 L` and `L ≤ H`.  This is what turns the family's
own `hTlo` into `T_ann ≥ Nd/H` — and it is why `TannGate` is not the binding `T`-floor. -/
theorem capfloor_twoj_le_H {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) : 2 ^ j ≤ H := by
  have hjL : j ≤ Nat.log 2 L := hb.2.2.2.2.2.1
  have hLH : L ≤ H := hb.2.2.1
  have hH : 4000000 ≤ H := le_trans R.hHlo_floor hb.1
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0
    have hj : j = 0 := by simpa using hjL
    subst hj
    simpa using (by omega : 1 ≤ H)
  · exact le_trans (le_trans (Nat.pow_le_pow_right (by norm_num) hjL)
      (Nat.pow_log_le_self 2 (by omega))) hLH

/-- ⟦THE WORKING POINT, CORE⟧ the four facts every field on this page reads:
`10^{21} ≤ log H`, `√H ≤ log Nd`, `0 < T_ann`, and `½·log Nd ≤ log T_ann`. -/
theorem capfloor_core {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) ∧ Real.sqrt (H : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) ∧
      0 < Tann ∧ Real.log ((Nd : ℕ) : ℝ) / 2 ≤ Real.log Tann := by
  have hlo : R.Hlo ≤ H := hb.1
  obtain ⟨-, h50⟩ := regime_Hfloor_of_loglogFloor50 (le_trans hfl hlo)
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hexp50 : Real.exp 50 ≤ Real.log (H : ℝ) := by
    have := Real.exp_le_exp.mpr h50
    rwa [Real.exp_log hlogH0] at this
  have hv : (10 : ℝ) ^ (21 : ℕ) ≤ Real.log (H : ℝ) :=
    le_trans capfloor_ten21_le_exp50 hexp50
  -- the base
  have hsqrtH : Real.sqrt (H : ℝ) ≤ Real.log (A : ℝ) := s13_socketBase_logA_ge_sqrt hfl hb
  have hA : 0 < A := hb.2.2.2.2.2.2.2.1
  have hA0 : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hANR : (A : ℝ) ≤ ((Nd : ℕ) : ℝ) := by exact_mod_cast hAN
  have hNd0 : (0 : ℝ) < ((Nd : ℕ) : ℝ) := lt_of_lt_of_le hA0 hANR
  have hm : Real.sqrt (H : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) :=
    le_trans hsqrtH (Real.log_le_log hA0 hANR)
  -- the height
  have h2j : 2 ^ j ≤ H := capfloor_twoj_le_H hb
  have h2jR : ((2 ^ j : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2j
  have h2j0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by positivity
  have hTpos : 0 < Tann := lt_of_lt_of_le (div_pos hNd0 h2j0) hTlo
  have hlogdiv : Real.log ((Nd : ℕ) : ℝ) - Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log Tann := by
    have h := Real.log_le_log (div_pos hNd0 h2j0) hTlo
    rwa [Real.log_div (ne_of_gt hNd0) (ne_of_gt h2j0)] at h
  have hlog2j : Real.log ((2 ^ j : ℕ) : ℝ) ≤ Real.log (H : ℝ) := Real.log_le_log h2j0 h2jR
  have hHhalf : Real.log (H : ℝ) ≤ Real.sqrt (H : ℝ) / 2 := capfloor_logH_le_half_sqrt hHR
  exact ⟨hv, hm, hTpos, by linarith⟩

/-- ⟦THE `μ`/`Λ` PAIR⟧ `e^{v/4} ≤ log(5T_ann+1)` and `v/4 ≤ loglog(5T_ann+1)`, `v = log H`. -/
theorem capfloor_muLambda {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    Real.exp (Real.log (H : ℝ) / 4) ≤ Real.log (5 * Tann + 1) ∧
      Real.log (H : ℝ) / 4 ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core hfl hb hAN hTlo
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := by nlinarith [hv, (by positivity :
    (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ))]
  -- `√H = e^{v/2} = e^{v/4}·e^{v/4}`
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  have hsplit : Real.exp (Real.log (H : ℝ) / 2)
      = Real.exp (Real.log (H : ℝ) / 4) * Real.exp (Real.log (H : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hq0 : (0 : ℝ) < Real.exp (Real.log (H : ℝ) / 4) := Real.exp_pos _
  have hq2 : (2 : ℝ) ≤ Real.exp (Real.log (H : ℝ) / 4) := by
    have h := Real.add_one_le_exp (Real.log (H : ℝ) / 4)
    have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    linarith
  -- `log T_ann ≥ ½ log Nd ≥ ½ √H = ½ e^{v/2} ≥ e^{v/4}`
  have hstep : Real.exp (Real.log (H : ℝ) / 4) ≤ Real.log Tann := by
    have h1 : Real.sqrt (H : ℝ) / 2 ≤ Real.log Tann := by linarith
    rw [hsq, hsplit] at h1
    nlinarith [h1, hq0, hq2]
  have hmono : Real.log Tann ≤ Real.log (5 * Tann + 1) :=
    Real.log_le_log hTpos (by linarith)
  refine ⟨le_trans hstep hmono, ?_⟩
  have hpos : (0 : ℝ) < Real.exp (Real.log (H : ℝ) / 4) := Real.exp_pos _
  have h := Real.log_le_log hpos (le_trans hstep hmono)
  rwa [Real.log_exp] at h

/-! ### §2 — `T0_Tann` (field `S13FramesB:1007`) -/

/-- ⟦`T0_Tann`, SHARP⟧ the height floor is met by anything below the socket's own forced
height `e^{√H/2}` (and `√H ≥ e^{5·10^{20}}`). -/
theorem capfloor_T0_Tann_sharp {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {T₀ Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hT₀ : T₀ ≤ Real.exp (Real.sqrt (H : ℝ) / 2)) : T₀ ≤ Tann := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core hfl hb hAN hTlo
  have h1 : Real.sqrt (H : ℝ) / 2 ≤ Real.log Tann := by linarith
  have h2 : Real.exp (Real.sqrt (H : ℝ) / 2) ≤ Real.exp (Real.log Tann) :=
    Real.exp_le_exp.mpr h1
  rw [Real.exp_log hTpos] at h2
  linarith

/-- ⟦`T0_Tann`, AT THE REGISTER NUMERAL⟧ `T₀ ≤ e^{e^{100}}` suffices. -/
theorem capfloor_T0_Tann {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {T₀ Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) : T₀ ≤ Tann := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core hfl hb hAN hTlo
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  -- `e^{100} ≤ √H/2`
  have hE : Real.exp 100 ≤ Real.sqrt (H : ℝ) / 2 := by
    have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
    have hmono : Real.exp 101 ≤ Real.exp (Real.log (H : ℝ) / 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hv, h21])
    have hsplit : Real.exp 101 = Real.exp 100 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp : (0 : ℝ) < Real.exp 100 := Real.exp_pos _
    rw [hsq]
    nlinarith [hmono, hsplit, he1, hp]
  exact capfloor_T0_Tann_sharp hfl hb hAN hTlo (le_trans hT₀ (Real.exp_le_exp.mpr hE))

/-! ### §3 — the four floor gates.

`PortNonVacuous.gates_jointly_satisfiable`'s body, inlined AT THE GIVEN `T_ann`: there the
witness `T` is *chosen* to make `loglog(5T+1) = s` a max of the four demands; here `T_ann` is
handed to us by the family and the four demands are checked against `Λ ≥ v/4` instead.  Its
`∃ T` shape cannot be cited — the witness collides with `logqT_L`'s cap on `log(q·T_ann)`. -/

/-- The `Λ`-side numeric core: `160 + 96·log v ≤ v/4` at `v ≥ 10^{21}`. -/
theorem capfloor_lam_core {v : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v) :
    160 + 96 * Real.log v ≤ v / 4 := by
  have h := capfloor_logv_le hv
  norm_num at h ⊢
  linarith

/-- `log q ≤ 12·log v` from `SocketBase`'s modulus range `q ≤ arcDen 12 H`. -/
theorem capfloor_logq_le {R : ChowlaRegime} {M H L q j A s : ℕ}
    (hb : SocketBase R M H L q j A s) :
    Real.log (q : ℝ) ≤ 12 * Real.log (Real.log (H : ℝ)) ∧ (1 : ℝ) ≤ (q : ℝ) := by
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hlogH0 : (0 : ℝ) < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hq : 0 < q := hb.2.2.2.1
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqA : (q : ℝ) ≤ arcDen 12 H := hb.2.2.2.2.1
  have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
    rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [harcpow] at hqA
  refine ⟨?_, hq1⟩
  have h := Real.log_le_log (by linarith : (0 : ℝ) < (q : ℝ)) hqA
  rwa [Real.log_pow] at h

/-- ⟦`floor1`, `S13FramesB:1009`⟧ `8·log(40000·vkStripConst q) ≤ loglog(5T_ann+1)`.
At `vkStripConst q = 5000q` the demand is `8·log(2·10^8·q) ≤ Λ`, i.e. `160 + 96·log v ≤ v/4`
after `q ≤ v^{12}` — met with ~`10^{17}` orders to spare. -/
theorem capfloor_floor1 {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨-, hΛ⟩ := capfloor_muLambda hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le hb
  have hvk : (40000 : ℝ) * vkStripConst q = 200000000 * (q : ℝ) := by
    rw [vkStripConst]; ring
  have hsplit : Real.log (200000000 * (q : ℝ))
      = Real.log 200000000 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have hnum : Real.log 200000000 ≤ 20 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 200000000)
      (le_trans (by norm_num : (200000000 : ℝ) ≤ 300000000) capfloor_twoE8_le_exp20)
    rwa [Real.log_exp] at h
  have hcore := capfloor_lam_core hv
  rw [hvk, hsplit]
  linarith

/-- ⟦`floor2`, `S13FramesB:1011`⟧ the `+8104` companion — trivial at the working point. -/
theorem capfloor_floor2 {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨-, hΛ⟩ := capfloor_muLambda hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le hb
  have hvk : (20000 : ℝ) * (vkStripConst q + 8104) = 100000000 * (q : ℝ) + 162080000 := by
    rw [vkStripConst]; ring
  have hub : 100000000 * (q : ℝ) + 162080000 ≤ 300000000 * (q : ℝ) := by linarith
  have hlb : (0 : ℝ) < 100000000 * (q : ℝ) + 162080000 := by linarith
  have hmono := Real.log_le_log hlb hub
  have hsplit : Real.log (300000000 * (q : ℝ))
      = Real.log 300000000 + Real.log (q : ℝ) :=
    Real.log_mul (by norm_num) (by linarith)
  have hnum : Real.log 300000000 ≤ 20 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 300000000) capfloor_twoE8_le_exp20
    rwa [Real.log_exp] at h
  have hcore := capfloor_lam_core hv
  have hlq0 : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hlvl : (0 : ℝ) ≤ Real.log (Real.log (H : ℝ)) := by linarith
  rw [hvk]
  rw [hsplit] at hmono
  linarith

/-- The `Kq`-arm numeric core: `E·W ≤ E^3·(v/4)^4` at `W ≤ 12·log v + E + 1`, `E ≥ 101`,
`v ≥ 10^{21}`. -/
theorem capfloor_floor3_numeric {v E W : ℝ} (hv : (10 : ℝ) ^ (21 : ℕ) ≤ v) (hE : 101 ≤ E)
    (hW : W ≤ 12 * Real.log v + E + 1) :
    E * W ≤ E ^ (3 : ℕ) * (v / 4) ^ (4 : ℕ) := by
  have hlv := capfloor_logv_le hv
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le h21 hv
  have hE0 : (0 : ℝ) < E := by linarith
  have hvbig : (1000000000000000000000 : ℝ) ≤ v := le_trans (by norm_num) hv
  have hlv' : Real.log v ≤ v / 10000000000 := le_trans hlv (by norm_num)
  -- `W ≤ 12·(v/10^10) + E + 1 ≤ v + E + 1`
  have hWv : W ≤ v + E + 1 := by linarith
  have hvq : (v / 4) ^ (4 : ℕ) = v ^ (4 : ℕ) / 256 := by ring
  rw [hvq]
  have h1 : v + E + 1 ≤ v * E := by nlinarith [hvbig, hE]
  have hxx : (65536 : ℝ) ≤ v * v := by nlinarith [hvbig]
  have hv3 : (256 : ℝ) ≤ v ^ (3 : ℕ) := by
    have hid : v ^ (3 : ℕ) = v * (v * v) := by ring
    rw [hid]; nlinarith [hvbig, hxx]
  have hfac : (1 : ℝ) ≤ E * v ^ (3 : ℕ) / 256 := by nlinarith [hv3, hE]
  have hpos : (0 : ℝ) ≤ E * (v * E) := by positivity
  have h2 : E * (v * E) ≤ E ^ (3 : ℕ) * (v ^ (4 : ℕ) / 256) := by
    calc E * (v * E) = (E * (v * E)) * 1 := by ring
      _ ≤ (E * (v * E)) * (E * v ^ (3 : ℕ) / 256) := mul_le_mul_of_nonneg_left hfac hpos
      _ = E ^ (3 : ℕ) * (v ^ (4 : ℕ) / 256) := by ring
  have hA : E * W ≤ E * (v + E + 1) := mul_le_mul_of_nonneg_left hWv hE0.le
  have hB : E * (v + E + 1) ≤ E * (v * E) := mul_le_mul_of_nonneg_left h1 hE0.le
  linarith

/-- `e^{3v/16} ≤ μ^{3/4}` and `(v/4)^4 ≤ Λ^4` — the two RHS legs floors 3 and 4 share. -/
theorem capfloor_rhs_legs {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    Real.exp 300 * (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨hμ, hΛ⟩ := capfloor_muLambda hfl hb hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  -- leg 1
  have hleg1 : Real.exp 300 ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) := by
    have hstep : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_nonneg _) hμ (by norm_num)
    have heq : (Real.exp (Real.log (H : ℝ) / 4)) ^ ((3 : ℝ) / 4)
        = Real.exp (Real.log (H : ℝ) / 4 * (3 / 4)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [heq] at hstep
    refine le_trans (Real.exp_le_exp.mpr ?_) hstep
    nlinarith [hv, h21]
  -- leg 2
  have hleg2 : (Real.log (H : ℝ) / 4) ^ (4 : ℕ)
      ≤ (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hΛ 4
  have hp1 : (0 : ℝ) < Real.exp 300 := Real.exp_pos _
  have hp2 : (0 : ℝ) ≤ (Real.log (H : ℝ) / 4) ^ (4 : ℕ) := by positivity
  exact mul_le_mul hleg1 hleg2 hp2 (le_trans hp1.le hleg1)

/-- ⟦`floor3`, `S13FramesB:1014`⟧ the `Kq` arm.  ⟦REGISTER⟧ `Kq ≤ e^{100} = 2.7·10^{43}`. -/
theorem capfloor_floor3 {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Kq Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) (hKq : Kq ≤ Real.exp 100) :
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le hb
  have hlegs := capfloor_rhs_legs hfl hb hAN hTlo
  set E : ℝ := Real.exp 100 with hEdef
  have hE : (101 : ℝ) ≤ E := by
    have := Real.add_one_le_exp (100 : ℝ); rw [hEdef]; linarith
  have hE0 : (0 : ℝ) < E := by linarith
  -- the LHS's log factor
  have hexpE : (3 : ℝ) ≤ Real.exp E := by
    have := Real.add_one_le_exp E; linarith
  have hbox : Real.exp E + 3 ≤ Real.exp (E + 1) := by
    rw [Real.exp_add]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith [Real.exp_pos E, hexpE, he1]
  have hbox0 : (0 : ℝ) < Real.exp E + 3 := by positivity
  have hboxlog : Real.log (Real.exp E + 3) ≤ E + 1 := by
    have h := Real.log_le_log hbox0 hbox
    rwa [Real.log_exp] at h
  have hWsplit : Real.log ((q : ℝ) * (Real.exp E + 3))
      = Real.log (q : ℝ) + Real.log (Real.exp E + 3) :=
    Real.log_mul (by linarith) (by linarith)
  have hW0 : (0 : ℝ) ≤ Real.log ((q : ℝ) * (Real.exp E + 3)) := by
    refine Real.log_nonneg ?_
    nlinarith [hq1, hexpE]
  have hW : Real.log ((q : ℝ) * (Real.exp E + 3)) ≤ 12 * Real.log (Real.log (H : ℝ)) + E + 1 := by
    rw [hWsplit]; linarith
  -- assemble
  have hstep : Kq * Real.log ((q : ℝ) * (Real.exp E + 3))
      ≤ E * Real.log ((q : ℝ) * (Real.exp E + 3)) :=
    mul_le_mul_of_nonneg_right hKq hW0
  have hnum := capfloor_floor3_numeric hv hE hW
  have hE3 : Real.exp 300 = E ^ (3 : ℕ) := by
    rw [hEdef, ← Real.exp_nat_mul]; norm_num
  rw [hE3] at hlegs
  linarith

/-- ⟦`floor4`, `S13FramesB:1018`⟧ the `Ks` arm.  ⟦REGISTER⟧ `Ks ≥ e^{-100} = 3.7·10^{-44}`. -/
theorem capfloor_floor4 {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) (hKs : Real.exp (-100) ≤ Ks) :
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) := by
  obtain ⟨hv, -, -, -⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨hlq, hq1⟩ := capfloor_logq_le hb
  have hlegs := capfloor_rhs_legs hfl hb hAN hTlo
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  -- the LHS: `q^{1/16} ≤ v^{3/4} ≤ v`
  have hqA : (q : ℝ) ≤ Real.log (H : ℝ) ^ (12 : ℕ) := by
    have h := hb.2.2.2.2.1
    have harcpow : arcDen 12 H = Real.log (H : ℝ) ^ (12 : ℕ) := by
      rw [arcDen, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rwa [harcpow] at h
  have hstep1 : (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ (Real.log (H : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow (Nat.cast_nonneg q) hqA (by norm_num)
  have hstep2 : (Real.log (H : ℝ) ^ (12 : ℕ)) ^ ((1 : ℝ) / 16)
      = Real.log (H : ℝ) ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_natCast (Real.log (H : ℝ)) 12, ← Real.rpow_mul hv0.le]
    norm_num
  have hv1 : (1 : ℝ) ≤ Real.log (H : ℝ) := by nlinarith [hv, h21]
  have hstep3 : Real.log (H : ℝ) ^ ((3 : ℝ) / 4) ≤ Real.log (H : ℝ) := by
    calc Real.log (H : ℝ) ^ ((3 : ℝ) / 4) ≤ Real.log (H : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
      _ = Real.log (H : ℝ) := Real.rpow_one _
  have hLHS : (q : ℝ) ^ ((1 : ℝ) / 16) ≤ Real.log (H : ℝ) := by
    rw [hstep2] at hstep1; linarith
  -- the RHS
  set E : ℝ := Real.exp 100 with hEdef
  have hE : (101 : ℝ) ≤ E := by
    have := Real.add_one_le_exp (100 : ℝ); rw [hEdef]; linarith
  have hE0 : (0 : ℝ) < E := by linarith
  have hE3 : Real.exp 300 = E ^ (3 : ℕ) := by
    rw [hEdef, ← Real.exp_nat_mul]; norm_num
  rw [hE3] at hlegs
  have hKsE : 1 / E ≤ Ks := by
    have h : Real.exp (-100 : ℝ) = 1 / E := by
      rw [hEdef, Real.exp_neg]; simp
    rwa [h] at hKs
  have hRpos : (0 : ℝ) ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) := by
    refine le_trans ?_ hlegs
    positivity
  have hmul : (1 / E) * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
      * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ))
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
    mul_le_mul_of_nonneg_right hKsE hRpos
  refine le_trans ?_ hmul
  refine le_trans hLHS ?_
  -- `v ≤ (1/E)·E^3·(v/4)^4 = E²·v^4/256`
  have hinner : (1 / E) * (E ^ (3 : ℕ) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      ≤ (1 / E) * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) :=
    mul_le_mul_of_nonneg_left hlegs (by positivity)
  refine le_trans ?_ hinner
  have hEq : (1 / E) * (E ^ (3 : ℕ) * (Real.log (H : ℝ) / 4) ^ (4 : ℕ))
      = E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (4 : ℕ) / 256) := by
    field_simp; ring
  rw [hEq]
  have h256 : (256 : ℝ) ≤ Real.log (H : ℝ) := by
    refine le_trans (by norm_num) hv
  have hxx : (65536 : ℝ) ≤ Real.log (H : ℝ) * Real.log (H : ℝ) := by nlinarith [h256]
  have hv3 : (256 : ℝ) ≤ Real.log (H : ℝ) ^ (3 : ℕ) := by
    have hid : Real.log (H : ℝ) ^ (3 : ℕ)
        = Real.log (H : ℝ) * (Real.log (H : ℝ) * Real.log (H : ℝ)) := by ring
    rw [hid]; nlinarith [h256, hxx]
  have hE2 : (1 : ℝ) ≤ E ^ (2 : ℕ) := by nlinarith [hE]
  have hfac : (1 : ℝ) ≤ E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (3 : ℕ) / 256) := by
    have h1 : (1 : ℝ) ≤ Real.log (H : ℝ) ^ (3 : ℕ) / 256 := by linarith
    nlinarith [hE2, h1]
  have hid2 : E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (4 : ℕ) / 256)
      = Real.log (H : ℝ) * (E ^ (2 : ℕ) * (Real.log (H : ℝ) ^ (3 : ℕ) / 256)) := by ring
  rw [hid2]
  nlinarith [hfac, hv0]

/-! ### §4 — the razor pair `QTann` / `kappa30Q` (fields `S13FramesB:999`, `:1001`)

Both read `Q2_reg` (the band gate `log 𝒬K₂ ≤ √(log Nd)`), which is supplied by the
`hcapWS`-adjacent slot (`S12Compose:311-312`) and enters here as a hypothesis. -/

/-- `1 < 𝒬K₂` at every `M ≥ 1` — the positivity `kappa30_of_TannGate` asks for. -/
theorem capfloor_one_lt_QK2 {M : ℕ} (hM : 1 ≤ M) :
    1 < ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
  have hA : 0 < Adoor M := by rw [Adoor]; positivity
  have hE : 0 < calE (Adoor M) (3072 * M) 2 := by
    rw [calE]
    refine Nat.mul_pos (Nat.mul_pos hA (pow_pos (by omega : 0 < 3072 * M) _)) ?_
    positivity
  have h : 1 < calQK (Adoor M) (3072 * M) M 2 := by
    rw [calQK]
    refine Nat.one_lt_two_pow_iff.mpr ?_
    have : 0 < (2 ^ 2 * M) * calE (Adoor M) (3072 * M) 2 :=
      Nat.mul_pos (by positivity) hE
    omega
  exact_mod_cast h

/-- ⟦THE `TannGate`, PRODUCED (not consumed)⟧ `TannGate Nd (q·T_ann)` at the working point.
The gate asks `e^{30√(log Nd)} ≤ q·T_ann`; `hTlo` gives `log T_ann ≥ ½·log Nd = ½·r²` with
`r := √(log Nd) ≥ 2.5·10^{20}`, and `½r² ≥ 30r` from `r ≥ 60`. -/
theorem capfloor_tannGate {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann) :
    TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) := by
  obtain ⟨hv, hm, hTpos, hlogT⟩ := capfloor_core hfl hb hAN hTlo
  obtain ⟨-, hq1⟩ := capfloor_logq_le hb
  have h21 : (0 : ℝ) < (10 : ℝ) ^ (21 : ℕ) := by positivity
  have hv0 : (0 : ℝ) < Real.log (H : ℝ) := lt_of_lt_of_le h21 hv
  have hlo : R.Hlo ≤ H := hb.1
  have hH4 : 4000000 ≤ H := le_trans R.hHlo_floor hlo
  have hHR : (4000000 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH4
  have hH0 : (0 : ℝ) < (H : ℝ) := by linarith
  -- `log Nd ≥ √H = e^{v/2} ≥ (v/4)² = v²/16`
  have hsq : Real.sqrt (H : ℝ) = Real.exp (Real.log (H : ℝ) / 2) := capfloor_sqrt_eq_exp hH0
  have hexpsq : Real.exp (Real.log (H : ℝ) / 2)
      = Real.exp (Real.log (H : ℝ) / 4) * Real.exp (Real.log (H : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  have hquart : Real.log (H : ℝ) / 4 ≤ Real.exp (Real.log (H : ℝ) / 4) := by
    have := Real.add_one_le_exp (Real.log (H : ℝ) / 4); linarith
  have hq0 : (0 : ℝ) ≤ Real.log (H : ℝ) / 4 := by linarith
  have hmsq : Real.log (H : ℝ) ^ (2 : ℕ) / 16 ≤ Real.log ((Nd : ℕ) : ℝ) := by
    have h : (Real.log (H : ℝ) / 4) * (Real.log (H : ℝ) / 4) ≤ Real.sqrt (H : ℝ) := by
      rw [hsq, hexpsq]; nlinarith [hquart, hq0]
    nlinarith [h, hm]
  have hm0 : (0 : ℝ) ≤ Real.log ((Nd : ℕ) : ℝ) := by nlinarith [hmsq, hv0]
  set r : ℝ := Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) with hr
  have hr2 : r * r = Real.log ((Nd : ℕ) : ℝ) := Real.mul_self_sqrt hm0
  have hr0 : (0 : ℝ) ≤ r := Real.sqrt_nonneg _
  have hnum : (10 : ℝ) ^ (21 : ℕ) = 1000000000000000000000 := by norm_num
  rw [hnum] at hv
  have hr60 : (60 : ℝ) ≤ r := by nlinarith [hr2, hmsq, hv, hr0, hv0]
  -- `log(q·T_ann) ≥ log T_ann ≥ ½·r² ≥ 30r`
  have hlogq : (0 : ℝ) ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hqT : Real.log ((q : ℝ) * Tann) = Real.log (q : ℝ) + Real.log Tann :=
    Real.log_mul (by linarith) (ne_of_gt hTpos)
  have hkey : 30 * r ≤ Real.log ((q : ℝ) * Tann) := by
    rw [hqT]; nlinarith [hlogT, hr2, hr60, hr0, hlogq]
  have hqT0 : (0 : ℝ) < (q : ℝ) * Tann := by positivity
  unfold TannGate
  rw [rpow_half_eq_sqrt, ← hr]
  calc Real.exp (30 * r) ≤ Real.exp (Real.log ((q : ℝ) * Tann)) := Real.exp_le_exp.mpr hkey
    _ = (q : ℝ) * Tann := Real.exp_log hqT0

/-- ⟦`QTann`, `S13FramesB:999`⟧ `𝒬K₂ ≤ q·T_ann` — `Q2_reg` exponentiated against the gate
(`log 𝒬K₂ ≤ r ≤ 30r ≤ log(q·T_ann)`). -/
theorem capfloor_QTann {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann := by
  have hgate := capfloor_tannGate hfl hb hAN hTlo (q := q)
  unfold TannGate at hgate
  rw [rpow_half_eq_sqrt] at hgate
  have hQ1 : 1 < ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := capfloor_one_lt_QK2 hM
  have hQ0 : (0 : ℝ) < ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by linarith
  have hr0 : (0 : ℝ) ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) := Real.sqrt_nonneg _
  calc ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      = Real.exp (Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)) := (Real.exp_log hQ0).symm
    _ ≤ Real.exp (30 * Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :=
        Real.exp_le_exp.mpr (by linarith)
    _ ≤ (q : ℝ) * Tann := hgate

/-- ⟦`kappa30Q`, `S13FramesB:1001`⟧ `30 ≤ log(q·T_ann)/log 𝒬K₂` — `USetPins.kappa30_of_TannGate`
at `Q := 𝒬K₂`, `hQpin := Q2_reg`, `hT :=` §4's produced gate. -/
theorem capfloor_kappa30Q {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hAN : A ≤ Nd) (hM : 1 ≤ M)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ))) :
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) := by
  refine kappa30_of_TannGate ((Nd : ℕ) : ℝ) ((q : ℝ) * Tann) (calQK (Adoor M) (3072 * M) M 2)
    (capfloor_one_lt_QK2 hM) ?_ (capfloor_tannGate hfl hb hAN hTlo)
  rw [rpow_half_eq_sqrt]; exact hQ2reg

/-! ### §5 — ⟦THE BUNDLE⟧ the eight fields at the shared binder + the register -/

/-- **⟦W-FLOOR'S SUPPLIER⟧** (`s13CapFloor_all`) — EIGHT fields of
`S13FramesB.S13CapGatePerBlock` at one binder.

⟦THE SHARED BINDER⟧ `SocketBase R M H L q j A s` + the capstone's absorbed
`loglogFloor50 ≤ R.Hlo` + `1 ≤ M` + a base `Nd ≥ A` (in the wire `Nd = A + s`) + the family's
OWN lower height binder `hTlo : Nd/2^j ≤ T_ann` (`S12Compose:317` at `T_ann = 2T`) + `Q2_reg`
(supplied at `S12Compose:311-312`).

⟦THE CONSTANT REGISTER — three lines, stated not buried⟧
`hT₀ : T₀ ≤ e^{e^{100}}`, `hKq : Kq ≤ e^{100}`, `hKs : e^{-100} ≤ Ks`.  Nothing is assumed
about `Cq`, `cs`, `C`, `Rrad`, `Rbd`, `CR`, `EP2`, `εr`, `P`, `Q` — those are other waves'
fields.  No `[NeZero q]` instance is needed: `SocketBase`'s own `0 < q` serves.

The conjuncts are in `S13CapGatePerBlock` field order: `QTann`, `kappa30Q`, `T0_Tann`,
`floor1`, `floor2`, `floor3`, `floor4`, `Q2_reg`. -/
theorem s13CapFloor_all {R : ChowlaRegime} {M H L q j A s Nd : ℕ} {T₀ Kq Ks Tann : ℝ}
    (hfl : loglogFloor50 ≤ R.Hlo) (hb : SocketBase R M H L q j A s) (hM : 1 ≤ M) (hAN : A ≤ Nd)
    (hTlo : ((Nd : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ Tann)
    (hQ2reg : Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)))
    (hT₀ : T₀ ≤ Real.exp (Real.exp 100)) (hKq : Kq ≤ Real.exp 100)
    (hKs : Real.exp (-100) ≤ Ks) :
    ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ≤ (q : ℝ) * Tann ∧
    30 ≤ Real.log ((q : ℝ) * Tann)
      / Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ) ∧
    T₀ ≤ Tann ∧
    8 * Real.log (40000 * vkStripConst q) ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    8 + Real.log (20000 * (vkStripConst q + 8104)) / 100
      ≤ Real.log (Real.log (5 * Tann + 1)) ∧
    Kq * Real.log ((q : ℝ) * (Real.exp (Real.exp 100) + 3))
      ≤ (Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ) ∧
    (q : ℝ) ^ ((1 : ℝ) / 16)
      ≤ Ks * ((Real.log (5 * Tann + 1)) ^ ((3 : ℝ) / 4)
        * (Real.log (Real.log (5 * Tann + 1))) ^ (4 : ℕ)) ∧
    Real.log ((calQK (Adoor M) (3072 * M) M 2 : ℕ) : ℝ)
      ≤ Real.sqrt (Real.log ((Nd : ℕ) : ℝ)) :=
  ⟨capfloor_QTann hfl hb hAN hM hTlo hQ2reg,
   capfloor_kappa30Q hfl hb hAN hM hTlo hQ2reg,
   capfloor_T0_Tann hfl hb hAN hTlo hT₀,
   capfloor_floor1 hfl hb hAN hTlo,
   capfloor_floor2 hfl hb hAN hTlo,
   capfloor_floor3 hfl hb hAN hTlo hKq,
   capfloor_floor4 hfl hb hAN hTlo hKs,
   hQ2reg⟩

end Salt.MR

