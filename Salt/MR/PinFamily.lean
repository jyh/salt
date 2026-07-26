/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FarStar
import Salt.MR.Transfer34
import Salt.MR.CofactorLocal
import Salt.MR.LambdaMass

/-!
# THE PARALLEL PIN FAMILY at `log y = L^{2/5}` (`PinFamily`)

`⟦V6b⟧`/`⟦MORNING RATIFICATIONS 7/26⟧` of `docs/exploration/hsup-design.md` ratify **R2**:
a PARALLEL family of pinned stones at

  `y₂ := exp(L^{2/5})`,  `η₂ := 1/log y₂ = L^{−2/5}`,  `L = log k`,

standing beside — never replacing — the corpus pin `y = L⁴`, `η = 1/(4 log L)`.  Iron rule 1
is respected literally: **no landed statement is touched, no existing file is edited**; every
stone below is a NEW twin.

## Why `2/5`

The far arm's truncation height is forced to `T* = y·k^{1/log y}`, so

  `log T* = log y + L/log y`.

At the corpus pin that is `L/(4 log L)` — nearly `L`, and `CofactorLocal.farErr_local_le`
then carries `log T*/(log W)^{1/2} ≍ √L/log L → ∞` (`farErr_local_window_ge`: the wall).
At `log y = L^{2/5}` it is `L^{2/5} + L^{3/5} ≍ L^{3/5}`, and against R3's SHARPENED
denominator `(log W)^{3/4}` (`Transfer34.farErr34`) the quotient is

  `L^{3/5}/L^{3/4} = L^{−3/20} → 0`.

`3/20 = 0.15` versus the consumer's demand `2·θ₂₉₃ ≈ 0.0068`: **the wall closes**, with an
explicit threshold.  That is §5's `farErr34_local_closes` — THE PRIZE.  Any exponent in
`(1/2, 3/4)` would do; `2/5` is the ⟦V6b⟧-PINNED choice (it keeps `η₂` comfortably small, so
the `S1′` E-slot stays inside `caseAS`'s `4·L^{−1/2+1/1000}` — §6).

## The master gate

Every stone here is gated by `pin2Gate := exp 32768 ≤ k`, i.e. `L ≥ 2¹⁵`.  The numeral is
chosen so the three `L`-powers are EXACT at the gate:

  `L^{1/5} ≥ 8`,  `L^{2/5} ≥ 64`,  `L^{3/5} ≥ 512`,

which discharges every `y₂`-gate the §8.3 chain asks for (`10 ≤ y₂`, `131072 ≤ y₂`,
`y₂ ≤ √X`, `√(log X) ≤ y₂`, `η₂ ≤ 1/64`, `1/L < η₂`) with no asymptotics anywhere.

## What lands

* **§1–§2 — the pin and its gates** (`ypin2`, `eta2`, `Tstar2`; `pin2_basic` and the named
  gate lemmas).  `log_le_rpow_fifth` is the one growth fact the family needs.
* **§3 — the `S1′` re-instantiation** (`prop21_uniform_at_scale_pin2`): `LambdaMass`'s
  `prop21_unconditional_uniform_absC` is ALREADY free-`y`; the pin-2 gates discharge its
  three `y`-hypotheses EXACTLY (no `logpow4_le_sqrt_ev'` asymptotic is needed — `y₂ ≤ √X` is
  a numeral fact at the gate).  RE-INSTANTIATED, not cloned.
* **§4 — FarStar at `y₂`, whole** (`farKfarStar2`, `far_kernel_bound_star2`,
  `far_mass_cancel2`, `far_kfar_star2_le`, `far_supF_bound2`, `hfar_star2`).  The exact
  `k^{η₂}` cancellation with residual `k^{−1/L}·y₂^{−η₂} = e^{−2}` — the SAME `e^{−2}`, at
  the new pin, confirming ⟦V6b⟧'s "at ANY `y`".  The margin IMPROVES from `L^{−1/2}/log L`
  to `L^{2}/exp(L^{2/5})`.
* **§5 — THE PRIZE** (`log_Tstar2_self`, `farErr34_local_le_pin2`,
  `farErr34_local_closes_of_gate`, **`farErr34_local_closes`**): the composed certificate.
* **§6 — the E-slot** (`E_slot_pin2_le`, `E_slot_pin2_closes`): `S1′`'s error at `y₂` is
  `∝ log y₂ = L^{2/5}`, i.e. `L^{−3/5}` after the `X/log X` normalisation, comfortably inside
  `caseAS`'s `4·L^{−1/2+1/1000}` slot.
* **§7 — the F-2 assembly twin** (`cofactor_Rbd34_assembled`): R3's Zeno, the zero-edit wire
  of `Rbd34_grade_priced` over the pin-2 far radius.

## The `widthKamp` page at `A₂ := (y₂/2)^{1/8}` — HALF improves, HALF BREAKS

`GradeConst.pin_width_gates` asks `4 ≤ (y/2)^{1/8}` AND `y ≤ 2·(2(X+h)/h)⁸`.  The first
IMPROVES at `y₂` (`width_pin_gates_pin2`).  The second is a real BANDWIDTH constraint —
`≈ 512·L⁴` at `h = X/√L` — and `y₂ = exp(L^{2/5})` VIOLATES it
(`width_pin_gate_bandwidth_fails_pin2`, a strict inequality past `L ≥ 2²⁰`).  So the width
layer does NOT re-instantiate at `y₂` with `h` still pinned at `X/√L`; that is ⟦V6b⟧ freeze
risk (ii)'s one genuine hit, recorded rather than papered over.  The far arm (§4) and the
payoff (§5) never touch the width gate.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §0 — the arithmetic of the `1/5`-scale

Two facts carry the whole family: an exact `rpow` numeral page at base `2¹⁵`, and the growth
bound `log L ≤ (5/e)·L^{1/5}` (derivative-free: `log s ≤ s/e` at `s = L^{1/5}`). -/

/-- `x = y⁵` with `y ≥ 0` ⟹ `x^{p/5} = y^p` for every real `p`.  The exact numeral page:
at `x = 32768 = 8⁵` this gives `x^{1/5} = 8`, `x^{2/5} = 64`, `x^{3/5} = 512`. -/
private lemma rpow_div_five {x y : ℝ} (hy : 0 ≤ y) (h : y ^ (5 : ℕ) = x) (p : ℝ) :
    x ^ (p / 5) = y ^ p := by
  subst h
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]
  congr 1
  push_cast
  ring

private lemma gate_rpow_fifth : (32768 : ℝ) ^ ((1 : ℝ) / 5) = 8 := by
  rw [rpow_div_five (y := 8) (by norm_num) (by norm_num) 1, Real.rpow_one]

private lemma gate_rpow_two_fifths : (32768 : ℝ) ^ ((2 : ℝ) / 5) = 64 := by
  rw [rpow_div_five (y := 8) (by norm_num) (by norm_num) 2,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private lemma gate_rpow_three_fifths : (32768 : ℝ) ^ ((3 : ℝ) / 5) = 512 := by
  rw [rpow_div_five (y := 8) (by norm_num) (by norm_num) 3,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- **The growth fact.**  `log L ≤ (5/e)·L^{1/5}` for `L > 0` — `log s ≤ s/e` (i.e.
`log(s/e) ≤ s/e − 1`) applied at `s = L^{1/5}`, whose log is `(1/5)·log L`.  No derivative,
no asymptotics; the constant `5/e ≈ 1.839` is what every "`log L` is negligible against a
power of `L`" step below charges. -/
theorem log_le_rpow_fifth {L : ℝ} (hL : 0 < L) :
    Real.log L ≤ 5 / Real.exp 1 * L ^ ((1 : ℝ) / 5) := by
  have hu0 : (0 : ℝ) < L ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hL _
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hlog : Real.log (L ^ ((1 : ℝ) / 5) / Real.exp 1)
      ≤ L ^ ((1 : ℝ) / 5) / Real.exp 1 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hu0) (ne_of_gt he0), Real.log_exp, Real.log_rpow hL] at hlog
  have hstep : Real.log L / 5 ≤ L ^ ((1 : ℝ) / 5) / Real.exp 1 := by
    have h1 : (1 : ℝ) / 5 * Real.log L = Real.log L / 5 := by ring
    linarith [hlog]
  calc Real.log L = 5 * (Real.log L / 5) := by ring
    _ ≤ 5 * (L ^ ((1 : ℝ) / 5) / Real.exp 1) := by linarith
    _ = 5 / Real.exp 1 * L ^ ((1 : ℝ) / 5) := by ring

/-- The three `L`-powers multiply as they should: `L^{1/5}·L^{1/5} = L^{2/5}`,
`L^{2/5}·L^{3/5} = L`, `L^{1/5}·L^{2/5} = L^{3/5}`. -/
private lemma rpow_fifths_mul {L : ℝ} (hL : 0 < L) :
    L ^ ((1 : ℝ) / 5) * L ^ ((1 : ℝ) / 5) = L ^ ((2 : ℝ) / 5)
      ∧ L ^ ((2 : ℝ) / 5) * L ^ ((3 : ℝ) / 5) = L
      ∧ L ^ ((1 : ℝ) / 5) * L ^ ((2 : ℝ) / 5) = L ^ ((3 : ℝ) / 5) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.rpow_add hL]; norm_num
  · rw [← Real.rpow_add hL]; norm_num
  · rw [← Real.rpow_add hL]; norm_num

/-- `a ≤ b → 0 ≤ c → a/c ≤ b/c` — the one division form §4/§5 need.  The `rpow`
denominators below have NO free positivity, so the `0 ≤ c` side condition is load-bearing. -/
private lemma div_le_div_same {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c := by
  have h : a * c⁻¹ ≤ b * c⁻¹ := mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hc)
  rwa [← div_eq_mul_inv, ← div_eq_mul_inv] at h

/-! ## §1 — the pin -/

/-- **The R2 pin: `y₂ = exp(L^{2/5})`.**  Stated as a function of `L` (the corpus writes its
own pin as `y = L⁴`, also a function of `L`), so `y₂ = ypin2 (log k)` at scale `k`. -/
def ypin2 (L : ℝ) : ℝ := Real.exp (L ^ ((2 : ℝ) / 5))

/-- **The R2 shift: `η₂ = 1/log y₂ = L^{−2/5}`.**  Given in closed form; `eta2_eq_inv_log`
is the identification with `1/log y₂` that every corpus binder asks for. -/
def eta2 (L : ℝ) : ℝ := L ^ (-((2 : ℝ) / 5))

/-- **The R2 truncation height: `T*₂ = y₂·k^{η₂}`.**  `FarStar.Tstar`'s shape at the new pin.
`Tstar2_eq_exp` evaluates it: `T*₂ = exp(L^{2/5} + L^{3/5})` at `L = log k`. -/
def Tstar2 (k L : ℝ) : ℝ := ypin2 L * k ^ eta2 L

/-- **The master gate `exp 32768`** (`L ≥ 2¹⁵`), chosen so that `L^{1/5} ≥ 8`,
`L^{2/5} ≥ 64`, `L^{3/5} ≥ 512` are EXACT numerals at the gate. -/
def pin2Gate : ℝ := Real.exp 32768

lemma pin2Gate_pos : 0 < pin2Gate := Real.exp_pos _

/-! ## §2 — the gates (law #253: every gate in-statement, every threshold explicit) -/

/-- `log y₂ = L^{2/5}` — unconditional (`log ∘ exp`).  This is the identity that makes the
whole family a re-instantiation rather than a re-derivation. -/
theorem log_ypin2 (L : ℝ) : Real.log (ypin2 L) = L ^ ((2 : ℝ) / 5) := by
  unfold ypin2; exact Real.log_exp _

lemma ypin2_pos (L : ℝ) : 0 < ypin2 L := Real.exp_pos _

/-- `η₂ = 1/log y₂` — the corpus's `hη` binder, discharged in closed form for `L > 0`. -/
theorem eta2_eq_inv_log {L : ℝ} (hL : 0 < L) : eta2 L = 1 / Real.log (ypin2 L) := by
  rw [log_ypin2, eta2, Real.rpow_neg hL.le, one_div]

lemma eta2_pos {L : ℝ} (hL : 0 < L) : 0 < eta2 L := Real.rpow_pos_of_pos hL _

/-- **The `L`-power page at the gate.**  `L ≥ 32768` gives the three exact numerals. -/
theorem pin2_powers {L : ℝ} (hL : 32768 ≤ L) :
    8 ≤ L ^ ((1 : ℝ) / 5) ∧ 64 ≤ L ^ ((2 : ℝ) / 5) ∧ 512 ≤ L ^ ((3 : ℝ) / 5) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← gate_rpow_fifth]; exact Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  · rw [← gate_rpow_two_fifths]; exact Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  · rw [← gate_rpow_three_fifths]; exact Real.rpow_le_rpow (by norm_num) hL (by norm_num)

/-- **THE `y₂` GATE BUNDLE.**  Everything the §8.3 chain asks of a pin, at `y₂`, from the
single hypothesis `exp 32768 ≤ k`:

`0 < k`, `L ≥ 32768`, `L^{2/5} ≥ 64`, `log y₂ = L^{2/5}`, `η₂ = 1/log y₂`, `0 < η₂`,
`η₂ ≤ 1/64`, `1/L < η₂`, `e ≤ y₂`, `131072 ≤ y₂`, `y₂ ≤ √k`, `√L ≤ y₂`, `y₂ ≤ k`.

Compare `FarClose.pin_basic64F`, whose `y = L⁴` analogues these replace verbatim in shape.
The two that the old pin got only asymptotically — `y ≤ √X` (`logpow4_le_sqrt_ev'`) and
`√(log X) ≤ y` — are NUMERAL facts here. -/
theorem pin2_basic {k L : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k) :
    0 < k ∧ 32768 ≤ L ∧ 64 ≤ L ^ ((2 : ℝ) / 5) ∧ Real.log (ypin2 L) = L ^ ((2 : ℝ) / 5)
      ∧ eta2 L = 1 / Real.log (ypin2 L) ∧ 0 < eta2 L ∧ eta2 L ≤ 1 / 64 ∧ 1 / L < eta2 L
      ∧ Real.exp 1 ≤ ypin2 L ∧ (131072 : ℝ) ≤ ypin2 L ∧ ypin2 L ≤ Real.sqrt k
      ∧ Real.sqrt L ≤ ypin2 L ∧ ypin2 L ≤ k := by
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le pin2Gate_pos hk
  have hkbig : (32769 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (32768 : ℝ)]
  have hL32 : (32768 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 32768]
    exact Real.log_le_log (Real.exp_pos 32768) hk
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨h15, h25, h35⟩ := pin2_powers hL32
  obtain ⟨-, hmul25, -⟩ := rpow_fifths_mul hL0
  have hlogy : Real.log (ypin2 L) = L ^ ((2 : ℝ) / 5) := log_ypin2 L
  have hη : eta2 L = 1 / Real.log (ypin2 L) := eta2_eq_inv_log hL0
  have hη0 : (0 : ℝ) < eta2 L := eta2_pos hL0
  have hη64 : eta2 L ≤ 1 / 64 := by
    rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 64)]
    linarith
  have hηL : 1 / L < eta2 L := by
    rw [hη, hlogy, div_lt_div_iff₀ hL0 (by linarith)]
    nlinarith
  -- `2·L^{2/5} ≤ L`, the shape both `y₂ ≤ √k` and `η₂ ≤ 1/2` come from
  have htwo : 2 * L ^ ((2 : ℝ) / 5) ≤ L := by nlinarith
  have hylo : Real.exp 1 ≤ ypin2 L := Real.exp_le_exp.mpr (by linarith)
  have hybig : (131072 : ℝ) ≤ ypin2 L := by
    have h1 : Real.exp 12 ≤ ypin2 L := Real.exp_le_exp.mpr (by linarith)
    have h2 : (131072 : ℝ) ≤ Real.exp 12 := by
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h12 : Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      have hpw := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he 12
      rw [h12]
      norm_num at hpw ⊢
      linarith
    linarith
  have hysq : ypin2 L ≤ Real.sqrt k := by
    have hkey : ypin2 L ^ 2 ≤ k := by
      have h1 : ypin2 L ^ 2 = Real.exp (2 * L ^ ((2 : ℝ) / 5)) := by
        unfold ypin2; rw [← Real.exp_nat_mul]; norm_num
      rw [h1, show k = Real.exp L from by rw [hL, Real.exp_log hk0]]
      exact Real.exp_le_exp.mpr htwo
    exact (Real.le_sqrt (ypin2_pos L).le hk0.le).mpr hkey
  have hsqL : Real.sqrt L ≤ ypin2 L := by
    have hlogL : Real.log L ≤ L ^ ((2 : ℝ) / 5) := by
      have h1 := log_le_rpow_fifth hL0
      obtain ⟨hm, -, -⟩ := rpow_fifths_mul hL0
      have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h2 : 5 / Real.exp 1 * L ^ ((1 : ℝ) / 5) ≤ L ^ ((2 : ℝ) / 5) := by
        rw [← hm, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    have hLy : L ≤ ypin2 L := by
      have h1 : Real.exp (Real.log L) ≤ ypin2 L := Real.exp_le_exp.mpr hlogL
      rwa [Real.exp_log hL0] at h1
    have hsq : Real.sqrt L ≤ L := by
      have h1 : Real.sqrt L ≤ Real.sqrt (L * L) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_mul_self hL0.le] at h1
    linarith
  have hyk : ypin2 L ≤ k := by
    have h1 : Real.sqrt k ≤ k := by
      have h2 : Real.sqrt k ≤ Real.sqrt (k * k) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_mul_self hk0.le] at h2
    linarith
  exact ⟨hk0, hL32, h25, hlogy, hη, hη0, hη64, hηL, hylo, hybig, hysq, hsqL, hyk⟩

/-- `10 ≤ y₂` — the `LambdaMass` gate, from `131072 ≤ y₂`. -/
theorem ten_le_ypin2 {k L : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k) :
    (10 : ℝ) ≤ ypin2 L := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hy, -, -, -⟩ := pin2_basic hk hL
  linarith

/-- **The `widthKamp` amplitude at `A₂ := (y₂/2)^{1/8}` — the HALF that improves.**
`GradeConst.pin_width_gates`'s width floor `4 ≤ (y/2)^{1/8}` holds with enormous room at
`y₂` (`≥ (e^{64}/2)^{1/8}`), versus the old pin's tight `(L⁴/2)^{1/8}`.

**But see `width_pin_gate_bandwidth_fails_pin2` below: the OTHER half of
`pin_width_gates` — `y ≤ 2·(2(X+h)/h)⁸` at `h = X/√L` — is FALSE at `y₂`.**  The width
route is pinned to `y = L⁴` through its bandwidth gate, not only through `A`. -/
theorem width_pin_gates_pin2 {k L : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k) :
    (4 : ℝ) ≤ (ypin2 L / 2) ^ ((1 : ℝ) / 8) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hy, -, -, -⟩ := pin2_basic hk hL
  have h1 : (65536 : ℝ) ≤ ypin2 L / 2 := by linarith
  have h2 : (4 : ℝ) = (65536 : ℝ) ^ ((1 : ℝ) / 8) := by
    have h3 : (4 : ℝ) ^ (8 : ℕ) = 65536 := by norm_num
    rw [← h3, ← Real.rpow_natCast (4 : ℝ) 8, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [h2]
  exact Real.rpow_le_rpow (by norm_num) h1 (by norm_num)

private lemma gate20_rpow_fifth : (1048576 : ℝ) ^ ((1 : ℝ) / 5) = 16 := by
  rw [rpow_div_five (y := 16) (by norm_num) (by norm_num) 1, Real.rpow_one]

private lemma gate20_rpow_two_fifths : (1048576 : ℝ) ^ ((2 : ℝ) / 5) = 256 := by
  rw [rpow_div_five (y := 16) (by norm_num) (by norm_num) 2,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- **⟦V6b⟧ FREEZE RISK (ii), THE ONE REAL HIT: the width route's BANDWIDTH gate breaks at
`y₂`.**  `GradeConst.pin_width_gates`'s fourth conjunct is

  `y ≤ 2·(2(X+h)/h)⁸ = 2·(2(√L+1))⁸ ≈ 512·L⁴`   (at the corpus pin `h = X/√L`),

a genuine CONSTRAINT — the width `A = (y/2)^{1/8}` may not exceed the kernel's effective
bandwidth `T₀ = 2(X+h)/h`.  At `y = L⁴` it holds with a factor `512` to spare; at
`y₂ = exp(L^{2/5})` it FAILS, and not marginally:

  `2·(2(√L+1))⁸ < y₂`  for every `L ≥ 2²⁰`.

So the `GradeConst`/`GradeWindowC` width layer does NOT re-instantiate at `y₂` with `h`
still pinned at `X/√L`; a pin-2 width route would have to re-pin `h` (or read `A` off `T₀`
instead of off `y`).  Recorded here rather than papered over: the far arm (§4) and the
payoff (§5) are unaffected — they never use the width gate. -/
theorem width_pin_gate_bandwidth_fails_pin2 {L : ℝ} (hL : 1048576 ≤ L) :
    2 * (2 * (Real.sqrt L + 1)) ^ 8 < ypin2 L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hs1 : (1 : ℝ) ≤ Real.sqrt L := by nlinarith
  have h15 : (16 : ℝ) ≤ L ^ ((1 : ℝ) / 5) := by
    rw [← gate20_rpow_fifth]; exact Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  have h25 : (256 : ℝ) ≤ L ^ ((2 : ℝ) / 5) := by
    rw [← gate20_rpow_two_fifths]; exact Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  obtain ⟨hm, -, -⟩ := rpow_fifths_mul hL0
  have hv0 : (0 : ℝ) < L ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hL0 _
  -- (a) the polynomial majorant `2·(2(√L+1))⁸ ≤ 131072·L⁴`
  have hpoly : 2 * (2 * (Real.sqrt L + 1)) ^ 8 ≤ 131072 * L ^ 4 := by
    have h1 : (2 * (Real.sqrt L + 1)) ^ 8 ≤ (4 * Real.sqrt L) ^ 8 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 8
    have h2 : (4 * Real.sqrt L) ^ 8 = 65536 * L ^ 4 := by
      have h3 : (Real.sqrt L) ^ 8 = L ^ 4 := by
        have h4 : (Real.sqrt L) ^ 8 = (Real.sqrt L * Real.sqrt L) ^ 4 := by ring
        rw [h4, hsq]
      calc (4 * Real.sqrt L) ^ 8 = 65536 * (Real.sqrt L) ^ 8 := by ring
        _ = 65536 * L ^ 4 := by rw [h3]
    linarith
  -- (b) `log(131072·L⁴) < L^{2/5}`
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hb : 16 * L ^ ((1 : ℝ) / 5) ≤ L ^ ((2 : ℝ) / 5) := by nlinarith
  have hlog := log_le_rpow_fifth hL0
  have heq : 4 * (5 / Real.exp 1 * L ^ ((1 : ℝ) / 5)) = 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5) := by
    ring
  have h1 : 4 * Real.log L ≤ 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5) := by rw [← heq]; linarith
  have hcoef : (1.25 : ℝ) / Real.exp 1 ≤ 0.46 := by rw [div_le_iff₀ he0]; linarith
  have h2 : 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5) ≤ 0.46 * L ^ ((2 : ℝ) / 5) := by
    have h3 : 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5)
        = 1.25 / Real.exp 1 * (16 * L ^ ((1 : ℝ) / 5)) := by ring
    have h4 : 1.25 / Real.exp 1 * (16 * L ^ ((1 : ℝ) / 5))
        ≤ 1.25 / Real.exp 1 * L ^ ((2 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h5 : 1.25 / Real.exp 1 * L ^ ((2 : ℝ) / 5) ≤ 0.46 * L ^ ((2 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_right hcoef (by linarith)
    rw [h3]; linarith
  have hc : Real.log 131072 ≤ 12 := by
    have hexp12 : (131072 : ℝ) ≤ Real.exp 12 := by
      have he27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
      have h12 : Real.exp 12 = Real.exp 1 ^ (12 : ℕ) := by
        rw [← Real.exp_nat_mul]; norm_num
      have hpw := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7) he27 12
      rw [h12]
      norm_num at hpw ⊢
      linarith
    have h6 : Real.log 131072 ≤ Real.log (Real.exp 12) :=
      Real.log_le_log (by norm_num) hexp12
    rwa [Real.log_exp] at h6
  have hkey : Real.log (131072 * L ^ 4) < L ^ ((2 : ℝ) / 5) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    linarith
  -- (c) exponentiate
  have hstep : (131072 : ℝ) * L ^ 4 < ypin2 L := by
    have h7 : (131072 : ℝ) * L ^ 4 = Real.exp (Real.log (131072 * L ^ 4)) :=
      (Real.exp_log (by positivity)).symm
    rw [h7]
    exact Real.exp_lt_exp.mpr hkey
  linarith

/-! ## §3 — the `S1′` representation RE-INSTANTIATED at `y₂`

`LambdaMass.prop21_unconditional_uniform_absC` is already FREE in `y`: its three `y`-gates
are `10 ≤ y`, `y ≤ √X`, `√(log X) ≤ y`, plus `η = 1/log y` and `0 < c₀ − 2η`.  §2 discharges
all five at `y₂`.  Nothing is cloned — the landed stone is instantiated. -/

/-- **A-7b (iii) at the R2 pin (`prop21_uniform_at_scale_pin2`).**  The datum-hoisted uniform
`S1′` bound at

  `h = X/√(log X)`,  `c₀ = 1 + 1/log X`,  `y = y₂ = exp((log X)^{2/5})`,  `η = η₂`,

with the SAME `(C_E, C_R)` as the corpus pin — they are supplied by
`prop21_unconditional_uniform_absC` before any pin is named.  The error's `log y` factor is
now literally `(log X)^{2/5}` (this is the E-slot of §6).

Twin of `LambdaMass.prop21_uniform_at_scale_absC`; the ONLY differences are the pin and the
fact that `y₂ ≤ √X` is a numeral fact here, so `logpow4_le_sqrt_ev'` is not needed. -/
theorem prop21_uniform_at_scale_pin2 :
    ∃ X₀ C_E C_R : ℝ, 0 ≤ C_E ∧ 0 ≤ C_R ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ : ℝ), ∀ X : ℝ, X₀ ≤ X →
      ‖(∑' n, seamCoeff (ellLin g) (fun _ => 1) t₀ n
            * (hatK X (X / Real.sqrt (Real.log X)) n : ℂ))
          - prop21RHS (fun p => g p * (p : ℂ) ^ (-(t₀ : ℂ) * I)) t₀ X
              (X / Real.sqrt (Real.log X)) (1 + 1 / Real.log X)
              (ypin2 (Real.log X)) (eta2 (Real.log X))‖
        ≤ C_E * ((X + X / Real.sqrt (Real.log X))
              / Real.log (X + X / Real.sqrt (Real.log X))) * (Real.log X) ^ ((2 : ℝ) / 5)
          + C_R * (X / Real.log X) * (Real.log X) ^ ((2 : ℝ) / 5) := by
  obtain ⟨X₀, C_E, C_R, hCE0, hCR0, hbound⟩ := prop21_unconditional_uniform_absC
  refine ⟨max X₀ pin2Gate, C_E, C_R, hCE0, hCR0, ?_⟩
  intro g hg t₀ X hXlb
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hXlb
  have hXg : pin2Gate ≤ X := le_trans (le_max_right _ _) hXlb
  obtain ⟨hX0, hL32, h25, hlogy, hη, hη0, hη64, -, -, hy131072, hysq, hsqL, -⟩ :=
    pin2_basic hXg rfl
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hc₀ : (1 : ℝ) < 1 + 1 / Real.log X := by
    have hpos : (0 : ℝ) < 1 / Real.log X := by positivity
    linarith
  have hc' : (0 : ℝ) < 1 + 1 / Real.log X - 2 * eta2 (Real.log X) := by
    have hpos : (0 : ℝ) < 1 / Real.log X := by positivity
    linarith
  have hmain := hbound g hg t₀ (X := X) (h := X / Real.sqrt (Real.log X))
    (c₀ := 1 + 1 / Real.log X) (y := ypin2 (Real.log X)) (η := eta2 (Real.log X))
    hX₀ rfl hc₀ hη hc' (by linarith) hysq hsqL
  rwa [hlogy] at hmain

/-! ## §4 — FarStar, WHOLE, at `y₂`

`FarClose`'s `far_kernel_bound_T` and `far_window_mass_le` and `SupClose`'s
`joint_supF_pin_at` all carry `hy : y = L⁴` as a hypothesis, so they are free in `T` but NOT
free in `y`.  Their INTERIORS are free in `y` — `TruncFactor.crossKerFar_le_tail`,
`WindowBridge.window_mass_product` and `PretSupply.supF_pret_pointwise` know nothing about a
pin.  §4 re-runs the three pages at `y₂` from those interiors.

**⟦V6b⟧ FREEZE RISK (i), DISCHARGED**: `supF_pret_pointwise`'s only `y`-hypotheses are
`e ≤ y` and `α, β ≤ 1/log y`; at `y₂` the first is `L^{2/5} ≥ 1` and the second is the
definition of `η₂`.  Its interior is pin-agnostic.

**The margin.**  The `k`-power cancellation is EXACT at `y₂` with the SAME residual `e^{−2}`
(`far_mass_cancel2`) — confirming ⟦V6b⟧'s "at ANY `y`" — and the far page improves from
`FarStar`'s `O(L^{−1/2}/log L)` to `O(L³/exp(L^{2/5}))`, i.e. faster than any power. -/

/-- The pin's amplitude ratio `4(k+h)/(h·T) = 4(√L+1)/T` at `h = k/√L`
(`FarClose`'s private `far_ratio_calcF`, re-derived). -/
private lemma far_ratio_calc2 {X s Q : ℝ} (hX : 0 < X) (hs : 0 < s) (hQ : 0 < Q) :
    4 * (X + X / s) / (X / s * Q) = 4 * (s + 1) / Q := by
  have hX' : X ≠ 0 := ne_of_gt hX
  have hs' : s ≠ 0 := ne_of_gt hs
  have hQ' : Q ≠ 0 := ne_of_gt hQ
  field_simp

/-- The pin's scale factor `(k+h)^{c₀} ≤ 9·k` (`GradeConst`'s private `pin_rpow_scale`,
re-derived at the pin-2 gate). -/
private lemma pin_rpow_scale2 {k h L c₀ : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k)
    (hh : h = k / Real.sqrt L) (hc₀ : c₀ = 1 + 1 / L) :
    (k + h) ^ c₀ ≤ 9 * k := by
  obtain ⟨hk0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hkexp : Real.exp 32768 ≤ k := hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt (by linarith)
  have hh0 : (0 : ℝ) < h := by rw [hh]; positivity
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (32768 : ℝ)]
  have hhk : h ≤ k / 8 := by
    rw [hh, div_le_div_iff₀ hs0 (by norm_num)]; nlinarith
  have hkh98 : k + h ≤ 9 / 8 * k := by linarith
  have hlogkh : Real.log (k + h) ≤ 2 * L := by
    have hsq : k + h ≤ k * k := by nlinarith
    have h1 : Real.log (k + h) ≤ Real.log (k * k) := Real.log_le_log hkh0 hsq
    rw [Real.log_mul hk0.ne' hk0.ne', ← hL] at h1
    linarith
  have he2 : Real.exp 2 ≤ 8 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hfrac : (k + h) ^ (1 / L : ℝ) ≤ 8 := by
    rw [Real.rpow_def_of_pos hkh0]
    have hexp : Real.log (k + h) * (1 / L) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hL0]; linarith
    calc Real.exp (Real.log (k + h) * (1 / L)) ≤ Real.exp 2 := Real.exp_le_exp.mpr hexp
      _ ≤ 8 := he2
  have hsplit : (k + h) ^ c₀ = (k + h) * (k + h) ^ (1 / L : ℝ) := by
    rw [hc₀, Real.rpow_add hkh0, Real.rpow_one]
  rw [hsplit]
  calc (k + h) * (k + h) ^ (1 / L : ℝ) ≤ (9 / 8 * k) * 8 :=
        mul_le_mul hkh98 hfrac (Real.rpow_nonneg hkh0.le _) (by linarith)
    _ = 9 * k := by ring

/-- **THE EXACT CANCELLATION AT `y₂` (`far_mass_cancel2`).**

  `(k/y₂)^{η₂−1/L}·y₂^{−1/L} = k^{η₂}/e²`.

Identical in form and in residual to `FarStar`'s `far_mass_cancel` at `y = L⁴`: the `ℓ¹`
excess IS a `k`-power `k^{η₂} = k^{1/log y₂}`, and the two leftovers `k^{−1/L}` and
`y₂^{−η₂}` are each exactly `e^{−1}`.  ⟦V6b⟧'s claim "the residual is `e^{−2}` at ANY `y`"
is therefore VERIFIED, not assumed: nothing in the identity mentions the pin's shape. -/
private lemma far_mass_cancel2 {k L : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k) :
    (k / ypin2 L) ^ (eta2 L - 1 / L) * (ypin2 L) ^ (-(1 / L))
      = k ^ eta2 L / (Real.exp 1 * Real.exp 1) := by
  obtain ⟨hk0, hL32, h25, hlogy, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hy0 : (0 : ℝ) < ypin2 L := ypin2_pos L
  have hune : L ^ ((2 : ℝ) / 5) ≠ 0 := by linarith
  have hηu : eta2 L = 1 / L ^ ((2 : ℝ) / 5) := by rw [eta2_eq_inv_log hL0, hlogy]
  rw [Real.rpow_def_of_pos (div_pos hk0 hy0), Real.rpow_def_of_pos hy0,
    Real.rpow_def_of_pos hk0, ← Real.exp_add,
    show Real.exp 1 * Real.exp 1 = Real.exp 2 from by rw [← Real.exp_add]; norm_num,
    ← Real.exp_sub, Real.log_div hk0.ne' hy0.ne', hlogy, ← hL, hηu]
  congr 1
  field_simp
  ring

/-- **F-2b at `y₂` (`far_window_mass_le2`).**  `WindowBridge.window_mass_product` at the two
lines of the far kernel, with the shifts `δ := η₂ − 1/L` (low) and `σ := 1/L` (high).  Twin
of `FarClose.far_window_mass_le`. -/
theorem far_window_mass_le2 {d : ℕ → ℂ} (hd : ∀ p, p.Prime → ‖d p‖ ≤ 1) {k L c₀ y η : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
        ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η))
      * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
        ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀)
      ≤ (Real.log 4 + 4) ^ 2 * ((k / y) ^ (η - 1 / L) * y ^ (-(1 / L)))
          * (min (Real.log (⌈k / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / (η - 1 / L))
              * min (Real.log (⌈k / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / (1 / L))) := by
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, hηL, hylo, -, -, -, hyk⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hy1 : (1 : ℝ) ≤ y := by
    rw [hy]; linarith [Real.exp_one_gt_d9, hylo]
  have hy0 : (0 : ℝ) < y := by linarith
  have hXy : (1 : ℝ) ≤ k / y := (one_le_div hy0).mpr (by rw [hy]; exact hyk)
  have hδ0 : (0 : ℝ) < η - 1 / L := by rw [hη]; linarith
  have hδ1 : η - 1 / L ≤ 1 := by
    have : (0 : ℝ) < 1 / L := by positivity
    rw [hη]; linarith
  have hσ0 : (0 : ℝ) < 1 / L := by positivity
  have hlow : 1 - (η - 1 / L) ≤ c₀ - η := by rw [hc₀]; ring_nf; linarith
  have hhigh : 1 + 1 / L ≤ c₀ := by rw [hc₀]
  exact window_mass_product d hd hy1 hXy hδ0 hδ1 hσ0 hlow hhigh

/-- **FS-2 at `y₂` — the far kernel value (`farKfarStar2`).**  `FarClose.far_kernel_bound_T`'s
right-hand side at the R2 pin (`y = y₂`, `c₀ = 1+1/L`, `η = η₂`, `h = k/√L`) and at the
truncation height `T := T*₂`. -/
def farKfarStar2 (d : ℕ → ℂ) (k L : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊,
      ‖lambdaLin (restrictAbove (ypin2 L) d) n‖ / (n : ℝ) ^ (1 + 1 / L - eta2 L))
    * (∑ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊,
        ‖lambdaLin (restrictAbove (ypin2 L) d) n‖ / (n : ℝ) ^ (1 + 1 / L))
    * ((k + k / Real.sqrt L) ^ (1 + 1 / L) * (4 * (Real.sqrt L + 1) / Tstar2 k L))

/-- **F-2 at `y₂`, at a FREE truncation height (`far_kernel_bound_T2`).**  The twin of
`FarClose.far_kernel_bound_T`, re-derived from `TruncFactor.crossKerFar_le_tail` (the
`y`-agnostic interior) because the landed stone pins `y = L⁴`. -/
theorem far_kernel_bound_T2 {d : ℕ → ℂ} {t₀' k L c₀ y η T : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (_hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) (hT : 0 < T) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar d k (k / Real.sqrt L) y c₀ t₀' α β T
        ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
              ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η))
            * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
              ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀)
            * ((k + k / Real.sqrt L) ^ c₀ * (4 * (Real.sqrt L + 1) / T)) := by
  intro α hα β hβ
  obtain ⟨hk0, hL32, -, -, -, hη0, hη64, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hkexp : Real.exp 32768 ≤ k := hk
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (32768 : ℝ)]
  have hX1 : (1 : ℝ) ≤ k := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hh0 : (0 : ℝ) < k / Real.sqrt L := by positivity
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hc : 0 < c₀ - α - β := by
    rw [hc₀]
    have h1 : α ≤ η := hα.2
    have h2 : β ≤ η := hβ.2
    rw [hη] at h1 h2
    linarith
  have hMm0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
      ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η) := window_mass_nonneg d k y _
  have hMp0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
      ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀ := window_mass_nonneg d k y _
  have hbm : ∀ τ : ℝ, ‖windowSum d k y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
          ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η) := by
    intro τ
    refine norm_windowSum_le_mass d k y (c₀ - η) ?_
    rw [show (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp]
    linarith [hβ.2]
  have hbp : ∀ τ : ℝ, ‖windowSum d k y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
          ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀ := by
    intro τ
    refine norm_windowSum_le_mass d k y c₀ ?_
    rw [show (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp]
    linarith [hβ.1]
  refine (crossKerFar_le_tail hX1 hh0 hc hT hMm0 hMp0 hbm hbp).trans ?_
  have hbase : (1 : ℝ) ≤ k + k / Real.sqrt L := by linarith
  have hbase0 : (0 : ℝ) < k + k / Real.sqrt L := by linarith
  have hsplit : 4 * (k + k / Real.sqrt L) ^ (c₀ - α - β + 1) / (k / Real.sqrt L * T)
      = (k + k / Real.sqrt L) ^ (c₀ - α - β)
        * (4 * (k + k / Real.sqrt L) / (k / Real.sqrt L * T)) := by
    rw [Real.rpow_add hbase0, Real.rpow_one]; ring
  rw [hsplit, far_ratio_calc2 hk0 hs0 hT]
  have hrpow : (k + k / Real.sqrt L) ^ (c₀ - α - β) ≤ (k + k / Real.sqrt L) ^ c₀ :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hα.1, hβ.1])
  have hamp : (0 : ℝ) ≤ 4 * (Real.sqrt L + 1) / T := by positivity
  gcongr

/-- **FS-2 at `y₂` — the `hKfar` binder (`far_kernel_bound_star2`).**  `far_kernel_bound_T2`
instantiated at `T := T*₂`.  The only input is `0 < T*₂`. -/
theorem far_kernel_bound_star2 {d : ℕ → ℂ} {t₀' k L c₀ y η : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar d k (k / Real.sqrt L) y c₀ t₀' α β (Tstar2 k L) ≤ farKfarStar2 d k L := by
  obtain ⟨hk0, -, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hT : 0 < Tstar2 k L := mul_pos (ypin2_pos L) (Real.rpow_pos_of_pos hk0 _)
  intro α hα β hβ
  have hmain := far_kernel_bound_T2 (d := d) (t₀' := t₀') hk hL hy hη hc₀ hT α hα β hβ
  subst hy
  subst hη
  subst hc₀
  exact hmain

/-- **`2·L⁴ ≤ y₂` at the gate** — the ONE growth fact the far margin needs.  `log(2L⁴)
= log 2 + 4·log L ≤ 0.94·L^{2/5}` via `log_le_rpow_fifth` and `L^{1/5} ≥ 8`. -/
theorem two_mul_pow_four_le_ypin2 {L : ℝ} (hL : 32768 ≤ L) : 2 * L ^ 4 ≤ ypin2 L := by
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨h15, h25, -⟩ := pin2_powers hL
  obtain ⟨hm, -, -⟩ := rpow_fifths_mul hL0
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : (2.7182818283 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hv0 : (0 : ℝ) < L ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hL0 _
  have hlog := log_le_rpow_fifth hL0
  have hb : 8 * L ^ ((1 : ℝ) / 5) ≤ L ^ ((2 : ℝ) / 5) := by nlinarith
  have hcoef : (2.5 : ℝ) / Real.exp 1 ≤ 0.92 := by
    rw [div_le_iff₀ he0]; linarith
  have hchain : 4 * Real.log L ≤ 0.92 * L ^ ((2 : ℝ) / 5) := by
    have heq : 4 * (5 / Real.exp 1 * L ^ ((1 : ℝ) / 5))
        = 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5) := by ring
    have h1 : 4 * Real.log L ≤ 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5) := by
      rw [← heq]; linarith
    have h2 : 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5)
        ≤ 2.5 / Real.exp 1 * L ^ ((2 : ℝ) / 5) := by
      have h3 : 20 / Real.exp 1 * L ^ ((1 : ℝ) / 5)
          = 2.5 / Real.exp 1 * (8 * L ^ ((1 : ℝ) / 5)) := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hb (by positivity)
    have h4 : 2.5 / Real.exp 1 * L ^ ((2 : ℝ) / 5) ≤ 0.92 * L ^ ((2 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_right hcoef (by linarith)
    linarith
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hkey : Real.log (2 * L ^ 4) ≤ L ^ ((2 : ℝ) / 5) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    linarith
  have h1 : (2 : ℝ) * L ^ 4 = Real.exp (Real.log (2 * L ^ 4)) :=
    (Real.exp_log (by positivity)).symm
  rw [h1]
  exact Real.exp_le_exp.mpr hkey

/-- **FS-3a at `y₂` — the `Kfar` numeral (`far_kfar_star2_le`).**

  `Kfar(T*₂) ≤ 720·(log 4 + 4)²·k·L²/y₂`.

The four numerals: `1 + 2/(η₂−1/L) ≤ 5·L^{2/5}` (from `1/L ≤ η₂/2`, i.e. `L^{3/5} ≥ 2`),
`2 + L ≤ 2L`, `(k+h)^{c₀} ≤ 9k`, `4(√L+1) ≤ 8√L`; the cancellation `far_mass_cancel2`, which
turns `[(k/y₂)^{η₂−1/L}·y₂^{−1/L}]/T*₂` into `1/(e²·y₂)`; and `L^{2/5} ≤ √L`, which collapses
`L^{2/5}·L·√L` to `L²`.  The denominator is `y₂ = exp(L^{2/5})` — SUPER-polynomial, versus
`FarStar`'s `L³`. -/
theorem far_kfar_star2_le {d : ℕ → ℂ} (hd : ∀ p, p.Prime → ‖d p‖ ≤ 1) {k L : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) :
    farKfarStar2 d k L ≤ 720 * (Real.log 4 + 4) ^ 2 * (k * L ^ 2 / ypin2 L) := by
  obtain ⟨hk0, hL32, h25, hlogy, -, hη0, hη64, hηL, -, -, -, -, -⟩ := pin2_basic hk hL
  obtain ⟨-, -, h35⟩ := pin2_powers hL32
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]; exact Real.sqrt_le_sqrt (by linarith)
  have hy0 : (0 : ℝ) < ypin2 L := ypin2_pos L
  have hkη0 : (0 : ℝ) < k ^ eta2 L := Real.rpow_pos_of_pos hk0 _
  have hT0 : (0 : ℝ) < Tstar2 k L := mul_pos hy0 hkη0
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- the `ℓ¹` shift: `1/L ≤ η₂/2`, so `1 + 2/(η₂−1/L) ≤ 5·L^{2/5}`
  have hηval : eta2 L = 1 / L ^ ((2 : ℝ) / 5) := by rw [eta2_eq_inv_log hL0, hlogy]
  have htwo : 2 * L ^ ((2 : ℝ) / 5) ≤ L := by
    obtain ⟨-, hmul, -⟩ := rpow_fifths_mul hL0
    nlinarith
  have hhalf : 1 / L ≤ eta2 L / 2 := by
    rw [hηval, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hgap0 : (0 : ℝ) < eta2 L - 1 / L := by linarith
  have hM1 : min (Real.log (⌈k / ypin2 L⌉₊ : ℝ) + (Real.log 4 + 4))
      (1 + 2 / (eta2 L - 1 / L)) ≤ 5 * L ^ ((2 : ℝ) / 5) := by
    refine le_trans (min_le_right _ _) ?_
    have h1 : 2 / (eta2 L - 1 / L) ≤ 2 / (eta2 L / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    have h2 : 2 / (eta2 L / 2) = 4 * L ^ ((2 : ℝ) / 5) := by
      rw [hηval, div_div, one_div, div_inv_eq_mul]; ring
    rw [h2] at h1
    linarith
  have hM2 : min (Real.log (⌈k / ypin2 L⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / (1 / L))
      ≤ 2 * L := by
    refine le_trans (min_le_right _ _) ?_
    rw [one_div_one_div]; linarith
  have hM10 : (0 : ℝ) ≤ min (Real.log (⌈k / ypin2 L⌉₊ : ℝ) + (Real.log 4 + 4))
      (1 + 2 / (eta2 L - 1 / L)) :=
    le_min window_grade_pos.le (by positivity)
  have hM20 : (0 : ℝ) ≤ min (Real.log (⌈k / ypin2 L⌉₊ : ℝ) + (Real.log 4 + 4))
      (2 + 1 / (1 / L)) := by
    refine le_min window_grade_pos.le ?_
    rw [one_div_one_div]; linarith
  -- the mass product, cancelled
  have hMass := far_window_mass_le2 hd hk hL rfl rfl rfl
  have hWW : (∑ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊,
        ‖lambdaLin (restrictAbove (ypin2 L) d) n‖ / (n : ℝ) ^ (1 + 1 / L - eta2 L))
      * (∑ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊,
        ‖lambdaLin (restrictAbove (ypin2 L) d) n‖ / (n : ℝ) ^ (1 + 1 / L))
      ≤ (Real.log 4 + 4) ^ 2 * (k ^ eta2 L / (Real.exp 1 * Real.exp 1))
          * (5 * L ^ ((2 : ℝ) / 5) * (2 * L)) := by
    refine hMass.trans ?_
    rw [far_mass_cancel2 hk hL]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hM1 hM2 hM20 (by positivity)) ?_
    positivity
  have hWW0 : (0 : ℝ) ≤ (∑ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊,
        ‖lambdaLin (restrictAbove (ypin2 L) d) n‖ / (n : ℝ) ^ (1 + 1 / L - eta2 L))
      * (∑ n ∈ Finset.Ioo ⌊ypin2 L⌋₊ ⌈k / ypin2 L⌉₊,
        ‖lambdaLin (restrictAbove (ypin2 L) d) n‖ / (n : ℝ) ^ (1 + 1 / L)) :=
    mul_nonneg (window_mass_nonneg d k (ypin2 L) _) (window_mass_nonneg d k (ypin2 L) _)
  -- the amplitude × tail factor
  have hfac : (k + k / Real.sqrt L) ^ (1 + 1 / L) * (4 * (Real.sqrt L + 1) / Tstar2 k L)
      ≤ 9 * k * (8 * Real.sqrt L / (ypin2 L * k ^ eta2 L)) := by
    have hsc : (k + k / Real.sqrt L) ^ (1 + 1 / L) ≤ 9 * k := pin_rpow_scale2 hk hL rfl rfl
    have hrat : 4 * (Real.sqrt L + 1) / Tstar2 k L
        ≤ 8 * Real.sqrt L / (ypin2 L * k ^ eta2 L) := by
      have hTeq : Tstar2 k L = ypin2 L * k ^ eta2 L := rfl
      have hden : (0 : ℝ) < ypin2 L * k ^ eta2 L := by positivity
      rw [hTeq, div_le_div_iff₀ hden hden]
      nlinarith [hs8, hden]
    refine mul_le_mul hsc hrat ?_ (by positivity)
    exact div_nonneg (by positivity) hT0.le
  have hfac0 : (0 : ℝ) ≤ (k + k / Real.sqrt L) ^ (1 + 1 / L)
      * (4 * (Real.sqrt L + 1) / Tstar2 k L) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (div_nonneg (by positivity) hT0.le)
  have hB0 : (0 : ℝ) ≤ (Real.log 4 + 4) ^ 2 * (k ^ eta2 L / (Real.exp 1 * Real.exp 1))
      * (5 * L ^ ((2 : ℝ) / 5) * (2 * L)) := by positivity
  -- assemble
  unfold farKfarStar2
  refine (mul_le_mul hWW hfac hfac0 hB0).trans ?_
  have hkηne : k ^ eta2 L ≠ 0 := ne_of_gt hkη0
  have hyne : ypin2 L ≠ 0 := ne_of_gt hy0
  have hene : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have hEq : (Real.log 4 + 4) ^ 2 * (k ^ eta2 L / (Real.exp 1 * Real.exp 1))
        * (5 * L ^ ((2 : ℝ) / 5) * (2 * L))
        * (9 * k * (8 * Real.sqrt L / (ypin2 L * k ^ eta2 L)))
      = 720 * (Real.log 4 + 4) ^ 2 * (k * (L ^ ((2 : ℝ) / 5) * Real.sqrt L * L) / ypin2 L)
          * (1 / (Real.exp 1 * Real.exp 1)) := by
    field_simp
    ring
  rw [hEq]
  -- `L^{2/5}·√L·L ≤ L²` and `1/e² ≤ 1`
  have hsqrt : L ^ ((2 : ℝ) / 5) ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hcollapse : L ^ ((2 : ℝ) / 5) * Real.sqrt L * L ≤ L ^ 2 := by
    have h1 : L ^ ((2 : ℝ) / 5) * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
      mul_le_mul_of_nonneg_right hsqrt hs0.le
    have h2 : L ^ ((2 : ℝ) / 5) * Real.sqrt L ≤ L := by
      calc L ^ ((2 : ℝ) / 5) * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L := h1
        _ = L := hsq
    calc L ^ ((2 : ℝ) / 5) * Real.sqrt L * L ≤ L * L :=
          mul_le_mul_of_nonneg_right h2 hL0.le
      _ = L ^ 2 := by ring
  have hone : 1 / (Real.exp 1 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.exp_one_gt_d9, Real.exp_pos 1]
  have hstep : 720 * (Real.log 4 + 4) ^ 2
      * (k * (L ^ ((2 : ℝ) / 5) * Real.sqrt L * L) / ypin2 L)
      ≤ 720 * (Real.log 4 + 4) ^ 2 * (k * L ^ 2 / ypin2 L) := by
    have hc0 : (0 : ℝ) ≤ 720 * (Real.log 4 + 4) ^ 2 := by positivity
    refine mul_le_mul_of_nonneg_left ?_ hc0
    exact div_le_div_same (mul_le_mul_of_nonneg_left hcollapse hk0.le) hy0.le
  have hA0 : (0 : ℝ) ≤ 720 * (Real.log 4 + 4) ^ 2
      * (k * (L ^ ((2 : ℝ) / 5) * Real.sqrt L * L) / ypin2 L) := by positivity
  calc 720 * (Real.log 4 + 4) ^ 2 * (k * (L ^ ((2 : ℝ) / 5) * Real.sqrt L * L) / ypin2 L)
        * (1 / (Real.exp 1 * Real.exp 1))
      ≤ 720 * (Real.log 4 + 4) ^ 2
          * (k * (L ^ ((2 : ℝ) / 5) * Real.sqrt L * L) / ypin2 L) * 1 :=
        mul_le_mul_of_nonneg_left hone hA0
    _ = 720 * (Real.log 4 + 4) ^ 2
          * (k * (L ^ ((2 : ℝ) / 5) * Real.sqrt L * L) / ypin2 L) := mul_one _
    _ ≤ 720 * (Real.log 4 + 4) ^ 2 * (k * L ^ 2 / ypin2 L) := hstep

/-- **The crown's currency, floored** (`FarStar`'s private `log_price_floor`, re-derived). -/
private lemma log_price_floor2 {X L : ℝ} (hXe : Real.exp 1 ≤ X) (hXL : Real.log X ≤ 2 * L) :
    1 / (2 * L) ≤ Real.log X ^ (-(1 / (32 * Real.exp 1))) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hu1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hXe
  have hu0 : (0 : ℝ) < Real.log X := by linarith
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have ha1 : 1 / (32 * Real.exp 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h1 : Real.log X ^ (-(1 : ℝ)) ≤ Real.log X ^ (-(1 / (32 * Real.exp 1))) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
  have h2 : Real.log X ^ (-(1 : ℝ)) = (Real.log X)⁻¹ := by
    rw [Real.rpow_neg hu0.le, Real.rpow_one]
  have h3 : 1 / (2 * L) ≤ (Real.log X)⁻¹ := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hu0 hXL
  rw [h2] at h1
  linarith

/-- **The far arm's ABSOLUTE constant at `T*₂`** — `Cfar₂ = (720/π)·C_S·C_F·e^{24/e}·
(log 4+4)²`.  No `k`, no `X`, no `L`. -/
def farCStar2 : ℝ := 720 * rhsCSF * Real.exp (24 / Real.exp 1) * (Real.log 4 + 4) ^ 2 / Real.pi

lemma farCStar2_nonneg : 0 ≤ farCStar2 := by
  have h := rhsCSF_pos
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  unfold farCStar2
  positivity

/-- **FS-3 at `y₂` — THE FAR SOCKET (`hfar_star2`).**  `FarClose.rhs_grade_at_scale_closed`'s
`hfar` binder, discharged at `T := T*₂`, with `Cfar := farCStar2` absolute:

  `(1/π)·η₂²·(Ffar·Kfar(T*₂)) ≤ farCStar2·k·(log X)^{−1/(32e)}`.

The page: `Ffar = farFbound L = C_S·C_F·e^{24/e}·L` (UNCHANGED — `far_supF_bound2` shows the
`σ`-sup page does not move with the pin), `η₂² ≤ 1`, `Kfar(T*₂)` by `far_kfar_star2_le`, and
the crown's currency floored by `log_price_floor2`.  The residual margin is `2L⁴/y₂ ≤ 1`
(`two_mul_pow_four_le_ypin2`) — versus `FarStar`'s `2/(√L·log L)`: the same socket, with an
exponentially larger margin. -/
theorem hfar_star2 {d : ℕ → ℂ} (hd : ∀ p, p.Prime → ‖d p‖ ≤ 1) {k L y η X : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (_hy : y = ypin2 L) (hη : η = eta2 L)
    (hXe : Real.exp 1 ≤ X) (hX2k : X ≤ 2 * k) :
    (1 / Real.pi) * (η ^ 2 * (farFbound L * farKfarStar2 d k L))
      ≤ farCStar2 * k * Real.log X ^ (-(1 / (32 * Real.exp 1))) := by
  obtain ⟨hk0, hL32, h25, -, -, hη0, hη64, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hy0 : (0 : ℝ) < ypin2 L := ypin2_pos L
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCSF : (0 : ℝ) < rhsCSF := rhsCSF_pos
  -- the crown's currency, floored
  have hlogX : Real.log X ≤ 2 * L := by
    have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
    have h1 : Real.log X ≤ Real.log (2 * k) := Real.log_le_log hX0 hX2k
    rw [Real.log_mul (by norm_num) hk0.ne', ← hL] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith
  have hfloor := log_price_floor2 hXe hlogX
  have hC0 : (0 : ℝ) ≤ farCStar2 * k := mul_nonneg farCStar2_nonneg hk0.le
  have hK := far_kfar_star2_le hd hk hL
  have hFnn : (0 : ℝ) ≤ farFbound L := farFbound_nonneg hL0.le
  have hηsq : η ^ 2 ≤ 1 := by rw [hη]; nlinarith
  have hηsq0 : (0 : ℝ) ≤ η ^ 2 := by positivity
  have hmargin : 2 * L ^ 4 ≤ ypin2 L := two_mul_pow_four_le_ypin2 hL32
  calc (1 / Real.pi) * (η ^ 2 * (farFbound L * farKfarStar2 d k L))
      ≤ (1 / Real.pi) * (η ^ 2 * (farFbound L
          * (720 * (Real.log 4 + 4) ^ 2 * (k * L ^ 2 / ypin2 L)))) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK hFnn) hηsq0)
          (by positivity)
    _ = farCStar2 * k * (η ^ 2 * L ^ 3 / ypin2 L) := by
        unfold farFbound farCStar2
        field_simp
    _ ≤ farCStar2 * k * (1 / (2 * L)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC0
        rw [div_le_div_iff₀ hy0 (by linarith)]
        nlinarith [hmargin, hηsq, hηsq0, pow_pos hL0 3, pow_pos hL0 4]
    _ ≤ farCStar2 * k * Real.log X ^ (-(1 / (32 * Real.exp 1))) :=
        mul_le_mul_of_nonneg_left hfloor hC0

/-! ### §4f — the `supF` page at `y₂` (⟦V6b⟧ FREEZE RISK (i)) -/

/-- `rhsFbound 0 L σ ≤ farFbound L` on `σL ≥ 1` (`FarClose`'s private `rhsFbound_zero_le`,
re-derived).  Note it is `y`-FREE: the `σ`-sup of the `M = 0` majorant over
`σ ∈ [1/L, η+1/L]` is `farFbound L` at EVERY pin, because the sup is attained at the LEFT
endpoint `σ = 1/L`, which does not move.  This is why the far `F`-page is unchanged at
`y₂`. -/
private lemma rhsFbound_zero_le2 {L σ : ℝ} (hσ0 : 0 < σ) (hσL : 1 ≤ σ * L) :
    rhsFbound 0 L σ ≤ farFbound L := by
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hσL0 : (0 : ℝ) < σ * L := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (σ * L) := Real.log_nonneg hσL
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hkey : -(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48)
      = 1 / Real.exp 1 * Real.log (σ * L) + 24 / Real.exp 1 := by
    field_simp
    ring
  have h2c : 1 / Real.exp 1 ≤ 1 := by rw [div_le_one he0]; linarith
  have hexp_le : -(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48)
      ≤ Real.log (σ * L) + 24 / Real.exp 1 := by
    rw [hkey]
    nlinarith
  have hstep : Real.exp (-(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48))
      ≤ σ * L * Real.exp (24 / Real.exp 1) := by
    have hrw : σ * L * Real.exp (24 / Real.exp 1)
        = Real.exp (Real.log (σ * L) + 24 / Real.exp 1) := by
      rw [Real.exp_add, Real.exp_log hσL0]
    rw [hrw]
    exact Real.exp_le_exp.mpr hexp_le
  have hpos : (0 : ℝ) ≤ rhsCSF * (1 / σ) := by
    have := rhsCSF_pos; positivity
  unfold rhsFbound farFbound
  calc rhsCSF * (1 / σ) * Real.exp (-(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48))
      ≤ rhsCSF * (1 / σ) * (σ * L * Real.exp (24 / Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hstep hpos
    _ = rhsCSF * Real.exp (24 / Real.exp 1) * L := by field_simp

/-- **S-A at `y₂` — the pointwise pin `supF` (`joint_supF_pin_at2`).**  `SupClose`'s
`joint_supF_pin_at` re-derived at the R2 pin from `PretSupply.supF_pret_pointwise`, whose
interior asks only `e ≤ y` and `α, β ≤ 1/log y` — both are DEFINITIONAL at `y₂`.

⟦V6b⟧ FREEZE RISK (i) is discharged here: nothing in the `supF` interior sees the pin's
shape, so the conclusion `rhsFbound M L (β + 1/L)` is byte-identical to the corpus's. -/
theorem joint_supF_pin_at2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀' M k L c₀ y η : ℝ} (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L)
    (hη : η = eta2 L) (hc₀eq : c₀ = 1 + 1 / L)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαη : α ≤ η) (hβη : β ≤ η) (t : ℝ)
    (hMt : M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L) := by
  obtain ⟨hk0, hL32, h25, hlogy, hηeq, hη0, hη64, -, hylo, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
  have hylo' : Real.exp 1 ≤ y := by rw [hy]; exact hylo
  have hηy : η = 1 / Real.log y := by rw [hy, hη]; exact hηeq
  have hη4 : η ≤ 1 / 4 := by rw [hη]; linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hσL : 1 / (β + 1 / L) ≤ L := by
    rw [div_le_iff₀ hσ0]
    have h1 : L * (1 / L) = 1 := by field_simp
    nlinarith
  have hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ k := by
    rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring]
    calc Real.exp (1 / (β + 1 / L)) ≤ Real.exp L := Real.exp_le_exp.mpr hσL
      _ = k := by rw [hL, Real.exp_log hk0]
  have hP := supF_pret_pointwise (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (y := y)
    hgtw (c := 1 / (2 * Real.exp 1)) (t₀ := t₀') (t := t) (X := k) (c₀ := c₀)
    (α := α) (β := β) (by positivity)
    (by
      rw [div_le_div_iff₀ (by positivity) (Real.exp_pos 1)]
      nlinarith [Real.exp_pos 1])
    hylo' (by rw [hc₀eq]; linarith) hα0 hβ0
    (by rw [← hηy]; exact hαη) (by rw [← hηy]; exact hβη)
    (by rw [hc₀eq]; linarith) hYX
  rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring, ← hL] at hP
  refine hP.trans ?_
  unfold rhsFbound rhsCSF
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hMt hc0.le]
  · have : (0 : ℝ) ≤ 1 / (β + 1 / L) := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) this

/-- **F-1 at `y₂` — the far `supF` binder (`far_supF_bound2`).**  The far arm's `β`-uniform
`𝒮·𝓛` majorant at the R2 pin, with the SAME constant `farFbound L = C_S·C_F·e^{24/e}·L` as
the corpus pin.  The `σ`-sup runs over `σ = β + 1/L ∈ [1/L, η₂ + 1/L]` and is attained at
`σ = 1/L`, which the pin does not move — so THE F-PAGE IS UNCHANGED at `y₂` (the honest
answer to the brief's "the sup ≈ η₂·L-shape... work honestly"). -/
theorem far_supF_bound2 {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀' k L c₀ y η : ℝ}
    (hk : pin2Gate ≤ k) (hL : L = Real.log k) (hy : y = ypin2 L) (hη : η = eta2 L)
    (hc₀ : c₀ = 1 + 1 / L) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
        ≤ farFbound L := by
  intro α hα β hβ t
  obtain ⟨hk0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hk hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hM0 : (0 : ℝ) ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
      (costwist (t - t₀')) k :=
    pretDistSq_nonneg _ _ _
      (fun n => ellLin_norm_le_one (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) hgtw n)
      (fun n => le_of_eq (costwist_norm (t - t₀') n))
  refine (joint_supF_pin_at2 hg hk hL hy hη hc₀ hα.1 hβ.1 hα.2 hβ.2 t hM0).trans ?_
  have hσ0 : (0 : ℝ) < β + 1 / L := by
    have : (0 : ℝ) < 1 / L := by positivity
    linarith [hβ.1]
  have hσL : 1 ≤ (β + 1 / L) * L := by
    have hid : (β + 1 / L) * L = β * L + 1 := by field_simp
    have : (0 : ℝ) ≤ β * L := mul_nonneg hβ.1 hL0.le
    rw [hid]; linarith
  exact rhsFbound_zero_le2 hσ0 hσL

/-! ## §5 — THE PRIZE: the wall closes at the ratified pins

`CofactorLocal.farErr_local_le` prices the LOCALIZED far arm at `Rmax = T*(Y, log Y)`; its
companion `farErr_local_window_ge` shows that at `q = 1/2` the price DIVERGES like
`√(log W)/loglog W`.  Here the same page is run at the R2 height `T*₂` and against R3's
sharpened denominator `(log W)^{3/4}` (`Transfer34.farErr34`).  `log T*₂ = L^{2/5} + L^{3/5}`
against `(log W)^{3/4} ≥ L^{3/4}/2` gives `L^{−3/20}` — a DECAYING certificate, with the
threshold explicit. -/

/-- **`log T*₂ = L^{2/5} + L^{3/5}`.**  The exact exit factor GS 7.1's `d`-split hands
`ballErr34`, with nothing absorbed.  Twin of `CofactorLocal.log_Tstar_self`, whose value is
`4·loglog Y + log Y/(4 loglog Y)` — a `L/log L` scale.  This one is `L^{3/5}`. -/
theorem log_Tstar2_self {Y : ℝ} (hY : pin2Gate ≤ Y) :
    Real.log (Tstar2 Y (Real.log Y))
      = (Real.log Y) ^ ((2 : ℝ) / 5) + (Real.log Y) ^ ((3 : ℝ) / 5) := by
  obtain ⟨hY0, hL32, -, hlogy, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hY rfl
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hy0 : (0 : ℝ) ≠ ypin2 (Real.log Y) := ne_of_lt (ypin2_pos _)
  have hr0 : (Y : ℝ) ^ eta2 (Real.log Y) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hY0 _)
  have hmul : (Real.log Y) ^ (-((2 : ℝ) / 5)) * (Real.log Y) ^ ((1 : ℝ))
      = (Real.log Y) ^ ((3 : ℝ) / 5) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hsum : eta2 (Real.log Y) * Real.log Y = (Real.log Y) ^ ((3 : ℝ) / 5) := by
    rw [eta2, ← hmul, Real.rpow_one]
  unfold Tstar2
  rw [Real.log_mul (Ne.symm hy0) hr0, Real.log_rpow hY0, hlogy, hsum]

/-- **L-4 at the R2 pin, `q = 3/4` (`farErr34_local_le_pin2`).**  The certificate (upper):

  `farErr34 W Y (T*₂) ≤ 4·ballSupC34·(3 + loglog Y + (log Y)^{2/5} + (log Y)^{3/5})
                          / (log W)^{3/4}`.

Every constant is explicit (law #253): the `3` absorbs `1 + 2·log 2`, `loglog Y` absorbs the
`log(1 + log Y)` of the weight, and the two `L`-powers are `log T*₂` verbatim
(`log_Tstar2_self`).  Compare `CofactorLocal.farErr_local_le`, whose numerator carries
`log Y/(4·loglog Y)`. -/
theorem farErr34_local_le_pin2 {W Y : ℝ} (hY : pin2Gate ≤ Y) (hW : 0 ≤ Real.log W) :
    farErr34 W Y (Tstar2 Y (Real.log Y))
      ≤ 4 * ballSupC34
          * (3 + Real.log (Real.log Y) + (Real.log Y) ^ ((2 : ℝ) / 5)
              + (Real.log Y) ^ ((3 : ℝ) / 5))
        / (Real.log W) ^ ((3 : ℝ) / 4) := by
  obtain ⟨hY0, hL32, h25, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hY rfl
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log Y) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.log Y by
      linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h
  have hlogT := log_Tstar2_self hY
  have hT0 : (0 : ℝ) < Tstar2 Y (Real.log Y) := by
    unfold Tstar2
    exact mul_pos (ypin2_pos _) (Real.rpow_pos_of_pos hY0 _)
  have hT1 : (1 : ℝ) ≤ Tstar2 Y (Real.log Y) := by
    have h1 : Real.exp 0 ≤ Real.exp (Real.log (Tstar2 Y (Real.log Y))) := by
      refine Real.exp_le_exp.mpr ?_
      rw [hlogT]
      have h35 : (0 : ℝ) ≤ (Real.log Y) ^ ((3 : ℝ) / 5) := Real.rpow_nonneg hL0.le _
      linarith
    rwa [Real.exp_zero, Real.exp_log hT0] at h1
  have hprod : (3 : ℝ) ≤ Tstar2 Y (Real.log Y) * (1 + Real.log Y) := by nlinarith
  have hstep1 : Real.log (3 + Tstar2 Y (Real.log Y) * (1 + Real.log Y))
      ≤ Real.log (2 * (Tstar2 Y (Real.log Y) * (1 + Real.log Y))) :=
    Real.log_le_log (by linarith) (by linarith)
  have hstep2 : Real.log (2 * (Tstar2 Y (Real.log Y) * (1 + Real.log Y)))
      = Real.log 2 + Real.log (Tstar2 Y (Real.log Y)) + Real.log (1 + Real.log Y) := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (ne_of_gt hT0) (by linarith)]
    ring
  have hstep3 : Real.log (1 + Real.log Y) ≤ Real.log 2 + Real.log (Real.log Y) := by
    have h1 : Real.log (1 + Real.log Y) ≤ Real.log (2 * Real.log Y) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_mul (by norm_num) (ne_of_gt hL0)] at h1
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hnum : 1 + Real.log (3 + Tstar2 Y (Real.log Y) * (1 + Real.log Y))
      ≤ 3 + Real.log (Real.log Y) + (Real.log Y) ^ ((2 : ℝ) / 5)
        + (Real.log Y) ^ ((3 : ℝ) / 5) := by
    rw [hlogT] at hstep2; linarith
  have hC0 : (0 : ℝ) < ballSupC34 := ballSupC34_pos
  have hmul : 4 * ballSupC34 * (1 + Real.log (3 + Tstar2 Y (Real.log Y) * (1 + Real.log Y)))
      ≤ 4 * ballSupC34 * (3 + Real.log (Real.log Y) + (Real.log Y) ^ ((2 : ℝ) / 5)
          + (Real.log Y) ^ ((3 : ℝ) / 5)) :=
    mul_le_mul_of_nonneg_left hnum (by positivity)
  unfold farErr34
  exact div_le_div_same hmul (Real.rpow_nonneg hW _)

/-- **THE CLOSURE, gate form (`farErr34_local_closes_of_gate`).**  On the co-factor window's
own geometry `log Y ≤ 2·log W` (i.e. `k₀ ≤ M ≤ 2k₀` after logs), for ANY target exponent
`ρ ≥ 0`:

  `32·ballSupC34 ≤ (log Y)^{3/20 − ρ}  ⟹  farErr34 W Y (T*₂) ≤ (log Y)^{−ρ}`.

`3/20` is the whole R2+R3 gain: `log T*₂ ≍ L^{3/5}` over `(log W)^{3/4} ≍ L^{3/4}`.  Against
it the consumer's demand is `ρ = ρ₂₉₃ = 3·θ₂₉₃ ≈ 0.0102` (or ⟦V6b⟧'s re-derived `2·θ₂₉₃`) —
both far below `3/20 = 0.15`, so the gate is a THRESHOLD, not an obstruction. -/
theorem farErr34_local_closes_of_gate {W Y ρ : ℝ} (hY : pin2Gate ≤ Y)
    (hWY : Real.log Y ≤ 2 * Real.log W)
    (hgate : 32 * ballSupC34 ≤ (Real.log Y) ^ ((3 : ℝ) / 20 - ρ)) :
    farErr34 W Y (Tstar2 Y (Real.log Y)) ≤ (Real.log Y) ^ (-ρ) := by
  obtain ⟨hY0, hL32, h25, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hY rfl
  obtain ⟨h15, -, h35⟩ := pin2_powers hL32
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hW0 : (0 : ℝ) < Real.log W := by linarith
  have hC0 : (0 : ℝ) < ballSupC34 := ballSupC34_pos
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log Y) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ Real.log Y by
      linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h
  -- (a) the numerator: `3 + loglog Y + L^{2/5} + L^{3/5} ≤ 4·L^{3/5}`
  have hlogL : Real.log (Real.log Y) ≤ (Real.log Y) ^ ((3 : ℝ) / 5) := by
    have h1 := log_le_rpow_fifth hL0
    obtain ⟨-, -, hm⟩ := rpow_fifths_mul hL0
    have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h2 : 5 / Real.exp 1 * (Real.log Y) ^ ((1 : ℝ) / 5) ≤ (Real.log Y) ^ ((3 : ℝ) / 5) := by
      rw [← hm, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have h2535 : (Real.log Y) ^ ((2 : ℝ) / 5) ≤ (Real.log Y) ^ ((3 : ℝ) / 5) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hnum : 3 + Real.log (Real.log Y) + (Real.log Y) ^ ((2 : ℝ) / 5)
      + (Real.log Y) ^ ((3 : ℝ) / 5) ≤ 4 * (Real.log Y) ^ ((3 : ℝ) / 5) := by linarith
  -- (b) the denominator: `(log W)^{3/4} ≥ (1/2)·(log Y)^{3/4}`
  have hden : 1 / 2 * (Real.log Y) ^ ((3 : ℝ) / 4) ≤ (Real.log W) ^ ((3 : ℝ) / 4) := by
    have hs0 : (0 : ℝ) < (Real.log Y) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    have hhalf34 : (1 : ℝ) / 2 ≤ ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow_of_exponent_ge (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
        (show (3 : ℝ) / 4 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at h
    have hmulr : ((1 : ℝ) / 2 * Real.log Y) ^ ((3 : ℝ) / 4)
        = ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) * (Real.log Y) ^ ((3 : ℝ) / 4) :=
      Real.mul_rpow (by norm_num) hL0.le
    calc 1 / 2 * (Real.log Y) ^ ((3 : ℝ) / 4)
        ≤ ((1 : ℝ) / 2) ^ ((3 : ℝ) / 4) * (Real.log Y) ^ ((3 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hhalf34 hs0.le
      _ = ((1 : ℝ) / 2 * Real.log Y) ^ ((3 : ℝ) / 4) := hmulr.symm
      _ ≤ (Real.log W) ^ ((3 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  -- (c) compose
  have hstep := farErr34_local_le_pin2 (W := W) hY (by linarith)
  have hnum0 : (0 : ℝ) ≤ 4 * ballSupC34 * (3 + Real.log (Real.log Y)
      + (Real.log Y) ^ ((2 : ℝ) / 5) + (Real.log Y) ^ ((3 : ℝ) / 5)) := by
    have h1 : (0 : ℝ) ≤ (Real.log Y) ^ ((2 : ℝ) / 5) := Real.rpow_nonneg hL0.le _
    have h2 : (0 : ℝ) ≤ (Real.log Y) ^ ((3 : ℝ) / 5) := Real.rpow_nonneg hL0.le _
    positivity
  have hhalf0 : (0 : ℝ) < 1 / 2 * (Real.log Y) ^ ((3 : ℝ) / 4) := by
    have hs0 : (0 : ℝ) < (Real.log Y) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    linarith
  have hshrink : 4 * ballSupC34 * (3 + Real.log (Real.log Y)
        + (Real.log Y) ^ ((2 : ℝ) / 5) + (Real.log Y) ^ ((3 : ℝ) / 5))
      / (Real.log W) ^ ((3 : ℝ) / 4)
      ≤ 4 * ballSupC34 * (4 * (Real.log Y) ^ ((3 : ℝ) / 5))
        / (1 / 2 * (Real.log Y) ^ ((3 : ℝ) / 4)) := by
    refine div_le_div₀ ?_ ?_ hhalf0 hden
    · have h2 : (0 : ℝ) ≤ (Real.log Y) ^ ((3 : ℝ) / 5) := Real.rpow_nonneg hL0.le _
      positivity
    · exact mul_le_mul_of_nonneg_left hnum (by positivity)
  have hval : 4 * ballSupC34 * (4 * (Real.log Y) ^ ((3 : ℝ) / 5))
        / (1 / 2 * (Real.log Y) ^ ((3 : ℝ) / 4))
      = (32 * ballSupC34) * ((Real.log Y) ^ ((3 : ℝ) / 5)
          * ((Real.log Y) ^ ((3 : ℝ) / 4))⁻¹) := by
    have hs0 : (0 : ℝ) < (Real.log Y) ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    field_simp
    ring
  have hratio : (Real.log Y) ^ ((3 : ℝ) / 5) * ((Real.log Y) ^ ((3 : ℝ) / 4))⁻¹
      = (Real.log Y) ^ (-((3 : ℝ) / 20)) := by
    rw [← Real.rpow_neg hL0.le, ← Real.rpow_add hL0]
    congr 1
    ring
  have hfin : (32 * ballSupC34) * (Real.log Y) ^ (-((3 : ℝ) / 20))
      ≤ (Real.log Y) ^ (-ρ) := by
    have hpow0 : (0 : ℝ) < (Real.log Y) ^ (-((3 : ℝ) / 20)) :=
      Real.rpow_pos_of_pos hL0 _
    have hcomb : (Real.log Y) ^ ((3 : ℝ) / 20 - ρ) * (Real.log Y) ^ (-((3 : ℝ) / 20))
        = (Real.log Y) ^ (-ρ) := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    calc (32 * ballSupC34) * (Real.log Y) ^ (-((3 : ℝ) / 20))
        ≤ (Real.log Y) ^ ((3 : ℝ) / 20 - ρ) * (Real.log Y) ^ (-((3 : ℝ) / 20)) :=
          mul_le_mul_of_nonneg_right hgate hpow0.le
      _ = (Real.log Y) ^ (-ρ) := hcomb
  calc farErr34 W Y (Tstar2 Y (Real.log Y))
      ≤ 4 * ballSupC34 * (3 + Real.log (Real.log Y) + (Real.log Y) ^ ((2 : ℝ) / 5)
          + (Real.log Y) ^ ((3 : ℝ) / 5)) / (Real.log W) ^ ((3 : ℝ) / 4) := hstep
    _ ≤ 4 * ballSupC34 * (4 * (Real.log Y) ^ ((3 : ℝ) / 5))
        / (1 / 2 * (Real.log Y) ^ ((3 : ℝ) / 4)) := hshrink
    _ = (32 * ballSupC34) * (Real.log Y) ^ (-((3 : ℝ) / 20)) := by rw [hval, hratio]
    _ ≤ (Real.log Y) ^ (-ρ) := hfin

/-- `3/20 − ρ₂₉₃ > 0` and `3/20 − 2·θ₂₉₃ > 0`: the two live targets are strictly inside R2's
gain.  (`θ₂₉₃ = 1/(32(3e+1)) ≈ 0.00341`, `ρ₂₉₃ = 3θ₂₉₃ ≈ 0.0102`.) -/
theorem three_twentieths_gap : 0 < (3 : ℝ) / 20 - rho293 ∧ 0 < (3 : ℝ) / 20 - 2 * theta293 := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hθ : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
  have hd : (0 : ℝ) < 32 * (3 * Real.exp 1 + 1) := by linarith
  have hθlt : theta293 < 1 / 100 := by
    rw [hθ, div_lt_div_iff₀ hd (by norm_num)]
    linarith
  have hθ0 : 0 < theta293 := by rw [hθ]; positivity
  have hρ : rho293 = 3 * theta293 := rfl
  constructor <;> [rw [hρ]; skip] <;> linarith

/-- **THE PRIZE — `farErr34_local_closes`.**  There is an explicit `Y₀` beyond which the
LOCALIZED far arm, at the R2 truncation height and R3's `3/4` denominator, meets the CASE-B
consumer's grade demand:

  `∀ W Y, Y₀ ≤ Y → log Y ≤ 2·log W  ⟹  farErr34 W Y (T*₂(Y)) ≤ (log Y)^{−ρ₂₉₃}`.

This is the inequality ⟦V6a⟧ proved IMPOSSIBLE at the old pin
(`USetResiduals.farErr_TannGate_floor`, `ambient_cap_below_TannGate_floor`) and ⟦V6b⟧'s R1
alone left divergent (`CofactorLocal.farErr_local_window_ge`).  **The second wall is
closed.**  The threshold is `Y₀ = max(exp 32768, exp((32·ballSupC34)^{1/(3/20−ρ₂₉₃)}))` —
finite, explicit, and free of the `TannGate` tower. -/
theorem farErr34_local_closes :
    ∃ Y₀ : ℝ, pin2Gate ≤ Y₀ ∧
      ∀ W Y : ℝ, Y₀ ≤ Y → Real.log Y ≤ 2 * Real.log W →
        farErr34 W Y (Tstar2 Y (Real.log Y)) ≤ (Real.log Y) ^ (-rho293) := by
  obtain ⟨hgap, -⟩ := three_twentieths_gap
  have hC0 : (0 : ℝ) < ballSupC34 := ballSupC34_pos
  set ε : ℝ := (3 : ℝ) / 20 - rho293 with hε
  set A : ℝ := 32 * ballSupC34 with hA
  have hA0 : (0 : ℝ) < A := by rw [hA]; linarith
  refine ⟨max pin2Gate (Real.exp (A ^ (1 / ε))), le_max_left _ _, ?_⟩
  intro W Y hY hWY
  have hYg : pin2Gate ≤ Y := le_trans (le_max_left _ _) hY
  have hYe : Real.exp (A ^ (1 / ε)) ≤ Y := le_trans (le_max_right _ _) hY
  obtain ⟨hY0, hL32, -, -, -, -, -, -, -, -, -, -, -⟩ := pin2_basic hYg rfl
  have hL0 : (0 : ℝ) < Real.log Y := by linarith
  have hthr : A ^ (1 / ε) ≤ Real.log Y := by
    have h := Real.log_le_log (Real.exp_pos _) hYe
    rwa [Real.log_exp] at h
  have hgate : A ≤ (Real.log Y) ^ ε := by
    have h1 : (A ^ (1 / ε)) ^ ε ≤ (Real.log Y) ^ ε :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hthr hgap.le
    have h2 : (A ^ (1 / ε)) ^ ε = A := by
      rw [← Real.rpow_mul hA0.le, one_div, inv_mul_cancel₀ (ne_of_gt hgap), Real.rpow_one]
    linarith [h2.symm.le, h2.le]
  exact farErr34_local_closes_of_gate hYg hWY (by rw [hA] at hgate; exact hgate)

/-! ## §6 — the E-slot (⟦V6b⟧ freeze risk (iii))

`S1′`'s error at the R2 pin is `∝ log y₂ = L^{2/5}` (§3), so after the `X/log X`
normalisation it is `C_E·L^{2/5}/L = C_E·L^{−3/5}`.  `CofactorGrade`'s CASE-A exit slot is
`4·L^{−1/2+1/1000}`.  Since `3/5 > 1/2 − 1/1000` the slot absorbs the E-term for every
`C_E`, with an explicit threshold: this is the `C_E`-dependent `X₀` ⟦V6b⟧ flags, kept LOOSE
exactly as the `2/5` choice permits. -/

/-- **The E-slot comparison, gate form.**  `C·L^{2/5}/L ≤ 4·L^{−1/2+1/1000}` as soon as
`C ≤ 4·L^{101/1000}`.  The exponent arithmetic: `2/5 − 1 = −3/5` and
`−3/5 + 101/1000 = −499/1000 = −1/2 + 1/1000`. -/
theorem E_slot_pin2_le {C L : ℝ} (hL : 32768 ≤ L) (hgate : C ≤ 4 * L ^ ((101 : ℝ) / 1000)) :
    C * L ^ ((2 : ℝ) / 5) / L ≤ 4 * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hmul : L ^ (-((3 : ℝ) / 5)) * L ^ ((1 : ℝ)) = L ^ ((2 : ℝ) / 5) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hsplit : L ^ ((2 : ℝ) / 5) / L = L ^ (-((3 : ℝ) / 5)) := by
    rw [← hmul, Real.rpow_one, mul_div_assoc, div_self (ne_of_gt hL0), mul_one]
  have hpow0 : (0 : ℝ) < L ^ (-((3 : ℝ) / 5)) := Real.rpow_pos_of_pos hL0 _
  have hcomb : L ^ ((101 : ℝ) / 1000) * L ^ (-((3 : ℝ) / 5))
      = L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    rw [← Real.rpow_add hL0]; congr 1; norm_num
  calc C * L ^ ((2 : ℝ) / 5) / L = C * (L ^ ((2 : ℝ) / 5) / L) := by ring
    _ = C * L ^ (-((3 : ℝ) / 5)) := by rw [hsplit]
    _ ≤ (4 * L ^ ((101 : ℝ) / 1000)) * L ^ (-((3 : ℝ) / 5)) :=
        mul_le_mul_of_nonneg_right hgate hpow0.le
    _ = 4 * (L ^ ((101 : ℝ) / 1000) * L ^ (-((3 : ℝ) / 5))) := by ring
    _ = 4 * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by rw [hcomb]

/-- **The E-slot closes** — for EVERY `C_E ≥ 0` there is an explicit `L₀` past which the
`S1′` error at `y₂` fits inside `caseAS`'s slot.  This is ⟦V6b⟧ freeze risk (iii) discharged:
the `X₀` grows with `C_E`, and the `L^{2/5}` choice makes the absorption loose. -/
theorem E_slot_pin2_closes (C : ℝ) :
    ∃ L₀ : ℝ, 32768 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      C * L ^ ((2 : ℝ) / 5) / L ≤ 4 * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
  refine ⟨max 32768 ((max C 4) ^ (1000 / (101 : ℝ))), le_max_left _ _, ?_⟩
  intro L hL
  have h32 : (32768 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hCm : (0 : ℝ) < max C 4 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hthr : (max C 4) ^ (1000 / (101 : ℝ)) ≤ L := le_trans (le_max_right _ _) hL
  have h1 : ((max C 4) ^ (1000 / (101 : ℝ))) ^ ((101 : ℝ) / 1000) ≤ L ^ ((101 : ℝ) / 1000) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hCm.le _) hthr (by norm_num)
  have h2 : ((max C 4) ^ (1000 / (101 : ℝ))) ^ ((101 : ℝ) / 1000) = max C 4 := by
    rw [← Real.rpow_mul hCm.le]
    norm_num
  refine E_slot_pin2_le h32 ?_
  have h3 : C ≤ max C 4 := le_max_left _ _
  have h4 : max C 4 ≤ L ^ ((101 : ℝ) / 1000) := by rw [← h2]; exact h1
  have h5 : (0 : ℝ) ≤ L ^ ((101 : ℝ) / 1000) := Real.rpow_nonneg hL0.le _
  linarith

/-! ## §7 — the F-2 assembly twin (R3's Zeno, the zero-edit wire) -/

/-- **`cofactor_Rbd34_assembled` — the CASE-B `R̄` at the R2/R3 pins.**  `Transfer34`'s
`Rbd34_grade_priced` with its far gate discharged by §5 rather than by an ambient
hypothesis: the far radius is the LOCALIZED, RE-PINNED height `T*₂(Ymax)`, and the resulting
grade `(log X)^{−ρ₂₉₃}` is exactly `USetPrice`'s `hRgrade` slot shape.

The gates in the statement (law #253): the CASE-A page's own three (`hk2`, `hkX`, `hlX`,
`hgate`), the pricing's lower radius pin `hRlow` (⟦V6a⟧'s silent-vacuity catch), the R2 gate
`hY`, the window geometry `hWY`, the scale comparison `hXY` (`log X ≤ log Ymax`, which turns
`(log Ymax)^{−ρ}` into `(log X)^{−ρ}`), and §5's threshold `hthr`.  ZERO edits to the landed
chain: `Rbd34_grade_priced` is applied verbatim. -/
theorem cofactor_Rbd34_assembled {X Cb kmin Ymax Rrad : ℝ}
    (hCb0 : 0 ≤ Cb) (hk2 : 2 ≤ kmin) (hkX : kmin ≤ X) (hlX : Real.exp 2 ≤ Real.log X)
    (hgate : (1 - 1 / Real.log (Real.log X)) * Real.log X ≤ Real.log kmin)
    (hRlow : seamRad X ≤ Rrad)
    (hY : pin2Gate ≤ Ymax) (hWY : Real.log Ymax ≤ 2 * Real.log kmin)
    (hXY : Real.log X ≤ Real.log Ymax)
    (hthr : 32 * ballSupC34 ≤ (Real.log Ymax) ^ ((3 : ℝ) / 20 - rho293)) :
    cofactorRbd34 (1 / Real.exp 1) Cb X theta293 kmin Ymax
        (Tstar2 Ymax (Real.log Ymax) - 1 + 1) Rrad
      ≤ gradeCR Cb * (Real.log X) ^ (-rho293) := by
  have he3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hL3 : (3 : ℝ) ≤ Real.log X := le_trans he3 hlX
  have hL0 : (0 : ℝ) < Real.log X := by linarith
  have hρ0 : (0 : ℝ) ≤ rho293 := by
    have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hθ : theta293 = 1 / (32 * (3 * Real.exp 1 + 1)) := rfl
    have : (0 : ℝ) < theta293 := by rw [hθ]; positivity
    have hρ : rho293 = 3 * theta293 := rfl
    rw [hρ]; linarith
  have hclose := farErr34_local_closes_of_gate (W := kmin) hY hWY hthr
  have htrans : (Real.log Ymax) ^ (-rho293) ≤ (Real.log X) ^ (-rho293) :=
    rpow_neg_le_rpow_neg_of_le hL0 hXY hρ0
  have hfar : farErr34 kmin Ymax (Tstar2 Ymax (Real.log Ymax) - 1 + 1)
      ≤ (Real.log X) ^ (-rho293) := by
    rw [sub_add_cancel]
    exact le_trans hclose htrans
  exact Rbd34_grade_priced hCb0 hk2 hkX hlX hgate hRlow hfar

end Salt.MR
