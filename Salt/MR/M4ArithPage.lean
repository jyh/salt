/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4Assembly
import Salt.MR.M4SecondRoad
import Salt.MR.RbdSupply

/-!
# ⟦A4 — THE ASSEMBLY'S ARITHMETIC PAGE⟧ (`M4ArithPage`)

Design provenance: the 0730 council's ⟦C4⟧ (the corrected six-debit page: the arm, the `M₀`
window, the `g`-arm's written form) and ⟦C1⟧ (the 12× anchor ask), both RATIFIED; the numbers
are `REF-A4-MATH`'s, re-derived here at the kernel's own bytes.  `M4Assembly` left exactly one
thing open — its `henv`, the comparison of the door grade against the second road's ceiling.
This file closes it.

## ⟦WHAT IS PRICED⟧

`M4Assembly.a2DoorGrade M X h C₁ M₀` has five summands.  Multiplied by the ⟦φ(q) LEDGER⟧'s
`arcDen 12 H` they must sit under `M4SecondRoad.m4_second_road_rs_ceiling`'s demand

```
      96(1+2π)² · strataResidual H² · (108/5 · RSan H)  ≤  δ₀² .
```

The page names the clearing value

```
      RSanDoor H  :=  doorRho / strataResidual H²,     doorRho := 2⁻³⁴¹ ,
```

and proves the three things a consumer needs: ⟦i⟧ `henv` at the `g`-arm base, ⟦ii⟧ ⟦gate 4⟧'s
read `m4ChiRowGraded M (fun _ H => RSanDoor H) j H ≤ RSanDoor H` above the door's floor, and
⟦iii⟧ the ceiling itself, at `δ₀ ≥ 2·10⁻⁴⁹`.

## ⟦THE ONE STRUCTURAL FINDING — `henv` NEEDS A GATE⟧

`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s `henv` is quantified

```
      ∀ H j A s : ℕ,  doorRowFloor M ≤ j →  arcDen 12 H · a2DoorGrade M (A+s) 2^j … ≤ RSbig j H
```

— with NO regime bound on `H` and NO lower bound on the base `A + s`.  That shape is **not
dischargeable at any analytic `RSbig`**, and the counterexample is two lines: take `H` in the
register (so `arcDen 12 H = (log H)¹² ≫ 1`) and `A + s = 2`.  The third summand alone is then
`188133·(log 2)^{−1/500} > 188132`, so the left side exceeds `10⁵·(log H)¹²` while
`RSanDoor H < 10⁻¹⁰²`.  Nothing about the arm, the anchor or the window can repair it: the
base is a free variable of `henv`.

The repair is ADDITIVE and is performed here: `m4_chiSummedFreeRowBig_of_doorGradeGated`
re-proves `M4Assembly.m4_chiSummedFreeRowBig_of_doorGrade` with both of its hypotheses gated
by `M4Assembly.SocketBase` — the socket's OWN antecedent bundle, which is exactly the context
in which the original proof applies `henv`.  No statement of `M4Assembly` is touched, no gate
is weakened, and the gated form is strictly more usable (its `hgrade` slot is weaker too).

## ⟦THE RATIFIED NUMBERS, AND WHERE EACH IS SPENT⟧

`DoorArithFrame M H j X C₁ M₀ K` carries them, field by field:

* `Hfloor` — `loglog H ≥ 50`.  Spent on `1 + 12·loglog H ≤ log H` (the `strataResidual`
  absorption, §1) and on `log(1+12λ) ≤ λ` wherever the refuter's exact `6000λ + 1000·log(1+12λ)`
  arm is read in its clean `7000λ` form.
* `arm` — `loglog X ≥ 7000·loglog H + 1.25·10⁵ + 36K`, the ⟦C4⟧ arm with ⟦C3⟧'s symbolic
  margined-floor constant `K` riding.  `K` is **carried, never evaluated**: per `RBD-WIRE-2`'s
  fence it is the `∃K` of `RbdSupply`'s §5 exit, NOT `cffKVt`.  Spent on summand 3 (which
  fixes the `7000` and the `1.25·10⁵`) and, slackly, on summand 4.
* `anchor` — ⟦C1⟧'s 12× ask in its derived form `14·loglog H + 269 ≤ 3.9·10⁹·(log₂M+1)`.
  `m4_arith_anchor_of_C1` shows `log₂M + 1 ≥ 2484` discharges it on the whole register.
  Spent on summand 2 (`a2Level1 M = (log Q₁)^{1/3}/P₁^{1/12}`, `P₁ = 2^{Adoor M}`).
* `M0_window` — the window's LOWER endpoint, exactly:
  `M₀ ≥ e·(loglog X/45 + 14·loglog H + 2·log(C₁+1) + 248)`.  Spent on summand 1.
  `m4_arith_M0_window_nonempty` puts it under `hErr`'s cap `2.7128·loglog X − 7.54`.
* `jfloor` — `j ≥ 21·loglog H + 368`.  Spent on summand 5 (`6315000/2^j`);
  `m4_arith_jfloor_of_anchor` derives it from `doorRowFloor M ≤ j` and the anchor.

## ⟦THE FOUR LOG SCALES, KEPT APART⟧

`Nat.log 2` (the dyadic index and the anchor `log₂M+1`); `arcDen 12 H = (log H)¹²` (the
modulus range and the `φ(q)` ledger — never evaluated, never a `log X`); `loglog H` (the
`H`-side scale, written `λ` in the comments); `loglog X` (the BASE-side scale, written `μ`).
`λ` and `μ` are separated by the arm and never conflated: every lemma below states both.

## ⟦THE CORNER⟧ (RELIFT-B's assembly finding (1))

Nothing here reads a `(q, T, X)` corner at all.  The grade `a2DoorGrade` is `T`-free and
`χ`-free by construction (`M4Assembly` §3), the ledger factor is `arcDen 12 H`, and the only
base-side quantity any summand reads is `log X` at the socket's own base `X = A + s`.  So the
window `q ≍ (log X)¹²`/`T ≤ X` unavailability does not bite: **no STOP finding on this page.**
-/

set_option maxRecDepth 40000
set_option exponentiation.threshold 3000

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE NUMERIC STONES

Every numeral this page spends, with its provenance.  `Real.exp 1 > 2.7` and mathlib's
nine-digit `log 2` are the only external inputs; each `log c ≤ n` below is `c ≤ e^n` read
through `2.7^k ≤ e^k`. -/

/-- Logs decide: on the positives, `log a ≤ log b → a ≤ b`. -/
theorem le_of_log_le' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : Real.log a ≤ Real.log b) :
    a ≤ b := by
  rw [← Real.exp_log ha, ← Real.exp_log hb]
  exact Real.exp_le_exp.mpr h

/-- `2.7 < e`, the only transcendental input on this page besides `log 2`. -/
theorem exp_one_gt_27 : (2.7 : ℝ) < Real.exp 1 := by
  have := Real.exp_one_gt_d9
  linarith

/-- `2.7^n ≤ e^n` — the ladder every numeral bound below climbs. -/
theorem pow_27_le_exp (n : ℕ) : (2.7 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) exp_one_gt_27.le n

/-- `log c ≤ n + r` from `c ≤ 2.7^n · (1 + r)`: the shape all five numeral bounds use
(`e^n ≥ 2.7^n` and `e^r ≥ 1 + r`). -/
theorem log_le_of_le_pow27 {c : ℝ} (hc : 0 < c) (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (h : c ≤ (2.7 : ℝ) ^ n * (1 + r)) : Real.log c ≤ (n : ℝ) + r := by
  rw [Real.log_le_iff_le_exp hc, Real.exp_add]
  have h1 : (2.7 : ℝ) ^ n ≤ Real.exp (n : ℝ) := pow_27_le_exp n
  have h2 : (1 : ℝ) + r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have h3 : (0 : ℝ) < (2.7 : ℝ) ^ n := by positivity
  calc c ≤ (2.7 : ℝ) ^ n * (1 + r) := h
    _ ≤ Real.exp (n : ℝ) * Real.exp r := by
        exact mul_le_mul h1 h2 (by linarith) (Real.exp_pos _).le

/-- `log y ≤ y/e` — `Real.log_le_sub_one_of_pos` read at `y/e`.  The only tool summand 4
needs against its `(1 + loglog X)²`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < y / Real.exp 1 by positivity)
  rwa [Real.log_div hy.ne' (Real.exp_ne_zero 1), Real.log_exp, sub_le_sub_iff_right] at h

theorem log_188133_le : Real.log 188133 ≤ 12.5 := by
  have := log_le_of_le_pow27 (c := (188133 : ℝ)) (by norm_num) 12 (r := 0.5) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_8448_le : Real.log 8448 ≤ 9.2 := by
  have := log_le_of_le_pow27 (c := (8448 : ℝ)) (by norm_num) 9 (r := 0.2) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_1787702400_le : Real.log 1787702400 ≤ 21.6 := by
  have := log_le_of_le_pow27 (c := (1787702400 : ℝ)) (by norm_num) 21 (r := 0.6) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_304128_le : Real.log 304128 ≤ 13 := by
  have := log_le_of_le_pow27 (c := (304128 : ℝ)) (by norm_num) 13 (r := 0) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

theorem log_6315000_le : Real.log 6315000 ≤ 16 := by
  have := log_le_of_le_pow27 (c := (6315000 : ℝ)) (by norm_num) 16 (r := 0) (by norm_num)
    (by norm_num)
  norm_num at this ⊢
  linarith

/-! ### The ball constant

`BallSup.ballSupC = renormaliseConst·e^{M/2+6}` with
`renormaliseConst = 28(1 + 2(log 4 + 36))·e⁸` (`Renormalise.lean:749`) and the landed
Meissel–Mertens numeral `RbdSupply.mertensM_le_two_thirds`. -/

theorem renormaliseConst_le_exp17 : renormaliseConst ≤ Real.exp 17 := by
  have hlog4 : Real.log 4 ≤ 1.4 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    rw [h]; linarith
  have hle : renormaliseConst ≤ 2123 * Real.exp 8 := by
    rw [renormaliseConst]
    have hpos : (0 : ℝ) < Real.exp 8 := Real.exp_pos 8
    have hcoef : 28 * (1 + 2 * (Real.log 4 + 36)) ≤ 2123 := by linarith
    exact mul_le_mul_of_nonneg_right hcoef hpos.le
  have h9 : (2123 : ℝ) ≤ Real.exp 9 := by
    have := pow_27_le_exp 9
    norm_num at this ⊢
    linarith
  calc renormaliseConst ≤ 2123 * Real.exp 8 := hle
    _ ≤ Real.exp 9 * Real.exp 8 := by
        exact mul_le_mul_of_nonneg_right h9 (Real.exp_pos 8).le
    _ = Real.exp 17 := by rw [← Real.exp_add]; norm_num

theorem renormaliseConst_pos : 0 < renormaliseConst := by
  rw [renormaliseConst]
  have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have : (0 : ℝ) < Real.exp 8 := Real.exp_pos 8
  positivity

/-- `log ballSupC ≤ 24` — `renormaliseConst ≤ e¹⁷` times `e^{M/2+6} ≤ e⁷` at `M ≤ 2/3`. -/
theorem log_ballSupC_le : Real.log ballSupC ≤ 24 := by
  rw [Real.log_le_iff_le_exp ballSupC_pos, ballSupC]
  have hM := mertensM_le_two_thirds
  have h7 : Real.exp (Salt.Mertens.mertensM / 2 + 6) ≤ Real.exp 7 :=
    Real.exp_le_exp.mpr (by linarith)
  calc renormaliseConst * Real.exp (Salt.Mertens.mertensM / 2 + 6)
      ≤ Real.exp 17 * Real.exp 7 := by
        exact mul_le_mul renormaliseConst_le_exp17 h7 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp 24 := by rw [← Real.exp_add]; norm_num

/-! ## §1 — THE `H`-SIDE SCALE: `arcDen 12 H · strataResidual H² ≤ (log H)¹⁴`

The ⟦φ(q) LEDGER⟧'s factor and the ceiling's `strataResidual` denominator travel together, and
the whole of the second road's `H`-motion is this one product.  `strataResidual H = 1 + 12λ`
and `1 + 12λ ≤ e^λ = log H` above `λ ≥ 44`, so the pair costs exactly two extra powers of
`log H` — which is why the ratified arm reads `7000λ` (`= 500·14λ`) and not `6000λ`. -/

/-- `50 ≤ loglog y` forces `1 < log y` (`log` is nonpositive on `(0,1]`). -/
theorem one_lt_log_of_loglog_ge {y : ℝ} (hy : 0 ≤ Real.log y) {c : ℝ} (hc : 0 < c)
    (h : c ≤ Real.log (Real.log y)) : 1 < Real.log y := by
  by_contra hcon
  have hle : Real.log y ≤ 1 := not_lt.mp hcon
  have : Real.log (Real.log y) ≤ 0 := Real.log_nonpos hy hle
  linarith

/-- `strataResidual H = 1 + 12·loglog H` — the ceiling's denominator, unfolded once. -/
theorem strataResidual_eq_of_pos {H : ℕ} (hL : 0 < Real.log (H : ℝ)) :
    strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) := by
  rw [strataResidual, arcDen, Real.log_rpow hL]

/-- `1 + 12λ ≤ e^λ` for `λ ≥ 44` — `e^λ = (e^{λ/2})² ≥ (1+λ/2)²= 1 + λ + λ²/4`. -/
theorem one_add_twelve_le_exp {l : ℝ} (hl : 44 ≤ l) : 1 + 12 * l ≤ Real.exp l := by
  have h2 : 1 + l / 2 ≤ Real.exp (l / 2) := by linarith [Real.add_one_le_exp (l / 2)]
  have hnn : (0 : ℝ) ≤ 1 + l / 2 := by linarith
  have hsq : (1 + l / 2) ^ 2 ≤ Real.exp (l / 2) ^ 2 := by
    exact pow_le_pow_left₀ hnn h2 2
  have hexp : Real.exp (l / 2) ^ 2 = Real.exp l := by
    rw [sq, ← Real.exp_add]; ring_nf
  nlinarith [hsq, hexp]

/-- **⟦THE `H`-SIDE PRICE⟧** — the ledger factor times the ceiling's denominator is at most
`e^{14·loglog H}`.  Everything else on this page is a `base`-side estimate. -/
theorem arcDen_mul_strataResidual_sq_le {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ))
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    arcDen 12 H * strataResidual H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ))) := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have hL : 0 < Real.log (H : ℝ) := by linarith
  have hexp : Real.log (H : ℝ) = Real.exp (Real.log (Real.log (H : ℝ))) :=
    (Real.exp_log hL).symm
  have harc : arcDen 12 H = Real.exp (12 * Real.log (Real.log (H : ℝ))) := by
    rw [arcDen, Real.rpow_def_of_pos hL]
    ring_nf
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos hL
  have hbound : 1 + 12 * Real.log (Real.log (H : ℝ))
      ≤ Real.exp (Real.log (Real.log (H : ℝ))) := one_add_twelve_le_exp (by linarith)
  have hnn : (0 : ℝ) ≤ 1 + 12 * Real.log (Real.log (H : ℝ)) := by linarith
  have hsq : strataResidual H ^ 2 ≤ Real.exp (2 * Real.log (Real.log (H : ℝ))) := by
    rw [hstr, show (2 : ℝ) * Real.log (Real.log (H : ℝ))
      = Real.log (Real.log (H : ℝ)) + Real.log (Real.log (H : ℝ)) by ring, Real.exp_add]
    calc (1 + 12 * Real.log (Real.log (H : ℝ))) ^ 2
        ≤ Real.exp (Real.log (Real.log (H : ℝ))) ^ 2 := pow_le_pow_left₀ hnn hbound 2
      _ = Real.exp (Real.log (Real.log (H : ℝ))) * Real.exp (Real.log (Real.log (H : ℝ))) := by
          ring
  calc arcDen 12 H * strataResidual H ^ 2
      ≤ Real.exp (12 * Real.log (Real.log (H : ℝ)))
          * Real.exp (2 * Real.log (Real.log (H : ℝ))) := by
        rw [harc]
        exact mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = Real.exp (14 * Real.log (Real.log (H : ℝ))) := by
        rw [← Real.exp_add]; ring_nf

/-! ## §2 — THE FRAME

Every ratified number, in one bundle, at ONE base.  Nothing is absorbed and nothing is
derived here: each field is spent by exactly one summand of §3. -/

/-- **⟦THE RATIFIED ARITHMETIC FRAME⟧** (`DoorArithFrame M H j X C₁ M₀ K`) — the council's
C4 + C1 numbers at one `(H, j, base)` corner.  `K` is ⟦C3⟧'s symbolic margined-floor constant
(`RbdSupply` §5's `∃K`, NOT `cffKVt`): carried, never evaluated. -/
structure DoorArithFrame (M H j : ℕ) (X C₁ M₀ K : ℝ) : Prop where
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
  /-- **⟦C4 — THE ARM⟧** `loglog X ≥ 7000·loglog H + 1.25·10⁵ + 36K`. -/
  arm : 7000 * Real.log (Real.log (H : ℝ)) + 125000 + 36 * K ≤ Real.log (Real.log X)
  /-- **⟦C1 — THE 12× ANCHOR⟧**, derived form: `14·loglog H + 269 ≤ 3.9·10⁹·(log₂M+1)`. -/
  anchor : 14 * Real.log (Real.log (H : ℝ)) + 269
    ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ)
  /-- the band constant is a constant. -/
  C1_nonneg : 0 ≤ C₁
  /-- **⟦C4 — THE `M₀` WINDOW, LOWER ENDPOINT⟧**
  `M₀ ≥ e·(loglog X/45 + 14·loglog H + 2·log(C₁+1) + 248)`. -/
  M0_window : Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + 248) ≤ M₀
  /-- **the window index floor** `j ≥ 21·loglog H + 368`. -/
  jfloor : 21 * Real.log (Real.log (H : ℝ)) + 368 ≤ (j : ℝ)

namespace DoorArithFrame

variable {M H j : ℕ} {X C₁ M₀ K : ℝ}

theorem one_lt_logH (h : DoorArithFrame M H j X C₁ M₀ K) : 1 < Real.log (H : ℝ) :=
  one_lt_log_of_loglog_ge h.logH_nonneg (by norm_num) h.Hfloor

theorem armWeak (h : DoorArithFrame M H j X C₁ M₀ K) :
    7000 * Real.log (Real.log (H : ℝ)) + 125000 ≤ Real.log (Real.log X) := by
  have := h.arm
  have := h.Knonneg
  linarith

theorem loglogX_ge (h : DoorArithFrame M H j X C₁ M₀ K) : 475000 ≤ Real.log (Real.log X) := by
  have h1 := h.armWeak
  have h2 := h.Hfloor
  linarith

theorem one_lt_logX (h : DoorArithFrame M H j X C₁ M₀ K) : 1 < Real.log X :=
  one_lt_log_of_loglog_ge h.logX_nonneg (show (0:ℝ) < 475000 by norm_num) h.loglogX_ge

end DoorArithFrame

/-! ## §3 — THE FIVE SUMMANDS

Each summand of `M4Assembly.a2DoorGrade`, priced against `e^{14·loglog H}` — §1's `H`-side
price — at its own field of the frame.  The budget: summand 3 takes `2⁻³⁴²`, the other four
take `2⁻³⁴⁴` each; `2⁻³⁴² + 4·2⁻³⁴⁴ = 2⁻³⁴¹ = doorRho`. -/

/-- **SUMMAND 1 — the `T₀`-band head, via the `M₀` window.**
`8448·cfbC₁(X,C₁)²·e^{−M₀/e} = 8448(C₁+1)²(log X)^{1/45}e^{−M₀/e}`; the window's lower
endpoint is exactly what makes it clear `2⁻³⁴⁴`. -/
theorem doorGrade_summand1_priced {H : ℕ} {X C₁ M₀ : ℝ}
    (hC₁ : 0 ≤ C₁) (hLX0 : 0 ≤ Real.log X) (hLX : 1 < Real.log X)
    (hM₀ : Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
        + 2 * Real.log (C₁ + 1) + 248) ≤ M₀) :
    8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 344 := by
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hC1pos : (0 : ℝ) < C₁ + 1 := by linarith
  have hseam : (0 : ℝ) < seamT0 X := by
    rw [seamT0]; exact Real.rpow_pos_of_pos hLXpos _
  have hsq : cfbC₁ X C₁ ^ 2 = (C₁ + 1) ^ 2 * seamT0 X := cfbC₁_sq hLX0
  have hcf : (0 : ℝ) < cfbC₁ X C₁ ^ 2 := by rw [hsq]; positivity
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  -- the exponential debit
  have hdebit : -(1 / Real.exp 1) * M₀
      ≤ -(Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
          + 2 * Real.log (C₁ + 1) + 248) := by
    have hinv : (0 : ℝ) < 1 / Real.exp 1 := by positivity
    have := mul_le_mul_of_nonneg_left hM₀ hinv.le
    rw [← mul_assoc] at this
    rw [show (1 / Real.exp 1) * Real.exp 1 = 1 by field_simp] at this
    rw [one_mul] at this
    linarith
  -- logs
  refine le_of_log_le' (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hcf.ne', Real.log_exp, Real.log_exp, hsq,
    Real.log_mul (by positivity) hseam.ne', seamT0, Real.log_rpow hLXpos,
    show ((C₁ + 1) : ℝ) ^ (2 : ℕ) = (C₁ + 1) * (C₁ + 1) by ring,
    Real.log_mul hC1pos.ne' hC1pos.ne']
  have hRHS : Real.log (1 / 2 ^ 344 : ℝ) = -(344 * Real.log 2) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow]
    push_cast; ring
  rw [hRHS]
  have h8448 := log_8448_le
  have hlog2 := Real.log_two_lt_d9
  linarith

/-- **SUMMAND 3 — the `𝒯`/rows grading residue, via the ARM.**
`188133·(log X)^{−1/500}`: the summand that FIXES the ratified arm.  Clearing `2⁻³⁴²` demands
`loglog X ≥ 7000·loglog H + 124601`; the ratified `1.25·10⁵` clears it with `399` to spare. -/
theorem doorGrade_summand3_priced {H : ℕ} {X : ℝ}
    (hLX : 1 < Real.log X)
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 125000 ≤ Real.log (Real.log X)) :
    188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 342 := by
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hrp : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hLXpos _
  refine le_of_log_le' (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hrp.ne', Real.log_exp, Real.log_rpow hLXpos]
  have hRHS : Real.log (1 / 2 ^ 342 : ℝ) = -(342 * Real.log 2) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow]
    push_cast; ring
  rw [hRHS]
  have h188 := log_188133_le
  have hlog2 := Real.log_two_lt_d9
  linarith

/-- **SUMMAND 4 — the ball residue, via the ARM (slackly).**
`304128·ballSupC²·(log X)^{−43/45}(1+loglog X)²`: its own `(log X)^{−43/45}` pays, the arm only
has to keep `14·loglog H ≤ loglog X/500`. -/
theorem doorGrade_summand4_priced {H : ℕ} {X : ℝ}
    (hLX : 1 < Real.log X) (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 125000 ≤ Real.log (Real.log X)) :
    304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ 1 / 2 ^ 344 := by
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hμ : (475000 : ℝ) ≤ Real.log (Real.log X) := by linarith
  have hrp : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hLXpos _
  have hone : (0 : ℝ) < 1 + Real.log (Real.log X) := by linarith
  have hball : (0 : ℝ) < ballSupC := ballSupC_pos
  refine le_of_log_le' (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_mul hrp.ne' (by positivity), Real.log_exp, Real.log_rpow hLXpos,
    show (ballSupC : ℝ) ^ (2 : ℕ) = ballSupC * ballSupC by ring,
    Real.log_mul hball.ne' hball.ne',
    show ((1 + Real.log (Real.log X)) : ℝ) ^ (2 : ℕ)
      = (1 + Real.log (Real.log X)) * (1 + Real.log (Real.log X)) by ring,
    Real.log_mul hone.ne' hone.ne']
  have hRHS : Real.log (1 / 2 ^ 344 : ℝ) = -(344 * Real.log 2) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow]
    push_cast; ring
  rw [hRHS]
  have h304 := log_304128_le
  have hbc := log_ballSupC_le
  have hlog2 := Real.log_two_lt_d9
  -- `log(1+μ) ≤ (1+μ)/e ≤ (10/27)(1+μ)`
  have hlogmu : Real.log (1 + Real.log (Real.log X))
      ≤ (10 / 27) * (1 + Real.log (Real.log X)) := by
    refine le_trans (log_le_div_exp_one hone) ?_
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [exp_one_gt_27, hone]
  -- the arm keeps `14·loglog H ≤ loglog X/500`
  have h14 : 14 * Real.log (Real.log (H : ℝ)) ≤ Real.log (Real.log X) / 500 - 250 := by
    linarith
  linarith

/-- **SUMMAND 5 — the `1/h` tail, via the window index floor.**
`6315000/2^j` at `j ≥ 21·loglog H + 368`. -/
theorem doorGrade_summand5_priced {H j : ℕ}
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (hj : 21 * Real.log (Real.log (H : ℝ)) + 368 ≤ (j : ℝ)) :
    6315000 / ((2 ^ j : ℕ) : ℝ) * Real.exp (14 * Real.log (Real.log (H : ℝ)))
      ≤ 1 / 2 ^ 344 := by
  have h2j : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [h2j]
  refine le_of_log_le' (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_div (by norm_num) h2jpos.ne', Real.log_pow, Real.log_exp]
  have hRHS : Real.log (1 / 2 ^ 344 : ℝ) = -(344 * Real.log 2) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow]
    push_cast; ring
  rw [hRHS]
  have h63 := log_6315000_le
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have hjl : (21 * Real.log (Real.log (H : ℝ)) + 368) * Real.log 2 ≤ (j : ℝ) * Real.log 2 := by
    refine mul_le_mul_of_nonneg_right hj ?_
    linarith
  nlinarith [hlam, hjl, hlo, hhi]

/-! ### Summand 2 — the level-1 grade, via the ⟦C1⟧ anchor

`a2Level1 M = (log Q₁)^{1/3}/P₁^{1/12}` with `P₁ = 2^{Adoor M}`, `Q₁ = 2^{M·Adoor M}` and
`Adoor M = 2³⁶(log₂M+1)`.  The `1/12` against `P₁` (not `P₁^{1/6}`) is the whole reason
⟦C1⟧'s ask is exactly 12×. -/

theorem calP_door_one (M : ℕ) : calP (Adoor M) (3072 * M) 1 = 2 ^ Adoor M := by
  rw [calP, calE_one]

theorem calQK_door_one (M : ℕ) : calQK (Adoor M) (3072 * M) M 1 = 2 ^ (M * Adoor M) := by
  rw [calQK, calE_one]
  norm_num

/-- **SUMMAND 2 — the level-1 grade, via the ⟦C1⟧ 12× ANCHOR.**
`1787702400·a2Level1 M` clears `2⁻³⁴⁴` under `14·loglog H + 269 ≤ 3.9·10⁹·(log₂M+1)` — the
derived form of the council's anchor ask (`Adoor M ≥ 207.75·loglog H` genre). -/
theorem doorGrade_summand2_priced {M H : ℕ} (hM : 1 ≤ M)
    (hanchor : 14 * Real.log (Real.log (H : ℝ)) + 269
      ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ)) :
    1787702400 * a2Level1 M * Real.exp (14 * Real.log (Real.log (H : ℝ)))
      ≤ 1 / 2 ^ 344 := by
  set m : ℕ := Nat.log 2 M + 1 with hm
  have hAd : Adoor M = 2 ^ 36 * m := by rw [Adoor, hm]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    have : 1 ≤ m := by omega
    exact_mod_cast this
  -- the two ladder values
  have hP : ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) = (2 : ℝ) ^ (Adoor M) := by
    rw [calP_door_one]; push_cast; ring
  have hQ : ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) = (2 : ℝ) ^ (M * Adoor M) := by
    rw [calQK_door_one]; push_cast; ring
  have hDpos : 0 < Adoor M := by rw [hAd]; positivity
  have hMD : 1 ≤ M * Adoor M := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) hDpos.ne')
  have hlogQ : Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)
      = ((M * Adoor M : ℕ) : ℝ) * Real.log 2 := by
    rw [hQ, Real.log_pow]
  have hlogP : Real.log ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ)
      = ((Adoor M : ℕ) : ℝ) * Real.log 2 := by
    rw [hP, Real.log_pow]
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hMD1 : (1 : ℝ) ≤ ((M * Adoor M : ℕ) : ℝ) := by exact_mod_cast hMD
  have hlogQpos : (0 : ℝ) < Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ) := by
    rw [hlogQ]
    exact mul_pos (by linarith) hlog2pos
  have hPpos : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) := by rw [hP]; positivity
  have hnum : (0 : ℝ)
      < (Real.log ((calQK (Adoor M) (3072 * M) M 1 : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
    Real.rpow_pos_of_pos hlogQpos _
  have hden : (0 : ℝ) < ((calP (Adoor M) (3072 * M) 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hPpos _
  have hlvlpos : (0 : ℝ) < a2Level1 M := by rw [a2Level1]; exact div_pos hnum hden
  refine le_of_log_le' (by positivity) (by positivity) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hlvlpos.ne', Real.log_exp, a2Level1,
    Real.log_div hnum.ne' hden.ne', Real.log_rpow hlogQpos, Real.log_rpow hPpos,
    hlogQ, hlogP]
  have hRHS : Real.log (1 / 2 ^ 344 : ℝ) = -(344 * Real.log 2) := by
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one, Real.log_pow]
    push_cast; ring
  rw [hRHS]
  -- ⟦the numerator: `M < 2^m`, so `log(M·D·log2) ≤ (m+36)log2 + log m`⟧
  have hMlt : (M : ℝ) < (2 : ℝ) ^ m := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) M
    have h2 : M < 2 ^ m := by rw [hm]; simpa [Nat.succ_eq_add_one] using h
    exact_mod_cast h2
  have hDR : ((Adoor M : ℕ) : ℝ) = 68719476736 * (m : ℝ) := by
    rw [hAd]; push_cast; ring
  have hMDR : ((M * Adoor M : ℕ) : ℝ) = (M : ℝ) * ((Adoor M : ℕ) : ℝ) := by push_cast; ring
  have hlog2hi := Real.log_two_lt_d9
  have hlog2lo := Real.log_two_gt_d9
  -- `log(m) ≤ m - 1`
  have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  -- the head, bounded
  have hhead : ((M * Adoor M : ℕ) : ℝ) * Real.log 2
      ≤ (2 : ℝ) ^ m * (68719476736 * (m : ℝ)) := by
    rw [hMDR, hDR]
    have hc : (0 : ℝ) ≤ 68719476736 * (m : ℝ) := by positivity
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hl2 : Real.log 2 ≤ 1 := by linarith
    calc (M : ℝ) * (68719476736 * (m : ℝ)) * Real.log 2
        ≤ (M : ℝ) * (68719476736 * (m : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left hl2 (by positivity)
      _ = (M : ℝ) * (68719476736 * (m : ℝ)) := by ring
      _ ≤ (2 : ℝ) ^ m * (68719476736 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hMlt.le hc
  have hloghead : Real.log (((M * Adoor M : ℕ) : ℝ) * Real.log 2)
      ≤ (m : ℝ) * Real.log 2 + Real.log 68719476736 + Real.log (m : ℝ) := by
    have hpos : (0 : ℝ) < ((M * Adoor M : ℕ) : ℝ) * Real.log 2 :=
      mul_pos (by linarith) hlog2pos
    have hstep : Real.log (((M * Adoor M : ℕ) : ℝ) * Real.log 2)
        ≤ Real.log ((2 : ℝ) ^ m * (68719476736 * (m : ℝ))) :=
      Real.log_le_log hpos hhead
    refine le_trans hstep (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) (by linarith)]
    ring
  have hlog687 : Real.log 68719476736 ≤ 26 := by
    have := log_le_of_le_pow27 (c := (68719476736 : ℝ)) (by norm_num) 26 (r := 0) (by norm_num)
      (by norm_num)
    norm_num at this ⊢
    linarith
  -- ⟦the two products `m·log 2`, pinned so the finish is linear in monomials⟧
  have hml2hi : (m : ℝ) * Real.log 2 ≤ (m : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hlog2hi.le (by linarith)
  have hml2lo : (m : ℝ) * 0.6931471803 ≤ (m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2lo.le (by linarith)
  have h1787 := log_1787702400_le
  rw [hDR]
  linarith

/-! ## §4 — THE GRADE, PRICED; AND `RSanDoor` -/

/-- **⟦THE DOOR'S CLEARING CONSTANT⟧** `doorRho = 2⁻³⁴¹ ≈ 2.28·10⁻¹⁰³`.  The ceiling's own
budget is `δ₀²/(96(1+2π)²·108/5) ≈ 3.62·10⁻¹⁰³` at `δ₀ = 2·10⁻⁴⁹`; `2⁻³⁴¹` sits under it with
a factor `1.59` to spare, and its logarithm is `−341·log 2` — a numeral this page can read
exactly, which is why it is a power of two and not a power of ten. -/
def doorRho : ℝ := 1 / 2 ^ 341

theorem doorRho_pos : 0 < doorRho := by rw [doorRho]; positivity

/-- **⟦THE DOOR'S ANALYTIC ENVELOPE⟧** (`RSanDoor H`) — the value ⟦gate 4⟧ reads and the
ceiling must accept: `doorRho/strataResidual H²`.  The `strataResidual` denominator is exactly
the `(1 + 12·loglog H)²` the second road's demand carries. -/
def RSanDoor (H : ℕ) : ℝ := doorRho / strataResidual H ^ 2

theorem RSanDoor_nonneg (H : ℕ) : 0 ≤ RSanDoor H := by
  rw [RSanDoor, doorRho]
  positivity

/-- **⟦THE PRICING — THE PAGE'S CORE⟧** (`a2DoorGrade_priced`).  At the ratified frame, the
`φ(q)`-debited door grade sits under the door's analytic envelope:

  `arcDen 12 H · a2DoorGrade M X 2^j C₁ M₀  ≤  RSanDoor H`.

The five summands are cleared one by one (§3) against §1's `H`-side price `e^{14·loglog H}`;
the budget `2⁻³⁴² + 4·2⁻³⁴⁴ = 2⁻³⁴¹` closes exactly. -/
theorem a2DoorGrade_priced {M H j : ℕ} {X C₁ M₀ K : ℝ}
    (hfr : DoorArithFrame M H j X C₁ M₀ K) :
    arcDen 12 H * a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ ≤ RSanDoor H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by
    rw [hstr]; have := hfr.Hfloor; linarith
  have hgrade0 : (0 : ℝ) ≤ a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
    refine a2DoorGrade_nonneg M (by linarith) ?_
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    push_cast
    exact this
  have harcpos : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  -- the reduction to the `e^{14λ}` price
  have hwt := arcDen_mul_strataResidual_sq_le hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoor, le_div_iff₀ (by positivity)]
  have hkey : arcDen 12 H * a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ * strataResidual H ^ 2
      ≤ Real.exp (14 * Real.log (Real.log (H : ℝ)))
          * a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
    have : arcDen 12 H * a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ * strataResidual H ^ 2
        = (arcDen 12 H * strataResidual H ^ 2) * a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ := by
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hwt hgrade0
  refine le_trans hkey ?_
  -- the five summands
  have h1 := doorGrade_summand1_priced (H := H) hfr.C1_nonneg hfr.logX_nonneg hLX
    hfr.M0_window
  have h2 := doorGrade_summand2_priced (H := H) hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced (H := H) hLX hfr.armWeak
  have h4 := doorGrade_summand4_priced (H := H) hLX hfr.Hfloor hfr.armWeak
  have h5 := doorGrade_summand5_priced (H := H) (j := j) hfr.Hfloor hfr.jfloor
  rw [a2DoorGrade, doorRho]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-! ## §5 — THE SOCKET, GATED; AND ⟦GATE 4⟧'s READ

`M4Assembly.m4_chiSummedFreeRowBig_of_doorGrade`'s `henv` carries no gate at all (see the
header's ⟦ONE STRUCTURAL FINDING⟧).  Here it is re-proved with both hypotheses gated by
`M4Assembly.SocketBase` — the socket's own antecedent bundle, verbatim, never weakened. -/

/-- **⟦THE GATED SOCKET⟧** (`m4_chiSummedFreeRowBig_of_doorGradeGated`) — `M4Assembly`'s
socket wire with `hgrade` and `henv` both taken only where the socket actually applies them.
The proof is `M4Assembly.m4_chiSummedFreeRowBig_of_doorGrade`'s, with `SocketBase` assembled
from the socket's binders instead of re-quantified. -/
theorem m4_chiSummedFreeRowBig_of_doorGradeGated {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ}
    {RSbig : ℕ → ℕ → ℝ}
    (hgrade : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∑ χ : DirichletCharacter ℂ q, chiFreeRowSq χ M j (A + s)
        ≤ (q.totient : ℝ)
            * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s)) (M₀ (A + s)))
    (henv : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSbig j H) :
    M4ChiSummedFreeRowBig R M RSbig := by
  intro H hlo hhi L hLH q hq hqQ j hjL hjfl A hA hAj hAsq hAx hAcap s hsL
  have hb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hh1 : (1 : ℝ) ≤ ((2 ^ j : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ j)
  have hh0 : (0 : ℝ) < ((2 ^ j : ℕ) : ℝ) := by linarith
  have hG0 : 0 ≤ a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
      (M₀ (A + s)) := a2DoorGrade_nonneg M (log_natCast_nonneg' (A + s)) hh0
  have hφq : (q.totient : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.totient_le q
  have hφarc : (q.totient : ℝ) ≤ arcDen 12 H := le_trans hφq hqQ
  refine le_trans (hgrade H L q j A s hb) ?_
  refine le_trans (mul_le_mul_of_nonneg_right hφarc hG0) ?_
  exact henv H L q j A s hb

/-- **⟦THE ARITHMETIC GATE, DISCHARGED⟧** (`m4_arith_henv`) — `henv` at `RSbig j H := RSanDoor H`,
under the ratified frame at every base the socket reaches. -/
theorem m4_arith_henv {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSanDoor H :=
  fun H L q j A s hb => a2DoorGrade_priced (harith H L q j A s hb)

/-- **⟦GATE 4, READ AT THE DOOR'S ENVELOPE⟧** (`m4_arith_gate4`) — `m4_second_road`'s
⟦gate 4⟧ `∀ j H, j₀ ≤ j → RS j H ≤ RSan H` at `j₀ := doorRowFloor M`, `RSan := RSanDoor`.
Above the floor the spliced grade IS `RSanDoor H`; the `else` branch is never read. -/
theorem m4_arith_gate4 (M : ℕ) :
    ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoor H) j H ≤ RSanDoor H :=
  m4ChiRowGraded_an (fun _ _ _ => le_rfl)

/-! ## §6 — THE CEILING MET

`M4SecondRoad.m4_second_road_rs_ceiling`'s demand, at `RSanDoor`.  The `strataResidual H²`
cancels the envelope's denominator exactly, leaving the absolute number
`96(1+2π)²·(108/5)·doorRho ≤ 110525·2⁻³⁴¹ ≤ 4·10⁻⁹⁸ ≤ δ₀²`. -/

/-- **⟦THE CEILING, MET⟧** (`m4_arith_rs_ceiling_met`) — the byte-exact demand of
`M4SecondRoad.m4_second_road_rs_ceiling`, satisfied by `RSanDoor` at the register's closing
constant `δ₀ ≥ 2·10⁻⁴⁹`.  Every hypothesis is in-statement: the `δ₀` floor, and the `H`-floor
that makes `strataResidual H` nonzero. -/
theorem m4_arith_rs_ceiling_met {δ₀ : ℝ} (hδ₀ : 2 / 10 ^ 49 ≤ δ₀) {H : ℕ}
    (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H) ≤ δ₀ ^ 2 := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by rw [hstr]; linarith
  have hcancel : strataResidual H ^ 2 * (108 / 5 * RSanDoor H) = 108 / 5 * doorRho := by
    rw [RSanDoor]
    field_simp
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (1 + 2 * Real.pi) ^ 2 ≤ 53.3 := by nlinarith
  have hrhopos : 0 < doorRho := doorRho_pos
  have hrho0 : (0 : ℝ) ≤ 108 / 5 * doorRho := by rw [doorRho]; positivity
  have hδpos : (0 : ℝ) < δ₀ := by
    have : (0 : ℝ) < 2 / 10 ^ 49 := by norm_num
    linarith
  have hδsq : (4 : ℝ) / 10 ^ 98 ≤ δ₀ ^ 2 := by
    have h : (2 : ℝ) / 10 ^ 49 ≤ δ₀ := hδ₀
    nlinarith
  calc 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
      = 96 * (1 + 2 * Real.pi) ^ 2 * (strataResidual H ^ 2 * (108 / 5 * RSanDoor H)) := by
        ring
    _ = 96 * (1 + 2 * Real.pi) ^ 2 * (108 / 5 * doorRho) := by rw [hcancel]
    _ ≤ 96 * 53.3 * (108 / 5 * doorRho) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hrho0
    _ ≤ 4 / 10 ^ 98 := by rw [doorRho]; norm_num
    _ ≤ δ₀ ^ 2 := hδsq

/-! ## §7 — THE EXIT: ⟦item 11⟧ AT THE DOOR'S ENVELOPE

`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s gate list with `henv` REPLACED by the
ratified arithmetic frame — the whole point of the page. -/

/-- **⟦A4 — THE ASSEMBLY, ARITHMETIC INCLUDED⟧** (`m4_chiSummedFreeRow_of_doorArith`).
⟦Item 11⟧ of `m4_second_road` at the spliced grade `m4ChiRowGraded M (fun _ H => RSanDoor H)`.

THE COMPLETE HYPOTHESIS LIST — `hM`, `hframe`, `hrows`, `hband` are `M4Assembly`'s own four
(unchanged, byte for byte), and `harith` REPLACES its `henv`:

* `hM` — `1 ≤ M`;
* `hframe` — `M4Assembly.DoorFuseFrame` at every base the socket reaches;
* `hrows` — the weighted seam-row family at `a2Mrow`, PER CHARACTER (carried, D2's slot);
* `hband` — the `T₀`-band, PER CHARACTER (discharged by
  `M4T0DatumDischarge.m4_hT0band_at_door_discharged`);
* `harith` — `DoorArithFrame M H j (A+s) (C₁ (A+s)) (M₀ (A+s)) K` at every base the socket
  reaches: the `H`-floor, the ⟦C4⟧ arm with ⟦C3⟧'s symbolic `K`, the ⟦C1⟧ anchor, the `M₀`
  window's lower endpoint, and the window-index floor.

Composed with `m4_arith_gate4` and `m4_arith_rs_ceiling_met` this is the second road's
⟦item 11⟧ + ⟦gate 4⟧ + the ceiling, at one set of numbers. -/
theorem m4_chiSummedFreeRow_of_doorArith {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K : ℝ}
    (hM : 1 ≤ M)
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoor H)) := by
  refine m4_chiSummedFreeRow_of_big
    (m4_chiSummedFreeRowBig_of_doorGradeGated (C₁ := C₁) (M₀ := M₀) ?_ (m4_arith_henv harith))
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §8 — WHERE THE FRAME'S FIELDS COME FROM

Each field of `DoorArithFrame` is discharged from the register's own objects: the `g`-arm
(⟦C4⟧'s written form), the ⟦C1⟧ anchor `log₂M + 1 ≥ 2484`, the door's window floor
`doorRowFloor M ≤ j`, and the `M₀` window's two endpoints. -/

/-- **⟦THE `g`-ARM, WRITTEN⟧** (`gArmDoor x₀ K ω H`) — ⟦C4⟧'s ratified form

  `g H ω = max x₀ (16·ω·(log H)¹²·exp(exp(7000·loglog H + 1.25·10⁵ + 36K)))`.

Both non-literal constants ride INSIDE `g`: the ineffective `x₀` of the rate's `∃x₀`, and
⟦C3⟧'s symbolic margined-floor constant `K` (the `∃K` of `RbdSupply` §5 — NOT `cffKVt`).
The `16·ω·arcDen 12 H` prefactor is the socket's own x-scale antecedent, divided out. -/
def gArmDoor (x₀ K ω : ℝ) (H : ℕ) : ℝ :=
  max x₀ (16 * ω * arcDen 12 H
    * Real.exp (Real.exp (7000 * Real.log (Real.log (H : ℝ)) + 125000 + 36 * K)))

/-- **⟦THE ARM, DERIVED FROM THE `g`-FLOOR⟧** (`m4_arith_arm_of_gArm`) — the register's
`g`-floor `g H ω ≤ x` composed with the socket's own x-scale antecedent
`x ≤ 16·ω·arcDen 12 H·A` yields the frame's `arm` field at the base `A`.  This is the
`regimeEnlargeX'` mechanism REF-A4-MATH's R-A4-3(b) confirmed gate-neutral: only `x` moves. -/
theorem m4_arith_arm_of_gArm {x₀ K ω : ℝ} {x : ℝ} {H A : ℕ}
    (hω : 0 < ω) (hL0 : 0 ≤ Real.log (H : ℝ))
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoor x₀ K ω H ≤ x)
    (hsock : x ≤ 16 * ω * arcDen 12 H * (A : ℝ)) :
    7000 * Real.log (Real.log (H : ℝ)) + 125000 + 36 * K ≤ Real.log (Real.log (A : ℝ)) := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  have hpre : (0 : ℝ) < 16 * ω * arcDen 12 H := by positivity
  set E : ℝ := 7000 * Real.log (Real.log (H : ℝ)) + 125000 + 36 * K with hE
  have h2 : 16 * ω * arcDen 12 H * Real.exp (Real.exp E) ≤ x :=
    le_trans (le_max_right _ _) hg
  have hAle : Real.exp (Real.exp E) ≤ (A : ℝ) := by
    have := le_trans h2 hsock
    exact le_of_mul_le_mul_left (by linarith [this]) hpre
  have hApos : (0 : ℝ) < (A : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hAle
  have hlogA : Real.exp E ≤ Real.log (A : ℝ) := by
    have := Real.log_le_log (Real.exp_pos (Real.exp E)) hAle
    rwa [Real.log_exp] at this
  have := Real.log_le_log (Real.exp_pos E) hlogA
  rwa [Real.log_exp] at this

/-- The arm survives the shift `A ↦ A + s`: `loglog` is monotone above `log A > 0`. -/
theorem m4_arith_arm_of_shift {A X E : ℝ} (hA : 0 < A) (hlogA : 0 < Real.log A) (hAX : A ≤ X)
    (h : E ≤ Real.log (Real.log A)) : E ≤ Real.log (Real.log X) :=
  le_trans h (Real.log_le_log hlogA (Real.log_le_log hA hAX))

/-- **⟦C1'S ANCHOR, SPENT⟧** (`m4_arith_anchor_of_C1`) — the council's granted anchor
`log₂M + 1 ≥ 2484` discharges the frame's `anchor` field on the WHOLE register, whose top is
`loglog H ≈ 9·10¹⁰` (`M4SecondRoad.g2_of_j0_floor`'s own reading); the cap `10¹¹` is stated,
not assumed, and the slack is `9.69·10¹² vs 1.4·10¹²`. -/
theorem m4_arith_anchor_of_C1 {M H : ℕ} (hM : 2484 ≤ Nat.log 2 M + 1)
    (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11) :
    14 * Real.log (Real.log (H : ℝ)) + 269
      ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ) := by
  have hmR : (2484 : ℝ) ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) := by exact_mod_cast hM
  linarith

/-- **⟦THE WINDOW-INDEX FLOOR, SPENT⟧** (`m4_arith_jfloor_of_anchor`) — the door's own floor
`doorRowFloor M = M·Adoor M ≤ j` with the ⟦C1⟧ anchor gives `j ≥ 2^2483 ≥ 2^42`, which
dwarfs `21·loglog H + 368` on the whole register. -/
theorem m4_arith_jfloor_of_anchor {M H j : ℕ} (hM : 2484 ≤ Nat.log 2 M + 1)
    (hj : doorRowFloor M ≤ j) (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11) :
    21 * Real.log (Real.log (H : ℝ)) + 368 ≤ (j : ℝ) := by
  have hlog : 2483 ≤ Nat.log 2 M := by omega
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, Nat.log_zero_right] at hlog
    omega
  have h1 : (2 : ℕ) ^ 2483 ≤ 2 ^ (Nat.log 2 M) := Nat.pow_le_pow_right (by norm_num) hlog
  have h2 : (2 : ℕ) ^ (Nat.log 2 M) ≤ M := Nat.pow_log_le_self 2 hM0
  have hAdpos : 0 < Adoor M := by rw [Adoor]; positivity
  have hfloor : (2 : ℕ) ^ 2483 ≤ doorRowFloor M := by
    rw [doorRowFloor]
    exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_right M hAdpos)
  have h42 : (2 : ℕ) ^ 42 ≤ (2 : ℕ) ^ 2483 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hjN : (2 : ℕ) ^ 42 ≤ j := le_trans h42 (le_trans hfloor hj)
  have hjN' : (4398046511104 : ℕ) ≤ j := le_trans (by norm_num) hjN
  have hjR : (4398046511104 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjN'
  linarith

/-- **⟦THE `M₀` WINDOW — LOWER ENDPOINT, NUMERICALLY⟧** (`m4_arith_M0_window_lower`).  The
frame's exact `M0_window` field follows from REF-A4-MATH's readable form
`M₀ ≥ 0.062·loglog X + 40·loglog H + 6·log(C₁+1) + 680` (their `0.06·loglog X + 32.62λ + 670`,
rounded UP and with the two `log` terms the census had absorbed carried explicitly). -/
theorem m4_arith_M0_window_lower {H : ℕ} {X C₁ M₀ : ℝ}
    (hlam : 0 ≤ Real.log (Real.log (H : ℝ))) (hmu : 0 ≤ Real.log (Real.log X))
    (hC : 0 ≤ Real.log (C₁ + 1))
    (h : 0.062 * Real.log (Real.log X) + 40 * Real.log (Real.log (H : ℝ))
        + 6 * Real.log (C₁ + 1) + 680 ≤ M₀) :
    Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + 248) ≤ M₀ := by
  have he : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have hsum : (0 : ℝ) ≤ Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + 248 := by linarith
  calc Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
        + 2 * Real.log (C₁ + 1) + 248)
      ≤ 2.7182818286 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
        + 2 * Real.log (C₁ + 1) + 248) := mul_le_mul_of_nonneg_right he hsum
    _ ≤ 0.062 * Real.log (Real.log X) + 40 * Real.log (Real.log (H : ℝ))
        + 6 * Real.log (C₁ + 1) + 680 := by linarith
    _ ≤ M₀ := h

/-- **⟦THE `M₀` WINDOW IS NON-EMPTY⟧** (`m4_arith_M0_window_nonempty`) — the lower endpoint of
`m4_arith_M0_window_lower` sits strictly under `hErr`'s cap `2.7128·loglog X − 7.54`, under the
arm and a mild `log(C₁+1) ≤ loglog H`.  So a discharger may CHOOSE `M₀` in the window; it is
not over-determined. -/
theorem m4_arith_M0_window_nonempty {H : ℕ} {X C₁ : ℝ}
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 125000 ≤ Real.log (Real.log X))
    (hCsmall : Real.log (C₁ + 1) ≤ Real.log (Real.log (H : ℝ))) :
    0.062 * Real.log (Real.log X) + 40 * Real.log (Real.log (H : ℝ))
        + 6 * Real.log (C₁ + 1) + 680
      ≤ 2.7128 * Real.log (Real.log X) - 7.54 := by
  linarith

/-! ## §9 — THE EXIT, BUNDLED

The three things `m4_second_road` needs of the door's row grade, at ONE hypothesis set. -/

/-- **⟦A4 — THE ARITHMETIC EXIT⟧** (`m4_arith_door_exit`).  At the ratified frame:

⟦i⟧ ⟦item 11⟧ `M4ChiSummed.M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoor H))`
  — `henv` discharged, no arithmetic left open;
⟦ii⟧ ⟦gate 4⟧'s read `∀ j H, doorRowFloor M ≤ j → m4ChiRowGraded … j H ≤ RSanDoor H`;
⟦iii⟧ `M4SecondRoad.m4_second_road_rs_ceiling`'s demand, MET, on the whole register.

THE COMPLETE HYPOTHESIS LIST: `hM` (`1 ≤ M`); `hδ₀` (the register's closing constant
`δ₀ ≥ 2·10⁻⁴⁹`); `hHreg` (the register's `H`-floor: `0 ≤ log H` and `loglog H ≥ 50` on
`[Hlo, Hhi]`); `hframe`/`hrows`/`hband` (`M4Assembly`'s three slots, byte for byte); and
`harith` (`DoorArithFrame` at every base the socket reaches — the arm, the anchor, the `M₀`
window, the window-index floor, with ⟦C3⟧'s `K` symbolic). -/
theorem m4_arith_door_exit {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K δ₀ : ℝ}
    (hM : 1 ≤ M) (hδ₀ : 2 / 10 ^ 49 ≤ δ₀)
    (hHreg : ∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
      0 ≤ Real.log (H : ℝ) ∧ 50 ≤ Real.log (Real.log (H : ℝ)))
    (hframe : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorFuseFrame M (A + s) j (Cs (A + s)) (Ccc (A + s)) (ε (A + s)))
    (hrows : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ,
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) ≤ T → 2 * T ≤ (((A + s : ℕ)) : ℝ) →
        TannGate (((A + s : ℕ)) : ℝ) (2 * T) → 5 ≤ Real.log (Real.log (2 * T)) →
        (((A + s : ℕ)) : ℝ) / ((2 ^ j : ℕ) : ℝ) / T
            * (∫ t in seamAnn (((A + s : ℕ)) : ℝ) (2 * T),
                ‖spoly (2 * (A + s)) (winCutH (A + s) (doorChiCoeff χ M)) t‖ ^ 2)
          ≤ a2Mrow (Cs (A + s)) (Ccc (A + s)) M (A + s) (((A + s : ℕ)) : ℝ) (ε (A + s)))
    (hband : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ t in (-(seamT0 (((A + s : ℕ)) : ℝ)))..(seamT0 (((A + s : ℕ)) : ℝ)),
          ‖dpolyA (winCutH (A + s) (doorChiCoeff χ M))
            (seamS0 (2 * (A + s)) (((A + s : ℕ)) : ℝ)) t‖ ^ 2)
          ≤ t0BandB (((A + s : ℕ)) : ℝ) (cfbC₁ (((A + s : ℕ)) : ℝ) (C₁ (A + s))) (M₀ (A + s)))
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrame M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoor H))
      ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
          m4ChiRowGraded M (fun _ H => RSanDoor H) j H ≤ RSanDoor H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoor H)
            ≤ δ₀ ^ 2) := by
  refine ⟨m4_chiSummedFreeRow_of_doorArith hM hframe hrows hband harith,
    m4_arith_gate4 M, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met hδ₀ hL0 hlam

/-! ## §GK — the G-lever: what this page owes the lever, and what it does not

⟦THE ARITHMETIC OF THIS PAGE IS K-INVARIANT.⟧  Run the transitive K-invariance test on each
statement:

* `calP_door_one`, `calQK_door_one` — LEVEL 1, hence `G`-blind (`GLever.calE_gk_one`).  They
  are re-read at the lever below (`calP_door_one_at_lever`, `calQK_door_one_at_lever`) and
  the values are **the same numerals**, `2^{A}` and `2^{M·A}`.
* `a2Level1 M` — level 1, so `M4Assembly.a2DoorGrade` is `G`-FREE outright: none of its five
  summands reads the ladder above level 1.  Therefore
  `doorGrade_summand1..5_priced`, `a2DoorGrade_priced`, `m4_arith_gate4`,
  `m4_arith_rs_ceiling_met`, `m4_arith_henv`, `m4_arith_anchor_of_C1`,
  `m4_arith_jfloor_of_anchor`, `m4_arith_arm_of_gArm`, the `M₀`-window pair and the whole
  `DoorArithFrame`/`RSanDoor`/`doorRho` block **carry over verbatim** — they get NO twin, and
  a `_gk` sibling of any of them would be a byte-for-byte duplicate.
  (`doorRowFloor M = M·Adoor M` is `G`-free too, so `m4ChiRowGraded`'s splice does not move.)

⟦WHAT IS NOT K-INVARIANT, AND WHERE IT LIVES.⟧  Exactly the socket wiring, and none of it is
declared in this file:

* `M4ChiSummed.chiFreeRowSq` reads `M4WaveClosed.doorChiCoeff χ M
  = memSCoeff (calP (Adoor M) (3072M)) (calQK (Adoor M) (3072M) M) 2 …` — LEVEL 2, so it
  moves;  with it move `M4ChiSocketWire.M4ChiSummedFreeRowBig` and
  `M4ChiSummed.M4ChiSummedFreeRow`.
* `M4Assembly.DoorFuseFrame` carries `ThmA2.a2RowsSum M Xd` (level 2) in its `gRows` field,
  so it moves; with it moves `M4Assembly.m4_chiFreeRowSq_sum_at_door`.

Consequently `m4_chiSummedFreeRowBig_of_doorGradeGated`, `m4_chiSummedFreeRow_of_doorArith`
and `m4_arith_door_exit` DO need `_gk` twins, but each of them is BLOCKED on twins owned by
other files (`doorChiCoeff_gk`, `chiFreeRowSq_gk`, `M4ChiSummedFreeRow{,Big}_gk`,
`DoorFuseFrame_gk`, `m4_chiFreeRowSq_sum_at_door_gk`).  Their proofs are otherwise the landed
ones verbatim — `ThmA2.a2Mrow_gk` (this group) is the only moved object they read here — so
they are one-line rewires once those land. -/

/-- **`P₁` AT THE LEVER IS THE SAME NUMERAL** — `calP_door_one` re-read at `s13GK K M`. -/
theorem calP_door_one_at_lever (K M : ℕ) : calP (Adoor M) (s13GK K M) 1 = 2 ^ Adoor M := by
  rw [calP, calE_gk_one]

/-- **`Q₁` AT THE LEVER IS THE SAME NUMERAL** — `calQK_door_one` re-read at `s13GK K M`. -/
theorem calQK_door_one_at_lever (K M : ℕ) :
    calQK (Adoor M) (s13GK K M) M 1 = 2 ^ (M * Adoor M) := by
  rw [calQK, calE_gk_one]
  norm_num

-- #audit (temporary)

end Salt.MR
