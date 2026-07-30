/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.M4ArithPage

/-!
# ⟦A4ρ — THE ARITHMETIC PAGE, RE-PARAMETRIZED OVER `ρ`⟧ (`M4ArithRho`)

Design provenance: the 2026-07-30 council's ⟦GRANT 2⟧ (the ρ-RE-PARAMETRIZATION), on the
DENSITY-SCOPE dossier's ⟦hδ₀⟧ finding.  This file is PURELY ADDITIVE: it touches no
declaration of `M4ArithPage`, weakens nothing, and re-proves the whole door-arithmetic page
with the fixed numeral `doorRho = 2⁻³⁴¹` replaced by a universally quantified `ρ ∈ (0, 1]`.

## ⟦THE PROBLEM THIS FIXES⟧

`M4ArithPage.m4_arith_rs_ceiling_met` (and hence `m4_arith_door_exit`) carries the hypothesis
`hδ₀ : 2/10⁴⁹ ≤ δ₀`.  That is **not derivable**: `δ₀` is bound existentially in
`Salt.Entropy.Chowla.SpineFinal.log_chowla_two_budget_head_g` as `cD3/(16C)·ε/(2K)` over three
opaque `∃`-witnesses, and the road exposes only `0 < δ₀`.  A fixed numeral `doorRho` that must
beat `δ₀²` therefore cannot be discharged.

The repair: make the clearing constant a PARAMETER.  Every numeral this page spends is
re-derived at a symbolic `ρ`, and the `ρ`-cost lands in exactly four places — the arm, the
anchor, the `M₀` window and the window-index floor — each of which is an `H`-free additive
constant once `ρ` is fixed.

## ⟦THE BUDGET SPLIT⟧

`M4ArithPage`'s split is `2⁻³⁴² + 4·2⁻³⁴⁴ = 2⁻³⁴¹`: summand 3 takes HALF the budget and the
other four take an EIGHTH each.  Mirrored exactly:

```
      summand 3  ≤  ρ/2 ,      summands 1, 2, 4, 5  ≤  ρ/8 ,      ρ/2 + 4·(ρ/8) = ρ .
```

## ⟦THE EXACT ARM — THE COEFFICIENT IS 500, NOT 1000⟧

Summand 3 is the summand that fixes the arm.  Writing `λ := loglog H`, `μ := loglog X`,
`L := log(1/ρ)`, its demand at budget `ρ/2` reads

```
      188133 · (log X)^{−1/500} · e^{14λ}  ≤  ρ/2
  ⟺   μ/500  ≥  14λ + log 188133 + log 2 + L
  ⟺   μ  ≥  7000λ + 500·L + 500·(log 188133 + log 2) .
```

With this page's own numerals (`log 188133 ≤ 12.5`, `log 2 < 0.6931471808`) the constant is
`500 · 13.1932 = 6596.6`, rounded UP to **6600**.  So the ratified ⟦C4⟧ arm becomes

```
      7000·loglog H  +  500·log(1/ρ)  +  6600  +  36K   ≤   loglog X .
```

**The coefficient of `log(1/ρ)` is 500.**  The dossier's "1000" is the coefficient in terms of
`δ₀`, not `ρ`: at the consumer's instantiation `ρ := δ₀²/110525` one has
`L = 2·log(1/δ₀) + log 110525`, so `500·L = 1000·log(1/δ₀) + 500·log 110525` — the `2·500` is
the SQUARE in `δ₀²`, and it appears only after `ρ` is eliminated.  At a symbolic `ρ` the
honest coefficient is 500, and 500 is what is stated (a weaker hypothesis, hence a stronger
theorem).

Sanity check against the frozen page: at `ρ = 2⁻³⁴¹` one has `L = 341·log 2 = 236.38`, so the
arm reads `7000λ + 118190 + 6600 = 7000λ + 124790`, against `M4ArithPage`'s ratified
`7000λ + 125000` — the same number to within the two pages' rounding, as it must be.

## ⟦THE OTHER THREE `ρ`-COSTS⟧

* `anchor` — `14λ + L + 33 ≤ 3.9·10⁹·(log₂M+1)` (the frozen page's `269` is
  `30.6 + 344·log 2`; the `ρ`-free part is `32.02`, rounded up to `33`).
* `M0_window` — `M₀ ≥ e·(μ/45 + 14λ + 2log(C₁+1) + L + 12)` (the frozen `248` is
  `9.04 + 344·log 2`; the `ρ`-free part is `11.28`, rounded up to `12`).
* `jfloor` — `j ≥ 21λ + 2L + 28` (the frozen `368` is `26.1 + 341·log 2/log 2`; the `ρ`-free
  part is `26.1`, rounded up to `28`, and `2 ≥ 1/log 2 = 1.4427` prices the `L`).

## ⟦THE CEILING CONSTANT, EXACTLY⟧

`M4SecondRoad.m4_second_road_rs_ceiling`'s demand at `RSanDoorRho ρ H := ρ/strataResidual H²`
cancels the `strataResidual H²` exactly, leaving the absolute number

```
      96 · (1 + 2π)² · (108/5) · ρ   ≤   δ₀² .
```

`96·(1+2π)²·108/5 = 109,993.67` exactly; at this page's own `π < 3.15` (mathlib's
`Real.pi_lt_d2`, giving `(1+2π)² ≤ 53.3`) the readable bound is `96·53.3·21.6 = 110,522.88`,
rounded UP to **110525**.  So the ceiling exit's hypothesis is

```
      0 < ρ   and   110525·ρ ≤ δ₀²   —   and NOTHING about δ₀ itself.
```

No positivity of `δ₀` is needed, let alone a numeric floor: `δ₀` occurs only through `δ₀²`.

## ⟦THE CONSUMER NOTE — WHY THE `ρ`-COST IS FREE⟧

`M4Exit.m4_exit_socket_split` (and its source
`SpineFinal.log_chowla_two_budget_head_g`) has the quantifier shape

```
      ∃ ε δ₀,  0 < ε ∧ 0 < δ₀ ∧  ∀ U1floor g,  ∃ R,  … g R.Hhi R.ω ≤ R.x …
```

— `δ₀` is FIXED BEFORE `g` is chosen.  The S11 spine therefore instantiates

```
      ρ  :=  doorRhoOfDelta δ₀  =  min 1 (δ₀²/110525)
```

immediately after `δ₀` is obtained (`doorRhoOfDelta_pos`, `doorRhoOfDelta_le_one`,
`doorRhoOfDelta_spec` supply the three facts the frame and the ceiling want), and only THEN
picks `g := gArmDoorRho x₀ K ω ρ`.  The whole `500·log(1/ρ)` cost rides inside `g`'s exponent,
where it is an `H`-free additive constant: **zero H-demand, zero new gate, and no numeric
claim about `δ₀` anywhere.**  The three caps the suppliers of the anchor and the `jfloor` ask
(`log(1/ρ) ≤ 10¹¹`) are likewise decidable once `δ₀` is fixed — they are not claims about the
opaque witness's SIZE but about the register's own width, met with 4 orders to spare at
`log(1/ρ) ≤ 10¹¹` (i.e. `ρ ≥ e^{−10¹¹}`).

## ⟦THE FOUR LOG SCALES, STILL APART⟧

`Nat.log 2` (the dyadic index and the anchor `log₂M+1`); `arcDen 12 H = (log H)¹²`;
`λ = loglog H`; `μ = loglog X`.  `L = log(1/ρ)` is a FIFTH, `H`-free and `X`-free scale and is
never conflated with any of them: it appears only additively, and every lemma below states it
explicitly.
-/

set_option maxRecDepth 40000
set_option exponentiation.threshold 3000

noncomputable section

open scoped BigOperators

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §0 — THE `ρ` SCALE

`L := log(1/ρ)`, and the two numeral stones the budget split needs. -/

/-- `log(1/ρ) = −log ρ` — the identity every summand's right-hand side is read through. -/
theorem log_one_div_eq_neg (ρ : ℝ) : Real.log (1 / ρ) = -Real.log ρ := by
  rw [one_div, Real.log_inv]

/-- `L ≥ 0` on `(0, 1]` — the ONE place `ρ ≤ 1` is spent (summands 4 and 5, and the window's
non-emptiness).  A consumer with `ρ > 1` simply shrinks it; `doorRhoOfDelta` does. -/
theorem log_one_div_nonneg {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) : 0 ≤ Real.log (1 / ρ) := by
  rw [log_one_div_eq_neg, neg_nonneg]
  exact Real.log_nonpos hρ0.le hρ1

/-- `log 8 = 3·log 2` — the eighth-budget's own numeral. -/
theorem log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
  push_cast; ring

/-! ## §1 — THE `ρ`-PARAMETRIC ENVELOPE AND FRAME -/

/-- **⟦THE DOOR'S ANALYTIC ENVELOPE, AT `ρ`⟧** (`RSanDoorRho ρ H`) — `M4ArithPage.RSanDoor`
with the fixed numeral `doorRho` replaced by the parameter: `ρ/strataResidual H²`.  The
`strataResidual` denominator is exactly the `(1 + 12·loglog H)²` the second road's demand
carries, and it cancels EXACTLY at the ceiling. -/
def RSanDoorRho (ρ : ℝ) (H : ℕ) : ℝ := ρ / strataResidual H ^ 2

theorem RSanDoorRho_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (H : ℕ) : 0 ≤ RSanDoorRho ρ H :=
  div_nonneg hρ (sq_nonneg _)

/-- At `ρ = doorRho` this IS `M4ArithPage.RSanDoor` — the frozen page is the `ρ = 2⁻³⁴¹`
instance, byte for byte. -/
theorem RSanDoorRho_doorRho (H : ℕ) : RSanDoorRho doorRho H = RSanDoor H := rfl

/-- **⟦THE RATIFIED ARITHMETIC FRAME, AT `ρ`⟧** (`DoorArithFrameRho M H j X C₁ M₀ K ρ`) —
`M4ArithPage.DoorArithFrame` with the four `ρ`-carrying fields.  `K` is ⟦C3⟧'s symbolic
margined-floor constant (`RbdSupply` §5's `∃K`, NOT `cffKVt`): carried, never evaluated.
`ρ` is likewise carried and never evaluated. -/
structure DoorArithFrameRho (M H j : ℕ) (X C₁ M₀ K ρ : ℝ) : Prop where
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
  /-- **the clearing parameter is positive** — the ONLY thing asked of `ρ` beyond `≤ 1`. -/
  rho_pos : 0 < ρ
  /-- **the clearing parameter is a budget** `ρ ≤ 1`, i.e. `log(1/ρ) ≥ 0`. -/
  rho_le_one : ρ ≤ 1
  /-- **⟦C4 — THE ARM, AT `ρ`⟧** `loglog X ≥ 7000·loglog H + 500·log(1/ρ) + 6600 + 36K`. -/
  arm : 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600 + 36 * K
    ≤ Real.log (Real.log X)
  /-- **⟦C1 — THE 12× ANCHOR, AT `ρ`⟧** `14·loglog H + log(1/ρ) + 33 ≤ 3.9·10⁹·(log₂M+1)`. -/
  anchor : 14 * Real.log (Real.log (H : ℝ)) + Real.log (1 / ρ) + 33
    ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ)
  /-- the band constant is a constant. -/
  C1_nonneg : 0 ≤ C₁
  /-- **⟦C4 — THE `M₀` WINDOW, LOWER ENDPOINT, AT `ρ`⟧**
  `M₀ ≥ e·(loglog X/45 + 14·loglog H + 2·log(C₁+1) + log(1/ρ) + 12)`. -/
  M0_window : Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12) ≤ M₀
  /-- **the window index floor, at `ρ`** `j ≥ 21·loglog H + 2·log(1/ρ) + 28`. -/
  jfloor : 21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28 ≤ (j : ℝ)

namespace DoorArithFrameRho

variable {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}

theorem logInvRho_nonneg (h : DoorArithFrameRho M H j X C₁ M₀ K ρ) :
    0 ≤ Real.log (1 / ρ) :=
  log_one_div_nonneg h.rho_pos h.rho_le_one

theorem one_lt_logH (h : DoorArithFrameRho M H j X C₁ M₀ K ρ) : 1 < Real.log (H : ℝ) :=
  one_lt_log_of_loglog_ge h.logH_nonneg (by norm_num) h.Hfloor

theorem armWeak (h : DoorArithFrameRho M H j X C₁ M₀ K ρ) :
    7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log X) := by
  have := h.arm
  have := h.Knonneg
  linarith

theorem loglogX_ge (h : DoorArithFrameRho M H j X C₁ M₀ K ρ) :
    356600 ≤ Real.log (Real.log X) := by
  have h1 := h.armWeak
  have h2 := h.Hfloor
  have h3 := h.logInvRho_nonneg
  linarith

theorem one_lt_logX (h : DoorArithFrameRho M H j X C₁ M₀ K ρ) : 1 < Real.log X :=
  one_lt_log_of_loglog_ge h.logX_nonneg (show (0:ℝ) < 356600 by norm_num) h.loglogX_ge

end DoorArithFrameRho

/-! ## §2 — THE FIVE SUMMANDS, AT `ρ`

Each summand of `M4Assembly.a2DoorGrade`, priced against `M4ArithPage`'s `H`-side price
`e^{14·loglog H}` at its own field of the `ρ`-frame.  The budget: summand 3 takes `ρ/2`, the
other four take `ρ/8` each; `ρ/2 + 4·(ρ/8) = ρ`. -/

/-- **SUMMAND 1 AT `ρ/8` — the `T₀`-band head, via the `M₀` window.**
`8448·cfbC₁(X,C₁)²·e^{−M₀/e}`; the window's lower endpoint carries `log(1/ρ)` explicitly, so
the whole `ρ`-cost of this summand is `e·log(1/ρ)` of `M₀`. -/
theorem doorGrade_summand1_priced_rho {H : ℕ} {X C₁ M₀ ρ : ℝ}
    (hρ : 0 < ρ) (hC₁ : 0 ≤ C₁) (hLX0 : 0 ≤ Real.log X) (hLX : 1 < Real.log X)
    (hM₀ : Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
        + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12) ≤ M₀) :
    8448 * cfbC₁ X C₁ ^ 2 * Real.exp (-(1 / Real.exp 1) * M₀)
        * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 8 := by
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
          + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12) := by
    have hinv : (0 : ℝ) < 1 / Real.exp 1 := by positivity
    have := mul_le_mul_of_nonneg_left hM₀ hinv.le
    rw [← mul_assoc] at this
    rw [show (1 / Real.exp 1) * Real.exp 1 = 1 by field_simp] at this
    rw [one_mul] at this
    linarith
  refine le_of_log_le' (by positivity) (div_pos hρ (by norm_num)) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hcf.ne', Real.log_exp, Real.log_exp, hsq,
    Real.log_mul (by positivity) hseam.ne', seamT0, Real.log_rpow hLXpos,
    show ((C₁ + 1) : ℝ) ^ (2 : ℕ) = (C₁ + 1) * (C₁ + 1) by ring,
    Real.log_mul hC1pos.ne' hC1pos.ne',
    Real.log_div hρ.ne' (by norm_num : (8 : ℝ) ≠ 0), log_eight_eq]
  have hLinv : Real.log (1 / ρ) = -Real.log ρ := log_one_div_eq_neg ρ
  have h8448 := log_8448_le
  have hlog2 := Real.log_two_lt_d9
  linarith

/-- **SUMMAND 2 AT `ρ/8` — the level-1 grade, via the ⟦C1⟧ 12× ANCHOR.**
`1787702400·a2Level1 M` clears `ρ/8` under `14·loglog H + log(1/ρ) + 33 ≤ 3.9·10⁹·(log₂M+1)`. -/
theorem doorGrade_summand2_priced_rho {M H : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hM : 1 ≤ M)
    (hanchor : 14 * Real.log (Real.log (H : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ)) :
    1787702400 * a2Level1 M * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 8 := by
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
  refine le_of_log_le' (by positivity) (div_pos hρ (by norm_num)) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hlvlpos.ne', Real.log_exp, a2Level1,
    Real.log_div hnum.ne' hden.ne', Real.log_rpow hlogQpos, Real.log_rpow hPpos,
    hlogQ, hlogP, Real.log_div hρ.ne' (by norm_num : (8 : ℝ) ≠ 0), log_eight_eq]
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
  have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have hhead : ((M * Adoor M : ℕ) : ℝ) * Real.log 2
      ≤ (2 : ℝ) ^ m * (68719476736 * (m : ℝ)) := by
    rw [hMDR, hDR]
    have hc : (0 : ℝ) ≤ 68719476736 * (m : ℝ) := by positivity
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
  have hLinv : Real.log (1 / ρ) = -Real.log ρ := log_one_div_eq_neg ρ
  rw [hDR]
  linarith

/-- **SUMMAND 3 AT `ρ/2` — the `𝒯`/rows grading residue, via the ARM.**
`188133·(log X)^{−1/500}`: **the summand that fixes the arm**.  Clearing `ρ/2` demands
`loglog X ≥ 7000·loglog H + 500·log(1/ρ) + 500·(log 188133 + log 2)`, and `6600` clears the
latter (`= 6596.6`) with `3.4` to spare. -/
theorem doorGrade_summand3_priced_rho {H : ℕ} {X ρ : ℝ}
    (hρ : 0 < ρ) (hLX : 1 < Real.log X)
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log X)) :
    188133 * (Real.log X) ^ (-(1 : ℝ) / 500)
        * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 2 := by
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hrp : (0 : ℝ) < (Real.log X) ^ (-(1 : ℝ) / 500) := Real.rpow_pos_of_pos hLXpos _
  refine le_of_log_le' (by positivity) (div_pos hρ (by norm_num)) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by norm_num) hrp.ne', Real.log_exp, Real.log_rpow hLXpos,
    Real.log_div hρ.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  have hLinv : Real.log (1 / ρ) = -Real.log ρ := log_one_div_eq_neg ρ
  have h188 := log_188133_le
  have hlog2 := Real.log_two_lt_d9
  linarith

/-- **SUMMAND 4 AT `ρ/8` — the ball residue, via the ARM (slackly).**
`304128·ballSupC²·(log X)^{−43/45}(1+loglog X)²`: its own `(log X)^{−43/45}` pays; the arm's
`6600` alone already covers the whole `ρ`-cost, with a factor `107` of slack on the `L`-term. -/
theorem doorGrade_summand4_priced_rho {H : ℕ} {X ρ : ℝ}
    (hρ : 0 < ρ) (hLrho : 0 ≤ Real.log (1 / ρ)) (hLX : 1 < Real.log X)
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log X)) :
    304128 * ballSupC ^ 2
        * ((Real.log X) ^ (-(43 : ℝ) / 45) * (1 + Real.log (Real.log X)) ^ 2)
        * Real.exp (14 * Real.log (Real.log (H : ℝ))) ≤ ρ / 8 := by
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hμ : (356600 : ℝ) ≤ Real.log (Real.log X) := by linarith
  have hrp : (0 : ℝ) < (Real.log X) ^ (-(43 : ℝ) / 45) := Real.rpow_pos_of_pos hLXpos _
  have hone : (0 : ℝ) < 1 + Real.log (Real.log X) := by linarith
  have hball : (0 : ℝ) < ballSupC := ballSupC_pos
  refine le_of_log_le' (by positivity) (div_pos hρ (by norm_num)) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_mul hrp.ne' (by positivity), Real.log_exp, Real.log_rpow hLXpos,
    show (ballSupC : ℝ) ^ (2 : ℕ) = ballSupC * ballSupC by ring,
    Real.log_mul hball.ne' hball.ne',
    show ((1 + Real.log (Real.log X)) : ℝ) ^ (2 : ℕ)
      = (1 + Real.log (Real.log X)) * (1 + Real.log (Real.log X)) by ring,
    Real.log_mul hone.ne' hone.ne',
    Real.log_div hρ.ne' (by norm_num : (8 : ℝ) ≠ 0), log_eight_eq]
  have hLinv : Real.log (1 / ρ) = -Real.log ρ := log_one_div_eq_neg ρ
  have h304 := log_304128_le
  have hbc := log_ballSupC_le
  have hlog2 := Real.log_two_lt_d9
  -- `log(1+μ) ≤ (1+μ)/e ≤ (10/27)(1+μ)`
  have hlogmu : Real.log (1 + Real.log (Real.log X))
      ≤ (10 / 27) * (1 + Real.log (Real.log X)) := by
    refine le_trans (log_le_div_exp_one hone) ?_
    rw [div_le_iff₀ (Real.exp_pos 1)]
    nlinarith [exp_one_gt_27, hone]
  linarith

/-- **SUMMAND 5 AT `ρ/8` — the `1/h` tail, via the window index floor.**
`6315000/2^j` at `j ≥ 21·loglog H + 2·log(1/ρ) + 28`; the coefficient `2 ≥ 1/log 2` is what
prices `log(1/ρ)` in a DYADIC index. -/
theorem doorGrade_summand5_priced_rho {H j : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (hLrho : 0 ≤ Real.log (1 / ρ))
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (hj : 21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28 ≤ (j : ℝ)) :
    6315000 / ((2 ^ j : ℕ) : ℝ) * Real.exp (14 * Real.log (Real.log (H : ℝ)))
      ≤ ρ / 8 := by
  have h2j : ((2 ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
  have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [h2j]
  refine le_of_log_le' (by positivity) (div_pos hρ (by norm_num)) ?_
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_div (by norm_num) h2jpos.ne', Real.log_pow, Real.log_exp,
    Real.log_div hρ.ne' (by norm_num : (8 : ℝ) ≠ 0), log_eight_eq]
  have hLinv : Real.log (1 / ρ) = -Real.log ρ := log_one_div_eq_neg ρ
  have h63 := log_6315000_le
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  -- the dyadic index, linearised: `j·log 2 ≥ (21λ + 2L + 28)·0.6931471803`
  have hbrack : (0 : ℝ) ≤ 21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28 := by
    linarith
  have hprod : (21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28) * 0.6931471803
      ≤ (21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlo.le hbrack
  have hjl : (21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28) * Real.log 2
      ≤ (j : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_right hj (by linarith)
  linarith

/-! ## §3 — THE GRADE, PRICED AT `ρ` -/

/-- **⟦THE PRICING AT `ρ` — THE PAGE'S CORE⟧** (`a2DoorGrade_priced_rho`).  At the
`ρ`-parametric frame, the `φ(q)`-debited door grade sits under the `ρ`-envelope:

  `arcDen 12 H · a2DoorGrade M X 2^j C₁ M₀  ≤  RSanDoorRho ρ H`.

The five summands are cleared one by one (§2) against `M4ArithPage`'s `H`-side price
`e^{14·loglog H}`; the budget `ρ/2 + 4·(ρ/8) = ρ` closes exactly. -/
theorem a2DoorGrade_priced_rho {M H j : ℕ} {X C₁ M₀ K ρ : ℝ}
    (hfr : DoorArithFrameRho M H j X C₁ M₀ K ρ) :
    arcDen 12 H * a2DoorGrade M X ((2 ^ j : ℕ) : ℝ) C₁ M₀ ≤ RSanDoorRho ρ H := by
  have hL1 : 1 < Real.log (H : ℝ) := hfr.one_lt_logH
  have hLX : 1 < Real.log X := hfr.one_lt_logX
  have hLrho : 0 ≤ Real.log (1 / ρ) := hfr.logInvRho_nonneg
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
  have hwt := arcDen_mul_strataResidual_sq_le hfr.logH_nonneg hfr.Hfloor
  rw [RSanDoorRho, le_div_iff₀ (pow_pos hstrpos 2)]
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
  have h1 := doorGrade_summand1_priced_rho (H := H) hfr.rho_pos hfr.C1_nonneg hfr.logX_nonneg
    hLX hfr.M0_window
  have h2 := doorGrade_summand2_priced_rho (H := H) hfr.rho_pos hfr.Mpos hfr.anchor
  have h3 := doorGrade_summand3_priced_rho (H := H) hfr.rho_pos hLX hfr.armWeak
  have h4 := doorGrade_summand4_priced_rho (H := H) hfr.rho_pos hLrho hLX hfr.Hfloor hfr.armWeak
  have h5 := doorGrade_summand5_priced_rho (H := H) (j := j) hfr.rho_pos hLrho hfr.Hfloor
    hfr.jfloor
  rw [a2DoorGrade]
  ring_nf
  ring_nf at h1 h2 h3 h4 h5
  linarith

/-! ## §4 — THE SOCKET'S `henv`, AND ⟦GATE 4⟧'s READ, AT `ρ`

`M4ArithPage.m4_chiSummedFreeRowBig_of_doorGradeGated` is already `RSbig`-parametric, so it is
reused verbatim: nothing about the gating is `ρ`-dependent. -/

/-- **⟦THE ARITHMETIC GATE, DISCHARGED AT `ρ`⟧** (`m4_arith_henv_rho`) — `henv` at
`RSbig j H := RSanDoorRho ρ H`, under the `ρ`-frame at every base the socket reaches. -/
theorem m4_arith_henv_rho {R : ChowlaRegime} {M : ℕ} {C₁ M₀ : ℕ → ℝ} {K ρ : ℝ}
    (harith : ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    ∀ H L q j A s : ℕ, SocketBase R M H L q j A s →
      arcDen 12 H * a2DoorGrade M (((A + s : ℕ)) : ℝ) ((2 ^ j : ℕ) : ℝ) (C₁ (A + s))
          (M₀ (A + s))
        ≤ RSanDoorRho ρ H :=
  fun H L q j A s hb => a2DoorGrade_priced_rho (harith H L q j A s hb)

/-- **⟦GATE 4, READ AT THE `ρ`-ENVELOPE⟧** (`m4_arith_gate4_rho`) — `m4_second_road`'s
⟦gate 4⟧ at `j₀ := doorRowFloor M`, `RSan := RSanDoorRho ρ`. -/
theorem m4_arith_gate4_rho (M : ℕ) (ρ : ℝ) :
    ∀ j H : ℕ, doorRowFloor M ≤ j →
      m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H :=
  m4ChiRowGraded_an (fun _ _ _ => le_rfl)

/-! ## §5 — THE CEILING MET, WITH NO NUMERIC CLAIM ABOUT `δ₀`

`M4SecondRoad.m4_second_road_rs_ceiling`'s demand at `RSanDoorRho`.  The `strataResidual H²`
cancels the envelope's denominator EXACTLY, leaving the absolute number
`96(1+2π)²·(108/5)·ρ ≤ 110525·ρ ≤ δ₀²`. -/

/-- **⟦THE CEILING, MET AT `ρ`⟧** (`m4_arith_rs_ceiling_met_rho`) — the byte-exact demand of
`M4SecondRoad.m4_second_road_rs_ceiling`, satisfied by `RSanDoorRho ρ`.

THE COMPLETE HYPOTHESIS LIST: `0 < ρ`; `110525·ρ ≤ δ₀²`; and the `H`-floor that makes
`strataResidual H` nonzero.  **No hypothesis on `δ₀` at all** — not a numeric floor, not even
positivity: `δ₀` occurs only through `δ₀²`.  The exact constant is
`96(1+2π)²·108/5 = 109,993.67`; at this page's `π < 3.15` it reads `110,522.88`, and `110525`
is the honest round-up. -/
theorem m4_arith_rs_ceiling_met_rho {ρ δ₀ : ℝ} (hρ : 0 < ρ) (hρδ : 110525 * ρ ≤ δ₀ ^ 2)
    {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
      ≤ δ₀ ^ 2 := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have hstr : strataResidual H = 1 + 12 * Real.log (Real.log (H : ℝ)) :=
    strataResidual_eq_of_pos (by linarith)
  have hstrpos : (0 : ℝ) < strataResidual H := by rw [hstr]; linarith
  have hcancel : strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H) = 108 / 5 * ρ := by
    rw [RSanDoorRho]
    field_simp
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpipos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (1 + 2 * Real.pi) ^ 2 ≤ 53.3 := by nlinarith
  have hrho0 : (0 : ℝ) ≤ 108 / 5 * ρ := by positivity
  calc 96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
      = 96 * (1 + 2 * Real.pi) ^ 2 * (strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)) := by
        ring
    _ = 96 * (1 + 2 * Real.pi) ^ 2 * (108 / 5 * ρ) := by rw [hcancel]
    _ ≤ 96 * 53.3 * (108 / 5 * ρ) := mul_le_mul_of_nonneg_right (by nlinarith) hrho0
    _ ≤ 110525 * ρ := by nlinarith
    _ ≤ δ₀ ^ 2 := hρδ

/-! ### The consumer's `ρ`

`doorRhoOfDelta δ₀ = min 1 (δ₀²/110525)`: the value the S11 spine instantiates the moment
`δ₀` leaves `m4_exit_socket_split`'s `∃`.  The `min 1` costs nothing (the real `δ₀` is
astronomically small) and buys the frame's `ρ ≤ 1` field outright. -/

/-- **⟦THE CONSUMER'S `ρ`⟧** — `min 1 (δ₀²/110525)`. -/
def doorRhoOfDelta (δ₀ : ℝ) : ℝ := min 1 (δ₀ ^ 2 / 110525)

theorem doorRhoOfDelta_le_one (δ₀ : ℝ) : doorRhoOfDelta δ₀ ≤ 1 := min_le_left _ _

theorem doorRhoOfDelta_pos {δ₀ : ℝ} (hδ : δ₀ ≠ 0) : 0 < doorRhoOfDelta δ₀ := by
  rw [doorRhoOfDelta, lt_min_iff]
  refine ⟨by norm_num, ?_⟩
  have : (0 : ℝ) < δ₀ ^ 2 := by positivity
  positivity

/-- **⟦THE CEILING'S HYPOTHESIS, MET BY CONSTRUCTION⟧** — `110525·doorRhoOfDelta δ₀ ≤ δ₀²`,
for EVERY real `δ₀`.  This is the whole content of the re-parametrization: the numeric claim
that was unprovable about the opaque witness is now a definitional inequality. -/
theorem doorRhoOfDelta_spec (δ₀ : ℝ) : 110525 * doorRhoOfDelta δ₀ ≤ δ₀ ^ 2 := by
  have h : doorRhoOfDelta δ₀ ≤ δ₀ ^ 2 / 110525 := min_le_right _ _
  have := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 110525)
  calc 110525 * doorRhoOfDelta δ₀ ≤ 110525 * (δ₀ ^ 2 / 110525) := this
    _ = δ₀ ^ 2 := by ring

/-- **⟦THE CEILING, MET AT THE CONSUMER'S `ρ`⟧** — `m4_arith_rs_ceiling_met_rho` with the
hypothesis discharged: at `ρ := doorRhoOfDelta δ₀` the ceiling holds from `δ₀ ≠ 0` alone. -/
theorem m4_arith_rs_ceiling_met_of_delta {δ₀ : ℝ} (hδ : δ₀ ≠ 0)
    {H : ℕ} (hL0 : 0 ≤ Real.log (H : ℝ)) (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) :
    96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
        * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
      ≤ δ₀ ^ 2 :=
  m4_arith_rs_ceiling_met_rho (doorRhoOfDelta_pos hδ) (doorRhoOfDelta_spec δ₀) hL0 hlam

/-! ## §6 — ⟦ITEM 11⟧ AT THE `ρ`-ENVELOPE

`M4Assembly.m4_chiSummedFreeRow_of_doorAssembly`'s gate list with `henv` REPLACED by the
`ρ`-frame.  Byte for byte `M4ArithPage.m4_chiSummedFreeRow_of_doorArith` with `RSanDoor`
replaced by `RSanDoorRho ρ` and `DoorArithFrame` by `DoorArithFrameRho`. -/

/-- **⟦A4ρ — THE ASSEMBLY, ARITHMETIC INCLUDED⟧** (`m4_chiSummedFreeRow_of_doorArithRho`).
⟦Item 11⟧ of `m4_second_road` at the spliced grade `m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)`.

THE COMPLETE HYPOTHESIS LIST — `hM`, `hframe`, `hrows`, `hband` are `M4Assembly`'s own four
(unchanged, byte for byte), and `harith` is the `ρ`-frame at every base the socket reaches. -/
theorem m4_chiSummedFreeRow_of_doorArithRho {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K ρ : ℝ}
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
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H)) := by
  refine m4_chiSummedFreeRow_of_big
    (m4_chiSummedFreeRowBig_of_doorGradeGated (C₁ := C₁) (M₀ := M₀) ?_
      (m4_arith_henv_rho harith))
  intro H L q j A s hb
  obtain ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩ := hb
  haveI : NeZero q := ⟨hq.ne'⟩
  have hbb : SocketBase R M H L q j A s :=
    ⟨hlo, hhi, hLH, hq, hqQ, hjL, hjfl, hA, hAj, hAsq, hAx, hAcap, hsL⟩
  have hF := hframe H L q j A s hbb
  exact m4_chiFreeRowSq_sum_at_door hM hF.X_exp hF.X_three hF.h_four hF.h_window hF.tann
    hF.ceil5 (hrows H L q j A s hbb) (hband H L q j A s hbb) hF.gP1 hF.gRows
    ⟨hF.eps_lo, hF.eps_hi⟩ hF.L4096

/-! ## §7 — WHERE THE `ρ`-FRAME'S FIELDS COME FROM

Each field of `DoorArithFrameRho` is discharged from the register's own objects, exactly as in
`M4ArithPage` §8, with the `ρ`-cost carried explicitly. -/

/-- **⟦THE `g`-ARM, WRITTEN AT `ρ`⟧** (`gArmDoorRho x₀ K ω ρ H`) — ⟦C4⟧'s ratified form with
the `ρ`-cost inside:

  `g H ω = max x₀ (16·ω·(log H)¹²·exp(exp(7000·loglog H + 500·log(1/ρ) + 6600 + 36K)))`.

THREE non-literal constants now ride INSIDE `g`: the ineffective `x₀` of the rate's `∃x₀`,
⟦C3⟧'s symbolic `K`, and `ρ`.  All three are FIXED BEFORE `g` is chosen at
`m4_exit_socket_split`'s `∃ε δ₀ … ∀g ∃R`, so the `ρ`-cost imposes **zero H-demand**. -/
def gArmDoorRho (x₀ K ω ρ : ℝ) (H : ℕ) : ℝ :=
  max x₀ (16 * ω * arcDen 12 H
    * Real.exp (Real.exp (7000 * Real.log (Real.log (H : ℝ))
        + 500 * Real.log (1 / ρ) + 6600 + 36 * K)))

/-- **⟦THE ARM, DERIVED FROM THE `g`-FLOOR⟧** (`m4_arith_arm_of_gArmRho`) — the register's
`g`-floor `g H ω ≤ x` composed with the socket's own x-scale antecedent
`x ≤ 16·ω·arcDen 12 H·A` yields the `ρ`-frame's `arm` field at the base `A`. -/
theorem m4_arith_arm_of_gArmRho {x₀ K ω ρ : ℝ} {x : ℝ} {H A : ℕ}
    (hω : 0 < ω) (hL0 : 0 ≤ Real.log (H : ℝ))
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ)))
    (hg : gArmDoorRho x₀ K ω ρ H ≤ x)
    (hsock : x ≤ 16 * ω * arcDen 12 H * (A : ℝ)) :
    7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600 + 36 * K
      ≤ Real.log (Real.log (A : ℝ)) := by
  have hL1 : 1 < Real.log (H : ℝ) := one_lt_log_of_loglog_ge hL0 (by norm_num) hlam
  have harc : (0 : ℝ) < arcDen 12 H := by
    rw [arcDen]; exact Real.rpow_pos_of_pos (by linarith) _
  have hpre : (0 : ℝ) < 16 * ω * arcDen 12 H := by positivity
  set E : ℝ := 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600 + 36 * K
    with hE
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

/-- **⟦C1'S ANCHOR, SPENT AT `ρ`⟧** (`m4_arith_anchor_of_C1_rho`) — the council's granted
anchor `log₂M + 1 ≥ 2484` discharges the `ρ`-frame's `anchor` field on the whole register
(`loglog H ≤ 10¹¹`) for every `ρ ≥ e^{−10¹¹}`.  The slack is `9.69·10¹²` against `1.5·10¹²`.

The `ρ`-cap is not a claim about the opaque `δ₀`: once `δ₀` is fixed, `log(1/ρ) ≤ 10¹¹` is a
statement about the register's chosen width, and a consumer that needs more simply raises
`M`. -/
theorem m4_arith_anchor_of_C1_rho {M H : ℕ} {ρ : ℝ} (hM : 2484 ≤ Nat.log 2 M + 1)
    (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11)
    (hρcap : Real.log (1 / ρ) ≤ 10 ^ 11) :
    14 * Real.log (Real.log (H : ℝ)) + Real.log (1 / ρ) + 33
      ≤ 39 * 10 ^ 8 * ((Nat.log 2 M + 1 : ℕ) : ℝ) := by
  have hmR : (2484 : ℝ) ≤ ((Nat.log 2 M + 1 : ℕ) : ℝ) := by exact_mod_cast hM
  linarith

/-- **⟦THE WINDOW-INDEX FLOOR, SPENT AT `ρ`⟧** (`m4_arith_jfloor_of_anchor_rho`) — the door's
own floor `doorRowFloor M = M·Adoor M ≤ j` with the ⟦C1⟧ anchor gives `j ≥ 2^2483 ≥ 2^42`,
which dwarfs `21·loglog H + 2·log(1/ρ) + 28` on the whole register. -/
theorem m4_arith_jfloor_of_anchor_rho {M H j : ℕ} {ρ : ℝ} (hM : 2484 ≤ Nat.log 2 M + 1)
    (hj : doorRowFloor M ≤ j) (hHcap : Real.log (Real.log (H : ℝ)) ≤ 10 ^ 11)
    (hρcap : Real.log (1 / ρ) ≤ 10 ^ 11) :
    21 * Real.log (Real.log (H : ℝ)) + 2 * Real.log (1 / ρ) + 28 ≤ (j : ℝ) := by
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

/-- **⟦THE `M₀` WINDOW — LOWER ENDPOINT, NUMERICALLY, AT `ρ`⟧**
(`m4_arith_M0_window_lower_rho`).  The `ρ`-frame's exact `M0_window` field follows from the
readable form `M₀ ≥ 0.062·loglog X + 40·loglog H + 6·log(C₁+1) + 3·log(1/ρ) + 33`
(`e·12 = 32.62 ≤ 33`, `e·2 = 5.44 ≤ 6`, `e ≤ 3`). -/
theorem m4_arith_M0_window_lower_rho {H : ℕ} {X C₁ M₀ ρ : ℝ}
    (hlam : 0 ≤ Real.log (Real.log (H : ℝ))) (hmu : 0 ≤ Real.log (Real.log X))
    (hC : 0 ≤ Real.log (C₁ + 1)) (hLrho : 0 ≤ Real.log (1 / ρ))
    (h : 0.062 * Real.log (Real.log X) + 40 * Real.log (Real.log (H : ℝ))
        + 6 * Real.log (C₁ + 1) + 3 * Real.log (1 / ρ) + 33 ≤ M₀) :
    Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12) ≤ M₀ := by
  have he : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have hsum : (0 : ℝ) ≤ Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
      + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12 := by linarith
  calc Real.exp 1 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
        + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12)
      ≤ 2.7182818286 * (Real.log (Real.log X) / 45 + 14 * Real.log (Real.log (H : ℝ))
        + 2 * Real.log (C₁ + 1) + Real.log (1 / ρ) + 12) := mul_le_mul_of_nonneg_right he hsum
    _ ≤ 0.062 * Real.log (Real.log X) + 40 * Real.log (Real.log (H : ℝ))
        + 6 * Real.log (C₁ + 1) + 3 * Real.log (1 / ρ) + 33 := by linarith
    _ ≤ M₀ := h

/-- **⟦THE `M₀` WINDOW IS STILL NON-EMPTY AT `ρ`⟧** (`m4_arith_M0_window_nonempty_rho`) — the
lower endpoint sits strictly under `hErr`'s cap `2.7128·loglog X − 7.54`, under the `ρ`-arm and
a mild `log(C₁+1) ≤ loglog H`.  The `ρ`-cost is `3·log(1/ρ)` on the endpoint against
`2.7128·500·log(1/ρ) = 1356·log(1/ρ)` of new room from the arm — the window WIDENS as `ρ`
shrinks, by a factor `452`. -/
theorem m4_arith_M0_window_nonempty_rho {H : ℕ} {X C₁ ρ : ℝ}
    (hlam : 50 ≤ Real.log (Real.log (H : ℝ))) (hLrho : 0 ≤ Real.log (1 / ρ))
    (harm : 7000 * Real.log (Real.log (H : ℝ)) + 500 * Real.log (1 / ρ) + 6600
      ≤ Real.log (Real.log X))
    (hCsmall : Real.log (C₁ + 1) ≤ Real.log (Real.log (H : ℝ))) :
    0.062 * Real.log (Real.log X) + 40 * Real.log (Real.log (H : ℝ))
        + 6 * Real.log (C₁ + 1) + 3 * Real.log (1 / ρ) + 33
      ≤ 2.7128 * Real.log (Real.log X) - 7.54 := by
  linarith

/-! ## §8 — THE EXIT, BUNDLED, AT `ρ`

The three things `m4_second_road` needs of the door's row grade, at ONE hypothesis set — and
with `δ₀` appearing ONLY through `110525·ρ ≤ δ₀²`. -/

/-- **⟦A4ρ — THE ARITHMETIC EXIT⟧** (`m4_arith_door_exit_rho`).  At the `ρ`-frame:

⟦i⟧ ⟦item 11⟧ `M4ChiSummed.M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H))`
  — `henv` discharged, no arithmetic left open;
⟦ii⟧ ⟦gate 4⟧'s read `∀ j H, doorRowFloor M ≤ j → m4ChiRowGraded … j H ≤ RSanDoorRho ρ H`;
⟦iii⟧ `M4SecondRoad.m4_second_road_rs_ceiling`'s demand, MET, on the whole register.

THE COMPLETE HYPOTHESIS LIST: `hM` (`1 ≤ M`); `hρ` (`0 < ρ`); `hρδ` (`110525·ρ ≤ δ₀²` — the
ONLY place `δ₀` occurs, and it occurs squared); `hHreg` (the register's `H`-floor);
`hframe`/`hrows`/`hband` (`M4Assembly`'s three slots, byte for byte); and `harith` (the
`ρ`-frame at every base the socket reaches).

**`M4ArithPage.m4_arith_door_exit`'s `hδ₀ : 2/10⁴⁹ ≤ δ₀` is GONE** — replaced by a hypothesis
the consumer can meet by construction (`doorRhoOfDelta_spec`). -/
theorem m4_arith_door_exit_rho {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K ρ δ₀ : ℝ}
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hρδ : 110525 * ρ ≤ δ₀ ^ 2)
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
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K ρ) :
    M4ChiSummedFreeRow R M (m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H))
      ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
          m4ChiRowGraded M (fun _ H => RSanDoorRho ρ H) j H ≤ RSanDoorRho ρ H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2 * (108 / 5 * RSanDoorRho ρ H)
            ≤ δ₀ ^ 2) := by
  refine ⟨m4_chiSummedFreeRow_of_doorArithRho hM hframe hrows hband harith,
    m4_arith_gate4_rho M ρ, ?_⟩
  intro H hlo hhi
  obtain ⟨hL0, hlam⟩ := hHreg H hlo hhi
  exact m4_arith_rs_ceiling_met_rho hρ hρδ hL0 hlam

/-- **⟦A4ρ — THE ARITHMETIC EXIT AT THE CONSUMER'S `ρ`⟧** (`m4_arith_door_exit_of_delta`) —
`m4_arith_door_exit_rho` with `ρ := doorRhoOfDelta δ₀` and the ceiling hypothesis discharged.
The ONLY thing asked of the road's opaque `δ₀` is `δ₀ ≠ 0`, which `0 < δ₀` supplies. -/
theorem m4_arith_door_exit_of_delta {R : ChowlaRegime} {M : ℕ}
    {Cs Ccc C₁ M₀ ε : ℕ → ℝ} {K δ₀ : ℝ}
    (hM : 1 ≤ M) (hδ₀ : 0 < δ₀)
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
      DoorArithFrameRho M H j (((A + s : ℕ)) : ℝ) (C₁ (A + s)) (M₀ (A + s)) K
        (doorRhoOfDelta δ₀)) :
    M4ChiSummedFreeRow R M
        (m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H))
      ∧ (∀ j H : ℕ, doorRowFloor M ≤ j →
          m4ChiRowGraded M (fun _ H => RSanDoorRho (doorRhoOfDelta δ₀) H) j H
            ≤ RSanDoorRho (doorRhoOfDelta δ₀) H)
      ∧ (∀ H : ℕ, R.Hlo ≤ H → H ≤ R.Hhi →
          96 * (1 + 2 * Real.pi) ^ 2 * strataResidual H ^ 2
              * (108 / 5 * RSanDoorRho (doorRhoOfDelta δ₀) H)
            ≤ δ₀ ^ 2) :=
  m4_arith_door_exit_rho hM (doorRhoOfDelta_pos hδ₀.ne') (doorRhoOfDelta_spec δ₀) hHreg
    hframe hrows hband harith

end Salt.MR
