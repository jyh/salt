/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.HeadlineW2

/-!
# HDIAG — the `hdiag` discharge at the GLU-2W operating point (catch #68 repair, row 8′)

The `hdiag` hypothesis of `hBVblocksW_discharge'` (`Salt/Chen/PDiag.lean`) reads VERBATIM:

  `(hdiag : (y : ℝ) * (Nat.sqrt x : ℝ)`
  `    * ((2 : ℝ) ^ Nat.log w' x + ∑ d ∈ Nat.divisors Ps, nuChen d) ≤ Pdiag)`

At the frozen operating point (`y := opY x = ⌊x^{1/3}⌋`, `w' := opW'`, `Ps := opPs x`), this
file supplies a CLOSED `Pdiag := opPdiag x` and discharges the row, plus the compatibility
`opPdiag x ≤ x/(log x)^11` that feeds the `hSum` budget.

The two honest ingredients (the ν-side is landed in `PDiag.nuChen_sum_divisors_le`):

* **The tower crumb** (`crumb_le_rpow_at_op`): `2^{Nat.log opW' x} ≤ x^{1/7}` for every `x ≥ 1`.
  Mechanism: `opW'^{Nat.log opW' x} ≤ x` (`Nat.pow_log_le_self`) gives
  `Nat.log opW' x ≤ log x / log opW'`, so `2^{Nat.log opW' x} = x^{log 2 / log opW'} ≤ x^{1/7}`
  because `log opW' ≥ log 10⁶ ≥ 12 ≥ 7 log 2` (astronomic room — `log w'` is a FIXED constant
  `≈ 2·10⁹` at the tower, so the crumb exponent `log 2/log w' ≈ 3.5·10⁻¹⁰ ≪ 1/7`).

* **The ν-side** (`nu_sum_le_ratio_at_op` → `nu_sum_le_log_at_op`): the landed
  `nuChen_sum_divisors_le` at `u := w0R opEps`, `yR := opY x` (guards: `hthresh` via
  `w0R_threshold`, `hPlow`/`hPy` via `opf_Pslow`/`opf_Psy`, `huy` via `opf_tower`) gives
  `Σ_{d∣Ps} ν(d) ≤ (1+opEps)·log(opY x)/log(w0R opEps)`.  Since `log(w0R opEps) ≥ 2` is FIXED
  while `log(opY x) = (1/3)log x` GROWS, this is `≤ (1/3)log x ≤ log x` — a polylog quantity.

* **`opPdiag`/`hdiag_at_op`** (`opPdiag x := opY x · √x · (x^{1/7} + log x)`): the row is the
  factorwise sum `crumb + Σν ≤ x^{1/7} + log x` scaled by the nonnegative `opY x · √x`.

* **The compatibility** (`opPdiag_compat`): `opY x ≤ x^{1/3}`, `√x ≤ x^{1/2}`, `log x ≤ x^{1/7}`
  bound `opPdiag x ≤ 2·x^{41/42}`, and `2·(log x)^{11} ≤ x^{1/42}` (`a12_logpow_le_rpow`, polylog
  beats power) fits `2·x^{41/42} ≤ x/(log x)^{11}` with `x^{1/42}` of margin.  Entering `hSum` as
  `(1/2)·opPdiag x ≤ x/(2 log x^{11})`, this is a `1/(2 log x)` fraction of the `x/(log x)^{10}`
  budget — vanishing.

* **The slot match** (`hdiag_slot_at_op`): the `example` produces, for large `x`, both the EXACT
  `hdiag` hypothesis of `hBVblocksW_discharge'` at `Pdiag := opPdiag x` AND `opPdiag x ≤ x/L^{11}`.

No `sorry`, no `native_decide`, no new axioms (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset

namespace Salt.Chen

/-! ## Part A — the tower crumb `2^{Nat.log opW' x} ≤ x^{1/7}` -/

/-- **The tower crumb.**  `2^{Nat.log opW' x} ≤ x^{1/7}` for every `x ≥ 1`.  The exponent
`Nat.log opW' x ≤ log x / log opW'` (from `opW'^{Nat.log opW' x} ≤ x`), and
`log 2 / log opW' ≤ 1/7` because `log opW' ≥ log 10⁶ ≥ 12` while `7 log 2 < 4.86`. -/
theorem crumb_le_rpow_at_op (x : ℕ) (hx1 : 1 ≤ x) :
    (2 : ℝ) ^ (Nat.log opW' x) ≤ (x : ℝ) ^ ((1 : ℝ) / 7) := by
  have hxne : x ≠ 0 := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hLnn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by exact_mod_cast hx1)
  -- lower bounds on log opW'
  have hw'R : (10 : ℝ) ^ 6 ≤ (opW' : ℝ) := opf_w'big
  have hw'pos : (0 : ℝ) < (opW' : ℝ) := lt_of_lt_of_le (by norm_num) hw'R
  have hlogw'pos : 0 < Real.log (opW' : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 : ℝ) ^ 6) hw'R)
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogw'12 : (12 : ℝ) ≤ Real.log (opW' : ℝ) := by
    have h1 : Real.log ((10 : ℝ) ^ 6) ≤ Real.log (opW' : ℝ) :=
      Real.log_le_log (by norm_num) hw'R
    have h2 : Real.log ((10 : ℝ) ^ 6) = 6 * Real.log 10 := by rw [Real.log_pow]; push_cast; ring
    rw [h2] at h1; linarith [hlog10]
  -- exponent bound: Nat.log opW' x ≤ log x / log opW'
  set L := Nat.log opW' x with hLdef
  have hpow : (opW' : ℝ) ^ L ≤ (x : ℝ) := by
    have h : opW' ^ Nat.log opW' x ≤ x := Nat.pow_log_le_self opW' hxne
    rw [← hLdef] at h
    exact_mod_cast h
  have hlogpow : (L : ℝ) * Real.log (opW' : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (pow_pos hw'pos L) hpow
    rwa [Real.log_pow] at h
  have hLle : (L : ℝ) ≤ Real.log x / Real.log (opW' : ℝ) := by
    rw [le_div_iff₀ hlogw'pos]; nlinarith [hlogpow]
  have hratio : Real.log 2 / Real.log (opW' : ℝ) ≤ 1 / 7 := by
    rw [div_le_iff₀ hlogw'pos]
    nlinarith [Real.log_two_lt_d9, hlogw'12]
  calc (2 : ℝ) ^ L
      = (2 : ℝ) ^ (L : ℝ) := (Real.rpow_natCast (2 : ℝ) L).symm
    _ ≤ (2 : ℝ) ^ (Real.log x / Real.log (opW' : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hLle
    _ ≤ (x : ℝ) ^ ((1 : ℝ) / 7) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hxpos]
        apply Real.exp_le_exp.mpr
        rw [show Real.log 2 * (Real.log x / Real.log (opW' : ℝ))
              = Real.log x * (Real.log 2 / Real.log (opW' : ℝ)) by ring]
        exact mul_le_mul_of_nonneg_left hratio hLnn

/-! ## Part B — the ν-side (the landed `nuChen_sum_divisors_le` at the operating point) -/

/-- **The ν-side, raw form.**  `nuChen_sum_divisors_le` instantiated at `u := w0R opEps`,
`yR := opY x`, `ε := opEps`: `Σ_{d∣opPs x} ν(d) ≤ (1+opEps)·log(opY x)/log(w0R opEps)`.  The
`huy` guard `w0R opEps ≤ opY x` comes from `opf_tower` (`w0R ≤ opZ x ≤ opY x`); `hthresh` from
`w0R_threshold`; `hPlow`/`hPy` from `opf_Pslow`/`opf_Psy`. -/
theorem nu_sum_le_ratio_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∑ d ∈ Nat.divisors (opPs x), nuChen d
      ≤ (1 + opEps) * Real.log (opY x : ℝ) / Real.log (w0R opEps) := by
  obtain ⟨xt, _hxt8, htower⟩ := opf_tower
  refine ⟨xt, fun x hx => ?_⟩
  obtain ⟨-, hrow2, -, -, -, -, hrow7, -, -, -, -, -, -, -, -, -, -⟩ := htower x hx
  have huy : w0R opEps ≤ (opY x : ℝ) := le_trans hrow2 (by exact_mod_cast hrow7)
  exact nuChen_sum_divisors_le x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x)
    opf_eps_pos.le opf_w0R3 huy (w0R_threshold opf_eps_pos)
    (opf_Pslow x) (fun p hp => by exact_mod_cast opf_Psy x p hp)

/-- **The ν-side, reduced form.**  `Σ_{d∣opPs x} ν(d) ≤ log x`.  `log(w0R opEps) ≥ 2` (FIXED:
`w0R opEps ≥ 10⁶`) while `log(opY x) ≤ (1/3)log x` (`opf_window_floor_bounds`), so the ratio
`(1+opEps)·log(opY x)/log(w0R opEps) ≤ (1/3)log x ≤ log x`. -/
theorem nu_sum_le_log_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∑ d ∈ Nat.divisors (opPs x), nuChen d ≤ Real.log x := by
  obtain ⟨xr, hxr⟩ := nu_sum_le_ratio_at_op
  refine ⟨max xr (10 ^ 48), fun x hx => ?_⟩
  have hxrx : xr ≤ x := le_trans (le_max_left _ _) hx
  have h10n : (10 ^ 48 : ℕ) ≤ x := le_trans (le_max_right _ _) hx
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast h10n
  have hraw := hxr x hxrx
  have hLnn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (le_trans (by norm_num) hxR)
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogw2 : (2 : ℝ) ≤ Real.log (w0R opEps) := by
    have h1 : Real.log ((10 : ℝ) ^ 6) ≤ Real.log (w0R opEps) :=
      Real.log_le_log (by norm_num) opf_w0R_big
    have h2 : Real.log ((10 : ℝ) ^ 6) = 6 * Real.log 10 := by rw [Real.log_pow]; push_cast; ring
    rw [h2] at h1; linarith [hlog10]
  have hbpos : (0 : ℝ) < Real.log (w0R opEps) := by linarith [hlogw2]
  have hy_le : Real.log (opY x : ℝ) ≤ (1 : ℝ) / 3 * Real.log x := by
    rw [opY]
    exact (opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 3) (by norm_num)).2.2.1
  have hlogoy_nn : (0 : ℝ) ≤ Real.log (opY x : ℝ) := by
    rw [opY]
    exact Real.log_nonneg
      (le_trans (by norm_num)
        (opf_window_floor_bounds x hxR (γ := (1 : ℝ) / 3) (by norm_num)).2.1)
  have h1e2 : (1 : ℝ) + opEps ≤ 2 := by norm_num [opEps]
  refine le_trans hraw ?_
  rw [div_le_iff₀ hbpos]
  have hstep1 : (1 + opEps) * Real.log (opY x : ℝ) ≤ 2 * Real.log (opY x : ℝ) :=
    mul_le_mul_of_nonneg_right h1e2 hlogoy_nn
  have hnum : (1 + opEps) * Real.log (opY x : ℝ) ≤ (2 : ℝ) / 3 * Real.log x := by
    linarith [hstep1, hy_le]
  have hprod : (0 : ℝ) ≤ Real.log x * (Real.log (w0R opEps) - 2 / 3) :=
    mul_nonneg hLnn (by linarith [hlogw2])
  nlinarith [hnum, hprod]

/-! ## Part C — the closed `Pdiag` and the `hdiag` row -/

/-- The closed diagonal budget `Pdiag := opY x · √x · (x^{1/7} + log x)` — the honest
`x^{41/42+o(1)}`-scale shape (dominant term `x^{5/6}·x^{1/7} = x^{41/42}`). -/
noncomputable def opPdiag (x : ℕ) : ℝ :=
  (opY x : ℝ) * (Nat.sqrt x : ℝ) * ((x : ℝ) ^ ((1 : ℝ) / 7) + Real.log x)

/-- **`hdiag_at_op` — the `hdiag` row at the operating point.**  The VERBATIM `hdiag`
hypothesis of `hBVblocksW_discharge'` at `y := opY x`, `w' := opW'`, `Ps := opPs x`,
`Pdiag := opPdiag x`: the crumb `+` ν-side sum is `≤ x^{1/7} + log x`, scaled by the
nonnegative `opY x · √x`. -/
theorem hdiag_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (opY x : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ (Nat.log opW' x) + ∑ d ∈ Nat.divisors (opPs x), nuChen d)
      ≤ opPdiag x := by
  obtain ⟨xν, hxν⟩ := nu_sum_le_log_at_op
  refine ⟨max xν 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hxν' := hxν x (le_trans (le_max_left _ _) hx)
  have hcrumb := crumb_le_rpow_at_op x hx1
  have hsum : (2 : ℝ) ^ (Nat.log opW' x) + ∑ d ∈ Nat.divisors (opPs x), nuChen d
      ≤ (x : ℝ) ^ ((1 : ℝ) / 7) + Real.log x := add_le_add hcrumb hxν'
  have hnn : (0 : ℝ) ≤ (opY x : ℝ) * (Nat.sqrt x : ℝ) := by positivity
  unfold opPdiag
  exact mul_le_mul_of_nonneg_left hsum hnn

/-! ## Part D — the compatibility `opPdiag x ≤ x/(log x)^11` (the `hSum` budget) -/

/-- **`opPdiag_compat` — the diagonal fits the `hSum` budget.**  `opPdiag x ≤ x/(log x)^{11}`:
`opY x ≤ x^{1/3}`, `√x ≤ x^{1/2}`, `log x ≤ x^{1/7}` give `opPdiag x ≤ 2·x^{41/42}`, and
`2·(log x)^{11} ≤ x^{1/42}` (polylog beats power, `a12_logpow_le_rpow`) closes it with `x^{1/42}`
of margin. -/
theorem opPdiag_compat : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    opPdiag x ≤ (x : ℝ) / (Real.log x) ^ 11 := by
  obtain ⟨xa, hxa⟩ := a12_logpow_le_rpow ((11 : ℕ) : ℝ) (1 / 84) (by positivity) (by norm_num)
  obtain ⟨xb, hxb⟩ := a12_logpow_le_rpow 1 (1 / 7) (by norm_num) (by norm_num)
  refine ⟨max (max xa xb) (max (10 ^ 48) (2 ^ 84)), fun x hx => ?_⟩
  have hA : max xa xb ≤ x := le_trans (le_max_left _ _) hx
  have hB : max (10 ^ 48) (2 ^ 84) ≤ x := le_trans (le_max_right _ _) hx
  have hxa_x : xa ≤ x := le_trans (le_max_left _ _) hA
  have hxb_x : xb ≤ x := le_trans (le_max_right _ _) hA
  have h10n : (10 ^ 48 : ℕ) ≤ x := le_trans (le_max_left _ _) hB
  have h84n : (2 ^ 84 : ℕ) ≤ x := le_trans (le_max_right _ _) hB
  have hxa' := hxa x hxa_x
  have hxb' := hxb x hxb_x
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : 0 < x := lt_of_lt_of_le (by norm_num) h10n
    exact_mod_cast this
  have h10 : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast h10n
  have h84 : (2 : ℝ) ^ 84 ≤ (x : ℝ) := by exact_mod_cast h84n
  have h1x : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) h10
  have hLpos : 0 < Real.log x := Real.log_pos h1x
  have hLnn : (0 : ℝ) ≤ Real.log x := hLpos.le
  -- factor bounds
  have e1 : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [opY]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have e2 : (Nat.sqrt x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have hsq : ((Nat.sqrt x : ℝ)) ^ 2 ≤ (x : ℝ) := by exact_mod_cast Nat.sqrt_le' x
    have hnn : (0 : ℝ) ≤ (Nat.sqrt x : ℝ) := Nat.cast_nonneg _
    calc (Nat.sqrt x : ℝ) = Real.sqrt ((Nat.sqrt x : ℝ) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt hsq
      _ = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hlogx7 : Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 7) := by
    rw [Real.rpow_one] at hxb'; exact hxb'
  have e3 : (x : ℝ) ^ ((1 : ℝ) / 7) + Real.log x ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 7) := by
    have h := add_le_add (le_refl ((x : ℝ) ^ ((1 : ℝ) / 7))) hlogx7
    rwa [← two_mul] at h
  -- opPdiag x ≤ 2·x^{41/42}
  have hAle : (opY x : ℝ) * (Nat.sqrt x : ℝ)
      ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_le_mul e1 e2 (Nat.cast_nonneg _) (Real.rpow_nonneg hxpos.le _)
  have hstep : opPdiag x
      ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) * (2 * (x : ℝ) ^ ((1 : ℝ) / 7)) := by
    unfold opPdiag
    exact mul_le_mul hAle e3 (add_nonneg (Real.rpow_nonneg hxpos.le _) hLnn)
      (mul_nonneg (Real.rpow_nonneg hxpos.le _) (Real.rpow_nonneg hxpos.le _))
  have hval : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) * (2 * (x : ℝ) ^ ((1 : ℝ) / 7))
      = 2 * (x : ℝ) ^ ((41 : ℝ) / 42) := by
    have hadd1 : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2)
        = (x : ℝ) ^ ((1 : ℝ) / 3 + (1 : ℝ) / 2) := (Real.rpow_add hxpos _ _).symm
    have hadd2 : (x : ℝ) ^ ((1 : ℝ) / 3 + (1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 7)
        = (x : ℝ) ^ ((1 : ℝ) / 3 + (1 : ℝ) / 2 + (1 : ℝ) / 7) := (Real.rpow_add hxpos _ _).symm
    calc (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) * (2 * (x : ℝ) ^ ((1 : ℝ) / 7))
        = 2 * ((x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 7)) := by
          ring
      _ = 2 * ((x : ℝ) ^ ((1 : ℝ) / 3 + (1 : ℝ) / 2) * (x : ℝ) ^ ((1 : ℝ) / 7)) := by rw [hadd1]
      _ = 2 * (x : ℝ) ^ ((1 : ℝ) / 3 + (1 : ℝ) / 2 + (1 : ℝ) / 7) := by rw [hadd2]
      _ = 2 * (x : ℝ) ^ ((41 : ℝ) / 42) := by
          rw [show (1 : ℝ) / 3 + (1 : ℝ) / 2 + (1 : ℝ) / 7 = (41 : ℝ) / 42 by norm_num]
  -- the polylog tail: 2·(log x)^11 ≤ x^{1/42}
  have hL11 : (Real.log x) ^ (11 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 84) := by
    rwa [Real.rpow_natCast] at hxa'
  have hL11pos : (0 : ℝ) < (Real.log x) ^ (11 : ℕ) := by positivity
  have h2x84 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 84) := by
    have hcalc : ((2 : ℝ) ^ (84 : ℕ)) ^ ((1 : ℝ) / 84) = 2 := by
      rw [← Real.rpow_natCast (2 : ℝ) 84, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((84 : ℕ) : ℝ) * ((1 : ℝ) / 84) = 1 by norm_num, Real.rpow_one]
    calc (2 : ℝ) = ((2 : ℝ) ^ (84 : ℕ)) ^ ((1 : ℝ) / 84) := hcalc.symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 84) := Real.rpow_le_rpow (by positivity) h84 (by norm_num)
  have hstep3 : (x : ℝ) ^ ((1 : ℝ) / 84) * (x : ℝ) ^ ((1 : ℝ) / 84) = (x : ℝ) ^ ((1 : ℝ) / 42) := by
    rw [← Real.rpow_add hxpos, show (1 : ℝ) / 84 + (1 : ℝ) / 84 = (1 : ℝ) / 42 by norm_num]
  have h2L : 2 * (Real.log x) ^ (11 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 42) := by
    have s1 : 2 * (Real.log x) ^ (11 : ℕ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 84) :=
      mul_le_mul_of_nonneg_left hL11 (by norm_num)
    have hp : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 84) := Real.rpow_nonneg hxpos.le _
    have s2 : 2 * (x : ℝ) ^ ((1 : ℝ) / 84) ≤ (x : ℝ) ^ ((1 : ℝ) / 84) * (x : ℝ) ^ ((1 : ℝ) / 84) := by
      nlinarith [h2x84, hp, mul_nonneg hp (by linarith [h2x84] : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 84) - 2)]
    calc 2 * (Real.log x) ^ (11 : ℕ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 84) := s1
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 84) * (x : ℝ) ^ ((1 : ℝ) / 84) := s2
      _ = (x : ℝ) ^ ((1 : ℝ) / 42) := hstep3
  -- assemble
  rw [le_div_iff₀ hL11pos]
  calc opPdiag x * (Real.log x) ^ (11 : ℕ)
      ≤ (2 * (x : ℝ) ^ ((41 : ℝ) / 42)) * (Real.log x) ^ (11 : ℕ) :=
        mul_le_mul_of_nonneg_right (le_trans hstep (le_of_eq hval)) hL11pos.le
    _ = (x : ℝ) ^ ((41 : ℝ) / 42) * (2 * (Real.log x) ^ (11 : ℕ)) := by ring
    _ ≤ (x : ℝ) ^ ((41 : ℝ) / 42) * (x : ℝ) ^ ((1 : ℝ) / 42) :=
        mul_le_mul_of_nonneg_left h2L (Real.rpow_nonneg hxpos.le _)
    _ = (x : ℝ) ^ ((41 : ℝ) / 42 + (1 : ℝ) / 42) := (Real.rpow_add hxpos _ _).symm
    _ = (x : ℝ) ^ (1 : ℝ) := by rw [show (41 : ℝ) / 42 + (1 : ℝ) / 42 = (1 : ℝ) by norm_num]
    _ = (x : ℝ) := Real.rpow_one _

/-! ## Part E — the slot match: `hdiag_at_op` + `opPdiag_compat` feeding the consumer -/

/-- **The `hdiag` slot match.**  For large `x`, `opPdiag x` simultaneously (i) discharges the
EXACT `hdiag` hypothesis of `hBVblocksW_discharge'` (the first conjunct is character-for-character
the `hdiag` slot at `y := opY x`, `w' := opW'`, `Ps := opPs x`, `Pdiag := opPdiag x`) and
(ii) fits the `hSum` budget `opPdiag x ≤ x/(log x)^{11}`. -/
theorem hdiag_slot_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ((opY x : ℝ) * (Nat.sqrt x : ℝ)
        * ((2 : ℝ) ^ (Nat.log opW' x) + ∑ d ∈ Nat.divisors (opPs x), nuChen d) ≤ opPdiag x)
      ∧ opPdiag x ≤ (x : ℝ) / (Real.log x) ^ 11 := by
  obtain ⟨x1, hrow⟩ := hdiag_at_op
  obtain ⟨x2, hcompat⟩ := opPdiag_compat
  refine ⟨max x1 x2, fun x hx => ⟨hrow x ?_, hcompat x ?_⟩⟩
  · exact le_trans (le_max_left _ _) hx
  · exact le_trans (le_max_right _ _) hx

end Salt.Chen
