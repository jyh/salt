/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LandauL1
import Salt.LS.GaussSum

/-!
# The odd-`χ` functional-equation lane for the effective `L(1,χ)` lower bound

`Salt/MR/LandauL1.lean` names the `L₁` slot (`L1LowerEffective c A`: `c·q^{−A} ≤ (L(1,χ)).re`,
uniformly in `q`, at every real nonprincipal `χ`) and records the route verdict.  Its §(c) prices
the cheapest genuine power grade as the **Gauss-sum / functional-equation lane, odd `χ` only**.
This module executes that lane, and reports exactly where it stops.

## The identity chain (all unconditional here)

For `χ` primitive and ODD (`χ(−1) = −1`) modulo `N`, the archimedean factor is
`gammaFactor χ s = Gammaℝ (s+1)`, so `Gammaℝ 1 = 1` and `Gammaℝ 2 = 1/π` give

  `Λ(χ,0) = L(0,χ)`,   `Λ(χ,1) = L(1,χ)/π`,

and mathlib's functional equation `IsPrimitive.completedLFunction_one_sub` at `s = 1` reads
`Λ(χ,0) = N^{1/2}·W(χ)·Λ(χ⁻¹,1)`.  Hence (`LFunction_apply_zero_odd_fe`)

  `L(0,χ) = N^{1/2}·W(χ)·L(1,χ⁻¹)/π`,

with `‖W(χ)‖ = 1` (`rootNumber_norm_eq_one`, from `‖gaussSum χ ψ‖² = N` at primitive `χ` —
`Salt.LS.gaussSum_normSq`, valid for composite `N` too).  Taking norms
(`norm_LFunction_apply_one_odd`):

  `‖L(1,χ⁻¹)‖ = π·‖L(0,χ)‖/√N`.

For `χ` REAL (`χ² = 1`) one has `χ⁻¹ = χ`, and `L(1,χ)` is a positive real
(`Salt.SW.LFunction_apply_one_pos`), so `‖L(1,χ)‖ = (L(1,χ)).re` and the chain closes into the
**master reduction** (`L1_lower_odd_of_L0_floor`): a floor `1/N ≤ ‖L(0,χ)‖` upgrades to
`π·N^{−3/2} ≤ (L(1,χ)).re`.

The corresponding non-vanishing `L(0,χ) ≠ 0` (`LFunction_apply_zero_ne_zero_odd`) is
unconditional: it transports mathlib's `LFunction_apply_one_ne_zero` across the same identity.
So the *qualitative* half of the mission's `O-1` is landed; only the *quantitative* floor is not.

## THE ZENO (exact) — one missing mathlib value

The floor `1/N ≤ ‖L(0,χ)‖` is the classical rationality
`L(0,χ) = −(1/N)·Σ_{a} a·χ(a) ∈ (1/N)·ℤ \ {0}`.  Everything about it is landed here EXCEPT one
input, which mathlib does not have:

  **`hurwitzZetaOdd x 0 = 1/2 − x` for `x ∈ (0,1)`**  (`SawtoothOdd`).

This is precisely the `k = 0` case that `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`
excludes, with its own recorded reason: *"The formulae are correct for `s = 0` as well, but we do
not prove this case, since this requires Fourier series which are only conditionally convergent,
which is difficult to approach using the methods in the library at the present time."*  Concretely
`hurwitzZeta_neg_nat` (values at `−k` in terms of Bernoulli polynomials) is stated for `k ≠ 0`,
and `hurwitzZetaOdd_neg_two_mul_nat` for `k ≠ 0`; `hurwitzZetaEven`'s value at `0` IS available
(`hurwitzZetaEven_apply_zero`) and is what powers `ZMod.LFunction_apply_zero_of_even`, but there is
no odd counterpart anywhere in mathlib (checked: `hurwitzZetaOdd` has no `_apply_zero`, and no
`LFunction`-at-`0` lemma for odd `Φ`).  Equivalently the gap is the sawtooth Fourier series
`Σ_{n≥1} sin(2πnx)/n = π(1/2 − x)`: mathlib's `hasSum_one_div_nat_pow_mul_sin` covers exponents
`2k+1` with `k ≠ 0` only, since exponent `1` is not absolutely convergent.  `Abel`'s limit theorem
(`Mathlib/Analysis/Complex/AbelLimit.lean`) is present but does not by itself bridge to the
analytic continuation.

Everything downstream of the gap is therefore stated **conditionally on `SawtoothOdd`** and proved:
`LFunction_apply_zero_eq_sum_of_sawtooth` (the finite formula), `exists_int_sum_val_mul`
(integrality of `Σ a·χ(a)` at real `χ`), `L0_floor_of_sawtooth` (the `1/N` floor), and the
interface instances `L1_lower_odd_primitive_of_sawtooth` (grade `3/2`, primitive `χ`) and
`l1LowerOddEffective_of_sawtooth : SawtoothOdd → L1LowerOddEffective π (5/2)` (all odd real
nonprincipal `χ`, via the descent of §6).

## The descent (the mission's `O-4`) — LANDED, and cheap

`L1LowerOddEffective` as defined here does NOT require primitivity, because §6 discharges the
descent unconditionally: mathlib's `LFunction_changeLevel` gives
`L(1,χ) = L(1,χ*)·∏_{p ∣ N}(1 − χ*(p)/p)` for `χ*` the inducing primitive character, every factor
of the product is a positive real, and the crude but perfectly adequate bound
`∏_{p ∣ N}(1 − 1/p) = φ(N)/N ≥ 1/N` costs exactly one grade: `A = 3/2 ↝ A = 5/2`.  By
`door_L1_absorbed` (`LandauL1.lean`) the door is indifferent to `A`, so the grade loss is free.

## What this lane does NOT cover (recorded, not routed around)

`L1LowerEffective` quantifies over BOTH parities.  For `χ` EVEN the identity above degenerates —
`gammaFactor χ s = Gammaℝ s`, `Gammaℝ 0` is a pole, and `L(0,χ) = 0` for even nonprincipal `χ`
(mathlib's `ZMod.LFunction_apply_zero_of_even` gives `L(0,χ) = −χ(0)/2 = 0`), so the functional
equation carries NO information at `s = 1`.  The even anchor is the regulator (real quadratic
fields), i.e. the class-number lane of `LandauL1`'s §(a).  This module therefore inhabits an
odd-only interface, and the parity gap is a genuine mathematical boundary of the lane.
-/

namespace Salt.MR

open Complex DirichletCharacter

/-! ## §1 — the root number has modulus one -/

/-- **`‖W(χ)‖ = 1` at every primitive `χ`** (both parities, all moduli including composite).
`rootNumber χ = gaussSum χ ψ / I^ε / N^{1/2}`, and `‖gaussSum χ ψ‖ = √N` is
`Salt.LS.gaussSum_normSq` (the composite-modulus form, proved in the LS rung). -/
theorem rootNumber_norm_eq_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : ‖rootNumber χ‖ = 1 := by
  classical
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hg : ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ)‖ = Real.sqrt N := by
    have h := Salt.LS.gaussSum_normSq χ hχ
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hI : ‖(I : ℂ) ^ (if χ.Even then 0 else 1 : ℕ)‖ = 1 := by
    rw [norm_pow, Complex.norm_I, one_pow]
  have hNc : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt N := by
    rw [Complex.norm_natCast_cpow_of_pos hN, Real.sqrt_eq_rpow]
    norm_num
  rw [rootNumber, norm_div, norm_div, hg, hI, hNc]
  field_simp

/-! ## §2 — the odd archimedean factors, and the functional equation at `s = 1` -/

/-- An odd character has modulus `≠ 1` (in `ZMod 1`, `−1 = 1`, so `χ(−1) = 1 ≠ −1`). -/
theorem mod_ne_one_of_odd {N : ℕ} {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) : N ≠ 1 := by
  rintro rfl
  rw [DirichletCharacter.Odd, show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _,
    MulChar.map_one] at hodd
  exact absurd hodd (by norm_num)

/-- The inverse of an odd character is odd. -/
theorem odd_inv {N : ℕ} {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) : (χ⁻¹).Odd := by
  have h : (χ⁻¹) (-1) = (χ (-1))⁻¹ := MulChar.inv_apply_eq_inv' χ (-1)
  rw [DirichletCharacter.Odd] at hodd ⊢
  rw [h, hodd]
  norm_num

/-- **`Λ(χ,0) = L(0,χ)` for odd `χ`**: the odd gamma factor at `s = 0` is `Gammaℝ 1 = 1`. -/
theorem LFunction_apply_zero_eq_completed_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hodd : χ.Odd) : LFunction χ 0 = completedLFunction χ 0 := by
  rw [LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr (mod_ne_one_of_odd hodd)),
    hodd.gammaFactor_def]
  norm_num [Complex.Gammaℝ_one]

/-- **`Λ(χ,1) = L(1,χ)/π` for odd `χ`**: the odd gamma factor at `s = 1` is
`Gammaℝ 2 = π^{-1}·Γ(1) = 1/π`. -/
theorem LFunction_apply_one_eq_completed_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hodd : χ.Odd) : LFunction χ 1 = completedLFunction χ 1 * (Real.pi : ℂ) := by
  rw [LFunction_eq_completed_div_gammaFactor χ 1 (Or.inl one_ne_zero), hodd.gammaFactor_def]
  have h2 : Complex.Gammaℝ (1 + 1) = (Real.pi : ℂ)⁻¹ := by
    norm_num [Complex.Gammaℝ_def, Complex.Gamma_one, Complex.cpow_neg, Complex.cpow_one]
  rw [h2, div_eq_mul_inv, inv_inv]

/-- **The functional-equation bridge, odd primitive `χ` (any parity of the field of values —
`χ` is not assumed real here).**  `L(0,χ) = √N·W(χ)·L(1,χ⁻¹)/π`.  This is
`IsPrimitive.completedLFunction_one_sub` at `s = 1`, with both archimedean factors evaluated. -/
theorem LFunction_apply_zero_odd_fe {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    LFunction χ 0 = (N : ℂ) ^ (1 / 2 : ℂ) * rootNumber χ * LFunction χ⁻¹ 1 / (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfe := hprim.completedLFunction_one_sub 1
  rw [show (1 : ℂ) - 1 = 0 by ring, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring] at hfe
  rw [LFunction_apply_zero_eq_completed_odd hodd, hfe,
    LFunction_apply_one_eq_completed_odd (odd_inv hodd)]
  field_simp

/-! ## §3 — the norm identity and the non-vanishing at `s = 0` -/

/-- **The norm form of the bridge**: `‖L(1,χ⁻¹)‖ = π·‖L(0,χ)‖/√N` at every odd primitive `χ`.
Stated at this generality (no reality assumption) for the Siegel-coastline consumers. -/
theorem norm_LFunction_apply_one_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    ‖LFunction χ⁻¹ 1‖ = Real.pi * ‖LFunction χ 0‖ / Real.sqrt N := by
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hNp)
  have hNc : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt N := by
    rw [Complex.norm_natCast_cpow_of_pos hNp, Real.sqrt_eq_rpow]
    norm_num
  have h := congrArg norm (LFunction_apply_zero_odd_fe hprim hodd)
  rw [norm_div, norm_mul, norm_mul, hNc, rootNumber_norm_eq_one hprim] at h
  rw [Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] at h
  field_simp at h ⊢
  linarith [h]

/-- For a real character, `χ⁻¹ = χ`. -/
theorem inv_eq_self_of_sq_eq_one {N : ℕ} {χ : DirichletCharacter ℂ N} (hsq : χ ^ 2 = 1) :
    χ⁻¹ = χ :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hsq)

/-- **`L(0,χ) ≠ 0` for every odd primitive nonprincipal `χ`** — the qualitative half of the
mission's `O-1`, UNCONDITIONAL and with NO reality assumption.  Route: the functional equation
transports mathlib's `LFunction_apply_one_ne_zero` from `s = 1` to `s = 0`; no rationality is
used. -/
theorem LFunction_apply_zero_ne_zero_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hχ1 : χ ≠ 1) : LFunction χ 0 ≠ 0 := by
  have hb := norm_LFunction_apply_one_odd hprim hodd
  intro h0
  rw [h0, norm_zero] at hb
  simp only [mul_zero, zero_div] at hb
  exact (norm_ne_zero_iff.mpr
    (DirichletCharacter.LFunction_apply_one_ne_zero (inv_ne_one.mpr hχ1))) hb

/-! ## §4 — the master reduction: a floor at `s = 0` becomes the `q^{−3/2}` grade at `s = 1` -/

/-- `‖L(1,χ)‖ = (L(1,χ)).re` at real nonprincipal `χ` (the value is a positive real —
`Salt.SW.LFunction_apply_one_pos`). -/
theorem norm_LFunction_one_eq_re' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ1 : χ ≠ 1) (hsq : χ ^ 2 = 1) : ‖LFunction χ 1‖ = (LFunction χ 1).re := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp (Salt.SW.LFunction_apply_one_pos hχ1 hsq)
  have h : LFunction χ 1 = ((LFunction χ 1).re : ℂ) :=
    Complex.ext (Complex.ofReal_re _).symm (by simp [him])
  nth_rewrite 1 [h]
  rw [Complex.norm_real, Real.norm_of_nonneg hre.le]

/-- `x^{3/2} = x·√x` for `x ≥ 0`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num),
    Real.rpow_one, Real.sqrt_eq_rpow]

/-- **THE MASTER REDUCTION (unconditional).**  For odd real primitive nonprincipal `χ` mod `N`,
the floor `1/N ≤ ‖L(0,χ)‖` upgrades to the effective grade `π·N^{−3/2} ≤ (L(1,χ)).re`.

Every ingredient is landed: the functional equation, `‖W(χ)‖ = 1`, `Gammaℝ 1 = 1`,
`Gammaℝ 2 = 1/π`, and the positivity of `L(1,χ)`.  Only the hypothesis `hfloor` is open — see
§5. -/
theorem L1_lower_odd_of_L0_floor {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hsq : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (hfloor : 1 / (N : ℝ) ≤ ‖LFunction χ 0‖) :
    Real.pi / (N : ℝ) ^ (3 / 2 : ℝ) ≤ (LFunction χ 1).re := by
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hb := norm_LFunction_apply_one_odd hprim hodd
  rw [inv_eq_self_of_sq_eq_one hsq, norm_LFunction_one_eq_re' hχ1 hsq] at hb
  rw [rpow_three_halves hNR.le, hb, div_le_div_iff₀ (by positivity) hs]
  calc Real.pi * Real.sqrt N = Real.pi * (1 / (N : ℝ)) * ((N : ℝ) * Real.sqrt N) := by
        field_simp
    _ ≤ Real.pi * ‖LFunction χ 0‖ * ((N : ℝ) * Real.sqrt N) := by gcongr

/-! ## §5 — the one open input: the sawtooth value of `hurwitzZetaOdd` at `s = 0` -/

/-- **THE ZENO, as a named `Prop`.**  `hurwitzZetaOdd x 0 = 1/2 − x` for `x ∈ (0,1)` — the `k = 0`
case of `HurwitzZeta.hurwitzZeta_neg_nat`, which mathlib states only for `k ≠ 0` (see the module
docstring for mathlib's own recorded reason).  Note the open interval is forced: `hurwitzZetaOdd`
is odd on `ℝ/ℤ`, so its value at `x = 0` is `0`, not `1/2`. -/
def SawtoothOdd : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 →
    HurwitzZeta.hurwitzZetaOdd (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ)

/-- **The classical value `L(0,χ) = −(1/N)·Σ_a a·χ(a)`, granted `SawtoothOdd`.**
`ZMod.LFunction_def_odd` writes `L(s,χ)` as `N^{−s}·Σ_j χ(j)·hurwitzZetaOdd(j/N, s)`; at `s = 0`
the `j = 0` term dies (`χ 0 = 0`), the remaining arguments `j/N` lie in `(0,1)`, and
`Σ_j χ(j) = 0` kills the constant `1/2`. -/
theorem LFunction_apply_zero_eq_sum_of_sawtooth {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hsaw : SawtoothOdd) (hodd : χ.Odd) (hχ1 : χ ≠ 1) :
    LFunction χ 0 = -(1 / (N : ℂ)) * ∑ a : ZMod N, (a.val : ℂ) * χ a := by
  have hN1 : N ≠ 1 := mod_ne_one_of_odd hodd
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have key : ∀ j : ZMod N, χ j * HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle j) 0
      = χ j * (1 / 2 - (j.val : ℂ) / (N : ℂ)) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [χ.map_zero' hN1]; ring
    · congr 1
      rw [ZMod.toAddCircle_apply]
      have h1 : (0 : ℝ) < (j.val : ℝ) / N := by
        have : 0 < j.val := ZMod.val_pos.mpr hj
        positivity
      have h2 : (j.val : ℝ) / N < 1 := by
        rw [div_lt_one hNR]; exact_mod_cast ZMod.val_lt j
      rw [hsaw _ ⟨h1, h2⟩]
      push_cast
      ring
  rw [DirichletCharacter.LFunction, ZMod.LFunction_def_odd hodd.to_fun]
  simp_rw [key]
  rw [neg_zero, Complex.cpow_zero, one_mul]
  have hsum0 : ∑ j : ZMod N, χ j = 0 := MulChar.sum_eq_zero_of_ne_one hχ1
  calc ∑ j : ZMod N, χ j * (1 / 2 - (j.val : ℂ) / (N : ℂ))
      = 1 / 2 * (∑ j : ZMod N, χ j) - 1 / (N : ℂ) * ∑ j : ZMod N, (j.val : ℂ) * χ j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = -(1 / (N : ℂ)) * ∑ a : ZMod N, (a.val : ℂ) * χ a := by rw [hsum0]; ring

/-- Every value of a real character is `0`, `1` or `−1`. -/
theorem val_cases_of_sq_eq_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hsq : χ ^ 2 = 1)
    (a : ZMod N) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases hu : IsUnit a
  · have hp : (χ a) * (χ a) = 1 := by
      have h := MulChar.pow_apply' χ (n := 2) two_ne_zero a
      rw [hsq, MulChar.one_apply hu, pow_two] at h
      exact h.symm
    exact Or.inr (mul_self_eq_one_iff.mp hp)
  · exact Or.inl (MulChar.map_nonunit χ hu)

/-- **Integrality.**  At a real character (`χ² = 1`) every value is `0`, `1` or `−1`, so
`Σ_a a·χ(a)` is a rational integer.  This is the source of the `1/N` denominator. -/
theorem exists_int_sum_val_mul {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hsq : χ ^ 2 = 1) :
    ∃ m : ℤ, ∑ a : ZMod N, (a.val : ℂ) * χ a = (m : ℂ) := by
  classical
  set f : ZMod N → ℤ := fun a => if χ a = 1 then 1 else if χ a = -1 then -1 else 0 with hf
  have hfa : ∀ a : ZMod N, ((f a : ℤ) : ℂ) = χ a := by
    intro a
    rcases val_cases_of_sq_eq_one hsq a with h0 | h1 | h2
    · simp [hf, h0]
    · simp [hf, h1]
    · have e1 : χ a ≠ 1 := by rw [h2]; norm_num
      simp only [hf, if_neg e1, if_pos h2]
      rw [h2]
      norm_num
  refine ⟨∑ a : ZMod N, (a.val : ℤ) * f a, ?_⟩
  rw [Int.cast_sum]
  exact (Finset.sum_congr rfl fun a _ => by rw [Int.cast_mul, hfa a]; norm_num).symm

/-- **The `1/N` floor at `s = 0`, granted `SawtoothOdd`.**  `L(0,χ) = −m/N` with `m ∈ ℤ` and
`m ≠ 0` (the latter from the UNCONDITIONAL non-vanishing of §3), so `‖L(0,χ)‖ ≥ 1/N`. -/
theorem L0_floor_of_sawtooth {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hsaw : SawtoothOdd) (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hsq : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    1 / (N : ℝ) ≤ ‖LFunction χ 0‖ := by
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  obtain ⟨m, hm⟩ := exists_int_sum_val_mul hsq
  have hform := LFunction_apply_zero_eq_sum_of_sawtooth hsaw hodd hχ1
  rw [hm] at hform
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hform
    simp only [Int.cast_zero, mul_zero] at hform
    exact LFunction_apply_zero_ne_zero_odd hprim hodd hχ1 hform
  have habs : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hm0
  have hnn : ‖(1 : ℂ) / (N : ℂ)‖ = 1 / (N : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [hform, norm_mul, norm_neg, Complex.norm_intCast, hnn]
  calc 1 / (N : ℝ) = 1 / (N : ℝ) * 1 := by ring
    _ ≤ 1 / (N : ℝ) * |(m : ℝ)| := mul_le_mul_of_nonneg_left habs (by positivity)

/-- **The odd-`χ` production at primitive level, granted `SawtoothOdd`:**
`π·N^{−3/2} ≤ (L(1,χ)).re`, with the constant `π` explicit. -/
theorem L1_lower_odd_primitive_of_sawtooth {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hsaw : SawtoothOdd) (hprim : χ.IsPrimitive) (hodd : χ.Odd) (hsq : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    Real.pi / (N : ℝ) ^ (3 / 2 : ℝ) ≤ (LFunction χ 1).re :=
  L1_lower_odd_of_L0_floor hprim hodd hsq hχ1 (L0_floor_of_sawtooth hsaw hprim hodd hsq hχ1)

/-! ## §6 — the descent to the inducing primitive character (the mission's `O-4`)

Unconditional, and it costs exactly one grade.  The consumer interface of `LandauL1` does not
assume primitivity, so this section is what makes an odd instance of that shape possible at all.
-/

/-- The conductor of a character of nonzero level is nonzero. -/
instance instNeZeroConductor {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

/-- The inducing primitive character of a nonprincipal character is nonprincipal. -/
theorem primitiveCharacter_ne_one' {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  exact hχ1 (by rw [← changeLevel_primitiveCharacter χ, h]; simp)

/-- The inducing primitive character of an odd character is odd (`−1` is coprime to every
level). -/
theorem primitiveCharacter_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hodd : χ.Odd) :
    χ.primitiveCharacter.Odd := by
  have hco : IsCoprime (-1 : ℤ) (N : ℤ) := (isCoprime_one_left).neg_left
  have h := χ.primitiveCharacter_apply_of_isCoprime hco
  rw [DirichletCharacter.Odd] at hodd ⊢
  push_cast at h
  rw [h, hodd]

/-- The inducing primitive character of a real character is real (`changeLevel` is an injective
monoid map). -/
theorem primitiveCharacter_sq_eq_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hsq : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  rw [← changeLevel_eq_one_iff (χ := χ.primitiveCharacter ^ 2) χ.conductor_dvd_level,
    map_pow, changeLevel_primitiveCharacter]
  exact hsq

/-- **The descent identity** — mathlib's `LFunction_changeLevel` at `s = 1`:
`L(1,χ) = L(1,χ*)·∏_{p ∣ N}(1 − χ*(p)·p^{−1})`, `χ*` the inducing primitive character. -/
theorem LFunction_apply_one_descent {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ1 : χ ≠ 1) :
    LFunction χ 1 = LFunction χ.primitiveCharacter 1 *
      ∏ p ∈ N.primeFactors,
        (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-1 : ℂ)) := by
  have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := 1) (Or.inl (primitiveCharacter_ne_one' hχ1))
  rwa [changeLevel_primitiveCharacter] at h

/-- **The descent Euler factor is a real number `≥ 1/N`.**  At a real character each factor is
`1`, `1 − 1/p` or `1 + 1/p`, so the product dominates `∏_{p ∣ N}(1 − 1/p) = φ(N)/N ≥ 1/N`.
The bound is crude — the true size is `≍ 1/loglog N` — but it is a POWER, which is all the door
needs, and it is elementary. -/
theorem descent_prod_eq_real {N f : ℕ} [NeZero N] [NeZero f] {ψ : DirichletCharacter ℂ f}
    (hsq : ψ ^ 2 = 1) :
    ∃ r : ℝ, 1 / (N : ℝ) ≤ r ∧
      ∏ p ∈ N.primeFactors, (1 - ψ (p : ZMod f) * (p : ℂ) ^ (-1 : ℂ)) = (r : ℂ) := by
  classical
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  set g : ℕ → ℝ := fun p => if ψ (p : ZMod f) = 1 then 1 - (p : ℝ)⁻¹
    else if ψ (p : ZMod f) = -1 then 1 + (p : ℝ)⁻¹ else 1 with hg
  have hstep : ∀ p ∈ N.primeFactors,
      (1 - ψ (p : ZMod f) * (p : ℂ) ^ (-1 : ℂ)) = ((g p : ℝ) : ℂ) ∧ 1 - 1 / (p : ℝ) ≤ g p := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hcpow : (p : ℂ) ^ (-1 : ℂ) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.cpow_neg, Complex.cpow_one]
      push_cast
      ring
    rw [hcpow]
    rcases val_cases_of_sq_eq_one hsq (p : ZMod f) with h0 | h1 | h2
    · have e1 : ψ (p : ZMod f) ≠ 1 := by rw [h0]; norm_num
      have e2 : ψ (p : ZMod f) ≠ -1 := by rw [h0]; norm_num
      rw [h0]
      refine ⟨by simp [hg, e1, e2], by
        simp only [hg, if_neg e1, if_neg e2]
        have := one_div_pos.mpr hpR
        linarith⟩
    · rw [h1]
      refine ⟨by simp only [hg, if_pos h1]; push_cast; ring, by
        simp only [hg, if_pos h1]; rw [one_div]⟩
    · have e1 : ψ (p : ZMod f) ≠ 1 := by rw [h2]; norm_num
      rw [h2]
      refine ⟨by simp only [hg, if_neg e1, if_pos h2]; push_cast; ring, by
        simp only [hg, if_neg e1, if_pos h2, one_div]; linarith [inv_pos.mpr hpR]⟩
  have hprodeq : ∏ p ∈ N.primeFactors, (1 - ψ (p : ZMod f) * (p : ℂ) ^ (-1 : ℂ))
      = ((∏ p ∈ N.primeFactors, g p : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun p hp => (hstep p hp).1
  refine ⟨∏ p ∈ N.primeFactors, g p, ?_, hprodeq⟩
  have htot : (Nat.totient N : ℝ) = N * ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors N)
    push_cast at h
    exact h
  have hmono : ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹) ≤ ∏ p ∈ N.primeFactors, g p := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
      have hinv : (p : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact h1
      linarith
    · have h := (hstep p hp).2
      rwa [one_div] at h
  have hphi : (1 : ℝ) ≤ (Nat.totient N : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hNp
  calc 1 / (N : ℝ) ≤ (Nat.totient N : ℝ) / N := by gcongr
    _ = ∏ p ∈ N.primeFactors, (1 - (p : ℝ)⁻¹) := by rw [htot]; field_simp
    _ ≤ ∏ p ∈ N.primeFactors, g p := hmono

/-- **THE ODD PRODUCTION, at every real nonprincipal odd `χ` (no primitivity), granted
`SawtoothOdd`:** `π·N^{−5/2} ≤ (L(1,χ)).re`.  The exponent is `3/2` from the functional equation
plus `1` from the descent. -/
theorem L1_lower_odd_of_sawtooth {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hsaw : SawtoothOdd) (hodd : χ.Odd) (hsq : χ ^ 2 = 1) (hχ1 : χ ≠ 1) :
    Real.pi / (N : ℝ) ^ (5 / 2 : ℝ) ≤ (LFunction χ 1).re := by
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  set f := χ.conductor with hfdef
  have hfle : f ≤ N := Nat.le_of_dvd hNp χ.conductor_dvd_level
  have hfp : 0 < f := Nat.pos_of_ne_zero (NeZero.ne f)
  have hfR : (0 : ℝ) < f := by exact_mod_cast hfp
  have hbase := L1_lower_odd_primitive_of_sawtooth hsaw χ.primitiveCharacter_isPrimitive
    (primitiveCharacter_odd hodd) (primitiveCharacter_sq_eq_one hsq)
    (primitiveCharacter_ne_one' hχ1)
  obtain ⟨r, hr, hprodeq⟩ := descent_prod_eq_real (N := N) (f := f)
    (primitiveCharacter_sq_eq_one hsq)
  have hid := LFunction_apply_one_descent hχ1
  rw [hprodeq] at hid
  have hre : (LFunction χ 1).re = (LFunction χ.primitiveCharacter 1).re * r := by
    rw [hid]; simp [Complex.mul_re]
  have hfpow : (0 : ℝ) < (f : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hfR _
  have hbase0 : 0 ≤ (LFunction χ.primitiveCharacter 1).re := le_trans (by positivity) hbase
  have hstep : Real.pi / (N : ℝ) ^ (3 / 2 : ℝ) ≤ (LFunction χ.primitiveCharacter 1).re := by
    refine le_trans ?_ hbase
    apply div_le_div_of_nonneg_left Real.pi_pos.le hfpow
    exact Real.rpow_le_rpow hfR.le (by exact_mod_cast hfle) (by norm_num)
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hr
  have hsplit : (N : ℝ) ^ (5 / 2 : ℝ) = (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hNR, Real.rpow_one]
  rw [hsplit, hre]
  have h1 : Real.pi / ((N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ))
      = (Real.pi / (N : ℝ) ^ (3 / 2 : ℝ)) * (1 / (N : ℝ)) := by field_simp
  rw [h1]
  gcongr

/-! ## §7 — the odd interface, and its relation to `LandauL1`'s -/

/-- **The odd-`χ` effective lower bound at grade `A`** — `LandauL1.L1LowerEffective` with the
quantifier narrowed to ODD real nonprincipal characters.  Primitivity is NOT assumed (§6 discharges
the descent), so this is exactly the odd half of the target interface. -/
def L1LowerOddEffective (c A : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 → χ.Odd →
    c / (q : ℝ) ^ A ≤ (DirichletCharacter.LFunction χ 1).re

/-- The full interface restricts to the odd one — the free direction.  (The converse is FALSE as a
route: the even branch has no functional-equation anchor at all; see the module docstring.) -/
theorem l1LowerOddEffective_of_l1LowerEffective {c A : ℝ} (h : L1LowerEffective c A) :
    L1LowerOddEffective c A :=
  fun q _ χ hχ1 hsq _ => h q χ hχ1 hsq

/-- **`O-3`: the interface instance, granted `SawtoothOdd`.**  `π·q^{−5/2} ≤ (L(1,χ)).re`,
uniformly in `q`, at every odd real nonprincipal `χ`. -/
theorem l1LowerOddEffective_of_sawtooth (hsaw : SawtoothOdd) :
    L1LowerOddEffective Real.pi (5 / 2) :=
  fun _ _ _ hχ1 hsq hodd => L1_lower_odd_of_sawtooth hsaw hodd hsq hχ1

/-- The same instance normalised to `c = 1 ≤ 1`, the shape `LandauL1.L1_lower_real_effective`
demands of its constant. -/
theorem l1LowerOddEffective_one_of_sawtooth (hsaw : SawtoothOdd) :
    L1LowerOddEffective 1 (5 / 2) := by
  intro q _ χ hχ1 hsq hodd
  refine le_trans ?_ (l1LowerOddEffective_of_sawtooth hsaw q χ hχ1 hsq hodd)
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have : (0 : ℝ) < (q : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hq _
  gcongr
  linarith [Real.pi_gt_three]

end Salt.MR
