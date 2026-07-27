/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.LandauL1
import Salt.SW.EulerBridge
import Salt.SW.Siegel

/-!
# The imprimitive→primitive descent for the `L(1,χ)` floor

Every production route for an effective `L(1,χ)` lower bound (`LandauL1.L1LowerEffective`)
proves its bound for **primitive** `χ` only: the functional-equation/Gauss-sum lane needs
`|W(χ)| = 1` (primitive), the class-number lane needs the fundamental discriminant.  The
consumer `LandauL1.chi_floor_real_uniform` quantifies over **all** real nonprincipal `χ`.
This module is the bridge between the two, and it costs exactly one power of `q`.

## The mechanism

For `χ mod q` induced by the primitive `χ₁ = χ.primitiveCharacter` of level
`f = χ.conductor ∣ q`, `Salt.SW.LFunction_eq_primitive_mul` gives at `s = 1`

  `L(χ,1) = L(χ₁,1) · ∏_{p ∣ q} (1 − χ₁(p)/p)`.

Each Euler correction factor obeys `‖1 − χ₁(p)/p‖ ≥ 1 − 1/p ≥ 1/p` (`p ≥ 2`), so the
correction is `≥ ∏_{p ∣ q} 1/p ≥ 1/q` in norm (§1).  For real `χ` the value `L(χ,1)` is a
POSITIVE REAL (`Salt.SW.LFunction_apply_one_pos`), so `(L(χ,1)).re = ‖L(χ,1)‖`, and the norm
factorises: a primitive floor `c·f^{−A}` descends to `c·q^{−(A+1)}` (§3).  By
`LandauL1.door_L1_absorbed` the extra `+1` in the exponent is free — the door is indifferent
to the grade `A ≥ 0`.

## A note on the reality hypothesis (the shape actually needed)

The per-factor lower bound uses only `‖χ₁(p)‖ ≤ 1`, NOT the real case analysis
`χ₁(p) ∈ {0, ±1}`: §1 is therefore stated for an arbitrary character and an arbitrary
`Re s ≥ 1`, which is strictly stronger than the quadratic-only form.  Reality enters only
once, in §3, and through `LFunction_apply_one_pos` — the fact that makes `‖·‖` and `.re`
interchangeable on the left of the chain, so that the NORM lower bound on the correction (as
opposed to a lower bound on its real part, which would need the case analysis) suffices.

## Contents

* §1 `norm_one_sub_le_of_one_le_re`, `norm_eulerProd_lower`, `eulerCorr_prod_lower_real` —
  D-1: the Euler-correction product is `≥ 1/q` in norm on `Re s ≥ 1`.
* §2 `primitiveCharacter_ne_one`, `primitiveCharacter_quadratic`,
  `primitiveCharacter_conductor_le` — the transport of the three hypotheses
  (nonprincipal / real / level) to the inducing character.
* §3 `L1LowerEffective_descend` — D-2: a primitive-restricted floor at grade `A` yields the
  full `L1LowerEffective` at grade `A + 1`.
* §4 `primitiveCharacter_neg_one`, `primitiveCharacter_odd_iff` — D-3: parity is preserved by
  induction, plus `L1LowerEffectiveOdd` and `L1LowerEffectiveOdd_descend`, the odd-parity
  descent that an odd-primitive production (Gauss-sum lane) plugs into.

## Honesty

Nothing here produces a floor: §3 and §4 are implications whose hypothesis is exactly the
primitive-restricted production, still unlanded (`LandauL1`'s Zeno).  What is removed is the
primitivity gap — quantitatively, at the cost of one power of `q`.
-/

namespace Salt.MR

open Complex DirichletCharacter Salt.SW

/-! ## §1 — D-1: the Euler correction is `≥ 1/q` in norm on `Re s ≥ 1` -/

/-- Per-factor lower bound: `‖1 − ψ(p)·p^{−s}‖ ≥ 1/p` for a prime `p` and `Re s ≥ 1`.
Uses only `‖ψ(p)‖ ≤ 1`: `‖ψ(p)p^{−s}‖ ≤ p^{−Re s} ≤ 1/p`, and `1 − 1/p ≥ 1/p` for `p ≥ 2`.
(For real `ψ` the factor is one of `1`, `1 − 1/p`, `1 + 1/p`; the norm bound covers all
three without the case analysis.) -/
lemma norm_one_sub_le_of_one_le_re {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 ≤ s.re) : (1 : ℝ) / (p : ℝ) ≤ ‖1 - ψ p * (p : ℂ) ^ (-s)‖ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  -- `‖p^{−s}‖ = p^{−σ} ≤ p^{−1} = 1/p`
  have hcp : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / (p : ℝ) := by
    rw [norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    have h1 : ((p : ℝ)) ^ (-s.re) ≤ ((p : ℝ)) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : ((p : ℝ)) ^ (-1 : ℝ) = 1 / (p : ℝ) := by rw [Real.rpow_neg_one, one_div]
    linarith [h1, h2.le, h2.symm.le]
  have hmul : ‖ψ p * (p : ℂ) ^ (-s)‖ ≤ 1 / (p : ℝ) := by
    rw [norm_mul]
    calc ‖ψ p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * (1 / (p : ℝ)) :=
          mul_le_mul (ψ.norm_le_one _) hcp (norm_nonneg _) zero_le_one
      _ = 1 / (p : ℝ) := one_mul _
  -- `‖1 − z‖ ≥ 1 − ‖z‖ ≥ 1 − 1/p ≥ 1/p`
  have hlow : (1 : ℝ) - ‖ψ p * (p : ℂ) ^ (-s)‖ ≤ ‖1 - ψ p * (p : ℂ) ^ (-s)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (ψ p * (p : ℂ) ^ (-s))
    rwa [norm_one] at h
  have hhalf : (1 : ℝ) / (p : ℝ) ≤ 1 - 1 / (p : ℝ) := by
    rw [div_le_iff₀ hp0]
    have : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith
    nlinarith
  linarith

/-- **D-1 (product form).** For ANY character `ψ` (any level) and `Re s ≥ 1`,
`‖∏_{p ∣ q} (1 − ψ(p)p^{−s})‖ ≥ 1/q`.  The mirror of `SiegelArm.eulerFactor_prod_lower`
(the principal-character template `ψ = 1`) with the character twist carried through: the
per-factor bound `≥ 1/p` and `∏_{p ∣ q} p ∣ q`.  The empty product (`q = 1`) is the
statement `1 ≤ 1`. -/
theorem norm_eulerProd_lower {M : ℕ} (ψ : DirichletCharacter ℂ M) (q : ℕ) [NeZero q] {s : ℂ}
    (hs : 1 ≤ s.re) :
    1 / (q : ℝ) ≤ ‖∏ p ∈ q.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s))‖ := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [norm_prod]
  have hnn : ∀ p ∈ q.primeFactors, (0 : ℝ) ≤ (1 : ℝ) / (p : ℝ) := by
    intro p hp
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    positivity
  have hcmp : ∏ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ)
      ≤ ∏ p ∈ q.primeFactors, ‖1 - ψ p * (p : ℂ) ^ (-s)‖ :=
    Finset.prod_le_prod hnn
      (fun p hp => norm_one_sub_le_of_one_le_re ψ (Nat.prime_of_mem_primeFactors hp) hs)
  have hprodpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    have hpos : 0 < ∏ p ∈ q.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    exact_mod_cast hpos
  have heq : ∏ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ)
      = 1 / ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    simp [one_div, Finset.prod_inv_distrib]
  have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  have hfin : 1 / (q : ℝ) ≤ ∏ p ∈ q.primeFactors, (1 : ℝ) / (p : ℝ) := by
    rw [heq]; exact one_div_le_one_div_of_le hprodpos hle
  linarith

/-- **D-1, in the `eulerCorr` shape the factorization speaks.**  For `χ mod q` and `Re s ≥ 1`,
`‖eulerCorr χ s‖ ≥ 1/q`: the imprimitive→primitive correction of
`Salt.SW.LFunction_eq_primitive_mul` costs at most a factor `q`.  Stated for arbitrary `χ`;
the real (`χ² = 1`) case is the one §3 consumes. -/
theorem eulerCorr_prod_lower_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 ≤ s.re) : 1 / (q : ℝ) ≤ ‖eulerCorr χ s‖ := by
  rw [eulerCorr]
  exact norm_eulerProd_lower χ.primitiveCharacter q hs

/-- The `s = 1` instance, the one the descent uses: `1/q ≤ ‖eulerCorr χ 1‖`. -/
theorem eulerCorr_one_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    1 / (q : ℝ) ≤ ‖eulerCorr χ 1‖ :=
  eulerCorr_prod_lower_real χ (by simp)

/-! ## §2 — transporting the hypotheses to the inducing character -/

/-- A nonprincipal character induces a nonprincipal primitive character.  (Equivalently:
`χ = 1 ↔ χ.conductor = 1`, so the principal corner is exactly the corner the interface
excludes.) -/
lemma primitiveCharacter_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := fun h =>
  hχ (by rw [← changeLevel_primitiveCharacter χ, h, changeLevel_one])

/-- A real (quadratic) character induces a real primitive character.  The descent direction of
`SW.changeLevel_quadratic`: `changeLevel` is an injective monoid hom (`changeLevel_injective`,
`NeZero q`), so `changeLevel (χ₁²) = χ² = 1 = changeLevel 1` forces `χ₁² = 1`. -/
lemma primitiveCharacter_quadratic {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hsq : χ ^ 2 = 1) : χ.primitiveCharacter ^ 2 = 1 := by
  have hmap : changeLevel χ.conductor_dvd_level (χ.primitiveCharacter ^ 2)
      = changeLevel χ.conductor_dvd_level (1 : DirichletCharacter ℂ χ.conductor) := by
    rw [map_pow, changeLevel_primitiveCharacter, hsq, changeLevel_one]
  exact changeLevel_injective χ.conductor_dvd_level hmap

/-- The conductor divides, hence is at most, the level. -/
lemma primitiveCharacter_conductor_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.conductor ≤ q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level

/-- For real nonprincipal `χ`, `L(χ,1)` is a positive real, so its norm IS its real part.
This is the fact that lets §3 spend a NORM lower bound on the Euler correction (D-1) rather
than a lower bound on its real part. -/
lemma norm_LFunction_one_eq_re {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hsq : χ ^ 2 = 1) : ‖LFunction χ 1‖ = (LFunction χ 1).re := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp (LFunction_apply_one_pos hχ hsq)
  set z : ℂ := LFunction χ 1 with hz
  have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
  calc ‖z‖ = ‖((z.re : ℝ) : ℂ)‖ := by rw [hz']
    _ = |z.re| := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = z.re := abs_of_nonneg hre.le

/-! ## §3 — D-2: the descent -/

/-- **The imprimitive→primitive descent.**  Given the floor `c·f^{−A}` for every PRIMITIVE
real nonprincipal character of every level `f`, the same floor holds for EVERY real
nonprincipal character at grade `A + 1`, i.e. `L1LowerEffective c (A+1)`.

The chain, at `χ mod q` with `χ₁ = χ.primitiveCharacter` of level `f = χ.conductor ∣ q`:

  `c·q^{−(A+1)} = (c·q^{−A})·(1/q) ≤ (c·f^{−A})·(1/q) ≤ (L(χ₁,1)).re·‖eulerCorr χ 1‖`
  `≤ ‖L(χ₁,1)‖·‖eulerCorr χ 1‖ = ‖L(χ,1)‖ = (L(χ,1)).re`,

using `f ≤ q` and `A ≥ 0` for the first inequality, the hypothesis and D-1
(`eulerCorr_one_lower`) for the second, `Complex.re_le_norm` for the third,
`SW.LFunction_eq_primitive_mul` for the equality, and `norm_LFunction_one_eq_re` (reality of
`χ`) for the last.  The `+1` in the grade is free at the consumer: `door_L1_absorbed` absorbs
any `A ≥ 0`. -/
theorem L1LowerEffective_descend {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hprim : ∀ (f : ℕ) [NeZero f] (ψ : DirichletCharacter ℂ f), ψ.IsPrimitive → ψ ≠ 1 →
      ψ ^ 2 = 1 → c / (f : ℝ) ^ A ≤ (LFunction ψ 1).re) :
    L1LowerEffective c (A + 1) := by
  intro q _ χ hχ1 hsq
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hf1 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hf0 : (0 : ℝ) < (χ.conductor : ℝ) := by exact_mod_cast hf1
  have hfq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast primitiveCharacter_conductor_le χ
  -- the floor at the inducing character
  have hfloor : c / (χ.conductor : ℝ) ^ A ≤ (LFunction χ.primitiveCharacter 1).re :=
    hprim χ.conductor χ.primitiveCharacter (primitiveCharacter_isPrimitive χ)
      (primitiveCharacter_ne_one hχ1) (primitiveCharacter_quadratic hsq)
  have hfApos : (0 : ℝ) < (χ.conductor : ℝ) ^ A := Real.rpow_pos_of_pos hf0 A
  have hprimre : (0 : ℝ) ≤ (LFunction χ.primitiveCharacter 1).re :=
    le_trans (div_pos hc hfApos).le hfloor
  -- the correction, `≥ 1/q` in norm
  have hcorr : 1 / (q : ℝ) ≤ ‖eulerCorr χ 1‖ := eulerCorr_one_lower χ
  -- the exponent split `q^{A+1} = q^A · q`
  have hsplit : c / (q : ℝ) ^ (A + 1) = (c / (q : ℝ) ^ A) * (1 / (q : ℝ)) := by
    rw [Real.rpow_add hq0, Real.rpow_one]
    field_simp
  have hstep1 : c / (q : ℝ) ^ A ≤ c / (χ.conductor : ℝ) ^ A := by
    have hpow : (χ.conductor : ℝ) ^ A ≤ (q : ℝ) ^ A := Real.rpow_le_rpow hf0.le hfq hA
    gcongr
  calc c / (q : ℝ) ^ (A + 1)
      = (c / (q : ℝ) ^ A) * (1 / (q : ℝ)) := hsplit
    _ ≤ (c / (χ.conductor : ℝ) ^ A) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep1 (by positivity)
    _ ≤ (LFunction χ.primitiveCharacter 1).re * ‖eulerCorr χ 1‖ :=
        mul_le_mul hfloor hcorr (by positivity) hprimre
    _ ≤ ‖LFunction χ.primitiveCharacter 1‖ * ‖eulerCorr χ 1‖ :=
        mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)
    _ = ‖LFunction χ 1‖ := by
        rw [LFunction_eq_primitive_mul χ (Or.inl hχ1), norm_mul]
    _ = (LFunction χ 1).re := norm_LFunction_one_eq_re hχ1 hsq

/-! ## §4 — D-3: parity transport, and the odd-only descent -/

/-- The inducing character agrees with `χ` at `−1`: `χ₁(−1) = χ(−1)`.  Immediate from
mathlib's `primitiveCharacter_apply_of_isCoprime` at `a = (−1 : ℤ)` (coprime to every level).
This is the transport that lets an odd-primitive production reach all odd `χ`. -/
lemma primitiveCharacter_neg_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter (-1 : ZMod χ.conductor) = χ (-1 : ZMod q) := by
  have hcop : IsCoprime (-1 : ℤ) ((q : ℕ) : ℤ) := (isCoprime_one_left).neg_left
  have h := primitiveCharacter_apply_of_isCoprime χ hcop
  simpa using h

/-- **D-3 — parity is preserved by induction.**  `χ` is odd iff its inducing primitive
character is odd (`Odd ψ ↔ ψ(−1) = −1`). -/
lemma primitiveCharacter_odd_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter.Odd ↔ χ.Odd := by
  unfold DirichletCharacter.Odd
  rw [primitiveCharacter_neg_one χ]

/-- The odd-parity restriction of `LandauL1.L1LowerEffective`: the floor `c·q^{−A}` at every
real nonprincipal **odd** character.  This is the shape the Gauss-sum/functional-equation lane
produces (`L(1,χ) ≥ π·q^{−3/2}` for odd real primitive `χ`); the even case has no elementary
substitute (see `LandauL1`'s route verdict). -/
def L1LowerEffectiveOdd (c A : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 → χ.Odd →
    c / (q : ℝ) ^ A ≤ (DirichletCharacter.LFunction χ 1).re

/-- **The odd descent.**  The same bridge as `L1LowerEffective_descend`, with the parity side
condition threaded through `primitiveCharacter_odd_iff`: an ODD-primitive production at grade
`A` gives the odd floor at grade `A + 1` for all odd real nonprincipal `χ`, primitive or not.

This is the socket for the Gauss-sum lane: supply the hypothesis at `A = 3/2` and read off
`L1LowerEffectiveOdd c (5/2)`, which `door_L1_absorbed` (any `A ≥ 0`) discharges. -/
theorem L1LowerEffectiveOdd_descend {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hprim : ∀ (f : ℕ) [NeZero f] (ψ : DirichletCharacter ℂ f), ψ.IsPrimitive → ψ ≠ 1 →
      ψ ^ 2 = 1 → ψ.Odd → c / (f : ℝ) ^ A ≤ (LFunction ψ 1).re) :
    L1LowerEffectiveOdd c (A + 1) := by
  intro q _ χ hχ1 hsq hodd
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hf1 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hf0 : (0 : ℝ) < (χ.conductor : ℝ) := by exact_mod_cast hf1
  have hfq : (χ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast primitiveCharacter_conductor_le χ
  have hfloor : c / (χ.conductor : ℝ) ^ A ≤ (LFunction χ.primitiveCharacter 1).re :=
    hprim χ.conductor χ.primitiveCharacter (primitiveCharacter_isPrimitive χ)
      (primitiveCharacter_ne_one hχ1) (primitiveCharacter_quadratic hsq)
      ((primitiveCharacter_odd_iff χ).mpr hodd)
  have hfApos : (0 : ℝ) < (χ.conductor : ℝ) ^ A := Real.rpow_pos_of_pos hf0 A
  have hprimre : (0 : ℝ) ≤ (LFunction χ.primitiveCharacter 1).re :=
    le_trans (div_pos hc hfApos).le hfloor
  have hcorr : 1 / (q : ℝ) ≤ ‖eulerCorr χ 1‖ := eulerCorr_one_lower χ
  have hsplit : c / (q : ℝ) ^ (A + 1) = (c / (q : ℝ) ^ A) * (1 / (q : ℝ)) := by
    rw [Real.rpow_add hq0, Real.rpow_one]
    field_simp
  have hstep1 : c / (q : ℝ) ^ A ≤ c / (χ.conductor : ℝ) ^ A := by
    have hpow : (χ.conductor : ℝ) ^ A ≤ (q : ℝ) ^ A := Real.rpow_le_rpow hf0.le hfq hA
    gcongr
  calc c / (q : ℝ) ^ (A + 1)
      = (c / (q : ℝ) ^ A) * (1 / (q : ℝ)) := hsplit
    _ ≤ (c / (χ.conductor : ℝ) ^ A) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep1 (by positivity)
    _ ≤ (LFunction χ.primitiveCharacter 1).re * ‖eulerCorr χ 1‖ :=
        mul_le_mul hfloor hcorr (by positivity) hprimre
    _ ≤ ‖LFunction χ.primitiveCharacter 1‖ * ‖eulerCorr χ 1‖ :=
        mul_le_mul_of_nonneg_right (Complex.re_le_norm _) (norm_nonneg _)
    _ = ‖LFunction χ 1‖ := by
        rw [LFunction_eq_primitive_mul χ (Or.inl hχ1), norm_mul]
    _ = (LFunction χ 1).re := norm_LFunction_one_eq_re hχ1 hsq

end Salt.MR
