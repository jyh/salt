/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib

/-!
# Rung 4a — explicit gaps ≤ 12: the rational certificate (card C1, blueprint P2)

A machine-checked certificate for Maynard's `k = 5` optimization
(`docs/blueprints/explicit12-design.md`, §2, §6-C1). Everything here is exact
`ℚ` arithmetic — no analysis, no measure theory.

For a polynomial `F = Σ_α f_α · t^α` on the 5-simplex `Δ₅` (exponent vectors
`α : Fin 5 → ℕ`), the Dirichlet formula turns the sieve moments into exact
rationals:

* `I(F) = ∫_{Δ₅} F² = Σ_{α,β} f_α f_β · DInt (α + β)` with the `d = 0` Dirichlet
  integral `DInt c = (∏ᵢ cᵢ!) / (5 + Σᵢ cᵢ)!`;
* `J⁽ᵐ⁾(F) = Σ_{α,β} f_α f_β · JD α β m` with
  `JD α β m = (∏_{i≠m}(αᵢ+βᵢ)!)·(αₘ+βₘ+2)! / ((αₘ+1)(βₘ+1)·(6 + Σᵢ(αᵢ+βᵢ))!)`.

The certified degree-3 symmetric optimum is

`F★ = 7·1 − 19·m₁ + 28·m₂ + 30·m₁₁ − 15·m₃ − 21·m₂₁ − 19·m₁₁₁`

(monomial symmetric functions on 5 variables), fully expanded to its 56
monomials below. The certificate is

`I(F★) = 1597/399168`,  `Σ_m J⁽ᵐ⁾(F★) = 191881/23950080`,

so `M₅ = 191881/95820 = 2.00251… > 2`, i.e. `2·I(F★) < Σ_m J⁽ᵐ⁾(F★)`, which
after clearing the common denominator `23950080` is the trivial `191640 < 191881`.
-/

open Nat

namespace Salt.Twelve

/-! ## The `ℚ`-valued Dirichlet pairings -/

/-- The `d = 0` Dirichlet integral `∫_{Δ₅} ∏ᵢ tᵢ^{cᵢ} dt = (∏ᵢ cᵢ!) / (5 + Σᵢ cᵢ)!`.
This is the exact rational value of `I`'s bilinear kernel. -/
def DInt (c : Fin 5 → ℕ) : ℚ := (∏ i, (c i)!) / (5 + ∑ i, c i)!

/-- The `J⁽ᵐ⁾` bilinear kernel: `(∏_{i≠m}(αᵢ+βᵢ)!)·(αₘ+βₘ+2)!` divided by
`(αₘ+1)(βₘ+1)·(6 + Σᵢ(αᵢ+βᵢ))!`. The denominator exponent
`6 + Σᵢ(αᵢ+βᵢ) = 4 + (αₘ+βₘ+2) + Σ_{i≠m}(αᵢ+βᵢ)` is the `k = 4` Dirichlet
denominator on the 4-variable slice with the `αₘ+βₘ+2` budget power. -/
def JD (α β : Fin 5 → ℕ) (m : Fin 5) : ℚ :=
  (∏ i ∈ Finset.univ.erase m, ((α i + β i)! : ℚ)) * ((α m + β m + 2)! : ℚ) /
    (((α m + 1) * (β m + 1) : ℕ) * ((6 + ∑ i, (α i + β i))! : ℕ))

/-- Erase-free form of `JD`, using `∏_{i≠m} f = (∏ᵢ f) / f m` and
`(c+2)! = c! · (c+1)(c+2)`. Reduces with the same `Fin.prod_univ_five`
machinery as `DInt`, avoiding `Finset.erase` in the certificate evaluation. -/
lemma JD_eq (α β : Fin 5 → ℕ) (m : Fin 5) :
    JD α β m = (∏ i, ((α i + β i)! : ℚ)) * (((α m + β m + 1) * (α m + β m + 2) : ℕ) : ℚ) /
      (((α m + 1) * (β m + 1) : ℕ) * ((6 + ∑ i, (α i + β i))! : ℕ)) := by
  unfold JD
  have key : ((α m + β m + 2)! : ℚ)
      = ((α m + β m)! : ℚ) * (((α m + β m + 1) * (α m + β m + 2) : ℕ) : ℚ) := by
    push_cast [Nat.factorial_succ]; ring
  have hprod : (∏ i, ((α i + β i)! : ℚ))
      = ((α m + β m)! : ℚ) * ∏ i ∈ Finset.univ.erase m, ((α i + β i)! : ℚ) :=
    (Finset.mul_prod_erase Finset.univ (fun i => ((α i + β i)! : ℚ)) (Finset.mem_univ m)).symm
  rw [hprod, key]; ring

/-! ## Polynomial representation and the two quadratic forms -/

/-- A monomial `t^α` with a rational coefficient: `(α, f_α)`. -/
abbrev Mono : Type := (Fin 5 → ℕ) × ℚ

/-- A polynomial as a finite formal `ℚ`-combination of monomials. -/
abbrev Poly : Type := List Mono

/-- `I(F) = Σ_{α,β} f_α f_β · DInt (α + β)`, the exact rational value of
`∫_{Δ₅} F²`. -/
def Ical (F : Poly) : ℚ :=
  (F.map (fun p => (F.map (fun q => p.2 * q.2 * DInt (p.1 + q.1))).sum)).sum

/-- `J⁽ᵐ⁾(F) = Σ_{α,β} f_α f_β · JD α β m`, the exact rational value of the
`m`-th derivative sieve moment. -/
def Jcal (m : Fin 5) (F : Poly) : ℚ :=
  (F.map (fun p => (F.map (fun q => p.2 * q.2 * JD p.1 q.1 m)).sum)).sum

/-! ## The certified optimum `F★`

`F★ = 7·1 − 19·m₁ + 28·m₂ + 30·m₁₁ − 15·m₃ − 21·m₂₁ − 19·m₁₁₁`, expanded to all
56 monomials (`m_λ` = the sum over the distinct permutations of the exponent
vector `λ`). The 7 symmetric orbits contribute `1 + 5 + 5 + 10 + 5 + 20 + 10 = 56`
monomials. -/
def Fstar : Poly := [
  (![0,0,0,0,0], 7),
  (![0,0,0,0,1], -19),
  (![0,0,0,1,0], -19),
  (![0,0,1,0,0], -19),
  (![0,1,0,0,0], -19),
  (![1,0,0,0,0], -19),
  (![0,0,0,0,2], 28),
  (![0,0,0,2,0], 28),
  (![0,0,2,0,0], 28),
  (![0,2,0,0,0], 28),
  (![2,0,0,0,0], 28),
  (![0,0,0,1,1], 30),
  (![0,0,1,0,1], 30),
  (![0,0,1,1,0], 30),
  (![0,1,0,0,1], 30),
  (![0,1,0,1,0], 30),
  (![0,1,1,0,0], 30),
  (![1,0,0,0,1], 30),
  (![1,0,0,1,0], 30),
  (![1,0,1,0,0], 30),
  (![1,1,0,0,0], 30),
  (![0,0,0,0,3], -15),
  (![0,0,0,3,0], -15),
  (![0,0,3,0,0], -15),
  (![0,3,0,0,0], -15),
  (![3,0,0,0,0], -15),
  (![0,0,0,1,2], -21),
  (![0,0,0,2,1], -21),
  (![0,0,1,0,2], -21),
  (![0,0,1,2,0], -21),
  (![0,0,2,0,1], -21),
  (![0,0,2,1,0], -21),
  (![0,1,0,0,2], -21),
  (![0,1,0,2,0], -21),
  (![0,1,2,0,0], -21),
  (![0,2,0,0,1], -21),
  (![0,2,0,1,0], -21),
  (![0,2,1,0,0], -21),
  (![1,0,0,0,2], -21),
  (![1,0,0,2,0], -21),
  (![1,0,2,0,0], -21),
  (![1,2,0,0,0], -21),
  (![2,0,0,0,1], -21),
  (![2,0,0,1,0], -21),
  (![2,0,1,0,0], -21),
  (![2,1,0,0,0], -21),
  (![0,0,1,1,1], -19),
  (![0,1,0,1,1], -19),
  (![0,1,1,0,1], -19),
  (![0,1,1,1,0], -19),
  (![1,0,0,1,1], -19),
  (![1,0,1,0,1], -19),
  (![1,0,1,1,0], -19),
  (![1,1,0,0,1], -19),
  (![1,1,0,1,0], -19),
  (![1,1,1,0,0], -19)
]

/-! ## Sanity checks (verifier brief) -/

-- (a) `DInt` matches the Dirichlet formula at two hand-checkable instances.
/-- `vol Δ₅ = ∫_{Δ₅} 1 = DInt 0 = 1/5! = 1/120`. -/
example : DInt ![0, 0, 0, 0, 0] = 1 / 120 := by
  simp only [DInt, Fin.prod_univ_five, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num [Nat.factorial]

/-- `∫_{Δ₅} t₁ = DInt (1,0,0,0,0) = 1!·0!⁴/6! = 1/720`. -/
example : DInt ![1, 0, 0, 0, 0] = 1 / 720 := by
  simp only [DInt, Fin.prod_univ_five, Fin.sum_univ_five, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num [Nat.factorial]

-- (d) `F★` really is the 56-monomial expansion of its 7 symmetric orbits.
/-- `F★` has exactly 56 monomials. -/
example : Fstar.length = 56 := by decide

/-- The coefficients sum to `F★(1,…,1) = 7 − 19·5 + 28·5 + 30·10 − 15·5 − 21·20 − 19·10 = −333`,
cross-checking the orbit sizes `1,5,5,10,5,20,10`. -/
example : (Fstar.map Prod.snd).sum = -333 := by norm_num [Fstar]

/-! ## The certificate -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- This is a large closed-form `ℚ` certificate: the proof expands a 56×56
-- monomial double sum of exact Dirichlet rationals and evaluates it with
-- `simp` + `norm_num`, exceeding the default heartbeat/recursion budgets.
/-- `I(F★) = 1597/399168` (exact `ℚ`; matches the off-line Dirichlet computation). -/
theorem I_Fstar : Ical Fstar = 1597 / 399168 := by
  simp (config := { maxSteps := 100000000 }) only [Ical, Fstar, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, DInt, Fin.prod_univ_five, Fin.sum_univ_five, Pi.add_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- This is a large closed-form `ℚ` certificate: the proof expands a 56×56
-- monomial double sum of exact Dirichlet rationals and evaluates it with
-- `simp` + `norm_num`, exceeding the default heartbeat/recursion budgets.
/-- `J⁽0⁾(F★) = 191881/119750400` (each of the five equals `Σ_m J / 5`). -/
theorem J_Fstar_0 : Jcal 0 Fstar = 191881 / 119750400 := by
  simp (config := { maxSteps := 100000000 }) only [Jcal, Fstar, JD_eq, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Fin.prod_univ_five, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- This is a large closed-form `ℚ` certificate: the proof expands a 56×56
-- monomial double sum of exact Dirichlet rationals and evaluates it with
-- `simp` + `norm_num`, exceeding the default heartbeat/recursion budgets.
/-- `J⁽1⁾(F★) = 191881/119750400` (each of the five equals `Σ_m J / 5`). -/
theorem J_Fstar_1 : Jcal 1 Fstar = 191881 / 119750400 := by
  simp (config := { maxSteps := 100000000 }) only [Jcal, Fstar, JD_eq, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Fin.prod_univ_five, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- This is a large closed-form `ℚ` certificate: the proof expands a 56×56
-- monomial double sum of exact Dirichlet rationals and evaluates it with
-- `simp` + `norm_num`, exceeding the default heartbeat/recursion budgets.
/-- `J⁽2⁾(F★) = 191881/119750400` (each of the five equals `Σ_m J / 5`). -/
theorem J_Fstar_2 : Jcal 2 Fstar = 191881 / 119750400 := by
  simp (config := { maxSteps := 100000000 }) only [Jcal, Fstar, JD_eq, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Fin.prod_univ_five, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- This is a large closed-form `ℚ` certificate: the proof expands a 56×56
-- monomial double sum of exact Dirichlet rationals and evaluates it with
-- `simp` + `norm_num`, exceeding the default heartbeat/recursion budgets.
/-- `J⁽3⁾(F★) = 191881/119750400` (each of the five equals `Σ_m J / 5`). -/
theorem J_Fstar_3 : Jcal 3 Fstar = 191881 / 119750400 := by
  simp (config := { maxSteps := 100000000 }) only [Jcal, Fstar, JD_eq, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Fin.prod_univ_five, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num [Nat.factorial]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- This is a large closed-form `ℚ` certificate: the proof expands a 56×56
-- monomial double sum of exact Dirichlet rationals and evaluates it with
-- `simp` + `norm_num`, exceeding the default heartbeat/recursion budgets.
/-- `J⁽4⁾(F★) = 191881/119750400` (each of the five equals `Σ_m J / 5`). -/
theorem J_Fstar_4 : Jcal 4 Fstar = 191881 / 119750400 := by
  simp (config := { maxSteps := 100000000 }) only [Jcal, Fstar, JD_eq, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Fin.prod_univ_five, Fin.sum_univ_five,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  norm_num [Nat.factorial]

/-- `Σ_{m=0}^{4} J⁽ᵐ⁾(F★) = 191881/23950080` (exact `ℚ`; matches the off-line
Dirichlet computation). -/
theorem J_Fstar : (∑ m : Fin 5, Jcal m Fstar) = 191881 / 23950080 := by
  rw [Fin.sum_univ_five, J_Fstar_0, J_Fstar_1, J_Fstar_2, J_Fstar_3, J_Fstar_4]
  norm_num

/-- **The certificate.** `2·I(F★) < Σ_m J⁽ᵐ⁾(F★)`, i.e. `M₅ = (Σ_m J)/I > 2`:
the `k = 5` Maynard functional beats the `2` threshold with certified slack
`δ★ = 241/95820 ≈ 2.515·10⁻³`. -/
theorem M5_cert : 2 * Ical Fstar < ∑ m : Fin 5, Jcal m Fstar := by
  rw [I_Fstar, J_Fstar]; norm_num

end Salt.Twelve
