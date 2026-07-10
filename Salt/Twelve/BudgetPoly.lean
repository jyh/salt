/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.Certificate

/-!
# Rung 4a — the symbolic budget-polynomial layer (card W2-3, blueprint P3.e)

This module decouples the `ℚ`-arithmetic of the certificate (C1) from the
analysis (Crux 4, wave 3). Wave 3 concludes its multi-dimensional moment
estimates against a *budget polynomial* and its recursive Dirichlet
bookkeeping `simplexInt`; this file ties `simplexInt` back to C1's certified
`Ical`/`Jcal`.

A **budget polynomial** on `n` variables is a finite formal `ℚ`-combination of
*budget monomials* `coeff · (∏ᵢ tᵢ^{eᵢ}) · (1 − Σt)^d`, encoded as a triple
`(e : Fin n → ℕ, d : ℕ, coeff : ℚ)`:

* `simplexInt` integrates a budget polynomial over the `n`-simplex using the
  Dirichlet integral `DInt'(e,d) = (∏ᵢ eᵢ!)·d! / (n + d + Σᵢ eᵢ)!`;
* `ofPoly` lifts a C1 `Poly` (t-monomials, budget power `0`) into `BPoly 5`;
* `contractAt m` is the `∫₀^{1−Σ_{i≠m}tᵢ} · dtₘ` peel of coordinate `m`,
  producing a `BPoly 4` with a budget power;
* `mul`/`sq` multiply budget polynomials; `eval` evaluates over `ℝ`.

The two deliverables (Crux 4):

* `simplexInt_sq_ofPoly_eq_Ical : simplexInt (sq (ofPoly F)) = Ical F`;
* `simplexInt_sq_contractAt_eq_Jcal : simplexInt (sq (contractAt m F)) = Jcal m F`.

Both are proved for a **general** `F : Poly` by list/`Finset` algebra — the
semantic identity — so wave 3 may use them for any test polynomial, not only
`F★`.
-/

open Nat

namespace Salt.Twelve

/-! ## The budget polynomial and its simplex integral -/

/-- A budget polynomial on `n` variables: a list of budget monomials
`(e, d, coeff)` denoting `coeff · (∏ᵢ tᵢ^{eᵢ}) · (1 − Σt)^d`. -/
abbrev BPoly (n : ℕ) : Type := List ((Fin n → ℕ) × ℕ × ℚ)

/-- The Dirichlet integral of a single budget monomial over the `n`-simplex:
`∫_{Δₙ} (∏ᵢ tᵢ^{eᵢ})·(1 − Σt)^d dt = (∏ᵢ eᵢ!)·d! / (n + d + Σᵢ eᵢ)!`.
For `d = 0` this is C1's `DInt` (on `n = 5`). -/
def DInt' {n : ℕ} (e : Fin n → ℕ) (d : ℕ) : ℚ :=
  (((∏ i, (e i)!) * d ! : ℕ) : ℚ) / (((n + d + ∑ i, e i)! : ℕ) : ℚ)

/-- `simplexInt p = ∫_{Δₙ} p dt`, summing the Dirichlet integral of each monomial. -/
def simplexInt {n : ℕ} (p : BPoly n) : ℚ :=
  (p.map (fun m => m.2.2 * DInt' m.1 m.2.1)).sum

/-- Lift a C1 polynomial (t-monomials, no budget) into a budget polynomial on
the 5-simplex: each `Mono (e, c) ↦ (e, 0, c)`. -/
def ofPoly (F : Poly) : BPoly 5 :=
  F.map (fun a => (a.1, 0, a.2))

/-- The `∫₀^{1−Σ_{i≠m}tᵢ} · dtₘ` contraction of coordinate `m`. Each C1 monomial
`Mono (α, c)` maps to a `BPoly 4` monomial with the `m`-coordinate removed from
the exponent vector, budget power `αₘ + 1`, and coefficient `c/(αₘ+1)`, since
`∫₀^{1−Σ_{i≠m}tᵢ} tₘ^{αₘ} dtₘ = (1−Σ_{i≠m}tᵢ)^{αₘ+1}/(αₘ+1)`. -/
def contractAt (m : Fin 5) (F : Poly) : BPoly 4 :=
  F.map (fun a => (Fin.removeNth m a.1, a.1 m + 1, a.2 / ((a.1 m + 1 : ℕ) : ℚ)))

/-- The list product of budget polynomials: pair every pair of monomials, add
t-exponents (pointwise), add budget exponents, multiply coefficients. -/
def mul {n : ℕ} (p q : BPoly n) : BPoly n :=
  p.flatMap (fun a => q.map (fun b => (a.1 + b.1, a.2.1 + b.2.1, a.2.2 * b.2.2)))

/-- The square of a budget polynomial. -/
def sq {n : ℕ} (p : BPoly n) : BPoly n := mul p p

/-- Evaluation of a budget polynomial at a real point `t : Fin n → ℝ`: each
monomial `(e, d, c)` evaluates to `c · (∏ᵢ tᵢ^{eᵢ}) · (1 − Σt)^d`. This is the
wave-3 bridge between the symbolic layer and the analytic integral. -/
def eval {n : ℕ} (p : BPoly n) (t : Fin n → ℝ) : ℝ :=
  (p.map (fun m => (m.2.2 : ℝ) * (∏ i, t i ^ m.1 i) * (1 - ∑ i, t i) ^ m.2.1)).sum

/-! ## Sanity checks (verifier brief (b)) -/

/-- `∫_{Δ₅} 1 = simplexInt [(0, 0, 1)] = DInt' 0 0 = 1/5! = 1/120`. -/
example : simplexInt (n := 5) [(![0,0,0,0,0], 0, 1)] = 1 / 120 := by
  simp only [simplexInt, DInt', Fin.prod_univ_five, Fin.sum_univ_five, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num [Nat.factorial]

/-- `∫_{Δ₅} (1 − Σt) = simplexInt [(0, 1, 1)] = DInt' 0 1 = 1!/6! = 1/720`
(one budget instance). -/
example : simplexInt (n := 5) [(![0,0,0,0,0], 1, 1)] = 1 / 720 := by
  simp only [simplexInt, DInt', Fin.prod_univ_five, Fin.sum_univ_five, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  norm_num [Nat.factorial]

/-! ## `simplexInt` is additive and multiplicative in the list structure -/

/-- `simplexInt` is additive over list append. -/
lemma simplexInt_append {n : ℕ} (p q : BPoly n) :
    simplexInt (p ++ q) = simplexInt p + simplexInt q := by
  simp only [simplexInt, List.map_append, List.sum_append]

/-- The integral of a product expands as a double sum over the two factors. -/
lemma simplexInt_mul {n : ℕ} (p q : BPoly n) :
    simplexInt (mul p q)
    = (p.map (fun a =>
        (q.map (fun b => a.2.2 * b.2.2 * DInt' (a.1 + b.1) (a.2.1 + b.2.1))).sum)).sum := by
  induction p with
  | nil => simp [mul, simplexInt]
  | cons a p' ih =>
    have step : mul (a :: p') q
        = q.map (fun b => (a.1 + b.1, a.2.1 + b.2.1, a.2.2 * b.2.2)) ++ mul p' q := by
      simp only [mul, List.flatMap_cons]
    rw [step, simplexInt_append, ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    simp only [simplexInt, List.map_map, Function.comp_def]

/-- The integral of `sq (F.map g)` for any lift `g` of the C1 monomials. -/
lemma simplexInt_sq_map {n : ℕ} (g : Mono → (Fin n → ℕ) × ℕ × ℚ) (F : Poly) :
    simplexInt (sq (F.map g))
    = (F.map (fun a =>
        (F.map (fun b => (g a).2.2 * (g b).2.2 *
          DInt' ((g a).1 + (g b).1) ((g a).2.1 + (g b).2.1))).sum)).sum := by
  rw [sq, simplexInt_mul]
  simp only [List.map_map, Function.comp_def]

/-! ## The `d = 0` reduction: `DInt'` on `n = 5` collapses to C1's `DInt` -/

/-- On the 5-simplex with budget power `0`, `DInt'` is exactly C1's `DInt`. -/
lemma DInt'_zero (c : Fin 5 → ℕ) : DInt' c 0 = DInt c := by
  simp only [DInt', DInt, Nat.factorial_zero, mul_one, Nat.add_zero]

/-! ## Tie 1: `I` -/

/-- **Deliverable (Crux 4).** `simplexInt (sq (ofPoly F)) = Ical F` for a general
`F`: expanding `simplexInt` of `(ofPoly F)²` gives `Σ_{α,β} fα fβ DInt(α+β)`,
which is C1's definition of `Ical F`. -/
theorem simplexInt_sq_ofPoly_eq_Ical (F : Poly) :
    simplexInt (sq (ofPoly F)) = Ical F := by
  rw [ofPoly, simplexInt_sq_map, Ical]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  change a.2 * b.2 * DInt' (a.1 + b.1) (0 + 0) = a.2 * b.2 * DInt (a.1 + b.1)
  rw [Nat.add_zero, DInt'_zero]

/-! ## Tie 2: `J⁽ᵐ⁾` and the `contractAt`→`JD` budget bookkeeping -/

/-- **Crux of the budget bookkeeping.** The `simplexInt` term of a `contractAt`
pair `(α, β)` equals `fα fβ · JD α β m`. On the 4-variable slice the removed
coordinate contributes the `(αₘ+1)(βₘ+1)` divisor, the budget power
`(αₘ+1)+(βₘ+1) = αₘ+βₘ+2`, and shifts the Dirichlet denominator to
`4 + (αₘ+βₘ+2) + Σ_{i≠m}(αᵢ+βᵢ) = 6 + Σᵢ(αᵢ+βᵢ)` — matching `JD`. -/
lemma contract_term (α β : Fin 5 → ℕ) (m : Fin 5) (fα fβ : ℚ) :
    fα / ((α m + 1 : ℕ) : ℚ) * (fβ / ((β m + 1 : ℕ) : ℚ)) *
      DInt' (Fin.removeNth m α + Fin.removeNth m β) ((α m + 1) + (β m + 1))
    = fα * fβ * JD α β m := by
  -- Split the `Fin 5` product/sum over the removed coordinate `m`.
  have hprod5 : (∏ i : Fin 5, (α i + β i)!)
      = (α m + β m)! * ∏ i : Fin 4, (α (m.succAbove i) + β (m.succAbove i))! :=
    Fin.prod_univ_succAbove (fun j => (α j + β j)!) m
  have hsum5 : (∑ i : Fin 5, (α i + β i))
      = (α m + β m) + ∑ i : Fin 4, (α (m.succAbove i) + β (m.succAbove i)) :=
    Fin.sum_univ_succAbove (fun j => α j + β j) m
  -- The `removeNth` sums/products are the `succAbove` sums/products.
  have hQ : (∏ i : Fin 4, ((Fin.removeNth m α + Fin.removeNth m β) i)!)
      = ∏ i : Fin 4, (α (m.succAbove i) + β (m.succAbove i))! := by
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Pi.add_apply, Fin.removeNth_apply, Fin.removeNth_apply]
  have hS : (∑ i : Fin 4, (Fin.removeNth m α + Fin.removeNth m β) i)
      = ∑ i : Fin 4, (α (m.succAbove i) + β (m.succAbove i)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.add_apply, Fin.removeNth_apply, Fin.removeNth_apply]
  -- Budget power and Dirichlet denominator rewrites.
  have harg : (α m + 1) + (β m + 1) = α m + β m + 2 := by omega
  have hden : 4 + (α m + β m + 2)
        + (∑ i : Fin 4, (α (m.succAbove i) + β (m.succAbove i)))
      = 6 + ∑ i : Fin 5, (α i + β i) := by
    rw [hsum5]; omega
  -- The factorial identity `(c+2)! = c!·(c+1)(c+2)` and the numerator collect.
  have efac : (α m + β m + 2)! = (α m + β m)! * ((α m + β m + 1) * (α m + β m + 2)) := by
    have e1 : α m + β m + 2 = (α m + β m + 1) + 1 := by omega
    rw [e1, Nat.factorial_succ, Nat.factorial_succ]; ring
  have hnumN : (∏ i : Fin 4, (α (m.succAbove i) + β (m.succAbove i))!) * (α m + β m + 2)!
      = (∏ i : Fin 5, (α i + β i)!) * ((α m + β m + 1) * (α m + β m + 2)) := by
    rw [efac, hprod5]; ring
  -- The value of the budget Dirichlet integral on the 4-slice.
  have hval : DInt' (Fin.removeNth m α + Fin.removeNth m β) ((α m + 1) + (β m + 1))
      = (((∏ i : Fin 5, (α i + β i)!) * ((α m + β m + 1) * (α m + β m + 2)) : ℕ) : ℚ)
        / (((6 + ∑ i : Fin 5, (α i + β i))! : ℕ) : ℚ) := by
    unfold DInt'
    rw [hQ, hS, harg, hnumN, hden]
  -- Close by field arithmetic against the erase-free form of `JD`.
  have h1 : ((α m : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((β m : ℚ) + 1) ≠ 0 := by positivity
  have h3 : (((6 + ∑ i : Fin 5, (α i + β i))! : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  rw [JD_eq, hval]
  push_cast
  field_simp

/-- **Deliverable (Crux 4).** `simplexInt (sq (contractAt m F)) = Jcal m F` for a
general `F`: expanding `simplexInt` of `(contractAt m F)²` collects, pair by pair,
into `Σ_{α,β} fα fβ JD α β m`, which is C1's definition of `Jcal m F`. -/
theorem simplexInt_sq_contractAt_eq_Jcal (m : Fin 5) (F : Poly) :
    simplexInt (sq (contractAt m F)) = Jcal m F := by
  rw [contractAt, simplexInt_sq_map, Jcal]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun b _ => ?_)
  change a.2 / ((a.1 m + 1 : ℕ) : ℚ) * (b.2 / ((b.1 m + 1 : ℕ) : ℚ)) *
      DInt' (Fin.removeNth m a.1 + Fin.removeNth m b.1) ((a.1 m + 1) + (b.1 m + 1))
    = a.2 * b.2 * JD a.1 b.1 m
  exact contract_term a.1 b.1 m a.2 b.2

end Salt.Twelve
