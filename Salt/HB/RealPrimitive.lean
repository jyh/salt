/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.QuadCharSum
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Real primitive characters: the composite two-forms bound (node WEIL-TRIO-W4)

Heath-Brown's *Prime Twins and Siegel Zeros* (Proc. LMS (3) **47** (1983) 193–224) states at
p.217, without proof, that for a real primitive character `χ (mod q)`

`∑_{t mod q} χ (u t + u') χ (v t + v') ≪ (q, u v' - v u')`,

and at p.216 that a primitive character sums to zero over any congruence class to a proper
divisor of its modulus.  This file supplies both, together with the periodicity descent that
lets a full-length sum be traded for a sum of length `q / Δ`.

The prime case is `Salt/HB/QuadCharSum.lean`; here the `2`-power cases are decided outright
and the composite case is assembled by the Chinese Remainder Theorem.  The constant is `1`,
not `≪`: no `2 ^ ω(q)` appears anywhere.

## Main results

* `chi4_sum_two_forms_le_gcd`, `chi8_sum_two_forms_le_gcd`, `chi8'_sum_two_forms_le_gcd`
  (node W4-b) — the `2`-power cases `mod 4` and `mod 8`, in gcd form, by `decide`.
* `sum_range_nsmul_of_periodic` / `sum_range_eq_nsmul_of_dvd_of_periodic` (node W4-c′) — the
  `Δ`-fold periodicity descent `∑_{t < q} f t = Δ • ∑_{t < q/Δ} f t`.
* `HasTwoFormGcdBound` and `HasTwoFormGcdBound.mul` (node W4-c) — the two-forms property at
  constant one, and its multiplicativity across a coprime splitting of the modulus.
* `hasTwoFormGcdBound_prodPrimes` — the odd squarefree assembly.
* `sum_two_forms_le_gcd_of_split` (node W4-c) — **the exit theorem**: for `q = 2 ^ a * m`
  with `a ∈ {0, 2, 3}` and `m` odd squarefree, and `χ` presented as the CRT product of a
  `2`-part character from `{1, χ₄, χ₈, χ₈'}` with the quadratic characters at the odd primes
  of `m`, `|∑_{t mod q} χ (u t + u') χ (v t + v')| ≤ (q, u v' - v u')`.
* `sum_class_eq_zero_of_isPrimitive` (node W4-d) — the class-restricted vanishing: for `χ`
  primitive mod `q` and `f ∣ q`, `f ≠ q`, `∑_{b ≡ c (f)} χ b = 0`.

## Value ring

Everything is `ℤ`-valued (`MulChar _ ℤ`), matching the landed `QuadCharSum`.  A consumer
needing `ℂ` composes with `MulChar.ringHomComp (Int.castRingHom ℂ)` — a one-liner that
commutes with the finite sums and with `|·|` (`Int.cast_abs`).

## The structure hypothesis

`sum_two_forms_le_gcd_of_split` takes the decomposition of `χ` as a *hypothesis*, in the
exact form `∀ n, χ n = χ₂ (cast n) * ∏ p ∈ m.primeFactors, quadraticChar (ZMod p) (cast n)`.
That χ *has* such a decomposition, for `χ` real and primitive, is node W4-a (a separate
sub-wave); nothing here depends on it, so this file lands independently.
-/

namespace Salt.HB

open Finset

/-! ### W4-b: the `2`-power cases, in gcd form -/

section TwoPower

/-- **W4-b (mod 4).**  For the primitive quadratic character `χ₄` on `ZMod 4` and arbitrary
coefficients, `|∑_{t mod 4} χ₄ (u t + u') χ₄ (v t + v')| ≤ (4, u v' - v u')`.

A finite decision problem: `4 ^ 4 = 256` coefficient quadruples, each a sum of four terms.
The bound is attained (e.g. `u = v = 1`, `u' = 0`, `v' = 2` gives `-2` at gcd `2`), and the
sum vanishes whenever the determinant is a unit. -/
theorem chi4_sum_two_forms_le_gcd (u u' v v' : ZMod 4) :
    |∑ t : ZMod 4, ZMod.χ₄ (u * t + u') * ZMod.χ₄ (v * t + v')|
      ≤ (Nat.gcd 4 (u * v' - v * u').val : ℤ) := by
  revert u u' v v'
  decide

/-- **W4-b (mod 8, first character).**  For the primitive quadratic character `χ₈` on
`ZMod 8`, `|∑_{t mod 8} χ₈ (u t + u') χ₈ (v t + v')| ≤ (8, u v' - v u')`.
`8 ^ 4 = 4096` coefficient quadruples; decided. -/
theorem chi8_sum_two_forms_le_gcd (u u' v v' : ZMod 8) :
    |∑ t : ZMod 8, ZMod.χ₈ (u * t + u') * ZMod.χ₈ (v * t + v')|
      ≤ (Nat.gcd 8 (u * v' - v * u').val : ℤ) := by
  revert u u' v v'
  decide

/-- **W4-b (mod 8, second character).**  For the primitive quadratic character `χ₈'` on
`ZMod 8`, `|∑_{t mod 8} χ₈' (u t + u') χ₈' (v t + v')| ≤ (8, u v' - v u')`. -/
theorem chi8'_sum_two_forms_le_gcd (u u' v v' : ZMod 8) :
    |∑ t : ZMod 8, ZMod.χ₈' (u * t + u') * ZMod.χ₈' (v * t + v')|
      ≤ (Nat.gcd 8 (u * v' - v * u').val : ℤ) := by
  revert u u' v v'
  decide

end TwoPower

/-! ### W4-c′: the `Δ`-fold periodicity descent -/

section Periodicity

variable {M : Type*} [AddCommMonoid M]

/-- **W4-c′ (the raw form).**  If `f : ℕ → M` has period `r`, then summing it over a block of
length `Δ * r` is `Δ` copies of the sum over one period. -/
theorem sum_range_nsmul_of_periodic (f : ℕ → M) (r Δ : ℕ) (hper : ∀ t, f (t + r) = f t) :
    ∑ t ∈ range (Δ * r), f t = Δ • ∑ t ∈ range r, f t := by
  have hshift : ∀ k t : ℕ, f (k * r + t) = f t := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ m ihm =>
        intro t
        have hrw : (m + 1) * r + t = m * r + t + r := by ring
        rw [hrw, hper, ihm]
  induction Δ with
  | zero => simp
  | succ n ih =>
      have hrw : (n + 1) * r = n * r + r := by ring
      rw [hrw, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => hshift n i

/-- **W4-c′ (the divisor form).**  For `Δ ∣ q` and `f` of period `q / Δ`,
`∑_{t < q} f t = Δ • ∑_{t < q / Δ} f t`.

This is the step that passes from a full-length sum modulo `q` to the `q / Δ` object: N7
quotes it to replace the length-`q` completion by its length-`q/Δ` core. -/
theorem sum_range_eq_nsmul_of_dvd_of_periodic (f : ℕ → M) {q Δ : ℕ} (hΔ : Δ ∣ q)
    (hper : ∀ t, f (t + q / Δ) = f t) :
    ∑ t ∈ range q, f t = Δ • ∑ t ∈ range (q / Δ), f t := by
  obtain rfl | hΔ0 := Nat.eq_zero_or_pos Δ
  · obtain ⟨r, rfl⟩ := hΔ; simp
  · obtain ⟨r, rfl⟩ := hΔ
    have hr : Δ * r / Δ = r := Nat.mul_div_cancel_left r hΔ0
    rw [hr] at hper ⊢
    exact sum_range_nsmul_of_periodic f r Δ hper

end Periodicity

/-! ### W4-c: the composite two-forms bound, at constant one -/

section Composite

/-- **The two-forms property at the sharp constant `1`.**  `HasTwoFormGcdBound q f` says that
for every pair of linear forms over `ZMod q`,
`|∑_{t mod q} f (u t + u') f (v t + v')| ≤ (q, u v' - v u')`.

The sum runs over `Finset.range q` — one term per residue class — so that the statement carries
no `NeZero q` instance; that keeps the modulus a *plain* natural number, which is what makes the
induction over the prime factorization (`hasTwoFormGcdBound_jacobiChar`) go through without
dependent-type transport.  `sum_two_forms_range_eq_univ` converts to the `∑ t : ZMod q` form. -/
def HasTwoFormGcdBound (q : ℕ) (f : ZMod q → ℤ) : Prop :=
  ∀ u u' v v' : ZMod q,
    |∑ t ∈ range q, f (u * (t : ZMod q) + u') * f (v * (t : ZMod q) + v')|
      ≤ (Nat.gcd q (u * v' - v * u').val : ℤ)

/-- Summing a function of `ZMod q` over `Finset.range q` (via `Nat.cast`) is the same as
summing it over `ZMod q`. -/
theorem sum_range_natCast_eq_sum_univ {q : ℕ} [NeZero q] (g : ZMod q → ℤ) :
    ∑ t ∈ range q, g (t : ZMod q) = ∑ t : ZMod q, g t := by
  classical
  have himg : (range q).image (fun t : ℕ => (t : ZMod q)) = Finset.univ := by
    refine Finset.eq_univ_iff_forall.mpr fun x => ?_
    refine Finset.mem_image.mpr ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ?_⟩
    simp
  have hinj : ∀ s ∈ range q, ∀ t ∈ range q, (s : ZMod q) = (t : ZMod q) → s = t := by
    intro s hs t ht hst
    rw [← ZMod.val_cast_of_lt (Finset.mem_range.mp hs), ← ZMod.val_cast_of_lt
      (Finset.mem_range.mp ht), hst]
  rw [← himg, Finset.sum_image hinj]

/-- The `range`-form of the two-forms sum equals the `ZMod`-form. -/
theorem sum_two_forms_range_eq_univ {q : ℕ} [NeZero q] (f : ZMod q → ℤ) (u u' v v' : ZMod q) :
    ∑ t ∈ range q, f (u * (t : ZMod q) + u') * f (v * (t : ZMod q) + v')
      = ∑ t : ZMod q, f (u * t + u') * f (v * t + v') :=
  sum_range_natCast_eq_sum_univ (fun x => f (u * x + u') * f (v * x + v'))

/-- Reducing a residue modulo a divisor does not change its gcd with that divisor. -/
theorem gcd_val_castHom {q q' : ℕ} [NeZero q] [NeZero q'] (h : q' ∣ q) (x : ZMod q) :
    Nat.gcd q' (ZMod.castHom h (ZMod q') x).val = Nat.gcd q' x.val := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val x, ZMod.val_natCast,
    Nat.gcd_comm q' (x.val % q'), ← Nat.gcd_rec]

/-- **The CRT engine (node W4-c).**  If `f` factors as a product of a `q₁`-part and a
`q₂`-part through the Chinese Remainder Theorem, and each part has the two-forms property at
constant one, then so does `f` at the modulus `q₁ q₂`.

This is where the sharp constant pays for itself: the two bounds multiply to
`(q₁, det) · (q₂, det) = (q₁ q₂, det)` exactly, with no `2 ^ ω` residue. -/
theorem HasTwoFormGcdBound.mul {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] (hcop : Nat.Coprime q₁ q₂)
    {f₁ : ZMod q₁ → ℤ} {f₂ : ZMod q₂ → ℤ} {f : ZMod (q₁ * q₂) → ℤ}
    (hf : ∀ n : ZMod (q₁ * q₂), f n = f₁ (ZMod.cast n) * f₂ (ZMod.cast n))
    (h₁ : HasTwoFormGcdBound q₁ f₁) (h₂ : HasTwoFormGcdBound q₂ f₂) :
    HasTwoFormGcdBound (q₁ * q₂) f := by
  haveI : NeZero (q₁ * q₂) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q₂)⟩
  intro u u' v v'
  set π₁ : ZMod (q₁ * q₂) →+* ZMod q₁ := ZMod.castHom (dvd_mul_right q₁ q₂) (ZMod q₁) with hπ₁
  set π₂ : ZMod (q₁ * q₂) →+* ZMod q₂ := ZMod.castHom (dvd_mul_left q₂ q₁) (ZMod q₂) with hπ₂
  -- the CRT equivalence, in the form `s ↦ (π₁ s, π₂ s)`
  let E : ZMod (q₁ * q₂) ≃ ZMod q₁ × ZMod q₂ := (ZMod.chineseRemainder hcop).toEquiv
  have hE : ∀ s, E s = (π₁ s, π₂ s) := by
    intro s
    have h : ((ZMod.chineseRemainder hcop : ZMod (q₁ * q₂) ≃+* ZMod q₁ × ZMod q₂) :
        ZMod (q₁ * q₂) →+* ZMod q₁ × ZMod q₂) = RingHom.prod π₁ π₂ := RingHom.ext_zmod _ _
    exact congrArg (fun r : ZMod (q₁ * q₂) →+* ZMod q₁ × ZMod q₂ => r s) h
  -- split the sum
  have hsplit : ∑ t ∈ range (q₁ * q₂), f (u * (t : ZMod (q₁ * q₂)) + u')
        * f (v * (t : ZMod (q₁ * q₂)) + v')
      = (∑ t₁ : ZMod q₁, f₁ (π₁ u * t₁ + π₁ u') * f₁ (π₁ v * t₁ + π₁ v'))
        * (∑ t₂ : ZMod q₂, f₂ (π₂ u * t₂ + π₂ u') * f₂ (π₂ v * t₂ + π₂ v')) := by
    rw [sum_two_forms_range_eq_univ]
    have hb : ∑ s : ZMod (q₁ * q₂), f (u * s + u') * f (v * s + v')
        = ∑ p : ZMod q₁ × ZMod q₂,
            f₁ (π₁ u * p.1 + π₁ u') * f₁ (π₁ v * p.1 + π₁ v')
              * (f₂ (π₂ u * p.2 + π₂ u') * f₂ (π₂ v * p.2 + π₂ v')) := by
      refine Fintype.sum_bijective E E.bijective _ _ ?_
      intro s
      rw [hf (u * s + u'), hf (v * s + v'), hE s]
      simp only [← ZMod.castHom_apply (h := dvd_mul_right q₁ q₂),
        ← ZMod.castHom_apply (h := dvd_mul_left q₂ q₁), map_add, map_mul, ← hπ₁, ← hπ₂]
      ring
    rw [hb, Fintype.sum_prod_type, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  rw [hsplit, abs_mul]
  -- the two per-factor determinants are the reductions of the global one
  have hdet₁ : π₁ u * π₁ v' - π₁ v * π₁ u' = π₁ (u * v' - v * u') := by
    simp only [map_sub, map_mul]
  have hdet₂ : π₂ u * π₂ v' - π₂ v * π₂ u' = π₂ (u * v' - v * u') := by
    simp only [map_sub, map_mul]
  set D : ℕ := (u * v' - v * u').val with hD
  have hb₁ : |∑ t₁ : ZMod q₁, f₁ (π₁ u * t₁ + π₁ u') * f₁ (π₁ v * t₁ + π₁ v')|
      ≤ (Nat.gcd q₁ D : ℤ) := by
    have := h₁ (π₁ u) (π₁ u') (π₁ v) (π₁ v')
    rw [sum_two_forms_range_eq_univ, hdet₁, hπ₁, gcd_val_castHom] at this
    exact this
  have hb₂ : |∑ t₂ : ZMod q₂, f₂ (π₂ u * t₂ + π₂ u') * f₂ (π₂ v * t₂ + π₂ v')|
      ≤ (Nat.gcd q₂ D : ℤ) := by
    have := h₂ (π₂ u) (π₂ u') (π₂ v) (π₂ v')
    rw [sum_two_forms_range_eq_univ, hdet₂, hπ₂, gcd_val_castHom] at this
    exact this
  -- `(q₁, D) · (q₂, D) ≤ (q₁ q₂, D)`, by coprimality
  have hgcd : Nat.gcd q₁ D * Nat.gcd q₂ D ≤ Nat.gcd (q₁ * q₂) D := by
    have hcopg : Nat.Coprime (Nat.gcd q₁ D) (Nat.gcd q₂ D) :=
      (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left q₁ D) hcop).coprime_dvd_right
        (Nat.gcd_dvd_left q₂ D)
    refine Nat.le_of_dvd ?_ (Nat.dvd_gcd
      (Nat.mul_dvd_mul (Nat.gcd_dvd_left q₁ D) (Nat.gcd_dvd_left q₂ D))
      (hcopg.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_right q₁ D) (Nat.gcd_dvd_right q₂ D)))
    exact Nat.pos_of_ne_zero fun h =>
      (NeZero.ne (q₁ * q₂)) (Nat.eq_zero_of_gcd_eq_zero_left h)
  calc |∑ t₁ : ZMod q₁, f₁ (π₁ u * t₁ + π₁ u') * f₁ (π₁ v * t₁ + π₁ v')|
        * |∑ t₂ : ZMod q₂, f₂ (π₂ u * t₂ + π₂ u') * f₂ (π₂ v * t₂ + π₂ v')|
      ≤ (Nat.gcd q₁ D : ℤ) * (Nat.gcd q₂ D : ℤ) :=
        mul_le_mul hb₁ hb₂ (abs_nonneg _) (Int.natCast_nonneg _)
    _ ≤ (Nat.gcd (q₁ * q₂) D : ℤ) := by exact_mod_cast hgcd

/-! #### The admissible `2`-parts and the odd part -/

/-- The `2`-part at exponent `0`: a character mod `1` with `|χ 0| ≤ 1`. -/
theorem hasTwoFormGcdBound_of_modulus_one (f : ZMod 1 → ℤ) (hf : |f 0| ≤ 1) :
    HasTwoFormGcdBound 1 f := by
  intro u u' v v'
  have h0 : ∀ x : ZMod 1, x = 0 := fun x => Subsingleton.elim _ _
  simp only [Finset.sum_range_one, h0 (u * ((0 : ℕ) : ZMod 1) + u'),
    h0 (v * ((0 : ℕ) : ZMod 1) + v'), Nat.gcd_one_left, Nat.cast_one, abs_mul]
  exact mul_le_one₀ hf (abs_nonneg _) hf

/-- **W4-b as a `HasTwoFormGcdBound` (mod 4).**  Note `2 ^ 2 = 4`. -/
theorem hasTwoFormGcdBound_chi4 : HasTwoFormGcdBound 4 (fun x => ZMod.χ₄ x) := by
  intro u u' v v'
  rw [sum_two_forms_range_eq_univ]
  exact chi4_sum_two_forms_le_gcd u u' v v'

/-- **W4-b as a `HasTwoFormGcdBound` (mod 8, `χ₈`).**  Note `2 ^ 3 = 8`. -/
theorem hasTwoFormGcdBound_chi8 : HasTwoFormGcdBound 8 (fun x => ZMod.χ₈ x) := by
  intro u u' v v'
  rw [sum_two_forms_range_eq_univ]
  exact chi8_sum_two_forms_le_gcd u u' v v'

/-- **W4-b as a `HasTwoFormGcdBound` (mod 8, `χ₈'`).** -/
theorem hasTwoFormGcdBound_chi8' : HasTwoFormGcdBound 8 (fun x => ZMod.χ₈' x) := by
  intro u u' v v'
  rw [sum_two_forms_range_eq_univ]
  exact chi8'_sum_two_forms_le_gcd u u' v v'

/-- **The odd part.**  For an odd squarefree modulus `m` the real primitive character is the
Jacobi symbol `J(· | m)`, which *by definition* (`jacobiSym`) is the product of the Legendre
symbols — i.e. of the quadratic characters `quadraticChar (ZMod p)` — over the primes `p ∣ m`.
This is the "CRT product of a `quadraticChar` per odd prime" of the design freeze, packaged as
a function on `ZMod m` so that it can be fed to `HasTwoFormGcdBound`. -/
def jacobiChar (m : ℕ) (n : ZMod m) : ℤ := jacobiSym (n.val : ℤ) m

/-- At a prime `p`, `jacobiChar p` *is* the quadratic (Legendre) character on `ZMod p`. -/
theorem jacobiChar_prime {p : ℕ} [Fact p.Prime] (x : ZMod p) :
    jacobiChar p x = quadraticChar (ZMod p) x := by
  rw [jacobiChar, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym]
  congr 1
  push_cast
  simp

/-- **The per-odd-prime input.**  `jacobiChar p` has the two-forms property at constant one:
the sharp `QuadCharSum` bound when `p ∤ det`, the trivial bound when `p ∣ det`. -/
theorem hasTwoFormGcdBound_jacobiChar_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    HasTwoFormGcdBound p (jacobiChar p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  intro u u' v v'
  rw [sum_two_forms_range_eq_univ]
  simp only [jacobiChar_prime]
  by_cases hdet : u * v' - v * u' = 0
  · have hval : (u * v' - v * u').val = 0 := by rw [hdet]; simp
    rw [hval, Nat.gcd_zero_right]
    exact legendre_sum_two_forms_trivial u u' v v'
  · have hone : 1 ≤ Nat.gcd p (u * v' - v * u').val := by
      rcases Nat.eq_zero_or_pos (Nat.gcd p (u * v' - v * u').val) with h | h
      · exact absurd (Nat.eq_zero_of_gcd_eq_zero_left h) hp.pos.ne'
      · exact h
    refine le_trans (legendre_sum_two_forms_bound_one hp2 ?_) (by exact_mod_cast hone)
    rw [show u * v' - u' * v = u * v' - v * u' by ring]
    exact hdet

/-- **The odd squarefree assembly (node W4-c).**  For odd squarefree `m`, the Jacobi character
`J(· | m)` has the two-forms property at constant one.

Induction over the prime factorization (`Nat.recOnPosPrimePosCoprime`): squarefreeness collapses
the prime-power case to a single prime, where `hasTwoFormGcdBound_jacobiChar_prime` applies, and
the coprime step is `HasTwoFormGcdBound.mul` fed by the multiplicativity of `jacobiSym` in its
modulus. -/
theorem hasTwoFormGcdBound_jacobiChar : ∀ m : ℕ, Squarefree m → ¬ 2 ∣ m →
    HasTwoFormGcdBound m (jacobiChar m) := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero =>
      intro _ _ u u' v v'
      simp
  | one =>
      intro _ _ u u' v v'
      simp [jacobiChar]
  | prime_pow p n hp hn =>
      intro hsq hodd
      have hn1 : n = 1 := ((Nat.squarefree_pow_iff hp.ne_one hn.ne').mp hsq).2
      subst hn1
      rw [pow_one] at hodd ⊢
      exact hasTwoFormGcdBound_jacobiChar_prime hp (by rintro rfl; exact hodd dvd_rfl)
  | coprime a b ha hb hcop iha ihb =>
      intro hsq hodd
      haveI : NeZero a := ⟨by omega⟩
      haveI : NeZero b := ⟨by omega⟩
      have hsqa : Squarefree a := Squarefree.squarefree_of_dvd (dvd_mul_right a b) hsq
      have hsqb : Squarefree b := Squarefree.squarefree_of_dvd (dvd_mul_left b a) hsq
      have hodda : ¬ 2 ∣ a := fun h => hodd (h.mul_right b)
      have hoddb : ¬ 2 ∣ b := fun h => hodd (h.mul_left a)
      refine HasTwoFormGcdBound.mul hcop ?_ (iha hsqa hodda) (ihb hsqb hoddb)
      intro n
      have hcast₁ : ((ZMod.cast n : ZMod a).val : ℤ) = (n.val : ℤ) % (a : ℤ) := by
        rw [← ZMod.natCast_val n, ZMod.val_natCast]
        push_cast
        ring
      have hcast₂ : ((ZMod.cast n : ZMod b).val : ℤ) = (n.val : ℤ) % (b : ℤ) := by
        rw [← ZMod.natCast_val n, ZMod.val_natCast]
        push_cast
        ring
      rw [jacobiChar, jacobiChar, jacobiChar, hcast₁, hcast₂, ← jacobiSym.mod_left,
        ← jacobiSym.mod_left, jacobiSym.mul_right]

/-- **W4-c, the exit theorem (Heath-Brown p.217, composite case).**  Let `q = e · m` with `e`
the `2`-part (coprime to `m`), `m` odd squarefree, and let `χ : ZMod q → ℤ` be the CRT product
of an admissible `2`-part character `χ₂` and the Jacobi character `J(· | m)`.  Then

`|∑_{t mod q} χ (u t + u') χ (v t + v')| ≤ (q, u v' - v u')`

for **arbitrary** coefficients — constant `1`, no `2 ^ ω(q)`.

The structure is a *hypothesis*: the admissible `2`-parts are `e = 1` (trivial character,
`2 ^ 0`), `e = 4` with `χ₄` (`2 ^ 2`), and `e = 8` with `χ₈` or `χ₈'` (`2 ^ 3`), discharged by
`hasTwoFormGcdBound_of_modulus_one`, `hasTwoFormGcdBound_chi4`, `hasTwoFormGcdBound_chi8`,
`hasTwoFormGcdBound_chi8'` — that is exactly the exponent set `a ∈ {0, 2, 3}` of the structure
lemma.  That a real primitive `χ (mod q)` *admits* such a decomposition is node W4-a.

N7 quotes this as: the p.217 composite two-forms bound.  A `ℂ`-valued consumer composes with
`MulChar.ringHomComp (Int.castRingHom ℂ)`; a `MulChar (ZMod q) ℤ` is fed in as `⇑χ`. -/
theorem sum_two_forms_le_gcd_of_split {e m : ℕ} [NeZero e] [NeZero m]
    (hcop : Nat.Coprime e m) (hmsq : Squarefree m) (hmodd : ¬ 2 ∣ m)
    {χ : ZMod (e * m) → ℤ} {χ₂ : ZMod e → ℤ} (h₂ : HasTwoFormGcdBound e χ₂)
    (hχ : ∀ n : ZMod (e * m), χ n = χ₂ (ZMod.cast n) * jacobiChar m (ZMod.cast n))
    (u u' v v' : ZMod (e * m)) :
    |∑ t : ZMod (e * m), χ (u * t + u') * χ (v * t + v')|
      ≤ (Nat.gcd (e * m) (u * v' - v * u').val : ℤ) := by
  haveI : NeZero (e * m) := ⟨Nat.mul_ne_zero (NeZero.ne e) (NeZero.ne m)⟩
  have h := HasTwoFormGcdBound.mul hcop hχ h₂ (hasTwoFormGcdBound_jacobiChar m hmsq hmodd)
    u u' v v'
  rwa [sum_two_forms_range_eq_univ] at h

end Composite

/-! ### W4-d: the class-restricted vanishing -/

section ClassVanishing

/-- **W4-d (Heath-Brown p.216).**  Let `χ` be a primitive character mod `q` and let `f` be a
*proper* divisor of `q`.  Then `χ` sums to zero over every residue class mod `f`:

`∑_{b mod q, b ≡ c (f)} χ b = 0`,

for an arbitrary residue `c` — **no coprimality hypothesis on `c`**.

Proof: primitivity says `χ` does not factor through `f`, so — via
`DirichletCharacter.factorsThrough_iff_ker_unitsMap` — some unit `a ≡ 1 (mod f)` has `χ a ≠ 1`.
Multiplication by `a` permutes `ZMod q` and fixes the class `{b ≡ c (f)}` setwise, so the sum
`S` satisfies `χ a · S = S`; since the value ring is a domain and `χ a ≠ 1`, `S = 0`.

N7 quotes this as: the p.216 vanishing of a primitive character over a congruence class to a
proper divisor of the modulus. -/
theorem sum_class_eq_zero_of_isPrimitive {R : Type*} [CommRing R] [IsDomain R] {q : ℕ}
    [NeZero q] {χ : DirichletCharacter R q} (hprim : χ.IsPrimitive) {f : ℕ} (hf : f ∣ q)
    (hfq : f ≠ q) (c : ZMod f) :
    ∑ b ∈ Finset.univ.filter (fun b : ZMod q => ZMod.castHom hf (ZMod f) b = c), χ b = 0 := by
  classical
  -- primitivity: `χ` does not factor through the proper divisor `f`
  have hnft : ¬ χ.FactorsThrough f := by
    intro hft
    have hle : χ.conductor ≤ f := Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff χ).mpr hft)
    rw [DirichletCharacter.isPrimitive_def] at hprim
    rw [hprim] at hle
    exact hfq (Nat.le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hf) hle)
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hf] at hnft
  obtain ⟨x, hx1, hx2⟩ := SetLike.not_le_iff_exists.mp hnft
  -- the twisting unit: `a ≡ 1 (mod f)` with `χ a ≠ 1`
  have hcast : ZMod.castHom hf (ZMod f) (x : ZMod q) = 1 := by
    have h2 := congrArg Units.val (MonoidHom.mem_ker.mp hx1)
    rwa [ZMod.unitsMap_val, Units.val_one, ← ZMod.castHom_apply (h := hf)] at h2
  have hchi : χ (x : ZMod q) ≠ 1 := by
    intro h
    exact hx2 (MonoidHom.mem_ker.mpr (Units.ext (by rw [MulChar.coe_toUnitHom, h, Units.val_one])))
  -- multiplication by the unit permutes the class
  let E : ZMod q ≃ ZMod q :=
    { toFun := fun b => (x : ZMod q) * b
      invFun := fun b => ((x⁻¹ : (ZMod q)ˣ) : ZMod q) * b
      left_inv := fun b => by simp [← mul_assoc]
      right_inv := fun b => by simp [← mul_assoc] }
  set S : Finset (ZMod q) :=
    Finset.univ.filter (fun b : ZMod q => ZMod.castHom hf (ZMod f) b = c) with hS
  have hmem : ∀ b : ZMod q, b ∈ S ↔ E b ∈ S := by
    intro b
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    change _ ↔ ZMod.castHom hf (ZMod f) ((x : ZMod q) * b) = c
    rw [map_mul, hcast, one_mul]
  have hreindex : ∑ b ∈ S, χ ((x : ZMod q) * b) = ∑ b ∈ S, χ b :=
    Finset.sum_equiv E hmem (fun _ _ => rfl)
  have hfactor : ∑ b ∈ S, χ ((x : ZMod q) * b) = χ (x : ZMod q) * ∑ b ∈ S, χ b := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => map_mul χ _ b
  have hzero : (χ (x : ZMod q) - 1) * (∑ b ∈ S, χ b) = 0 := by
    rw [sub_mul, one_mul, ← hfactor, hreindex, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h) hchi
  · exact h

end ClassVanishing

end Salt.HB
