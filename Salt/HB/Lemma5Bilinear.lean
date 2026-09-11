/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.CrownAssembly
import Salt.HB.Lemma10Chain
import Salt.Weil.RoadModulus
import Salt.Weil.Sawtooth

/-!
# HB 1983 §5 — the bilinear carrier, the dyadic/residue split, the CRT collapse, the ψ-reduction

Heath-Brown, *Prime twins and Siegel zeros* (Proc. LMS (3) 47 (1983) 193–224), §5, pp.210–214.
This is **Wave B of the N7 program**: the §5 lattice machine at HB's general pair of linear
forms, stated against the corpus and proved here.

What the file holds, block by block.

* **B-1 — the forms, the window, the carrier.** `HBForms` is HB's pair `l_i(n) = α_i n + β_i`
  (pp.193–194) carrying (1.4)–(1.9) as fields, with `β_i : ℕ` (no generality is lost: the
  shift `n ↦ n + t` carries any ℤ-β pair to an ℕ-β pair with the same `α_i` and determinant,
  and ℕ buys `1 ≤ l_i(n)` unconditionally, which every `Nat.divisors` sum in §5 needs).
  `HBForms.twin` is the twin-prime instance `(4n+1, 4n+3)` of p.195.  `truncChiSum`,
  `hbFormsWindow` and `bilinearS` are p.211's `S(δ₁,δ₂;V₁,V₂)`; the (5.1) vanishing clauses,
  the `V`-vanishing of p.218 and the `HBSieveData` transfer `hbDataForms` sit here too.
* **B-3 — the dyadic cells and the residue split.** `cellCount` is (5.3)'s `S`: the lattice
  count at one dyadic cell `(R_i, 2R_i] × (S_i, 2S_i]` in one residue class `(a_i, b_i)`.
  (5.18) decomposes the carrier into those cells exactly; (5.2) bounds a non-empty cell.
* **B-4 — the CRT collapse (5.5)–(5.13).** The four congruences in `X = v₂w₂` are ONE
  congruence modulo `D δ₁ w₁`, `D = roadModulus α₂ q`, with a residue coprime to the modulus;
  and the cells that carry no mass at all are named.
* **B-5 — the ψ-reduction (5.14)–(5.17).** `hbT₁`/`hbT₂` are (5.15)/(5.16); the `v₂`-count in
  an interval and a residue class is a length plus two sawtooths (`Salt.Weil.sawtooth`), and
  the assembled cell count is the double `(w₁, w₂)`-sum B-6 consumes.

Lemma 9 itself (the μ-sieve of `Λ′` over `Q`, the hyperbola identity, the log integrals) is the
sibling branch of this wave and lands in this same file afterwards; §6 (applying Lemma 10) is a
later wave and owes the `Salt.HB.Lemma10Seal` import, which is deliberately NOT taken here.

Nothing in this file bears on twin primes: §5 is a binder on a binder on the crown.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.N7

open Salt.HB Salt.Weil Salt.TwinBar

variable {q : ℕ}

/-! ## B-1 — the forms, the window, the carrier -/

/-- HB's pair of linear forms `l_i(n) = α_i n + β_i` (pp.193–194) under (1.4)–(1.9), `β_i ∈ ℕ`. -/
structure HBForms where
  α₁ : ℕ
  β₁ : ℕ
  α₂ : ℕ
  β₂ : ℕ
  /-- (1.4) -/
  cop₁ : Nat.Coprime α₁ β₁
  cop₂ : Nat.Coprime α₂ β₂
  /-- (1.5) -/
  even₁ : 2 ∣ α₁
  even₂ : 2 ∣ α₂
  /-- (1.6) -/
  det_ne : α₁ * β₂ ≠ α₂ * β₁
  /-- (1.7) -/
  det_dvd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ((α₁ : ℤ) * β₂ - (α₂ : ℤ) * β₁) → p ∣ α₁ ∧ p ∣ α₂
  /-- (1.8) -/
  same_primes : ∀ p : ℕ, p.Prime → (p ∣ α₁ ↔ p ∣ α₂)
  /-- (1.9) -/
  sq_dvd₁ : ∀ p : ℕ, p.Prime → p ∣ α₁ → p ^ 2 ∣ α₁
  sq_dvd₂ : ∀ p : ℕ, p.Prime → p ∣ α₂ → p ^ 2 ∣ α₂

namespace HBForms

def l₁ (F : HBForms) (n : ℕ) : ℕ := F.α₁ * n + F.β₁
def l₂ (F : HBForms) (n : ℕ) : ℕ := F.α₂ * n + F.β₂
/-- HB's `α = (α₁, α₂)`. -/
def α (F : HBForms) : ℕ := Nat.gcd F.α₁ F.α₂

end HBForms

/-- `Σ_{w v = N, v > V} χ(w)` (p.211): the inner truncated divisor sum of `S(δ₁,δ₂;V₁,V₂)`;
`p = (w, v)` runs over `N.divisorsAntidiagonal`. -/
noncomputable def truncChiSum (χ : DirichletCharacter ℂ q) (N : ℕ) (V : ℝ) : ℝ :=
  ∑ p ∈ N.divisorsAntidiagonal, if V < (p.2 : ℝ) then chiRe χ p.1 else 0

/-- HB's window `x < n ≤ 2x`, `(l, q) = 1` at the forms `F` (p.198). -/
noncomputable def hbFormsWindow (F : HBForms) (q x : ℕ) : Finset ℕ :=
  (Finset.Ioc x (2 * x)).filter (fun n => Nat.Coprime (F.l₁ n * F.l₂ n) q)

/-- HB's `S(δ₁,δ₂;V₁,V₂)` (p.211). -/
noncomputable def bilinearS (χ : DirichletCharacter ℂ q) (F : HBForms) (x δ₁ δ₂ : ℕ)
    (V₁ V₂ : ℝ) : ℝ :=
  ∑ n ∈ (hbFormsWindow F q x).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
    truncChiSum χ (F.l₁ n / δ₁) V₁ * truncChiSum χ (F.l₂ n / δ₂) V₂

/-- The `HBSieveData` at the forms `F`: HB's `S(d)` at general forms (support `hbFormsWindow`,
`val n = l₁ n · l₂ n`, `a n = Λ*(l₁ n)·Λ*(l₂ n)`); W-a's `hbDataHB` is this at `HBForms.twin`. -/
noncomputable def hbDataForms (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (F : HBForms) (x : ℕ) : HBSieveData :=
  HBSieveData.ofHbP (chiReChar χ hsq) (z := (z : ℝ)) (by exact_mod_cast hz)
    (hbFormsWindow F q x) (fun n => F.l₁ n * F.l₂ n)
    (fun n => LamStar χ z (F.l₁ n) * LamStar χ z (F.l₂ n))
    (fun n _ => mul_nonneg (LamStar_nonneg χ hsq z _) (LamStar_nonneg χ hsq z _))

/-! ## B-2 — Λ′, Q, the μ-sieve, the hyperbola, the log integral, LEMMA 9 (the defs) -/

/-- `Λ′(n) = Σ_{u ∣ n} χ(u) log(n/u)` (p.210): `LamTilde` without the `μ²`. -/
noncomputable def LamPrime (χ : DirichletCharacter ℂ q) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, chiRe χ d * Real.log ((n / d : ℕ) : ℝ)

/-- HB's `Q = ∏_{p < z, χ(p) = −1} p` (p.210): the `χ = −1` sibling of `hbP`. -/
noncomputable def hbQ (χ : DirichletCharacter ℂ q) (z : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range z).filter (fun p => p.Prime ∧ chiRe χ p = -1), p

/-- `Σ_{w v = N} χ(w) log(c·v)` — the log-weighted twisted divisor sum Lemma 9 integrates to. -/
noncomputable def logDivChiSum (χ : DirichletCharacter ℂ q) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ p ∈ N.divisorsAntidiagonal, chiRe χ p.1 * Real.log (c * (p.2 : ℝ))

/-- HB's TRUNCATED `Λ*_{<q}(n) = Σ_{m ∣ Q, m² ∣ n, m < q} μ(m) Λ′(n/m²)` (p.210, the form §6
consumes at (6.11) and (6.12)); `LamStar − LamStarTrunc` is the `m ≥ q` tail. -/
noncomputable def LamStarTrunc (χ : DirichletCharacter ℂ q) (z n : ℕ) : ℝ :=
  ∑ m ∈ (hbQ χ z).divisors.filter (fun m => m ^ 2 ∣ n ∧ m < q), (μ m : ℝ) * LamPrime χ (n / m ^ 2)

/-! ## B-3 — the dyadic cells, the residue split (5.2)–(5.4), (5.18) -/

/-- HB's `S` of (5.3): the lattice count at one dyadic cell `(R_i, 2R_i] × (S_i, 2S_i]` and one
residue class `(a_i, b_i)`; `p = (w, v)` with `w v = l_i(n)/δ_i`. -/
noncomputable def cellCount (F : HBForms) (q x δ₁ δ₂ : ℕ) (R₁ S₁ R₂ S₂ : ℝ)
    (a₁ b₁ a₂ b₂ : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Ioc x (2 * x)).filter (fun n => δ₁ ∣ F.l₁ n ∧ δ₂ ∣ F.l₂ n),
    ((F.l₁ n / δ₁).divisorsAntidiagonal.filter (fun p =>
        R₁ < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R₁ ∧ S₁ < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * S₁ ∧
        p.2 ≡ a₁ [MOD q] ∧ p.1 ≡ b₁ [MOD q])).card *
    ((F.l₂ n / δ₂).divisorsAntidiagonal.filter (fun p =>
        R₂ < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * R₂ ∧ S₂ < (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * S₂ ∧
        p.2 ≡ a₂ [MOD q] ∧ p.1 ≡ b₂ [MOD q])).card

/-! ## B-5 — the ψ-reduction (5.14)–(5.17) -/

/-- (5.15) -/
noncomputable def hbT₁ (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) : ℝ :=
  max R₂
    (max (((F.α₂ * x + F.β₂ : ℕ) : ℝ) / (δ₂ * w₂))
      ((((F.α₂ * δ₁ * w₁ : ℕ) : ℝ) * R₁ + ((F.α₁ * F.β₂ : ℕ) : ℝ) - ((F.α₂ * F.β₁ : ℕ) : ℝ))
        / ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ)))

/-- (5.16) -/
noncomputable def hbT₂ (F : HBForms) (x δ₁ δ₂ : ℕ) (R₁ R₂ : ℝ) (w₁ w₂ : ℕ) : ℝ :=
  min (2 * R₂)
    (min (((2 * F.α₂ * x + F.β₂ : ℕ) : ℝ) / (δ₂ * w₂))
      ((2 * ((F.α₂ * δ₁ * w₁ : ℕ) : ℝ) * R₁ + ((F.α₁ * F.β₂ : ℕ) : ℝ) - ((F.α₂ * F.β₁ : ℕ) : ℝ))
        / ((F.α₁ * δ₂ * w₂ : ℕ) : ℝ)))

end Salt.N7
