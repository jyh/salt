/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.RosserDim4Instance
import Salt.HB.StarWindow
import Salt.MR.EvenChiDescent

/-!
# N5 WIRING — the star step's honest window plugged into the HB sieve interface

`Salt/HB/RosserDim4Instance.lean` lands the dimension-4 Rosser service layer over an
abstract `HBSieveData` (the character, the sifting modulus `P`, the window, the form value
`l(n)`, the weight `a(n)`, and HB's Lemma 1 as the field `a_nonneg`).  `Salt/HB/StarStep.lean`
and `Salt/HB/StarWindow.lean` land the star step: `Λ*`, its nonnegativity
(`LamStar_nonneg`), the sum `S⁽³⁾ = Σ_{n∈A} Λ*(n)Λ*(n+2)`, and the concrete window
`honestWindow χ z x`.  **This file is the wire between them** — it builds the interface at
the star step's own data and identifies the two `S⁽³⁾`s.  Nothing here is an estimate; a
wire is not the engine, and nothing in this file bears on twin primes.

## The one stone that was not free: the character

The interface's character is `DirichletCharacter ℝ q` (the sieve side wants a real value,
because `hbSiftSet` is cut out by `χ(p) = 1` in `ℝ`).  The star step's is
`DirichletCharacter ℂ q` together with `χ ^ 2 = 1`, and it reads the real part through
`Salt.TwinBar.chiRe χ n = (χ n).re`.  So the wire needs the **down-leg** `ℂ → ℝ` on the
quadratic locus.  That leg is not free (`MulChar.ringHomComp` has no inverse) and mathlib
does not carry it; salt builds it exactly once, in `Salt/MR/EvenChiDescent.lean`
(`Salt.MR.e4a_toR`, assembled on the unit group and extended by `MulChar.ofUnitHom`).
`chiReChar` is that construction fed by `MulChar.isQuadratic_iff_sq_eq_one`, and
`chiReChar_apply` is the only fact about it anyone needs: it **is** `Re ∘ χ`, at every
argument, units and non-units alike.

## ⚠️ TWO WINDOWS, AND THIS FILE DOES NOT CHOOSE BETWEEN THEM

State it plainly, because the mismatch is real and it is *not* resolved here.

* The **sieve side** sifts by `hbP χ_ℝ z = ∏ p` over `hbSiftSet` — the primes `2 < p < z`
  with `χ(p) = 1`.  That is HB's `P`.
* The **star side's** `honestWindow χ z x` is `{n ∈ (x, 2x] : (n(n+2), excPrimorial χ z) = 1}`,
  and `excPrimorial χ z` is the product of the primes `p < z` with `χ_ℝ(p) ≠ −1` — a
  *strictly larger* set of primes: it also carries the `p` with `χ(p) = 0` (i.e. `p ∣ q`)
  and it carries `p = 2`.
* HB's own support condition is `(l, qP) = 1`.

Which of these the reduction chain is ultimately stated on is **the N8 design block's
decision, not this file's**.  What this file does is fix the interface at the honest window
and prove that the interface's `S⁽³⁾` there is literally the star step's `S3` on the
`(l, P) = 1` subwindow (`hbData_S3_eq`) — an identification, carrying no claim that either
window is the right one.

## Main results

* `chiReChar` / `chiReChar_apply` / `chiReChar_prime` — the real character of a quadratic
  complex character, and its identification with `chiRe`.
* `hbSiftSet_chiReChar` — HB's sifting set, read off `chiRe` directly.
* `hbData` / `hbData_P` / `hbData_S3_eq` — the interface at the honest window, its sifting
  modulus, and the identification of the two `S⁽³⁾`s.
* `hbData_fl_sandwich` — `hbSieve_fl_sandwich` at `hbData`, with `H.S3` rewritten through
  `hbData_S3_eq`.  Mechanical; it exists so the service layer's conclusion is readable in
  the star step's own vocabulary.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction
open Salt.TwinBar
open Salt.BrunLower

namespace Salt.HB

variable {q : ℕ}

/-! ## §1 — the real character of a quadratic complex character -/

/-- **The down-leg, packaged for the sieve side.**  The real-valued Dirichlet character
attached to a quadratic `ℂ`-valued one.  This is `Salt.MR.e4a_toR` (salt's single home for
the `ℂ → ℝ` restriction) with the hypothesis converted from `χ ^ 2 = 1` to
`χ.IsQuadratic` by `MulChar.isQuadratic_iff_sq_eq_one`. -/
noncomputable def chiReChar (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) :
    DirichletCharacter ℝ q :=
  Salt.MR.e4a_toR χ (MulChar.isQuadratic_iff_sq_eq_one.mpr hsq)

/-- **`chiReChar` is `Re ∘ χ` on the nose**, at *every* argument.  At a unit this is the
round trip `e4a_toC_toR`; at a non-unit both sides are `0` (`MulChar.map_nonunit`), which
is why the identity needs no coprimality side condition. -/
theorem chiReChar_apply (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (a : ZMod q) :
    chiReChar χ hsq a = (χ a).re := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  have h : ((chiReChar χ hsq a : ℝ) : ℂ) = χ a := by
    calc ((chiReChar χ hsq a : ℝ) : ℂ)
        = Salt.MR.e4a_toC (Salt.MR.e4a_toR χ hQ) a := rfl
      _ = χ a := by rw [Salt.MR.e4a_toC_toR χ hQ]
  rw [← h, Complex.ofReal_re]

/-- The same identity in the corpus's own notation: at a natural-number argument
`chiReChar` is `Salt.TwinBar.chiRe`.  This is the equation the sieve-side definitions
(`hbSiftSet`, `hbP`) are read through. -/
theorem chiReChar_prime (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (p : ℕ) :
    chiReChar χ hsq (p : ZMod q) = chiRe χ p :=
  chiReChar_apply χ hsq (p : ZMod q)

/-- **HB's sifting set at the wired character**, with the `⌈z⌉₊` bookkeeping discharged for
an integer `z`: the primes `2 < p < z` with `χ_ℝ(p) = 1`.  The `(p : ℝ) < z` conjunct of
`mem_hbSiftSet` is absorbed by `p ∈ range z`. -/
theorem hbSiftSet_chiReChar (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (z : ℕ) :
    hbSiftSet (chiReChar χ hsq) (z : ℝ)
      = (Finset.range z).filter (fun p => p.Prime ∧ 2 < p ∧ chiRe χ p = 1) := by
  ext p
  rw [mem_hbSiftSet, Finset.mem_filter, Finset.mem_range, chiReChar_prime]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by exact_mod_cast h3, h1, h2, h4⟩
  · rintro ⟨hlt, h1, h2, h4⟩
    exact ⟨h1, h2, by exact_mod_cast hlt, h4⟩

/-! ## §2 — the interface at the honest window -/

/-- **THE WIRE.**  The `HBSieveData` carried by the star step at the honest window:

* character `χ_ℝ = chiReChar χ hsq`, sifting modulus `P = hbP χ_ℝ z` (so all four
  `P`-fields come from `HBSieveData.ofHbP`);
* `support = honestWindow χ z x = {n ∈ (x, 2x] : (n(n+2), excPrimorial χ z) = 1}`;
* `val n = n(n+2)` — HB's `l(n) = l₁(n)l₂(n)` for the twin form;
* `a n = Λ*(n)·Λ*(n+2)`, whose nonnegativity (the `a_nonneg` field, HB's Lemma 1) is
  `LamStar_nonneg` twice.

⚠️ The window here is `excPrimorial`-coprimality, *not* `(l, P) = 1` and not HB's
`(l, qP) = 1`; see this file's header.  Choosing the window is N8's, not this wire's. -/
noncomputable def hbData (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) : HBSieveData :=
  HBSieveData.ofHbP (chiReChar χ hsq) (z := (z : ℝ)) (by exact_mod_cast hz)
    (honestWindow χ z x) (fun n => n * (n + 2))
    (fun n => LamStar χ z n * LamStar χ z (n + 2))
    (fun n _ => mul_nonneg (LamStar_nonneg χ hsq z n) (LamStar_nonneg χ hsq z (n + 2)))

/-- The wired situation sifts by HB's own modulus. -/
theorem hbData_P (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z) (x : ℕ) :
    (hbData χ hsq hz x).P = hbP (chiReChar χ hsq) (z : ℝ) := rfl

/-- **THE TWO `S⁽³⁾`s ARE ONE.**  The interface's sifted sum at `hbData` is the star step's
`S3` on the sub-window of `honestWindow` where `(l, P) = 1`.  Both sides are the same sum
of `Λ*(n)Λ*(n+2)` over the same finite set, so this is an identification and not an
estimate: it says the wire is connected, nothing more. -/
theorem hbData_S3_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ} (hz : 2 ≤ z)
    (x : ℕ) :
    (hbData χ hsq hz x).S3
      = S3 χ z ((honestWindow χ z x).filter
          (fun n => Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ)))) := rfl

/-- **The N5 exit theorem read in the star step's vocabulary.**  `hbSieve_fl_sandwich` at
`hbData`, with the interface's `S⁽³⁾` replaced by the star step's `S3` via `hbData_S3_eq`.
Purely mechanical: the hypotheses and all three conclusions are the service layer's, and
`(hbData …).z` is `(z : ℝ)` definitionally. -/
theorem hbData_fl_sandwich (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {z : ℕ}
    (hz : 2 ≤ z) (x : ℕ) {lam sRatio : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 / 4)
    (hzt : zThresh lam ≤ (z : ℝ)) (hs : levelE (Lam4 lam (z : ℝ)) ≤ sRatio) :
    -- (1) the sandwich (2.2), on the star step's `S3`
    (lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 2 (flB sRatio (Lam4 lam (z : ℝ)))
          (hbP (chiReChar χ hsq) (z : ℝ)) (hbData χ hsq hz x).S
        ≤ S3 χ z ((honestWindow χ z x).filter
            (fun n => Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ))))
      ∧ S3 χ z ((honestWindow χ z x).filter
            (fun n => Nat.Coprime (n * (n + 2)) (hbP (chiReChar χ hsq) (z : ℝ))))
          ≤ lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 1 (flB sRatio (Lam4 lam (z : ℝ)))
              (hbP (chiReChar χ hsq) (z : ℝ)) (hbData χ hsq hz x).S)
    -- (2) the main-term defect at `ρ₁ = G(d)/d`
    ∧ (W (hbData χ hsq hz x).sieve
          * (1 - flConst lam (Lam4 lam (z : ℝ)) * Real.exp (-(flRate lam) * sRatio))
          ≤ lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 2 (flB sRatio (Lam4 lam (z : ℝ)))
              (hbP (chiReChar χ hsq) (z : ℝ)) (fun d => nuG d)
        ∧ lamSum (Lam4 lam (z : ℝ)) (z : ℝ) 1 (flB sRatio (Lam4 lam (z : ℝ)))
              (hbP (chiReChar χ hsq) (z : ℝ)) (fun d => nuG d)
          ≤ W (hbData χ hsq hz x).sieve
              * (1 + lam * flConst lam (Lam4 lam (z : ℝ))
                  * Real.exp (-(flRate lam) * sRatio)))
    -- (3) the per-δ transfer, at any density `ρ_i` and any domination `B`
    ∧ (∀ (side : ℕ), side ≤ 2 → ∀ (rhoi : ℕ → ℝ) (B : ℝ),
        (∀ δ ∈ failSet (Lam4 lam (z : ℝ)) (z : ℝ) side (flB sRatio (Lam4 lam (z : ℝ)))
            (hbP (chiReChar χ hsq) (z : ℝ)),
          0 ≤ deltaSum (hbP (chiReChar χ hsq) (z : ℝ)) δ (fun d => nuG d)) →
        (∀ δ ∈ failSet (Lam4 lam (z : ℝ)) (z : ℝ) side (flB sRatio (Lam4 lam (z : ℝ)))
            (hbP (chiReChar χ hsq) (z : ℝ)),
          |deltaSum (hbP (chiReChar χ hsq) (z : ℝ)) δ rhoi|
            ≤ B * deltaSum (hbP (chiReChar χ hsq) (z : ℝ)) δ (fun d => nuG d)) →
        |lamSum (Lam4 lam (z : ℝ)) (z : ℝ) side (flB sRatio (Lam4 lam (z : ℝ)))
              (hbP (chiReChar χ hsq) (z : ℝ)) rhoi
            - moebSum (hbP (chiReChar χ hsq) (z : ℝ)) rhoi|
          ≤ B * |lamSum (Lam4 lam (z : ℝ)) (z : ℝ) side (flB sRatio (Lam4 lam (z : ℝ)))
                (hbP (chiReChar χ hsq) (z : ℝ)) (fun d => nuG d)
              - moebSum (hbP (chiReChar χ hsq) (z : ℝ)) (fun d => nuG d)|) := by
  have h := hbSieve_fl_sandwich (hbData χ hsq hz x) hlam hlam' hzt hs
  rw [hbData_S3_eq] at h
  exact h

end Salt.HB
