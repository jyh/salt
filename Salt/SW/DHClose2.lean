/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHCore
import Salt.SW.SelOpt

/-!
# T-BAL THE CLOSE — the local ζ·L split gift and the H(z) main-term scaffolding

This module hosts the T-BAL-ENDGAME stones layered on the landed suppliers
(`Salt/SW/DHCore.lean`, `SelOpt.lean`, `SelWeight.lean`, `DHExtract.lean`, `DHBal*.lean`).

## The load-bearing local split (catch #161, banked gift)

The exact local residue density `h(p) = 1 + χ_ℝ(p) − χ_ℝ(p)/p` (`selH`) splits its Selberg
reciprocal into the local `ζ` and `L(χ)` Euler factors:

  `1 − h(p)/p = (1 − 1/p)(1 − χ_ℝ(p)/p)`   (exact, `selH_local_split`),

whence the Selberg factor
  `1 + g(p) = p/(p − h(p)) = 1/((1 − 1/p)(1 − χ_ℝ(p)/p)) = ζ_p · L_p(χ)`
  (`one_add_selG_eq_local_inv`).

This is the structural fact that lets `H(z) = Σ_{r≤z, sf} g(r)` carry the `L(1,χ) = L₁`
main term: the `1/(1−1/p)` factors give the `log z` growth (`ζ`-part, removed by the
`b`-correction), the `1/(1−χ_ℝ(p)/p)` factors give `L₁`.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `native_decide`, no `sorry`.
-/

open Finset

noncomputable section

namespace Salt.SW

variable {q : ℕ}

/-! ## §1 — the local ζ·L split (the banked gift, catch #161) -/

/-- **The exact local split** (banked gift, catch #161). For `p ≥ 2` the Selberg local density
`h(p) = 1 + χ_ℝ(p) − χ_ℝ(p)/p` obeys `1 − h(p)/p = (1 − 1/p)·(1 − χ_ℝ(p)/p)` — the H-local
factor splits EXACTLY into the local `ζ`-factor `(1 − 1/p)` and the local `L(χ)`-factor
`(1 − χ_ℝ(p)/p)`. Pure field algebra (`p ≠ 0`), no character case split. -/
lemma selH_local_split (χ : DirichletCharacter ℂ q) {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℝ) - selH χ p / (p : ℝ) = (1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    positivity
  rw [selH]
  field_simp
  ring

/-- The local `ζ`-factor `1 − 1/p` is positive for `p ≥ 2`. -/
lemma one_sub_inv_pos {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
  linarith

/-- The local `L(χ)`-factor `1 − χ_ℝ(p)/p` is positive for `p ≥ 2` (real `χ`): the product with
the positive `ζ`-factor is `(p − h(p))/p > 0` (`selH_lt_of_prime`), and the `ζ`-factor is
positive. -/
lemma one_sub_chiRe_div_pos (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ}
    (hp : 2 ≤ p) : (0 : ℝ) < 1 - chiRe χ p / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt := selH_lt_of_prime χ hsq hp
  have hprod : (0 : ℝ) < (1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ)) := by
    rw [← selH_local_split χ hp, sub_pos, div_lt_one hp0]; exact hlt
  have hz := one_sub_inv_pos (p := p) hp
  rcases mul_pos_iff.mp hprod with ⟨_, hb⟩ | ⟨ha, _⟩
  · exact hb
  · exact absurd ha (not_lt.mpr hz.le)

/-- **`1 + g(p) = ζ_p·L_p(χ)` (the gift's headline).** For `p ≥ 2` and real `χ`,
`1 + selG χ p = 1/((1 − 1/p)(1 − χ_ℝ(p)/p))` — the Selberg factor is exactly the product of the
local `ζ` and `L(χ)` inverse-Euler factors. Route: `1 + g = p/(p − h)` and
`p − h = p·(1 − 1/p)(1 − χ/p)` (`selH_local_split`). -/
lemma one_add_selG_eq_local_inv (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {p : ℕ}
    (hp : 2 ≤ p) :
    1 + selG χ p = 1 / ((1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ))) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlt := selH_lt_of_prime χ hsq hp
  have hden : (0 : ℝ) < (p : ℝ) - selH χ p := by linarith
  have hsplit := selH_local_split χ hp
  -- (p − h)/p = (1−1/p)(1−χ/p)
  have hfac : (1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ)) = ((p : ℝ) - selH χ p) / (p : ℝ) := by
    rw [← hsplit]; field_simp
  rw [selG, hfac]
  rw [div_div_eq_mul_div, one_mul]
  rw [eq_div_iff hden.ne']
  field_simp
  ring

/-- **The H-block is the truncated ζ·L Euler product** (R5 stepping stone). For squarefree `m`
and real `χ`, the block sum of `g` over the divisors of `m` equals the finite product of the
local `ζ·L(χ)` factors over the primes of `m`:
`Σ_{a∣m} g(a) = ∏_{p∣m} 1/((1−1/p)(1−χ_ℝ(p)/p))`. Route: DIVPROD (`sum_divisors_prod_primeFactors`
at `f = selG`) gives `Σ_{a∣m} g(a) = ∏_{p∣m}(1 + g(p))`, then the gift
(`one_add_selG_eq_local_inv`) rewrites each factor. This is the exact structural identity the
`H_lower` route consumes: `H(z) = Σ_{r≤z, sf} g(r)` is the `r ≤ z` truncation of this block for
`m = ∏_{p≤z} p`, so `H(z)` inherits the `∏(1−1/p)⁻¹ ~ log z` (`ζ`-part) and `∏(1−χ/p)⁻¹ ~ L₁`
(`L(χ)`-part) structure. -/
lemma selHblock_divisors_eq (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) {m : ℕ}
    (hm : Squarefree m) :
    ∑ a ∈ m.divisors, selGmul χ a
      = ∏ p ∈ m.primeFactors, 1 / ((1 - 1 / (p : ℝ)) * (1 - chiRe χ p / (p : ℝ))) := by
  have key := sum_divisors_prod_primeFactors (f := selG χ) hm
  rw [show (∑ a ∈ m.divisors, selGmul χ a)
        = ∑ a ∈ m.divisors, ∏ p ∈ a.primeFactors, selG χ p from rfl, ← key]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [add_comm]
  exact one_add_selG_eq_local_inv χ hsq (Nat.prime_of_mem_primeFactors hp).two_le

/-! ## §2 — the R6 weighted-extraction regroup (the gcW swap; the first step of R6)

The weighted-detector coefficient `dhCoeffW χ λ n = dhA χ n · (Σ_{d∣n} λ_d)²` regroups by
`m = lcm(d,e)` (`dhWeightSqW_eq_sum_gcW`) into `dhA χ n · Σ_{m∣n} gcW λ m`. Swapping the
divisor sum against the outer partial sum collects the extraction into an `m`-indexed sum of
`m`-restricted `dhA` sums — the exact shape the freeze's R6 route consumes (`Σ_m gcW(m)·[the
m-restricted dhA sums]`). This regroup is EXACT and generic in the summand `f`. -/

/-- **R6 regroup (the gcW swap).** For any weight `λ`, any per-index factor `f`, and any bound
`Y`, the weighted extraction sum collects by `m = lcm` into an `m`-indexed sum of the
`m`-restricted `dhA` sums:
`Σ_{n≤Y} dhCoeffW χ λ n · f n = Σ_{m≤Y} gcW λ m · Σ_{n≤Y, m∣n} dhA χ n · f n`.
EXACT (via `dhWeightSqW_eq_sum_gcW` + the divisor↔multiples swap). This is the first,
mechanical step of the weighted R6 extraction; the per-`m` inner sum
`Σ_{n≤Y, m∣n} dhA χ n · f n` is the residual (see the `T-BAL-R6` flag). -/
lemma dhExtractionW_regroup (χ : DirichletCharacter ℂ q) (lam : ℕ → ℝ) (f : ℕ → ℝ) (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, dhCoeffW χ lam n * f n
      = ∑ m ∈ Finset.Icc 1 Y, gcW lam m
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n), dhA χ n * f n := by
  have hstep : ∀ n ∈ Finset.Icc 1 Y, dhCoeffW χ lam n * f n
      = ∑ m ∈ n.divisors, gcW lam m * (dhA χ n * f n) := by
    intro n _
    rw [dhCoeffW, dhWeightSqW_eq_sum_gcW,
      show dhA χ n * (∑ m ∈ n.divisors, gcW lam m) * f n
        = (∑ m ∈ n.divisors, gcW lam m) * (dhA χ n * f n) by ring, Finset.sum_mul]
  have hcomm : ∀ (n m : ℕ), (n ∈ Finset.Icc 1 Y ∧ m ∈ n.divisors)
      ↔ (n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n) ∧ m ∈ Finset.Icc 1 Y) := by
    intro n m
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hn1, hnY⟩, hmn, _hn0⟩
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos hmn (by omega)
      have hmn' : m ≤ n := Nat.le_of_dvd (by omega) hmn
      exact ⟨⟨⟨hn1, hnY⟩, hmn⟩, hm1, le_trans hmn' hnY⟩
    · rintro ⟨⟨⟨hn1, hnY⟩, hmn⟩, _hm1, _⟩
      exact ⟨⟨hn1, hnY⟩, hmn, by omega⟩
  calc ∑ n ∈ Finset.Icc 1 Y, dhCoeffW χ lam n * f n
      = ∑ n ∈ Finset.Icc 1 Y, ∑ m ∈ n.divisors, gcW lam m * (dhA χ n * f n) :=
        Finset.sum_congr rfl hstep
    _ = ∑ m ∈ Finset.Icc 1 Y, ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n),
          gcW lam m * (dhA χ n * f n) := Finset.sum_comm' hcomm
    _ = ∑ m ∈ Finset.Icc 1 Y, gcW lam m
          * ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => m ∣ n), dhA χ n * f n := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]

end Salt.SW

end
