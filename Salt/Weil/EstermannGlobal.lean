/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Estermann
import Mathlib

/-!
# WEIL-TRIO W3 — the global Estermann bound at an arbitrary modulus

Governing design: `docs/exploration/weil-trio-design-0806.md` (v2 DELTA §D3, §D8). This module
assembles the prime-power grades of W1 into the composite Estermann bound the road (N7) quotes,
at an **arbitrary** modulus `k ≥ 1` and **arbitrary** `a, b`:

`‖S(a,b;k)‖ ≤ 2^{v₂(k)/2} · d(k) · k^{1/2} · (k,a,b)^{1/2}`

(`norm_kloosterman_estermann_nat` / `norm_kloosterman_estermann`), with the 2-adic factor carried
**explicitly** — never absorbed into the constant. The odd part is θ-free: the odd-prime-power
grade `norm_kloosterman_prime_pow_gcd` (W1-c) has constant `c_e = 2 ≤ d(p^e)` uniformly in `e`, so
`∏_{p odd} c_{e_p} ≤ ∏_{p odd} d(p^{e_p}) = d(k_odd)`. The 2-part is the trivial bound
`‖S(a,b;2^κ)‖ ≤ 2^κ` (`norm_kloosterman_two_pow`, P6), and `2^κ = 2^{κ/2}·2^{κ/2}` splits as
"one half folds into `√k`, one half is the explicit 2-adic factor `2^{v₂(k)/2}`" — with the
divisor factor `d(2^κ) = κ+1 ≥ 1` and the 2-part gcd `(2^κ,a,b) ≥ 1` left as slack.

## The assembly

* `kloosterman_mul_of_coprime_unit_twist` (imported from `Salt.Weil.CompositeTail`, where it was
  consolidated on 2026-08-06) — twisted multiplicativity at **arbitrary** `a, b` (no `IsUnit a`)
  carrying `IsUnit` of the two Bézout twists `l₁, l₂`. The unit-`a` row
  `kloosterman_mul_of_coprime_unit` is now its corollary: that hypothesis was used only to state
  `IsUnit` of the *products* `lᵢ·(e a).ᵢ`, and W3 needs unit-ness of the twists alone (that is
  what preserves the gcd factor).
* `gcd_unit_twist_nat` — a unit twist `l` on `ZMod n` rewrites nat arguments as
  `l·(A : ZMod n) = (l.val·A : ZMod n)` and can only *shrink* the gcd datum:
  `(n, l.val·A, l.val·B) ∣ (n, A, B)` (coprimality of `l.val` to `n`).
* `natCast_chineseRemainder_fst/snd` — the CRT projections of a nat cast are nat casts.
* `norm_kloosterman_estermann_nat` — the recursion over `Nat.recOnPosPrimePosCoprime`, exactly the
  shape of `norm_kloosterman_le_tau_sqrt` (`Salt.Weil.CompositeFull`) but on the *non-unit*
  branch, so the gcd datum travels with it.

## The road form

`norm_kloosterman_estermann_road` specialises to the Kloosterman moduli of Heath-Brown 1983 §5,
`k = D·δ₁·w₁` with `δ₁, w₁` odd (W1-d, `factorization_two_kloosterman_modulus`): there the 2-adic
factor reads `2^{v₂(D)/2}`. N7 quotes this as Estermann (7.1); Lemma 10 then reads at
`k^{ε−1/4}`-grade, (5.19) at `x^{15/16+ε}`.

## ⚠️ The standing caveat (math-seat refutation, `docs/blueprints/flags.md`, 2026-08-06)

This is **(7.1) plus an explicit 2-adic factor**, not (7.1) verbatim: `2^{v₂(k)/2}` is *unbounded*
at general `k` (it grows to `√k`), so at general moduli the exit here is strictly weaker than
Heath-Brown's `≪ d(k)k^{1/2}(k,u,v)^{1/2}`. The loss is the 2-part alone — `norm_kloosterman_two_pow`
sits `2^{κ/2}` above the true `√(2^κ)` — and the odd part is *sharper* than HB (implied constant
`1`). The collapse of the factor to a bounded constant on road moduli is **not proved here and is
not implied by W1-d alone**: W1-d gives `v₂(k) = v₂(D)` with `D = α₂qΔ^{−1}`, which at the twin
instance `α₁ = α₂ = 4` is `max(2, v₂(q))` — bounded by `3` only through the structure lemma
`v₂(q) ≤ 3` (W4-a). A consumer wanting a numeric constant must discharge that separately; what is
delivered here is the two-row supply (this inequality + `two_pow_factorization_dvd_of_odd_cofactors`,
`Salt/Weil/GcdBranch.lean:355`).
-/

namespace Salt.Weil

open scoped BigOperators

/-! ### W3.0 — the supply repairs -/

-- `kloosterman_mul_of_coprime_unit_twist` (W3.0's twisted multiplicativity at arbitrary `a, b`
-- with unit Bézout twists) now lives in `Salt/Weil/CompositeTail.lean`, above its `IsUnit a`
-- corollary `kloosterman_mul_of_coprime_unit`, which is derived from it (WEIL-CONS, 2026-08-06).

/-- **The CRT projections of a nat cast are nat casts** (first coordinate): the Chinese-remainder
ring isomorphism is a ring hom, so it commutes with `Nat.cast`. -/
theorem natCast_chineseRemainder_fst {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] (h : Nat.Coprime c₁ c₂)
    (x : ℕ) : (ZMod.chineseRemainder h ((x : ℕ) : ZMod (c₁ * c₂))).1 = ((x : ℕ) : ZMod c₁) := by
  haveI : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  rw [map_natCast]
  exact Prod.fst_natCast x

/-- **The CRT projections of a nat cast are nat casts** (second coordinate). -/
theorem natCast_chineseRemainder_snd {c₁ c₂ : ℕ} [NeZero c₁] [NeZero c₂] (h : Nat.Coprime c₁ c₂)
    (x : ℕ) : (ZMod.chineseRemainder h ((x : ℕ) : ZMod (c₁ * c₂))).2 = ((x : ℕ) : ZMod c₂) := by
  haveI : NeZero (c₁ * c₂) := ⟨mul_ne_zero (NeZero.ne c₁) (NeZero.ne c₂)⟩
  rw [map_natCast]
  exact Prod.snd_natCast x

/-- **A unit twist keeps the gcd datum.** For a unit `l : ZMod n` the twisted arguments
`l·(A : ZMod n)`, `l·(B : ZMod n)` are again nat casts (of `l.val·A`, `l.val·B`), and their gcd
datum against the modulus can only shrink: `(n, l.val·A, l.val·B) ∣ (n, A, B)` — indeed they are
equal, but divisibility is the direction the assembly consumes. The mechanism is
`ZMod.val_coe_unit_coprime`: a unit's `val` is coprime to the modulus. -/
theorem gcd_unit_twist_nat {n : ℕ} [NeZero n] {l : ZMod n} (hl : IsUnit l) (A B : ℕ) :
    ∃ A' B' : ℕ, l * ((A : ℕ) : ZMod n) = ((A' : ℕ) : ZMod n)
      ∧ l * ((B : ℕ) : ZMod n) = ((B' : ℕ) : ZMod n)
      ∧ Nat.gcd n (Nat.gcd A' B') ∣ Nat.gcd n (Nat.gcd A B) := by
  obtain ⟨u, rfl⟩ := hl
  refine ⟨(u : ZMod n).val * A, (u : ZMod n).val * B, ?_, ?_, ?_⟩
  · rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
  · rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
  · have hcop : Nat.Coprime ((u : ZMod n).val) n := ZMod.val_coe_unit_coprime u
    rw [Nat.gcd_mul_left]
    refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
    have h2 : Nat.Coprime (Nat.gcd n ((u : ZMod n).val * Nat.gcd A B)) ((u : ZMod n).val) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _) hcop.symm
    exact h2.dvd_of_dvd_mul_left (Nat.gcd_dvd_right _ _)

/-! ### W3.1 — the global bound -/

/-- **W3 — the global Estermann bound (nat form).** For **any** modulus `k ≥ 1` (`NeZero k`) and
**any** naturals `A, B`,

`‖S(A, B; k)‖ ≤ 2^{v₂(k)/2} · d(k) · √k · √((k, A, B))`

with `v₂(k) = k.factorization 2` and `d(k) = #k.divisors`. The 2-adic factor
`√(2^{v₂ k}) = 2^{v₂(k)/2}` is carried **explicitly** (design §D3): it is the honest residue of the
trivial 2-part bound `‖S(a,b;2^κ)‖ ≤ 2^κ` (`norm_kloosterman_two_pow`), half of which folds into
`√k`. On the odd part there is no such factor — W1-c's `norm_kloosterman_prime_pow_gcd` has
constant `2 ≤ d(p^e)` uniformly in `e`.

The proof is the coprime recursion `Nat.recOnPosPrimePosCoprime`: at a prime power it is W1-c
(odd `p`) or P6 (`p = 2`); at a coprime product it is the twisted multiplicativity
`kloosterman_mul_of_coprime_unit_twist` together with the multiplicativity of `2^{v₂(·)}`, `d`,
`√·` and the divisibility `(c₁,A,B)·(c₂,A,B) ∣ (c₁c₂,A,B)`. -/
theorem norm_kloosterman_estermann_nat (k : ℕ) [NeZero k] (A B : ℕ) :
    ‖kloosterman ((A : ℕ) : ZMod k) ((B : ℕ) : ZMod k)‖
      ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) * Real.sqrt (k : ℝ)
          * Real.sqrt ((Nat.gcd k (Nat.gcd A B) : ℕ) : ℝ) := by
  have key : ∀ k : ℕ, ∀ [NeZero k], ∀ A B : ℕ,
      ‖kloosterman ((A : ℕ) : ZMod k) ((B : ℕ) : ZMod k)‖
        ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) * Real.sqrt (k : ℝ)
            * Real.sqrt ((Nat.gcd k (Nat.gcd A B) : ℕ) : ℝ) := by
    intro k
    refine Nat.recOnPosPrimePosCoprime
      (motive := fun k => ∀ [NeZero k], ∀ A B : ℕ,
        ‖kloosterman ((A : ℕ) : ZMod k) ((B : ℕ) : ZMod k)‖
          ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) * Real.sqrt (k : ℝ)
              * Real.sqrt ((Nat.gcd k (Nat.gcd A B) : ℕ) : ℝ)) ?_ ?_ ?_ ?_ k
    · -- prime powers
      intro p n hp hn _ A B
      haveI : Fact p.Prime := ⟨hp⟩
      have hpe : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
      have hgpos : 0 < Nat.gcd (p ^ n) (Nat.gcd A B) :=
        Nat.pos_of_ne_zero fun hz => hpe (Nat.gcd_eq_zero_iff.mp hz).1
      have hsqg : (1 : ℝ) ≤ Real.sqrt ((Nat.gcd (p ^ n) (Nat.gcd A B) : ℕ) : ℝ) := by
        have h := Real.sqrt_le_sqrt
          (show (1 : ℝ) ≤ ((Nat.gcd (p ^ n) (Nat.gcd A B) : ℕ) : ℝ) by exact_mod_cast hgpos)
        simpa using h
      have hcardpos : 1 ≤ ((p ^ n).divisors.card : ℝ) := by
        have : 0 < (p ^ n).divisors.card :=
          Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hpe⟩
        exact_mod_cast this
      by_cases hp2 : p = 2
      · -- the 2-part: the trivial bound `2^n`, split as `2^{n/2}·2^{n/2}`
        subst hp2
        have hfac : ((2 ^ n : ℕ).factorization) 2 = n := by
          simp [Nat.Prime.factorization_pow Nat.prime_two]
        have hkl := norm_kloosterman_two_pow ((A : ℕ) : ZMod (2 ^ n)) ((B : ℕ) : ZMod (2 ^ n))
        have hcast : (((2 ^ n : ℕ) : ℕ) : ℝ) = (2 : ℝ) ^ n := by push_cast; ring
        have hsq : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
          Real.mul_self_sqrt (by positivity)
        rw [hfac, hcast]
        refine hkl.trans ?_
        have hexpand : Real.sqrt ((2 : ℝ) ^ n) * (((2 ^ n : ℕ).divisors.card : ℕ) : ℝ)
              * Real.sqrt ((2 : ℝ) ^ n)
              * Real.sqrt ((Nat.gcd (2 ^ n) (Nat.gcd A B) : ℕ) : ℝ)
            = (2 : ℝ) ^ n * ((((2 ^ n : ℕ).divisors.card : ℕ) : ℝ)
                * Real.sqrt ((Nat.gcd (2 ^ n) (Nat.gcd A B) : ℕ) : ℝ)) := by
          rw [show Real.sqrt ((2 : ℝ) ^ n) * (((2 ^ n : ℕ).divisors.card : ℕ) : ℝ)
                  * Real.sqrt ((2 : ℝ) ^ n)
                  * Real.sqrt ((Nat.gcd (2 ^ n) (Nat.gcd A B) : ℕ) : ℝ)
                = (Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n))
                  * ((((2 ^ n : ℕ).divisors.card : ℕ) : ℝ)
                    * Real.sqrt ((Nat.gcd (2 ^ n) (Nat.gcd A B) : ℕ) : ℝ)) from by ring, hsq]
        rw [hexpand]
        have hone : (1 : ℝ) ≤ (((2 ^ n : ℕ).divisors.card : ℕ) : ℝ)
            * Real.sqrt ((Nat.gcd (2 ^ n) (Nat.gcd A B) : ℕ) : ℝ) := by
          nlinarith [hcardpos, hsqg]
        nlinarith [hone, pow_pos (show (0:ℝ) < 2 by norm_num) n]
      · -- the odd part: W1-c at constant `2 ≤ d(p^e)`
        have hfac : ((p ^ n : ℕ).factorization) 2 = 0 := by
          refine Nat.factorization_eq_zero_of_not_dvd (fun hdvd => hp2 ?_)
          exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
            (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd)).symm
        have h2card : (2 : ℝ) ≤ ((p ^ n).divisors.card : ℝ) := by
          have hne1 : p ^ n ≠ 1 := by
            have : 1 < p ^ n := Nat.one_lt_pow (by omega) hp.one_lt
            omega
          have hsub : ({1, p ^ n} : Finset ℕ) ⊆ (p ^ n).divisors := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Nat.one_mem_divisors.mpr hpe
            · exact Nat.mem_divisors_self _ hpe
          have hc : ({1, p ^ n} : Finset ℕ).card = 2 := by
            rw [Finset.card_insert_of_notMem (by simp [Ne.symm hne1]), Finset.card_singleton]
          have : 2 ≤ (p ^ n).divisors.card := by
            calc 2 = ({1, p ^ n} : Finset ℕ).card := hc.symm
              _ ≤ _ := Finset.card_le_card hsub
          exact_mod_cast this
        have hkl := norm_kloosterman_prime_pow_gcd hp2 n (by omega) A B
        rw [hfac]
        refine hkl.trans ?_
        have hcast : Real.sqrt ((p : ℝ) ^ n) = Real.sqrt ((p ^ n : ℕ) : ℝ) := by
          congr 1; push_cast; ring
        rw [hcast]
        have hs1 : (0 : ℝ) ≤ Real.sqrt ((p ^ n : ℕ) : ℝ) := Real.sqrt_nonneg _
        have hs2 : (0 : ℝ) ≤ Real.sqrt ((Nat.gcd (p ^ n) (Nat.gcd A B) : ℕ) : ℝ) :=
          Real.sqrt_nonneg _
        have hone : Real.sqrt ((2 : ℝ) ^ (0 : ℕ)) = 1 := by norm_num
        rw [hone, one_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2card hs1) hs2
    · -- `k = 0` is vacuous under `NeZero`
      intro hz A B
      exact absurd rfl hz.out
    · -- `k = 1`
      intro _ A B
      have := norm_kloosterman_le_modulus ((A : ℕ) : ZMod 1) ((B : ℕ) : ZMod 1)
      refine this.trans ?_
      simp
    · -- the coprime step
      intro d₁ d₂ hd₁ hd₂ hcop IH₁ IH₂ _ A B
      haveI : NeZero d₁ := ⟨by omega⟩
      haveI : NeZero d₂ := ⟨by omega⟩
      obtain ⟨l₁, l₂, hu₁, hu₂, hmul⟩ :=
        kloosterman_mul_of_coprime_unit_twist hcop ((A : ℕ) : ZMod (d₁ * d₂))
          ((B : ℕ) : ZMod (d₁ * d₂))
      obtain ⟨A₁, B₁, hA₁, hB₁, hg₁⟩ := gcd_unit_twist_nat hu₁ A B
      obtain ⟨A₂, B₂, hA₂, hB₂, hg₂⟩ := gcd_unit_twist_nat hu₂ A B
      rw [hmul, natCast_chineseRemainder_fst, natCast_chineseRemainder_fst,
        natCast_chineseRemainder_snd, natCast_chineseRemainder_snd, hA₁, hB₁, hA₂, hB₂, norm_mul]
      -- abbreviations
      set g := Nat.gcd A B with hgdef
      set F₁ := Real.sqrt ((2 : ℝ) ^ d₁.factorization 2) * (d₁.divisors.card : ℝ)
        * Real.sqrt (d₁ : ℝ) with hF₁
      set F₂ := Real.sqrt ((2 : ℝ) ^ d₂.factorization 2) * (d₂.divisors.card : ℝ)
        * Real.sqrt (d₂ : ℝ) with hF₂
      have hF₁0 : 0 ≤ F₁ := by rw [hF₁]; positivity
      have hF₂0 : 0 ≤ F₂ := by rw [hF₂]; positivity
      -- the two factor bounds, with the twisted gcd data pushed back to `(dᵢ, A, B)`
      have hb₁ : ‖kloosterman ((A₁ : ℕ) : ZMod d₁) ((B₁ : ℕ) : ZMod d₁)‖
          ≤ F₁ * Real.sqrt ((Nat.gcd d₁ g : ℕ) : ℝ) := by
        refine (IH₁ A₁ B₁).trans ?_
        have hle : ((Nat.gcd d₁ (Nat.gcd A₁ B₁) : ℕ) : ℝ) ≤ ((Nat.gcd d₁ g : ℕ) : ℝ) := by
          have : Nat.gcd d₁ (Nat.gcd A₁ B₁) ≤ Nat.gcd d₁ g :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero fun hz =>
              (NeZero.ne d₁) (Nat.gcd_eq_zero_iff.mp hz).1) hg₁
          exact_mod_cast this
        have := Real.sqrt_le_sqrt hle
        rw [hF₁]
        nlinarith [this, Real.sqrt_nonneg ((Nat.gcd d₁ (Nat.gcd A₁ B₁) : ℕ) : ℝ),
          Real.sqrt_nonneg ((2 : ℝ) ^ d₁.factorization 2), Real.sqrt_nonneg (d₁ : ℝ),
          Nat.cast_nonneg (α := ℝ) d₁.divisors.card, hF₁0]
      have hb₂ : ‖kloosterman ((A₂ : ℕ) : ZMod d₂) ((B₂ : ℕ) : ZMod d₂)‖
          ≤ F₂ * Real.sqrt ((Nat.gcd d₂ g : ℕ) : ℝ) := by
        refine (IH₂ A₂ B₂).trans ?_
        have hle : ((Nat.gcd d₂ (Nat.gcd A₂ B₂) : ℕ) : ℝ) ≤ ((Nat.gcd d₂ g : ℕ) : ℝ) := by
          have : Nat.gcd d₂ (Nat.gcd A₂ B₂) ≤ Nat.gcd d₂ g :=
            Nat.le_of_dvd (Nat.pos_of_ne_zero fun hz =>
              (NeZero.ne d₂) (Nat.gcd_eq_zero_iff.mp hz).1) hg₂
          exact_mod_cast this
        have := Real.sqrt_le_sqrt hle
        rw [hF₂]
        nlinarith [this, Real.sqrt_nonneg ((Nat.gcd d₂ (Nat.gcd A₂ B₂) : ℕ) : ℝ),
          Real.sqrt_nonneg ((2 : ℝ) ^ d₂.factorization 2), Real.sqrt_nonneg (d₂ : ℝ),
          Nat.cast_nonneg (α := ℝ) d₂.divisors.card, hF₂0]
      -- the product of the two bounds
      have hstep : ‖kloosterman ((A₁ : ℕ) : ZMod d₁) ((B₁ : ℕ) : ZMod d₁)‖
            * ‖kloosterman ((A₂ : ℕ) : ZMod d₂) ((B₂ : ℕ) : ZMod d₂)‖
          ≤ (F₁ * Real.sqrt ((Nat.gcd d₁ g : ℕ) : ℝ))
            * (F₂ * Real.sqrt ((Nat.gcd d₂ g : ℕ) : ℝ)) :=
        mul_le_mul hb₁ hb₂ (norm_nonneg _) (by positivity)
      refine hstep.trans ?_
      -- the constant is exactly multiplicative
      have hfacmul : ((d₁ * d₂ : ℕ).factorization) 2 = d₁.factorization 2 + d₂.factorization 2 := by
        rw [Nat.factorization_mul (by omega) (by omega)]; simp
      have hF : Real.sqrt ((2 : ℝ) ^ ((d₁ * d₂ : ℕ).factorization) 2)
            * (((d₁ * d₂ : ℕ).divisors.card : ℕ) : ℝ) * Real.sqrt ((d₁ * d₂ : ℕ) : ℝ)
          = F₁ * F₂ := by
        rw [hfacmul, pow_add, Real.sqrt_mul (by positivity),
          Nat.Coprime.card_divisors_mul hcop, hF₁, hF₂]
        push_cast
        rw [Real.sqrt_mul (by positivity)]
        ring
      rw [hF]
      -- the gcd datum is super-multiplicative
      have hgd : Nat.gcd d₁ g * Nat.gcd d₂ g ∣ Nat.gcd (d₁ * d₂) g := by
        refine Nat.dvd_gcd (Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)) ?_
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
        exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
          (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) hcop)
      have hgle : ((Nat.gcd d₁ g : ℕ) : ℝ) * ((Nat.gcd d₂ g : ℕ) : ℝ)
          ≤ ((Nat.gcd (d₁ * d₂) g : ℕ) : ℝ) := by
        have : Nat.gcd d₁ g * Nat.gcd d₂ g ≤ Nat.gcd (d₁ * d₂) g :=
          Nat.le_of_dvd (Nat.pos_of_ne_zero fun hz => by
            have := (Nat.gcd_eq_zero_iff.mp hz).1
            simp only [Nat.mul_eq_zero] at this
            omega) hgd
        exact_mod_cast this
      have hsqrtprod : Real.sqrt ((Nat.gcd d₁ g : ℕ) : ℝ) * Real.sqrt ((Nat.gcd d₂ g : ℕ) : ℝ)
          ≤ Real.sqrt ((Nat.gcd (d₁ * d₂) g : ℕ) : ℝ) := by
        rw [← Real.sqrt_mul (by positivity)]
        exact Real.sqrt_le_sqrt hgle
      calc (F₁ * Real.sqrt ((Nat.gcd d₁ g : ℕ) : ℝ)) * (F₂ * Real.sqrt ((Nat.gcd d₂ g : ℕ) : ℝ))
          = (F₁ * F₂) * (Real.sqrt ((Nat.gcd d₁ g : ℕ) : ℝ)
              * Real.sqrt ((Nat.gcd d₂ g : ℕ) : ℝ)) := by ring
        _ ≤ (F₁ * F₂) * Real.sqrt ((Nat.gcd (d₁ * d₂) g : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hsqrtprod (by positivity)
  exact key k A B

/-- **W3 — the global Estermann bound (`ZMod` form).** For any modulus `k ≥ 1` and any
`a, b : ZMod k`,

`‖S(a, b; k)‖ ≤ 2^{v₂(k)/2} · d(k) · √k · √((k, a, b))`,

the gcd datum read through `ZMod.val`. (`Nat.gcd k (Nat.gcd a.val b.val)` is `Nat.gcd_assoc`-equal
to the `((k, a), b)` bracketing.) This is the `D3` exit shape; the 2-adic factor is explicit. -/
theorem norm_kloosterman_estermann {k : ℕ} [NeZero k] (a b : ZMod k) :
    ‖kloosterman a b‖
      ≤ Real.sqrt ((2 : ℝ) ^ k.factorization 2) * (k.divisors.card : ℝ) * Real.sqrt (k : ℝ)
          * Real.sqrt ((Nat.gcd k (Nat.gcd a.val b.val) : ℕ) : ℝ) := by
  have ha : ((a.val : ℕ) : ZMod k) = a := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hb : ((b.val : ℕ) : ZMod k) = b := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have := norm_kloosterman_estermann_nat k a.val b.val
  rwa [ha, hb] at this

/-- **W3 — the road form; N7 quotes this as Estermann (7.1).** At the Kloosterman moduli of
Heath-Brown 1983 §5, `k = D·δ₁·w₁` with `δ₁, w₁` coprime to the even modulus `α` (support (5.1),
congruence (5.6), normalisation (1.5) — W1-d), the whole 2-part of `k` sits in `D`, so the explicit
2-adic factor reads `2^{v₂(D)/2}`:

`‖S(a, b; D δ₁ w₁)‖ ≤ 2^{v₂(D)/2} · d(k) · √k · √((k, a, b))`.

N7 quotes this as Estermann (7.1); Lemma 10 then reads at `k^{ε−1/4}`-grade, (5.19) at
`x^{15/16+ε}`.

⚠️ The 2-adic factor is stated, not discharged: `2^{v₂(D)/2} ≤ 2^{3/2} ≈ 2.83` requires
`v₂(D) ≤ 3`, and at the twin instance `α₁ = α₂ = 4` one has `v₂(D) = max(2, v₂(q))`, so that bound
is exactly the structure lemma `v₂(q) ≤ 3` (W4-a) — **not** a consequence of W1-d, and not proved
in this module (math-seat refutation, `docs/blueprints/flags.md`, 2026-08-06). -/
theorem norm_kloosterman_estermann_road {D δ₁ w₁ α : ℕ} [NeZero (D * δ₁ * w₁)] (hα : 2 ∣ α)
    (hδ : Nat.Coprime δ₁ α) (hw : Nat.Coprime w₁ α) (a b : ZMod (D * δ₁ * w₁)) :
    ‖kloosterman a b‖
      ≤ Real.sqrt ((2 : ℝ) ^ D.factorization 2) * ((D * δ₁ * w₁).divisors.card : ℝ)
          * Real.sqrt ((D * δ₁ * w₁ : ℕ) : ℝ)
          * Real.sqrt ((Nat.gcd (D * δ₁ * w₁) (Nat.gcd a.val b.val) : ℕ) : ℝ) := by
  have hD : D ≠ 0 := by
    intro h
    exact (NeZero.ne (D * δ₁ * w₁)) (by simp [h])
  have := norm_kloosterman_estermann (k := D * δ₁ * w₁) a b
  rwa [factorization_two_kloosterman_modulus hD hα hδ hw] at this

end Salt.Weil
