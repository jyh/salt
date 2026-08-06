/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.GcdBranch
import Mathlib

/-!
# WEIL-TRIO W1-c — the sharp Salié bound and the Estermann prime-power grade

Governing design: `docs/exploration/weil-trio-design-0806.md` (v2 DELTA §D1). The road
(N7) needs Estermann's `S(k; u,v) ≪ d(k)·k^{1/2}·(k,u,v)^{1/2}` at an **arbitrary** modulus
`k` and **arbitrary** `u, v`; the budget ruling `θ ≤ 1/50` leaves no room for the crude
odd-exponent bound `norm_kloosterman_prime_pow_odd` (which is `√p` above the truth). This
module closes the prime-power half at the sharp constant.

## The sharp odd-exponent bound (`norm_kloosterman_prime_pow_odd_sharp`)

For an odd prime `p`, `m ≥ 1`, a unit `a` and **any** `b`,
`‖S(a, b; p^{2m+1})‖ ≤ 2·p^m·√p = 2·√(p^{2m+1})`.

The proof is stationary phase with the *second-order* term retained — the one place in the
whole Weil track where the elementary route needs a genuine Gauss sum:

1. **Localise.** The shift family `1 + p^{m+1}z` (whose square already vanishes) collapses
   the sum onto the critical set `C = {t : p^{m+1}·w t = 0}`, `w t = a t − b t⁻¹`
   (`kloosterman_eq_sum_crit`). `#C ≤ 2·p^{m+1}` (`critN_card_le`).

2. **Shift again, one level finer.** For `m ≥ 1` the cube `(p^m z)^3` vanishes mod
   `p^{2m+1}`, so `1 + p^m z` is a unit with inverse `1 − p^m z + (p^m z)^2` (`ushift3`).
   Right multiplication by it *preserves* `C` (`crit_mul_ushift3`: the correction terms
   carry `p^{2m+1}` and `p^{3m+1}`) and multiplies the summand by the phase
   `ψ(p^m z·w t + (p^m z)^2·b t⁻¹)` (`klSummand_mul_ushift3`).

3. **The phase is a quadratic in `z` mod `p`.** On `C` one has `p^m ∣ (w t).val`, so both
   terms carry `p^{2m}` and — via `ψ_{p^{2m+1}}(p^{2m}·c) = ψ_p(c)`
   (`stdAddChar_pow_descend`) — the phase descends to `B z² + C z` on `ZMod p`, with
   `B = b t⁻¹ mod p` a **unit** (forced by membership in `C`; if `p ∣ b` then `C = ∅`).

4. **Average over `z : ZMod p`.** `p·S = ∑_{t ∈ C} ψ(f t)·∑_z ψ(B z² + C z)`, and the inner
   complete quadratic exponential sum has modulus exactly `√p` (`norm_quadExpSum`, proved
   from scratch by squaring + additive orthogonality — no `gaussSum` API needed). Hence
   `p·‖S‖ ≤ 2p^{m+1}·√p`, i.e. `‖S‖ ≤ 2·p^m·√p`.

## The prime-power grade (`norm_kloosterman_prime_pow_gcd`)

For an odd prime `p`, `e ≥ 1` and **arbitrary** naturals `A, B`,

`‖S(A, B; p^e)‖ ≤ 2 · √(p^e) · √((p^e, A, B))`,

i.e. the Estermann grade `c_e · p^{e/2} · (p^e,A,B)^{1/2}` with the **constant `c_e = 2`,
uniformly in `e`** — so `∏_p c_{e_p} = 2^{ω(k)} ≤ d(k)` for the composite assembly (W3).
The four branches: `e = 1` unit (Weil, `norm_kloosterman_prime_unit`); `e` even unit
(`norm_kloosterman_prime_pow_even`); `e` odd `≥ 3` unit (the sharp bound above); and the
non-unit branch, where W1-a's loss-neutral descent (`kloosterman_descent`) trades one power
of `p` in the modulus against exactly one power of `p` in the gcd.
-/

namespace Salt.Weil

open scoped BigOperators
open ComplexConjugate Finset

/-! ### The cubic shift family `1 + p^j z` -/

/-- `(p^j)^3 = 0` in `ZMod (p^k)` whenever `k ≤ 3j`. -/
lemma pj_cube_eq_zero {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 3 * j) :
    ((p : ZMod (p ^ k)) ^ j) ^ 3 = 0 := by
  rw [← pow_mul, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p (by omega)

/-- The **Salié shift unit** `1 + p^j z ∈ (ZMod (p^k))ˣ` at the level where only the *cube*
of `p^j z` vanishes (`k ≤ 3j`): the inverse is the truncated geometric series
`1 − p^j z + (p^j z)^2`. Compare `ushiftN` (`Salt.Weil.CompositeFull`), which needs the
*square* to vanish and therefore loses the second-order term this file exploits. -/
def ushift3 {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 3 * j) (z : ZMod (p ^ k)) :
    (ZMod (p ^ k))ˣ where
  val := 1 + (p : ZMod (p ^ k)) ^ j * z
  inv := 1 - (p : ZMod (p ^ k)) ^ j * z + ((p : ZMod (p ^ k)) ^ j * z) ^ 2
  val_inv := by
    have h3 : ((p : ZMod (p ^ k)) ^ j * z) ^ 3 = 0 := by
      have h := pj_cube_eq_zero (p := p) (k := k) (j := j) hkj
      calc ((p : ZMod (p ^ k)) ^ j * z) ^ 3 = ((p : ZMod (p ^ k)) ^ j) ^ 3 * z ^ 3 := by ring
        _ = 0 := by rw [h, zero_mul]
    have e : (1 + (p : ZMod (p ^ k)) ^ j * z)
        * (1 - (p : ZMod (p ^ k)) ^ j * z + ((p : ZMod (p ^ k)) ^ j * z) ^ 2)
        = 1 + ((p : ZMod (p ^ k)) ^ j * z) ^ 3 := by ring
    rw [e, h3, add_zero]
  inv_val := by
    have h3 : ((p : ZMod (p ^ k)) ^ j * z) ^ 3 = 0 := by
      have h := pj_cube_eq_zero (p := p) (k := k) (j := j) hkj
      calc ((p : ZMod (p ^ k)) ^ j * z) ^ 3 = ((p : ZMod (p ^ k)) ^ j) ^ 3 * z ^ 3 := by ring
        _ = 0 := by rw [h, zero_mul]
    have e : (1 - (p : ZMod (p ^ k)) ^ j * z + ((p : ZMod (p ^ k)) ^ j * z) ^ 2)
        * (1 + (p : ZMod (p ^ k)) ^ j * z)
        = 1 + ((p : ZMod (p ^ k)) ^ j * z) ^ 3 := by ring
    rw [e, h3, add_zero]

@[simp] lemma ushift3_val {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 3 * j) (z : ZMod (p ^ k)) :
    ((ushift3 hkj z : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = 1 + (p : ZMod (p ^ k)) ^ j * z := rfl

@[simp] lemma ushift3_inv_val {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 3 * j)
    (z : ZMod (p ^ k)) :
    (((ushift3 hkj z)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
      = 1 - (p : ZMod (p ^ k)) ^ j * z + ((p : ZMod (p ^ k)) ^ j * z) ^ 2 := rfl

/-! ### The Kloosterman summand and the Salié phase increment -/

/-- The Kloosterman summand `ψ(a t + b t⁻¹)`. -/
noncomputable def klSummand {N : ℕ} [NeZero N] (a b : ZMod N) (t : (ZMod N)ˣ) : ℂ :=
  ZMod.stdAddChar (a * (t : ZMod N) + b * ((t⁻¹ : (ZMod N)ˣ) : ZMod N))

lemma norm_klSummand {N : ℕ} [NeZero N] (a b : ZMod N) (t : (ZMod N)ˣ) :
    ‖klSummand a b t‖ = 1 := AddChar.norm_apply _ _

/-- The **Salié phase increment**: replacing `t` by `t·(1 + X)` multiplies the summand by
`ψ(X·w t + X²·(b t⁻¹))`, where `w t = a t − b t⁻¹` is `wexprGen`. -/
def salieShift {N : ℕ} (a b : ZMod N) (t : (ZMod N)ˣ) (X : ZMod N) : ZMod N :=
  X * wexprGen a b t + X ^ 2 * (b * ((t⁻¹ : (ZMod N)ˣ) : ZMod N))

/-- Restatement of `kloosterman_eq_sum_crit` in terms of `klSummand`. -/
lemma kloosterman_eq_sum_crit' {p k j : ℕ} [Fact p.Prime] (hkj : k ≤ 2 * j)
    (a b : ZMod (p ^ k)) :
    kloosterman a b
      = ∑ t : (ZMod (p ^ k))ˣ,
          (if (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0 then klSummand a b t else 0) :=
  kloosterman_eq_sum_crit hkj a b

/-- The summand under the cubic shift: `f(t·u_z) = f(t)·ψ(salieShift)`. -/
lemma klSummand_mul_ushift3 {p k j : ℕ} [Fact p.Prime] [NeZero (p ^ k)] (hkj : k ≤ 3 * j)
    (a b : ZMod (p ^ k)) (t : (ZMod (p ^ k))ˣ) (z : ZMod (p ^ k)) :
    klSummand a b (t * ushift3 hkj z)
      = klSummand a b t
        * ZMod.stdAddChar (salieShift a b t ((p : ZMod (p ^ k)) ^ j * z)) := by
  simp only [klSummand, salieShift, wexprGen, Units.val_mul, mul_inv_rev, ushift3_val,
    ushift3_inv_val]
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- **The critical set is shift-invariant.** The correction terms produced by
`t ↦ t·(1 + p^j z)` carry `p^{2j}` and `p^{3j}`, both killed by the outer `p^{j+1}` once
`p^{j+1}·p^j = 0`. -/
lemma crit_mul_ushift3 {p k j : ℕ} [Fact p.Prime] [NeZero (p ^ k)] (hkj : k ≤ 3 * j)
    (hkill : (p : ZMod (p ^ k)) ^ (j + 1) * (p : ZMod (p ^ k)) ^ j = 0)
    (a b : ZMod (p ^ k)) (t : (ZMod (p ^ k))ˣ) (z : ZMod (p ^ k)) :
    (p : ZMod (p ^ k)) ^ (j + 1) * wexprGen a b (t * ushift3 hkj z)
      = (p : ZMod (p ^ k)) ^ (j + 1) * wexprGen a b t := by
  have hQX : (p : ZMod (p ^ k)) ^ (j + 1) * ((p : ZMod (p ^ k)) ^ j * z) = 0 := by
    rw [← mul_assoc, hkill, zero_mul]
  simp only [wexprGen, Units.val_mul, mul_inv_rev, ushift3_val, ushift3_inv_val]
  linear_combination
    ((a * ((t : ZMod (p ^ k))) + b * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
      - (p : ZMod (p ^ k)) ^ j * z
        * (b * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))) * hQX

/-! ### The complete quadratic exponential sum mod `p` -/

/-- **The quadratic Gauss sum, magnitude form.** For an odd prime `p`, a unit `B` and any
`C`, `‖∑_{z ∈ ZMod p} e_p(B z² + C z)‖ = √p`.

Proved from scratch by the standard squaring trick: `T · conj T` becomes, after the
substitution `z ↦ y + h`, `∑_h e_p(Bh² + Ch)·∑_y e_p(2Bh·y)`, and additive orthogonality
kills every `h ≠ 0` because `2B` is a unit. This is the single non-elementary input the
sharp Salié bound needs, and it needs no `gaussSum` machinery. -/
theorem norm_quadExpSum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B : ZMod p} (hB : B ≠ 0)
    (C : ZMod p) :
    ‖∑ z : ZMod p, (ZMod.stdAddChar (B * z ^ 2 + C * z) : ℂ)‖ = Real.sqrt p := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hR : 0 < ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne p)
  have hconj : ∀ x : ZMod p, conj (ZMod.stdAddChar x : ℂ) = ZMod.stdAddChar (-x) := fun x => by
    rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  -- `2 ≠ 0` in `ZMod p`
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have hcast : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_num
    rw [hcast]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h)
  set T : ℂ := ∑ z : ZMod p, (ZMod.stdAddChar (B * z ^ 2 + C * z) : ℂ) with hT
  have key : T * conj T = (p : ℂ) := by
    -- expand and substitute `z = y + h`
    have h1 : T * conj T
        = ∑ y : ZMod p, ∑ h : ZMod p,
            ((ZMod.stdAddChar (B * (y + h) ^ 2 + C * (y + h)) : ℂ)
              * conj (ZMod.stdAddChar (B * y ^ 2 + C * y) : ℂ)) := by
      rw [hT, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.sum_mul]
      exact (Fintype.sum_equiv (Equiv.addLeft y)
        (fun h => (ZMod.stdAddChar (B * (y + h) ^ 2 + C * (y + h)) : ℂ)
          * conj (ZMod.stdAddChar (B * y ^ 2 + C * y) : ℂ))
        (fun z => (ZMod.stdAddChar (B * z ^ 2 + C * z) : ℂ)
          * conj (ZMod.stdAddChar (B * y ^ 2 + C * y) : ℂ))
        (fun x => by simp)).symm
    -- factor each summand
    have h2 : ∀ y h : ZMod p,
        ((ZMod.stdAddChar (B * (y + h) ^ 2 + C * (y + h)) : ℂ)
          * conj (ZMod.stdAddChar (B * y ^ 2 + C * y) : ℂ))
        = (ZMod.stdAddChar (B * h ^ 2 + C * h) : ℂ)
            * ZMod.stdAddChar (y * (2 * B * h)) := by
      intro y h
      rw [hconj, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
      congr 1
      ring
    -- orthogonality in `y`
    have horth : ∀ h : ZMod p,
        (∑ y : ZMod p, (ZMod.stdAddChar (y * (2 * B * h)) : ℂ))
          = if (2 * B * h) = 0 then (p : ℂ) else 0 := by
      intro h
      rw [AddChar.sum_mulShift (2 * B * h) (ZMod.isPrimitive_stdAddChar p), ZMod.card]
      split_ifs <;> simp
    have hz : ∀ h : ZMod p, (2 * B * h = 0) ↔ h = 0 := by
      intro h
      constructor
      · intro hh
        rcases mul_eq_zero.mp hh with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' h2ne
          · exact absurd h'' hB
        · exact h'
      · rintro rfl; ring
    calc T * conj T
        = ∑ y : ZMod p, ∑ h : ZMod p,
            ((ZMod.stdAddChar (B * h ^ 2 + C * h) : ℂ)
              * ZMod.stdAddChar (y * (2 * B * h))) := by
          rw [h1]; exact Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun h _ => h2 y h))
      _ = ∑ h : ZMod p, (ZMod.stdAddChar (B * h ^ 2 + C * h) : ℂ)
            * (∑ y : ZMod p, (ZMod.stdAddChar (y * (2 * B * h)) : ℂ)) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun h _ => (Finset.mul_sum _ _ _).symm)
      _ = ∑ h : ZMod p,
            (if h = 0 then (ZMod.stdAddChar (B * h ^ 2 + C * h) : ℂ) * (p : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun h _ => ?_)
          rw [horth h]
          by_cases hh : h = 0
          · rw [if_pos ((hz h).mpr hh), if_pos hh]
          · rw [if_neg (fun hcon => hh ((hz h).mp hcon)), if_neg hh, mul_zero]
      _ = (p : ℂ) := by simp
  have hnorm : ‖T‖ ^ 2 = (p : ℝ) := by
    have h := key
    rw [Complex.mul_conj'] at h
    exact_mod_cast h
  rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]

/-! ### The reduction `ZMod (p^k) → ZMod p` and unit detection -/

/-- `x` is a non-unit of `ZMod (p^k)` exactly when it reduces to `0` mod `p`. -/
lemma castHom_eq_zero_iff_not_isUnit {p k : ℕ} [Fact p.Prime] (hk : k ≠ 0) (x : ZMod (p ^ k)) :
    ZMod.castHom (dvd_pow_self p hk) (ZMod p) x = 0 ↔ ¬ IsUnit x := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [isUnit_of_prime_pow_iff (by omega : 1 ≤ k) x, not_not, ZMod.castHom_apply,
    ← ZMod.natCast_val x, ZMod.natCast_eq_zero_iff]

/-! ### W1-c — the sharp odd-exponent Salié bound -/

/-- **W1-c (THE stone): the sharp odd prime-power Kloosterman bound.** For an odd prime `p`,
`m ≥ 1`, a **unit** `a` and *any* `b`,

`‖S(a, b; p^{2m+1})‖ ≤ 2·p^m·√p = 2·√(p^{2m+1})`.

This is the Salié evaluation carried out to second order; it improves
`norm_kloosterman_prime_pow_odd` (the crude `2·p^{m+1}`) by the full factor `√p` that the
road's budget (`θ ≤ 1/50`) requires. See the module docstring for the four steps. -/
theorem norm_kloosterman_prime_pow_odd_sharp {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hm : 1 ≤ m) {a b : ZMod (p ^ (2 * m + 1))} (ha : IsUnit a) :
    ‖kloosterman a b‖ ≤ 2 * (p : ℝ) ^ m * Real.sqrt p := by
  classical
  have hprime : p.Prime := Fact.out
  haveI hp0 : NeZero p := ⟨hprime.ne_zero⟩
  haveI hNz : NeZero (p ^ (2 * m + 1)) := ⟨pow_ne_zero _ hprime.ne_zero⟩
  have hc3 : 2 * m + 1 ≤ 3 * m := by omega
  have hc2 : 2 * m + 1 ≤ 2 * (m + 1) := by omega
  have hkill : (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * (p : ZMod (p ^ (2 * m + 1))) ^ m = 0 := by
    rw [← pow_add, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p (by omega)
  -- Step 1+2: the shifted localisation, one identity per `z : ZMod p`.
  have hshift : ∀ z : ZMod p,
      kloosterman a b = ∑ t : (ZMod (p ^ (2 * m + 1)))ˣ,
        (if (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
          then klSummand a b t
            * ZMod.stdAddChar (salieShift a b t
                ((p : ZMod (p ^ (2 * m + 1))) ^ m
                  * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))))
          else 0) := by
    intro z
    rw [kloosterman_eq_sum_crit' (j := m + 1) hc2 a b]
    have hre : ∀ G : (ZMod (p ^ (2 * m + 1)))ˣ → ℂ,
        ∑ t, G t = ∑ t, G (t * ushift3 hc3 ((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))) :=
      fun G => Fintype.sum_bijective
        (· * (ushift3 hc3 ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))⁻¹)
        (Equiv.mulRight (ushift3 hc3 ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))⁻¹).bijective G
        (fun t => G (t * ushift3 hc3 ((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))))
        (fun t => by rw [mul_assoc, inv_mul_cancel, mul_one])
    rw [hre]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hP : (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
    · have hP' : (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1)
          * wexprGen a b (t * ushift3 hc3 ((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))) = 0 := by
        rw [crit_mul_ushift3 hc3 hkill a b t]; exact hP
      rw [if_pos hP', if_pos hP, klSummand_mul_ushift3 hc3 a b t]
    · have hP' : ¬ ((p : ZMod (p ^ (2 * m + 1))) ^ (m + 1)
          * wexprGen a b (t * ushift3 hc3 ((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))) = 0) := by
        rw [crit_mul_ushift3 hc3 hkill a b t]; exact hP
      rw [if_neg hP', if_neg hP]
  -- Step 4a: average the identity over `z : ZMod p`.
  have hsum : (p : ℂ) * kloosterman a b
      = ∑ t : (ZMod (p ^ (2 * m + 1)))ˣ,
        (if (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
          then klSummand a b t
            * (∑ z : ZMod p, (ZMod.stdAddChar (salieShift a b t
                ((p : ZMod (p ^ (2 * m + 1))) ^ m
                  * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))) : ℂ))
          else 0) := by
    have h1 : (p : ℂ) * kloosterman a b = ∑ _z : ZMod p, kloosterman a b := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [h1, Finset.sum_congr rfl (fun z _ => hshift z), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hP : (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
    · simp only [if_pos hP, ← Finset.mul_sum]
    · simp only [if_neg hP, Finset.sum_const, smul_zero]
  -- Step 3: the inner sum is a quadratic Gauss sum on the critical set.
  have hinner : ∀ t : (ZMod (p ^ (2 * m + 1)))ˣ,
      (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0 →
      ‖∑ z : ZMod p, (ZMod.stdAddChar (salieShift a b t
          ((p : ZMod (p ^ (2 * m + 1))) ^ m
            * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))) : ℂ)‖ ≤ Real.sqrt p := by
    intro t hcrit
    set π : ZMod (p ^ (2 * m + 1)) →+* ZMod p :=
      ZMod.castHom (dvd_pow_self p (by omega : 2 * m + 1 ≠ 0)) (ZMod p) with hπ
    -- `w t` has `p^m ∣ val`, so write `w t = p^m · c`
    have hdvd : p ^ m ∣ (wexprGen a b t).val := by
      have h0 : ((p ^ (m + 1) * (wexprGen a b t).val : ℕ) : ZMod (p ^ (2 * m + 1))) = 0 := by
        have hEq : ((p ^ (m + 1) * (wexprGen a b t).val : ℕ) : ZMod (p ^ (2 * m + 1)))
            = (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t := by
          push_cast
          rw [ZMod.natCast_zmod_val]
        rw [hEq, hcrit]
      rw [ZMod.natCast_eq_zero_iff] at h0
      have h1 : p ^ (m + 1) * p ^ m ∣ p ^ (m + 1) * (wexprGen a b t).val := by
        have he : p ^ (m + 1) * p ^ m = p ^ (2 * m + 1) := by rw [← pow_add]; congr 1; omega
        rw [he]; exact h0
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hprime.pos (m + 1))).mp h1
    obtain ⟨c, hc⟩ := hdvd
    have hw : wexprGen a b t = ((p ^ m * c : ℕ) : ZMod (p ^ (2 * m + 1))) := by
      rw [← hc, ZMod.natCast_zmod_val]
    -- `b · t⁻¹` reduces to a unit mod `p` (else the critical set is empty)
    have hBne : π (b * ((t⁻¹ : (ZMod (p ^ (2 * m + 1)))ˣ) : ZMod (p ^ (2 * m + 1)))) ≠ 0 := by
      intro hB0
      -- then `w t` reduces to `π a · π t ≠ 0`, contradicting `p ∣ (w t).val`
      have hwz : π (wexprGen a b t) = 0 := by
        rw [hw, hπ, map_natCast, ZMod.natCast_eq_zero_iff]
        exact Dvd.dvd.mul_right (dvd_pow_self p (by omega : m ≠ 0)) c
      have hexp : π (wexprGen a b t)
          = π a * π ((t : ZMod (p ^ (2 * m + 1))))
            - π (b * ((t⁻¹ : (ZMod (p ^ (2 * m + 1)))ˣ) : ZMod (p ^ (2 * m + 1)))) := by
        simp only [wexprGen, map_sub, map_mul]
      rw [hexp, hB0, sub_zero] at hwz
      have hau : π a ≠ 0 := by
        rw [hπ]
        intro h
        exact ((castHom_eq_zero_iff_not_isUnit (by omega) a).mp h) ha
      have htu : π ((t : ZMod (p ^ (2 * m + 1)))) ≠ 0 := by
        rw [hπ]
        intro h
        exact ((castHom_eq_zero_iff_not_isUnit (by omega) _).mp h) (Units.isUnit t)
      rcases mul_eq_zero.mp hwz with h' | h'
      · exact hau h'
      · exact htu h'
    -- rewrite the phase as `p^{2m} · Y`, then descend to `ZMod p`
    have hphase : ∀ z : ZMod p,
        (ZMod.stdAddChar (salieShift a b t
            ((p : ZMod (p ^ (2 * m + 1))) ^ m
              * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))) : ℂ)
          = ZMod.stdAddChar
              ((π (b * ((t⁻¹ : (ZMod (p ^ (2 * m + 1)))ˣ) : ZMod (p ^ (2 * m + 1))))) * z ^ 2
                + ((c : ℕ) : ZMod p) * z) := by
      intro z
      set Y : ZMod (p ^ (2 * m + 1)) :=
        ((c : ℕ) : ZMod (p ^ (2 * m + 1))) * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))
          + ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))) ^ 2
            * (b * ((t⁻¹ : (ZMod (p ^ (2 * m + 1)))ˣ) : ZMod (p ^ (2 * m + 1)))) with hY
      have hpow2 : ((p ^ (2 * m) : ℕ) : ZMod (p ^ (2 * m + 1)))
          = (p : ZMod (p ^ (2 * m + 1))) ^ m * (p : ZMod (p ^ (2 * m + 1))) ^ m := by
        rw [← pow_add, show m + m = 2 * m from by omega, Nat.cast_pow]
      have hstep : salieShift a b t
          ((p : ZMod (p ^ (2 * m + 1))) ^ m * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))
          = ((p ^ (2 * m) * Y.val : ℕ) : ZMod (p ^ (2 * m + 1))) := by
        rw [Nat.cast_mul, hpow2, ZMod.natCast_zmod_val, salieShift, hw, hY]
        push_cast
        ring
      rw [hstep, stdAddChar_pow_descend (p := p) (n := 2 * m) (c := Y.val)]
      congr 1
      have hYred : ((Y.val : ℕ) : ZMod p) = π Y := by
        rw [hπ, ZMod.castHom_apply, ZMod.natCast_val]
      rw [hYred, hY, map_add, map_mul, map_mul, map_pow]
      have hzz : π (((z.val : ℕ) : ZMod (p ^ (2 * m + 1)))) = z := by
        rw [hπ, map_natCast, ZMod.natCast_zmod_val]
      have hcc : π (((c : ℕ) : ZMod (p ^ (2 * m + 1)))) = ((c : ℕ) : ZMod p) := by
        rw [hπ, map_natCast]
      rw [hzz, hcc]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hphase z)]
    exact le_of_eq (norm_quadExpSum hp2 hBne _)
  -- Step 4b: assemble.
  have hcard := critN_card_le (p := p) (k := 2 * m + 1) (j := m + 1) hp2 (by omega) (b := b) ha
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt p := Real.sqrt_nonneg _
  have hbound : (p : ℝ) * ‖kloosterman a b‖ ≤ 2 * (p : ℝ) ^ (m + 1) * Real.sqrt p := by
    have h1 : (p : ℝ) * ‖kloosterman a b‖ = ‖(p : ℂ) * kloosterman a b‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [h1, hsum]
    calc ‖∑ t : (ZMod (p ^ (2 * m + 1)))ˣ,
            (if (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
              then klSummand a b t
                * (∑ z : ZMod p, (ZMod.stdAddChar (salieShift a b t
                    ((p : ZMod (p ^ (2 * m + 1))) ^ m
                      * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))) : ℂ))
              else 0)‖
        ≤ ∑ t : (ZMod (p ^ (2 * m + 1)))ˣ,
            ‖(if (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
              then klSummand a b t
                * (∑ z : ZMod p, (ZMod.stdAddChar (salieShift a b t
                    ((p : ZMod (p ^ (2 * m + 1))) ^ m
                      * ((z.val : ℕ) : ZMod (p ^ (2 * m + 1))))) : ℂ))
              else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ t : (ZMod (p ^ (2 * m + 1)))ˣ,
            (if (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
              then Real.sqrt p else 0) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          by_cases hP : (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0
          · rw [if_pos hP, if_pos hP, norm_mul, norm_klSummand, one_mul]
            exact hinner t hP
          · rw [if_neg hP, if_neg hP, norm_zero]
      _ = ((Finset.univ.filter (fun t : (ZMod (p ^ (2 * m + 1)))ˣ =>
              (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0)).card : ℝ)
            * Real.sqrt p := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (p : ℝ) ^ (m + 1) * Real.sqrt p := by
          have hle : ((Finset.univ.filter (fun t : (ZMod (p ^ (2 * m + 1)))ˣ =>
              (p : ZMod (p ^ (2 * m + 1))) ^ (m + 1) * wexprGen a b t = 0)).card : ℝ)
              ≤ 2 * (p : ℝ) ^ (m + 1) := by
            have h2 : ((2 * p ^ (m + 1) : ℕ) : ℝ) = 2 * (p : ℝ) ^ (m + 1) := by push_cast; ring
            rw [← h2]; exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hle hsqrt_nonneg
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  refine le_of_mul_le_mul_left ?_ hp_pos
  calc (p : ℝ) * ‖kloosterman a b‖ ≤ 2 * (p : ℝ) ^ (m + 1) * Real.sqrt p := hbound
    _ = (p : ℝ) * (2 * (p : ℝ) ^ m * Real.sqrt p) := by rw [pow_succ]; ring

/-! ### W1-c-final — the Estermann grade at a prime-power modulus -/

/-- **The unit branch at the sharp constant.** For an odd prime `p`, `e ≥ 1` and a unit `a`
(any `b`), `‖S(a, b; p^e)‖ ≤ 2·√(p^e)`. Assembled from Weil at `e = 1`
(`norm_kloosterman_prime_pow_one_unit`), the even Salié evaluation
(`norm_kloosterman_prime_pow_even`) and W1-c (`norm_kloosterman_prime_pow_odd_sharp`). -/
theorem norm_kloosterman_prime_pow_unit_sharp {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) {a b : ZMod (p ^ e)} (ha : IsUnit a) :
    ‖kloosterman a b‖ ≤ 2 * Real.sqrt ((p : ℝ) ^ e) := by
  have hprime : p.Prime := Fact.out
  have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rcases Nat.even_or_odd e with hev | hod
  · obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m := by
      obtain ⟨m, hm⟩ := hev; exact ⟨m, by omega⟩
    have hm : 1 ≤ m := by omega
    have hsq : Real.sqrt ((p : ℝ) ^ (2 * m)) = (p : ℝ) ^ m := by
      rw [pow_mul']
      exact Real.sqrt_sq (by positivity)
    rw [hsq]
    exact norm_kloosterman_prime_pow_even hp2 hm ha
  · obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m + 1 := by
      obtain ⟨m, hm⟩ := hod; exact ⟨m, by omega⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- `e = 1`: Weil
      have hsq : Real.sqrt ((p : ℝ) ^ (2 * 0 + 1)) = Real.sqrt p := by norm_num
      rw [hsq]
      exact norm_kloosterman_prime_pow_one_unit ha
    · have hsq : Real.sqrt ((p : ℝ) ^ (2 * m + 1)) = (p : ℝ) ^ m * Real.sqrt p := by
        rw [pow_succ, Real.sqrt_mul (by positivity), pow_mul']
        rw [Real.sqrt_sq (by positivity)]
      rw [hsq, ← mul_assoc]
      exact norm_kloosterman_prime_pow_odd_sharp hp2 hm ha

/-- **W1-c-final — the Estermann grade at a prime-power modulus.** For an odd prime `p`,
`e ≥ 1` and **arbitrary** naturals `A`, `B`,

`‖S(A, B; p^e)‖ ≤ 2 · √(p^e) · √((p^e, A, B))`.

The constant is `c_e = 2` **uniformly in `e`**, so the composite assembly (W3) inherits
`∏_p c_{e_p} = 2^{ω(k)} ≤ d(k)` — exactly the Estermann shape
`d(k)·k^{1/2}·(k,u,v)^{1/2}` that HB 1983 (7.1) demands. There is no `IsUnit` hypothesis:
the non-unit branch runs W1-a's loss-neutral descent (`kloosterman_descent`), which trades
one power of `p` in the modulus against exactly one power of `p` in the gcd.

N7 quotes this as the odd-prime-power input to the composite Estermann bound. -/
theorem norm_kloosterman_prime_pow_gcd {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∀ e : ℕ, 1 ≤ e → ∀ A B : ℕ,
      ‖kloosterman ((A : ℕ) : ZMod (p ^ e)) ((B : ℕ) : ZMod (p ^ e))‖
        ≤ 2 * Real.sqrt ((p : ℝ) ^ e)
            * Real.sqrt ((Nat.gcd (p ^ e) (Nat.gcd A B) : ℕ) : ℝ) := by
  have hprime : p.Prime := Fact.out
  intro e
  induction e using Nat.strong_induction_on with
  | _ e IH =>
    intro he A B
    haveI hNz : NeZero (p ^ e) := ⟨pow_ne_zero _ hprime.ne_zero⟩
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    -- the unit branch: gcd collapses to `1`
    have unitBranch : ∀ A B : ℕ, ¬ p ∣ A →
        ‖kloosterman ((A : ℕ) : ZMod (p ^ e)) ((B : ℕ) : ZMod (p ^ e))‖
          ≤ 2 * Real.sqrt ((p : ℝ) ^ e)
              * Real.sqrt ((Nat.gcd (p ^ e) (Nat.gcd A B) : ℕ) : ℝ) := by
      intro A B hA
      have hcop : Nat.gcd (p ^ e) (Nat.gcd A B) = 1 := by
        have h1 : Nat.Coprime p (Nat.gcd A B) := by
          rw [Nat.Prime.coprime_iff_not_dvd hprime]
          intro hdd
          exact hA (hdd.trans (Nat.gcd_dvd_left A B))
        exact Nat.Coprime.pow_left e h1
      rw [hcop]
      simp only [Nat.cast_one, Real.sqrt_one, mul_one]
      exact norm_kloosterman_prime_pow_unit_sharp hp2 he
        (ZMod.isUnit_natCast_iff_not_dvd_pow hprime (by omega) |>.mpr hA)
    have hppos : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg p
    have hpp : Real.sqrt ((p : ℕ) : ℝ) * Real.sqrt ((p : ℕ) : ℝ) = (p : ℝ) := by
      rw [← Real.sqrt_mul hppos, ← pow_two, Real.sqrt_sq hppos]
    by_cases hA : p ∣ A
    · by_cases hB : p ∣ B
      · -- both non-units
        rcases Nat.lt_or_ge e 2 with h1 | h2
        · -- `e = 1`: the trivial bound `φ(p) ≤ p = 2·√p·√p / 2`
          have he1 : e = 1 := by omega
          subst he1
          have hg1 : Nat.gcd (p ^ 1) (Nat.gcd A B) = p := by
            rw [pow_one]
            exact Nat.gcd_eq_left (Nat.dvd_gcd hA hB)
          rw [hg1]
          have hlhs : ‖kloosterman ((A : ℕ) : ZMod (p ^ 1)) ((B : ℕ) : ZMod (p ^ 1))‖
              ≤ ((p : ℝ)) := by
            refine (norm_kloosterman_le _ _).trans ?_
            rw [ZMod.card_units_eq_totient]
            have h := Nat.totient_le (p ^ 1)
            have hc : (((p ^ 1).totient : ℕ) : ℝ) ≤ ((p ^ 1 : ℕ) : ℝ) := by exact_mod_cast h
            refine hc.trans (le_of_eq ?_)
            push_cast
            ring
          refine hlhs.trans ?_
          have hs : Real.sqrt ((p : ℝ) ^ 1) = Real.sqrt ((p : ℕ) : ℝ) := by
            congr 1
            ring
          rw [hs]
          nlinarith [hpp, Real.sqrt_nonneg ((p : ℕ) : ℝ)]
        · -- `e ≥ 2`: the descent
          obtain ⟨A', rfl⟩ := hA
          obtain ⟨B', rfl⟩ := hB
          obtain ⟨f, rfl⟩ : ∃ f, e = f + 1 := ⟨e - 1, by omega⟩
          have hf : 1 ≤ f := by omega
          have hIH := IH f (by omega) (by omega) A' B'
          have hgcd' : Nat.gcd (p ^ (f + 1)) (Nat.gcd (p * A') (p * B'))
              = p * Nat.gcd (p ^ f) (Nat.gcd A' B') := by
            rw [Nat.gcd_mul_left p A' B', pow_succ']
            exact Nat.gcd_mul_left p (p ^ f) (Nat.gcd A' B')
          rw [kloosterman_descent hf A' B', norm_mul, Complex.norm_natCast, hgcd']
          have hsplit : Real.sqrt ((p * Nat.gcd (p ^ f) (Nat.gcd A' B') : ℕ) : ℝ)
              = Real.sqrt ((p : ℕ) : ℝ)
                * Real.sqrt ((Nat.gcd (p ^ f) (Nat.gcd A' B') : ℕ) : ℝ) := by
            rw [Nat.cast_mul, Real.sqrt_mul hppos]
          have hpow : Real.sqrt ((p : ℝ) ^ (f + 1))
              = Real.sqrt ((p : ℝ) ^ f) * Real.sqrt ((p : ℕ) : ℝ) := by
            rw [pow_succ, Real.sqrt_mul (by positivity)]
          rw [hsplit, hpow]
          have hgoal : (p : ℝ) * ‖kloosterman ((A' : ℕ) : ZMod (p ^ f))
              ((B' : ℕ) : ZMod (p ^ f))‖
              ≤ (p : ℝ) * (2 * Real.sqrt ((p : ℝ) ^ f)
                  * Real.sqrt ((Nat.gcd (p ^ f) (Nat.gcd A' B') : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hIH (le_of_lt hp_pos)
          refine hgoal.trans (le_of_eq ?_)
          calc (p : ℝ) * (2 * Real.sqrt ((p : ℝ) ^ f)
                * Real.sqrt ((Nat.gcd (p ^ f) (Nat.gcd A' B') : ℕ) : ℝ))
              = (Real.sqrt ((p : ℕ) : ℝ) * Real.sqrt ((p : ℕ) : ℝ))
                * (2 * Real.sqrt ((p : ℝ) ^ f)
                  * Real.sqrt ((Nat.gcd (p ^ f) (Nat.gcd A' B') : ℕ) : ℝ)) := by rw [hpp]
            _ = 2 * (Real.sqrt ((p : ℝ) ^ f) * Real.sqrt ((p : ℕ) : ℝ))
                * (Real.sqrt ((p : ℕ) : ℝ)
                  * Real.sqrt ((Nat.gcd (p ^ f) (Nat.gcd A' B') : ℕ) : ℝ)) := by ring
      · -- `B` is the unit: swap by symmetry
        rw [kloosterman_comm, Nat.gcd_comm A B]
        exact unitBranch B A hB
    · exact unitBranch A B hA

end Salt.Weil
