/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.CompositeFull
import Mathlib

/-!
# WEIL-TRIO W1 — the gcd branch (`W1-a`, `W1-b`, `W1-d`)

Governing design: `docs/exploration/weil-trio-design-0806.md` (the v2 DELTA, §D1–D2).
This module supplies the *non-unit* half of the Estermann grade
`‖S(a,b;k)‖ ≤ c_k · k^{1/2} · (k,a,b)^{1/2}` at a prime-power modulus, together with
the 2-adic bookkeeping lemma the road (N7) quotes to discharge the `2`-part.

## Contents

* **The level bridge** (`stdAddChar_mul_descend`, `stdAddChar_pow_descend`). The standard
  additive character `ψ_N j = exp(2πi j / N)` descends along a divisor of the modulus:
  `ψ_{p^{f+1}}(p·c) = ψ_{p^f}(c)` and `ψ_{p^{n+1}}(p^n·c) = ψ_p(c)` for a natural `c`.
  Everything else in the file (and the Salié stone in `Salt.Weil.Estermann`) is
  bookkeeping on top of these two identities.

* **W1-a — the gcd descent** (`kloosterman_descent`). For `p ∣ a`, `p ∣ b` and `e ≥ 2`,
  `S(a, b; p^e) = p · S(a/p, b/p; p^{e−1})`.
  This is **loss-neutral** for the target grade: the left side gains a factor `p` and the
  gcd `(p^e, a, b) = p·(p^{e−1}, a/p, b/p)` gains exactly `p^{1/2}` under the square root,
  while `p^{e/2}` loses `p^{1/2}` against `p^{(e−1)/2}` — so the induction carries the
  constant `c_e = 2` through untouched. (Note the descent drops **one** power of `p` from
  the modulus, not two: at `e = 2`, `p = 3`, `a = b = 3` one has `S = −3 = 3·S(1,1;3)`,
  whereas `3·S(1,1;3^0) = 3`.)

* **The localisation identity** (`kloosterman_eq_sum_crit`). The averaging/orthogonality
  step of `norm_kloosterman_prime_pow_ge_two` (`Salt.Weil.CompositeFull`) with the counting
  step removed: for `k ≤ 2j`, `S(a,b;p^k) = ∑_{t : p^j·w t = 0} ψ(a t + b t⁻¹)`, at
  **arbitrary** `a` (no unit hypothesis). Consumed by W1-b here and by the sharp Salié
  bound in `Salt.Weil.Estermann`.

* **W1-b — Ramanujan at prime powers** (`kloosterman_zero_right_prime_pow`,
  `norm_kloosterman_zero_right_prime_pow`). `S(a, 0; p^e) = 0` for a unit `a` and `e ≥ 2`
  (the Ramanujan sum `c_{p^e}(a) = μ(p^e)`), extending `kloosterman_zero_right`'s `e = 1`
  value `−1`.

* **W1-d — the 2-adic bookkeeping** (`factorization_two_mul_odd_mul_odd`,
  `factorization_two_kloosterman_modulus`, `two_pow_factorization_dvd_of_odd_cofactors`).
  Heath-Brown 1983's Kloosterman modulus at (5.11)/(5.12) is `k = D·δ₁·w₁` with
  `D = α₂ q Δ^{−1}`; the support conditions (5.1) `(δ₁,α) = 1` and (5.6) `(w₁,α) = 1`
  together with the standing normalisation (1.5) `2 ∣ α_i` force `δ₁` and `w₁` **odd**,
  so `v₂(k) = v₂(D)` — the whole 2-part of the modulus sits in `D`. This is the lemma
  that killed the W2 (2-adic stationary phase) stone.
-/

namespace Salt.Weil

open scoped BigOperators
open Finset

/-! ### The `stdAddChar` level bridge -/

/-- **The level bridge, one step.** `ψ_{p^{f+1}}(p·c) = ψ_{p^f}(c)` for a natural `c`:
both sides are `exp(2πi c / p^f)`. -/
lemma stdAddChar_mul_descend {p f : ℕ} [NeZero p] [NeZero (p ^ (f + 1))] [NeZero (p ^ f)]
    (c : ℕ) :
    (ZMod.stdAddChar ((p * c : ℕ) : ZMod (p ^ (f + 1))) : ℂ)
      = (ZMod.stdAddChar ((c : ℕ) : ZMod (p ^ f)) : ℂ) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hpf : ((p : ℂ)) ^ f ≠ 0 := pow_ne_zero _ hp
  congr 1
  push_cast [pow_succ]
  field_simp

/-- **The level bridge, full collapse.** `ψ_{p^{n+1}}(p^n·c) = ψ_p(c)` for a natural `c`:
both sides are `exp(2πi c / p)`. This is the identity that turns the second-order term of
the Salié shift into a genuine quadratic Gauss sum mod `p`. -/
lemma stdAddChar_pow_descend {p n : ℕ} [NeZero p] [NeZero (p ^ (n + 1))] (c : ℕ) :
    (ZMod.stdAddChar ((p ^ n * c : ℕ) : ZMod (p ^ (n + 1))) : ℂ)
      = (ZMod.stdAddChar ((c : ℕ) : ZMod p) : ℂ) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, ZMod.toCircle_natCast, ZMod.toCircle_natCast]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hpn : ((p : ℂ)) ^ n ≠ 0 := pow_ne_zero _ hp
  congr 1
  push_cast [pow_succ]
  field_simp

/-! ### Fibres of the prime-power reduction on units -/

/-- Every fibre of `ZMod.unitsMap : (ZMod p^k)ˣ → (ZMod p^j)ˣ` has exactly `p^{k−j}`
elements (`1 ≤ j ≤ k`, `p` prime): the map is surjective, so all fibres share the
cardinality `φ(p^k)/φ(p^j) = p^{k−j}`. -/
lemma unitsMap_prime_pow_fiber_card {p k j : ℕ} [Fact p.Prime] (hjk : j ≤ k) (hj : 1 ≤ j)
    (x : (ZMod (p ^ j))ˣ) :
    (Finset.univ.filter (fun t : (ZMod (p ^ k))ˣ =>
        ZMod.unitsMap (pow_dvd_pow p hjk) t = x)).card = p ^ (k - j) := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ j) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  set ρᵤ : (ZMod (p ^ k))ˣ →* (ZMod (p ^ j))ˣ := ZMod.unitsMap (pow_dvd_pow p hjk) with hρᵤ
  have hsurj : Function.Surjective ρᵤ := by
    rw [hρᵤ]; exact ZMod.unitsMap_surjective (pow_dvd_pow p hjk)
  set K := (univ.filter (fun t : (ZMod (p ^ k))ˣ => ρᵤ t = 1)).card with hKdef
  have hfib : ∀ y : (ZMod (p ^ j))ˣ, (univ.filter (fun t => ρᵤ t = y)).card = K :=
    fun y => MonoidHom.card_fiber_eq_of_mem_range ρᵤ (Set.mem_range.mpr (hsurj y))
      (Set.mem_range.mpr (hsurj 1))
  have hKeq : Fintype.card (ZMod (p ^ k))ˣ = Fintype.card (ZMod (p ^ j))ˣ * K := by
    rw [← Finset.card_univ (α := (ZMod (p ^ k))ˣ),
      Finset.card_eq_sum_card_fiberwise (fun t (_ : t ∈ univ) => mem_univ (ρᵤ t)),
      Finset.sum_congr rfl (fun y _ => hfib y), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hKval : K = p ^ (k - j) := by
    have hexp : p ^ (j - 1) * p ^ (k - j) = p ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    have htot : (p ^ k).totient = (p ^ j).totient * p ^ (k - j) := by
      rw [Nat.totient_prime_pow (Fact.out) (by omega : 0 < k),
        Nat.totient_prime_pow (Fact.out) (by omega : 0 < j), mul_right_comm, hexp]
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at hKeq
    have hpos : 0 < (p ^ j).totient := Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos j)
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [← hKeq, htot])
  rw [hfib x, hKval]

/-! ### W1-a — the gcd descent -/

/-- **W1-a (the gcd descent).** For a prime `p`, `f ≥ 1`, and naturals `A`, `B`,
`S(pA, pB; p^{f+1}) = p · S(A, B; p^f)`.

Both `pA·t` and `pB·t⁻¹` lose one level of the modulus under `ψ_{p^{f+1}}(p·x) = ψ_{p^f}(x)`,
so the summand depends on `t` only through its reduction to `(ZMod p^f)ˣ`; each such
reduction has a fibre of exactly `p` units (`unitsMap_prime_pow_fiber_card`).

Every element of `ZMod (p^{f+1})` divisible by `p` is of the form `(p·A : ℕ)`, so this is
the general "`p` divides both arguments" descent. It is **loss-neutral** for the Estermann
grade — see the module docstring. -/
theorem kloosterman_descent {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f) (A B : ℕ) :
    kloosterman ((p * A : ℕ) : ZMod (p ^ (f + 1))) ((p * B : ℕ) : ZMod (p ^ (f + 1)))
      = (p : ℂ) * kloosterman ((A : ℕ) : ZMod (p ^ f)) ((B : ℕ) : ZMod (p ^ f)) := by
  classical
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ (f + 1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ f) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hdvd : p ^ f ∣ p ^ (f + 1) := pow_dvd_pow p (Nat.le_succ f)
  set ρᵤ : (ZMod (p ^ (f + 1)))ˣ →* (ZMod (p ^ f))ˣ := ZMod.unitsMap hdvd with hρᵤ
  -- the target summand, as a function of the reduced unit
  set g : (ZMod (p ^ f))ˣ → ℂ := fun x =>
    ZMod.stdAddChar (((A : ℕ) : ZMod (p ^ f)) * (x : ZMod (p ^ f))
      + ((B : ℕ) : ZMod (p ^ f)) * ((x⁻¹ : (ZMod (p ^ f))ˣ) : ZMod (p ^ f))) with hg
  -- Step 1: the summand descends.
  have hsum : ∀ t : (ZMod (p ^ (f + 1)))ˣ,
      (ZMod.stdAddChar (((p * A : ℕ) : ZMod (p ^ (f + 1))) * (t : ZMod (p ^ (f + 1)))
        + ((p * B : ℕ) : ZMod (p ^ (f + 1)))
          * ((t⁻¹ : (ZMod (p ^ (f + 1)))ˣ) : ZMod (p ^ (f + 1)))) : ℂ) = g (ρᵤ t) := by
    intro t
    set T := (t : ZMod (p ^ (f + 1))).val with hT
    set U := ((t⁻¹ : (ZMod (p ^ (f + 1)))ˣ) : ZMod (p ^ (f + 1))).val with hU
    have h1 : (t : ZMod (p ^ (f + 1))) = ((T : ℕ) : ZMod (p ^ (f + 1))) :=
      (ZMod.natCast_zmod_val _).symm
    have h2 : ((t⁻¹ : (ZMod (p ^ (f + 1)))ˣ) : ZMod (p ^ (f + 1)))
        = ((U : ℕ) : ZMod (p ^ (f + 1))) := (ZMod.natCast_zmod_val _).symm
    have hL : ((p * A : ℕ) : ZMod (p ^ (f + 1))) * (t : ZMod (p ^ (f + 1)))
        + ((p * B : ℕ) : ZMod (p ^ (f + 1)))
          * ((t⁻¹ : (ZMod (p ^ (f + 1)))ˣ) : ZMod (p ^ (f + 1)))
        = ((p * (A * T + B * U) : ℕ) : ZMod (p ^ (f + 1))) := by
      rw [h1, h2]; push_cast; ring
    rw [hL, stdAddChar_mul_descend]
    -- identify the reduced argument
    have hTred : ((T : ℕ) : ZMod (p ^ f)) = ((ρᵤ t : (ZMod (p ^ f))ˣ) : ZMod (p ^ f)) := by
      rw [hT, ZMod.natCast_val, hρᵤ, ZMod.unitsMap_val]
    have hUred : ((U : ℕ) : ZMod (p ^ f))
        = (((ρᵤ t)⁻¹ : (ZMod (p ^ f))ˣ) : ZMod (p ^ f)) := by
      rw [hU, ZMod.natCast_val, ← map_inv ρᵤ t, hρᵤ, ZMod.unitsMap_val]
    rw [hg]
    congr 1
    push_cast
    rw [hTred, hUred]
  -- Step 2: sum over the fibres of `ρᵤ`.
  unfold kloosterman
  rw [Finset.sum_congr rfl (fun t _ => hsum t)]
  rw [← Finset.sum_fiberwise' (Finset.univ) ρᵤ g]
  have hcard : ∀ x : (ZMod (p ^ f))ˣ,
      (Finset.univ.filter (fun t : (ZMod (p ^ (f + 1)))ˣ => ρᵤ t = x)).card = p := by
    intro x
    have := unitsMap_prime_pow_fiber_card (p := p) (k := f + 1) (j := f)
      (Nat.le_succ f) hf x
    rw [hρᵤ]
    simpa using this
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_const, hcard x, nsmul_eq_mul]

/-! ### The localisation identity -/

/-- **Localisation (averaging + orthogonality), unit-free.** For `k ≤ 2j` and *arbitrary*
`a b : ZMod (p^k)`, the Kloosterman sum collapses onto the critical set
`{t : p^j · w t = 0}`, `w t = a t − b t⁻¹`.

This is the first half of `norm_kloosterman_prime_pow_ge_two`'s proof
(`Salt.Weil.CompositeFull`) with the counting step removed and the `IsUnit a` hypothesis
dropped — the shift family `1 + p^j z` needs only `(p^j)² = 0`. -/
lemma kloosterman_eq_sum_crit {p k j : ℕ} [Fact p.Prime] (hkj : k ≤ 2 * j)
    (a b : ZMod (p ^ k)) :
    kloosterman a b
      = ∑ t : (ZMod (p ^ k))ˣ,
          (if (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0
            then (ZMod.stdAddChar (a * (t : ZMod (p ^ k))
              + b * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) : ℂ)
            else 0) := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  set f : (ZMod (p ^ k))ˣ → ℂ :=
    fun t => ZMod.stdAddChar (a * (t : ZMod (p ^ k))
      + b * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) with hf
  have hkf : kloosterman a b = ∑ t, f t := rfl
  have hterm : ∀ z : ZMod (p ^ k),
      kloosterman a b
        = ∑ t, f t * ZMod.stdAddChar (z * ((p : ZMod (p ^ k)) ^ j * wexprGen a b t)) := by
    intro z
    have hre : ∑ t, f t = ∑ t, f (t * ushiftN hkj z) :=
      Fintype.sum_bijective (· * (ushiftN hkj z)⁻¹) (Equiv.mulRight (ushiftN hkj z)⁻¹).bijective f
        (fun t => f (t * ushiftN hkj z)) (fun t => by rw [mul_assoc, inv_mul_cancel, mul_one])
    rw [hkf, hre]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have harg : a * ((t * ushiftN hkj z : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
        + b * (((t * ushiftN hkj z)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
        = (a * (t : ZMod (p ^ k))
            + b * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
          + z * ((p : ZMod (p ^ k)) ^ j * wexprGen a b t) := by
      rw [Units.val_mul, mul_inv_rev, Units.val_mul, ushiftN_val, ushiftN_inv_val]
      simp only [wexprGen]; ring
    simp only [hf]
    rw [← AddChar.map_add_eq_mul, harg]
  have hAvg : ((p ^ k : ℕ) : ℂ) * kloosterman a b
      = ((p ^ k : ℕ) : ℂ)
        * ∑ t, (if (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0 then f t else 0) := by
    have hL : ((p ^ k : ℕ) : ℂ) * kloosterman a b
        = ∑ _z : ZMod (p ^ k), kloosterman a b := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [hL, Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Finset.mul_sum,
      AddChar.sum_mulShift ((p : ZMod (p ^ k)) ^ j * wexprGen a b t)
        (ZMod.isPrimitive_stdAddChar _), ZMod.card]
    split_ifs with h <;> ring
  have hNe : ((p ^ k : ℕ) : ℂ) ≠ 0 := by
    have : (p : ℕ) ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    exact_mod_cast this
  exact mul_left_cancel₀ hNe hAvg

/-! ### W1-b — Ramanujan at prime powers -/

/-- A prime-power residue is a unit exactly when `p` does not divide its `val`. -/
lemma isUnit_of_prime_pow_iff {p k : ℕ} [Fact p.Prime] (hk : 1 ≤ k) (x : ZMod (p ^ k)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out) (by omega)

/-- `(p : ZMod (p^k))^j ≠ 0` when `j < k` — the "no premature collapse" fact behind the
emptiness of the critical set in the degenerate branches. -/
lemma prime_pow_cast_ne_zero {p k j : ℕ} [Fact p.Prime] (hjk : j < k) :
    ((p : ZMod (p ^ k)) ^ j) ≠ 0 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hcast : (p : ZMod (p ^ k)) ^ j = ((p ^ j : ℕ) : ZMod (p ^ k)) := by push_cast; ring
  rw [hcast]
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt |>.mp h) (by omega)

/-- **W1-b (Ramanujan at prime powers).** For a prime `p`, `e ≥ 2`, and a **unit** `a`,
`S(a, 0; p^e) = 0`.

This is the Ramanujan sum `c_{p^e}(a) = μ(p^e) = 0` for `e ≥ 2`, extending
`kloosterman_zero_right`'s value `−1` at `e = 1`. Proof: localise at `j = e − 1`
(`kloosterman_eq_sum_crit`, legal since `e ≤ 2(e−1)` for `e ≥ 2`); the critical condition
`p^{e−1}·(a t) = 0` is unsatisfiable because `a t` is a unit and `p^{e−1} ≠ 0` in
`ZMod p^e`. -/
theorem kloosterman_zero_right_prime_pow {p e : ℕ} [Fact p.Prime] (he : 2 ≤ e)
    {a : ZMod (p ^ e)} (ha : IsUnit a) : kloosterman a 0 = 0 := by
  classical
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [kloosterman_eq_sum_crit (j := e - 1) (by omega) a 0]
  refine Finset.sum_eq_zero (fun t _ => ?_)
  rw [if_neg]
  intro hcrit
  -- `w t = a t`, a unit, so the product with `p^{e-1} ≠ 0` cannot vanish
  have hw : wexprGen a (0 : ZMod (p ^ e)) t = a * (t : ZMod (p ^ e)) := by
    simp [wexprGen]
  rw [hw] at hcrit
  have hu : IsUnit (a * (t : ZMod (p ^ e))) := ha.mul (Units.isUnit t)
  obtain ⟨v, hv⟩ := hu
  have : (p : ZMod (p ^ e)) ^ (e - 1) = 0 := by
    have h2 := congrArg (· * ((v⁻¹ : (ZMod (p ^ e))ˣ) : ZMod (p ^ e))) hcrit
    simpa [mul_assoc, ← hv, ← Units.val_mul] using h2
  exact prime_pow_cast_ne_zero (p := p) (k := e) (j := e - 1) (by omega) this

/-- **W1-b, norm form.** `‖S(a, 0; p^e)‖ ≤ 1` for a unit `a` and any `e ≥ 1` — the value is
`−1` at `e = 1` (`kloosterman_zero_right`, transported) and `0` beyond. -/
theorem norm_kloosterman_zero_right_prime_pow {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    {a : ZMod (p ^ e)} (ha : IsUnit a) : ‖kloosterman a (0 : ZMod (p ^ e))‖ ≤ 1 := by
  rcases eq_or_lt_of_le he with h1 | h2
  · -- `e = 1`: transport `kloosterman_zero_right` across `p ^ 1 = p`
    have key : ∀ N : ℕ, N = p ^ e → ∀ [NeZero N] (x : ZMod N), IsUnit x →
        ‖kloosterman x (0 : ZMod N)‖ ≤ 1 := by
      intro N hN
      subst hN
      rw [← h1, pow_one] at *
      intro _ x hx
      haveI : Fact p.Prime := ‹_›
      rw [kloosterman_zero_right hx, norm_neg, norm_one]
    haveI : NeZero (p ^ e) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    exact key (p ^ e) rfl a ha
  · rw [kloosterman_zero_right_prime_pow (by omega) ha, norm_zero]; norm_num

/-! ### W1-d — the 2-adic bookkeeping (HB (5.1)/(5.6) + (1.5)) -/

/-- Coprimality to an **even** modulus forces oddness: HB's (1.5) `2 ∣ α_i` turns
(5.1) `(δ₁,α) = 1` and (5.6) `(w₁,α) = 1` into "`δ₁`, `w₁` are odd". -/
theorem odd_of_coprime_of_two_dvd {n α : ℕ} (hα : 2 ∣ α) (h : Nat.Coprime n α) : Odd n := by
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have : (2 : ℕ) ∣ Nat.gcd n α := Nat.dvd_gcd h2 hα
  rw [Nat.Coprime] at h
  rw [h] at this
  omega

/-- **W1-d (core).** `v₂(D · d · w) = v₂(D)` when `d` and `w` are odd (and `D ≠ 0`). -/
theorem factorization_two_mul_odd_mul_odd {D d w : ℕ} (hD : D ≠ 0) (hd : Odd d) (hw : Odd w) :
    (D * d * w).factorization 2 = D.factorization 2 := by
  have hd' : d % 2 = 1 := Nat.odd_iff.mp hd
  have hw' : w % 2 = 1 := Nat.odd_iff.mp hw
  have hd0 : d ≠ 0 := by omega
  have hw0 : w ≠ 0 := by omega
  have hd2 : d.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  have hw2 : w.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by omega)
  rw [Nat.factorization_mul (Nat.mul_ne_zero hD hd0) hw0, Nat.factorization_mul hD hd0]
  simp [hd2, hw2]

/-- **W1-d (the form N7 quotes).** Heath-Brown 1983, §5: the Kloosterman modulus at the
Lemma-10 application (p.214) is `k = D·δ₁·w₁` with `D = α₂ q Δ^{−1}` ((5.12)). The support
condition (5.1) gives `(δ₁, α) = 1`, the congruence condition (5.6) gives `(w₁, α) = 1`, and
the standing normalisation (1.5) gives `2 ∣ α`. Hence

`v₂(D · δ₁ · w₁) = v₂(D)`

— the entire 2-part of the Kloosterman modulus sits in `D`, and the road's 2-adic factor is
bounded by `2^{v₂(D)/2}` with no 2-adic stationary-phase analysis. (This is the lemma that
retired the W2 stone; see `docs/exploration/weil-trio-design-0806.md` §D2.) -/
theorem factorization_two_kloosterman_modulus {D δ₁ w₁ α : ℕ} (hD : D ≠ 0) (hα : 2 ∣ α)
    (hδ : Nat.Coprime δ₁ α) (hw : Nat.Coprime w₁ α) :
    (D * δ₁ * w₁).factorization 2 = D.factorization 2 :=
  factorization_two_mul_odd_mul_odd hD (odd_of_coprime_of_two_dvd hα hδ)
    (odd_of_coprime_of_two_dvd hα hw)

/-- **W1-d (divisibility form).** Under the same hypotheses, `2^{v₂(k)} ∣ D` for
`k = D·δ₁·w₁`: the 2-part of the modulus is literally a divisor of `D`. -/
theorem two_pow_factorization_dvd_of_odd_cofactors {D δ₁ w₁ α : ℕ} (hD : D ≠ 0) (hα : 2 ∣ α)
    (hδ : Nat.Coprime δ₁ α) (hw : Nat.Coprime w₁ α) :
    2 ^ ((D * δ₁ * w₁).factorization 2) ∣ D := by
  rw [factorization_two_kloosterman_modulus hD hα hδ hw]
  exact Nat.ordProj_dvd D 2

end Salt.Weil
