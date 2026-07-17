/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.PrimePower
import Salt.Weil.Composite
import Salt.Weil.CompositeTail
import Salt.Weil.Descent
import Mathlib

/-!
# Weil track, W6.4 — the composite `τ(c)√c` assembly

This module closes HB-ENGINE's composite Weil link. It supplies the parked odd-exponent
prime-power bound as a special case of a single **general** prime-power estimate, then
iterates the unit-threaded factorization (`Salt.Weil.CompositeTail`) to an arbitrary modulus.

## (1) The general prime-power bound (`k ≥ 2`)

For an odd prime `p`, a unit `a`, and any `b`, and any shift exponent `j` with `k ≤ 2j` and
`j + 1 ≤ k`, `‖S(a, b; p^k)‖ ≤ 2·p^j`. This is the Salié / stationary-phase evaluation with the
`1 + p^j z` shift family (`(p^j)² = p^{2j} = 0` in `ZMod (p^k)` since `k ≤ 2j`); the critical
condition `p^j·w t = 0` reduces mod `p^{k-j}` to `ā ρ(t)² = b̄` in the cyclic group
`(ZMod p^{k-j})ˣ` (`≤ 2` roots), each root pulling back to a fibre of size `φ(p^k)/φ(p^{k-j}) =
p^j`. Taking `j = ⌈k/2⌉`:

* `k = 2m` (even) ⟹ `j = m`: `‖S‖ ≤ 2·p^m = 2·√(p^k)` — recovers
  `norm_kloosterman_prime_pow_even`.
* `k = 2m+1` (odd, `m ≥ 1`) ⟹ `j = m+1`: `‖S‖ ≤ 2·p^{m+1} = 2·√p·√(p^k)` — the **crude**
  odd-exponent bound (a factor `√p` above the sharp `2·p^{m+1/2}`, the missing `√p` being a
  one-variable quadratic Gauss sum). This is `norm_kloosterman_prime_pow_odd`, the parked node.

The elementary averaging + orthogonality route is entirely inside `ZMod (p^k)` — no appeal to
Weil's RH for curves; it mirrors `norm_kloosterman_prime_pow_even` with the shift exponent `m`
replaced by the parameter `j` and the reduction modulus `p^m` by `p^{k-j}`.

## (2) The composite assembly

Iterating `norm_kloosterman_le_mul_of_coprime_unit` over `Nat.factorization c` at a **unit**
first argument `a` plugs the per-prime-power bounds into an arbitrary odd modulus, yielding the
`τ(c)·(bound)` shape. The gcd factor of the classical `τ(c)√c√gcd(a,b,c)` collapses to `1` on
the unit branch (`gcd(a,c) = 1`), and the missing sharp odd `√p` factors are the honest gap
recorded above (the crude route inflates `√c` to `∏ p^{⌈k/2⌉}`).
-/

namespace Salt.Weil

open scoped BigOperators
open ComplexConjugate Finset

/-! ### (1) The general prime-power bound -/

/-- `(p^j)² = 0` in `ZMod (p^k)` whenever `k ≤ 2j` (`(p^j)² = p^{2j}` and `p^k ∣ p^{2j}`). This is
what makes `1 ± p^j z` a matched inverse pair for the shift family. -/
lemma pj_sq_eq_zero {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 2 * j) :
    ((p : ZMod (p ^ k)) ^ j) ^ 2 = 0 := by
  rw [← pow_mul, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p (by omega)

/-- The shift unit `u z = 1 + p^j · z ∈ (ZMod (p^k))ˣ`, with two-sided inverse `1 − p^j · z`
(valid when `k ≤ 2j`, so `(p^j)² = 0`). -/
def ushiftN {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 2 * j) (z : ZMod (p ^ k)) :
    (ZMod (p ^ k))ˣ where
  val := 1 + (p : ZMod (p ^ k)) ^ j * z
  inv := 1 - (p : ZMod (p ^ k)) ^ j * z
  val_inv := by
    rw [show (1 + (p : ZMod (p ^ k)) ^ j * z) * (1 - (p : ZMod (p ^ k)) ^ j * z)
      = 1 - ((p : ZMod (p ^ k)) ^ j) ^ 2 * z ^ 2 from by ring, pj_sq_eq_zero hkj, zero_mul,
      sub_zero]
  inv_val := by
    rw [show (1 - (p : ZMod (p ^ k)) ^ j * z) * (1 + (p : ZMod (p ^ k)) ^ j * z)
      = 1 - ((p : ZMod (p ^ k)) ^ j) ^ 2 * z ^ 2 from by ring, pj_sq_eq_zero hkj, zero_mul,
      sub_zero]

@[simp] lemma ushiftN_val {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 2 * j) (z : ZMod (p ^ k)) :
    ((ushiftN hkj z : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = 1 + (p : ZMod (p ^ k)) ^ j * z := rfl

@[simp] lemma ushiftN_inv_val {p k j : ℕ} [NeZero (p ^ k)] (hkj : k ≤ 2 * j) (z : ZMod (p ^ k)) :
    (((ushiftN hkj z)⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = 1 - (p : ZMod (p ^ k)) ^ j * z := rfl

/-- The phase difference `w t = a·t − b·t⁻¹` at a general modulus (shared between the character
sum and the counting lemma so the two filters match). -/
def wexprGen {N : ℕ} (a b : ZMod N) (t : (ZMod N)ˣ) : ZMod N :=
  a * (t : ZMod N) - b * ((t⁻¹ : (ZMod N)ˣ) : ZMod N)

/-- **The critical count.** For an odd prime `p`, `j + 1 ≤ k`, and a unit `a`, the number of units
`t` with `p^j · w t = 0` is `≤ 2·p^j`: the condition reduces mod `p^{k-j}` to `ā ρ(t)² = b̄` in the
cyclic group `(ZMod p^{k-j})ˣ` (`≤ 2` roots), each root's fibre under `ZMod.unitsMap` having size
`φ(p^k)/φ(p^{k-j}) = p^j`. -/
lemma critN_card_le {p k j : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hjk : j + 1 ≤ k)
    {a b : ZMod (p ^ k)} (ha : IsUnit a) :
    (Finset.univ.filter (fun t : (ZMod (p ^ k))ˣ =>
      (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0)).card ≤ 2 * p ^ j := by
  classical
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ (k - j)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ (k - j)))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 (k - j)
  have hdvd : p ^ (k - j) ∣ p ^ k := pow_dvd_pow p (by omega)
  set ρ : ZMod (p ^ k) →+* ZMod (p ^ (k - j)) := ZMod.castHom hdvd (ZMod (p ^ (k - j))) with hρ
  set ρᵤ : (ZMod (p ^ k))ˣ →* (ZMod (p ^ (k - j)))ˣ := ZMod.unitsMap hdvd with hρᵤ
  have hcoe : ∀ t : (ZMod (p ^ k))ˣ, ρ ((t : ZMod (p ^ k))) = ↑(ρᵤ t) := by
    intro t; rw [hρ, ZMod.castHom_apply, hρᵤ, ZMod.unitsMap_val]
  have hPann : ∀ x : ZMod (p ^ k),
      (p : ZMod (p ^ k)) ^ j * x = 0 ↔ ρ x = 0 := by
    intro x
    have hcast : (p : ZMod (p ^ k)) ^ j = ((p ^ j : ℕ) : ZMod (p ^ k)) := by push_cast; ring
    have hlhs : ((p ^ j : ℕ) : ZMod (p ^ k)) * x = 0 ↔ p ^ (k - j) ∣ x.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul]
      rw [ZMod.natCast_eq_zero_iff]
      constructor
      · intro h
        have h2 : p ^ j * p ^ (k - j) ∣ p ^ j * x.val := by
          rw [← pow_add, show j + (k - j) = k from by omega]; exact h
        exact (Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : p.Prime).pos j)).mp h2
      · intro h
        have hh : p ^ j * p ^ (k - j) ∣ p ^ j * x.val := mul_dvd_mul_left _ h
        have he : p ^ j * p ^ (k - j) = p ^ k := by rw [← pow_add]; congr 1; omega
        rwa [he] at hh
    have hrhs : ρ x = 0 ↔ p ^ (k - j) ∣ x.val := by
      rw [hρ]
      conv_lhs => rw [← ZMod.natCast_zmod_val x, map_natCast]
      rw [ZMod.natCast_eq_zero_iff]
    rw [hcast, hlhs, hrhs]
  have hcrit : ∀ t : (ZMod (p ^ k))ˣ,
      ((p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0)
        ↔ (ρ a * (↑(ρᵤ t) : ZMod (p ^ (k - j))) ^ 2 = ρ b) := by
    intro t
    have htt : ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * (t : ZMod (p ^ k)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have htt' : (t : ZMod (p ^ k)) * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hwt : wexprGen a b t * (t : ZMod (p ^ k)) = a * (t : ZMod (p ^ k)) ^ 2 - b := by
      have e : wexprGen a b t * (t : ZMod (p ^ k))
          = a * (t : ZMod (p ^ k)) ^ 2
            - b * (((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * (t : ZMod (p ^ k))) := by
        simp only [wexprGen]; ring
      rw [e, htt, mul_one]
    have hwt' : (a * (t : ZMod (p ^ k)) ^ 2 - b)
        * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) = wexprGen a b t := by
      have e : (a * (t : ZMod (p ^ k)) ^ 2 - b) * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))
          = a * (t : ZMod (p ^ k))
              * ((t : ZMod (p ^ k)) * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)))
            - b * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by ring
      rw [e, htt', mul_one]; simp only [wexprGen]
    have hiff : ((p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0)
        ↔ ((p : ZMod (p ^ k)) ^ j * (a * (t : ZMod (p ^ k)) ^ 2 - b) = 0) := by
      constructor
      · intro h
        have e2 : (p : ZMod (p ^ k)) ^ j * (a * (t : ZMod (p ^ k)) ^ 2 - b)
            = ((p : ZMod (p ^ k)) ^ j * wexprGen a b t) * (t : ZMod (p ^ k)) := by
          rw [← hwt]; ring
        rw [e2, h, zero_mul]
      · intro h
        have e2 : (p : ZMod (p ^ k)) ^ j * wexprGen a b t
            = ((p : ZMod (p ^ k)) ^ j * (a * (t : ZMod (p ^ k)) ^ 2 - b))
              * ((t⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) := by rw [← hwt']; ring
        rw [e2, h, zero_mul]
    rw [hiff, hPann, map_sub, map_mul, map_pow, hcoe t, sub_eq_zero]
  set RootsU : Finset (ZMod (p ^ (k - j)))ˣ :=
    univ.filter (fun x => ρ a * (↑x : ZMod (p ^ (k - j))) ^ 2 = ρ b) with hRoots
  have hRootscard : RootsU.card ≤ 2 := by
    rcases RootsU.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · simp [he]
    · have hx₀2 : ρ a * (↑x₀ : ZMod (p ^ (k - j))) ^ 2 = ρ b := by
        have h' := hx₀; rw [hRoots, mem_filter] at h'; exact h'.2
      have hle : RootsU.card
          ≤ (univ.filter (fun y : (ZMod (p ^ (k - j)))ˣ => y ^ 2 = 1)).card := by
        apply Finset.card_le_card_of_injOn (fun x => x * x₀⁻¹)
        · intro x hx
          rw [Finset.mem_coe, hRoots, mem_filter] at hx
          rw [Finset.mem_coe, mem_filter]
          refine ⟨mem_univ _, ?_⟩
          have hxeq : ρ a * (↑x : ZMod (p ^ (k - j))) ^ 2
              = ρ a * (↑x₀ : ZMod (p ^ (k - j))) ^ 2 := by rw [hx.2, hx₀2]
          have hsqcoe : (↑x : ZMod (p ^ (k - j))) ^ 2 = (↑x₀ : ZMod (p ^ (k - j))) ^ 2 :=
            (ha.map ρ).mul_right_injective hxeq
          have hsq : x ^ 2 = x₀ ^ 2 := by
            have hc : ((x ^ 2 : (ZMod (p ^ (k - j)))ˣ) : ZMod (p ^ (k - j)))
                = ((x₀ ^ 2 : (ZMod (p ^ (k - j)))ˣ) : ZMod (p ^ (k - j))) := by
              push_cast; exact hsqcoe
            exact Units.ext hc
          change (x * x₀⁻¹) ^ 2 = 1
          rw [mul_pow, hsq, inv_pow, mul_inv_cancel]
        · intro x _ y _ hxy
          exact mul_right_cancel hxy
      exact hle.trans (IsCyclic.card_pow_eq_one_le (by norm_num))
  have hincl : ∀ t ∈ univ.filter (fun t : (ZMod (p ^ k))ˣ =>
      (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0), ρᵤ t ∈ RootsU := by
    intro t ht
    rw [mem_filter] at ht
    rw [hRoots, mem_filter]
    exact ⟨mem_univ _, (hcrit t).mp ht.2⟩
  have hsurj : Function.Surjective ρᵤ := by rw [hρᵤ]; exact ZMod.unitsMap_surjective hdvd
  set K := (univ.filter (fun t : (ZMod (p ^ k))ˣ => ρᵤ t = 1)).card with hKdef
  have hfib : ∀ x : (ZMod (p ^ (k - j)))ˣ, (univ.filter (fun t => ρᵤ t = x)).card = K :=
    fun x => MonoidHom.card_fiber_eq_of_mem_range ρᵤ (Set.mem_range.mpr (hsurj x))
      (Set.mem_range.mpr (hsurj 1))
  have hKeq : Fintype.card (ZMod (p ^ k))ˣ = Fintype.card (ZMod (p ^ (k - j)))ˣ * K := by
    rw [← Finset.card_univ (α := (ZMod (p ^ k))ˣ),
      Finset.card_eq_sum_card_fiberwise (fun t (_ : t ∈ univ) => mem_univ (ρᵤ t)),
      Finset.sum_congr rfl (fun x _ => hfib x), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hKval : K = p ^ j := by
    have hexp : p ^ (k - j - 1) * p ^ j = p ^ (k - 1) := by rw [← pow_add]; congr 1; omega
    have htot : (p ^ k).totient = (p ^ (k - j)).totient * p ^ j := by
      rw [Nat.totient_prime_pow (Fact.out) (by omega : 0 < k),
        Nat.totient_prime_pow (Fact.out) (by omega : 0 < k - j), mul_right_comm, hexp]
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at hKeq
    have hpos : 0 < (p ^ (k - j)).totient :=
      Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos (k - j))
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [← hKeq, htot])
  calc (univ.filter (fun t : (ZMod (p ^ k))ˣ =>
          (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0)).card
      = ∑ x ∈ RootsU, ((univ.filter (fun t : (ZMod (p ^ k))ˣ =>
          (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0)).filter (fun t => ρᵤ t = x)).card :=
        Finset.card_eq_sum_card_fiberwise hincl
    _ ≤ ∑ _x ∈ RootsU, K := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        refine le_trans (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.filter_subset _ _))) ?_
        rw [hfib x]
    _ = RootsU.card * K := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * p ^ j := by rw [hKval]; exact Nat.mul_le_mul hRootscard le_rfl

/-- **The general prime-power Kloosterman bound.** For an odd prime `p`, a unit `a` (any `b`), and
a shift exponent `j` with `k ≤ 2j` and `j + 1 ≤ k`, `‖S(a, b; p^k)‖ ≤ 2·p^j`. Elementary averaging
+ orthogonality (Salié; no Gauss sum). Taking `j = ⌈k/2⌉` gives the even case (`2√(p^k)`) and the
crude odd case (`2√p·√(p^k)`). -/
theorem norm_kloosterman_prime_pow_ge_two {p k j : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hkj : k ≤ 2 * j) (hjk : j + 1 ≤ k) {a b : ZMod (p ^ k)} (ha : IsUnit a) :
    ‖kloosterman a b‖ ≤ 2 * (p : ℝ) ^ j := by
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
    rw [hL]
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Finset.mul_sum]
    rw [AddChar.sum_mulShift ((p : ZMod (p ^ k)) ^ j * wexprGen a b t)
      (ZMod.isPrimitive_stdAddChar _)]
    rw [ZMod.card]
    split_ifs with h <;> ring
  have hNe : ((p ^ k : ℕ) : ℂ) ≠ 0 := by
    have : (p : ℕ) ^ k ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    exact_mod_cast this
  have hS := mul_left_cancel₀ hNe hAvg
  calc ‖kloosterman a b‖
      = ‖∑ t, (if (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0 then f t else 0)‖ := by rw [hS]
    _ ≤ ∑ t, ‖(if (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0 then f t else 0)‖ :=
        norm_sum_le _ _
    _ = ∑ t, (if (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        split_ifs with h
        · rw [hf]; exact AddChar.norm_apply _ _
        · exact norm_zero
    _ = ((Finset.univ.filter
          (fun t : (ZMod (p ^ k))ˣ =>
            (p : ZMod (p ^ k)) ^ j * wexprGen a b t = 0)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ 2 * (p : ℝ) ^ j := by
        have hcount := critN_card_le hp2 hjk (a := a) (b := b) ha
        have h2 : ((2 * p ^ j : ℕ) : ℝ) = 2 * (p : ℝ) ^ j := by push_cast; ring
        rw [← h2]
        exact_mod_cast hcount

/-- **The parked odd-exponent bound.** For an odd prime `p`, `m ≥ 1`, a unit `a` (any `b`),
`‖S(a, b; p^{2m+1})‖ ≤ 2·p^{m+1}` (the crude Salié bound, `√p` above the sharp
`2·p^{m+1/2}`). Specialization of `norm_kloosterman_prime_pow_ge_two` at `j = m+1`. -/
theorem norm_kloosterman_prime_pow_odd {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    {a b : ZMod (p ^ (2 * m + 1))} (ha : IsUnit a) :
    ‖kloosterman a b‖ ≤ 2 * (p : ℝ) ^ (m + 1) :=
  norm_kloosterman_prime_pow_ge_two (j := m + 1) hp2 (by omega) (by omega) ha

/-! ### (2) The prime case at a unit — the degenerate `b = 0` fibre and the assembly -/

/-- **The degenerate Kloosterman sum** `S(a, 0; p) = −1` for a unit `a` at a prime modulus `p`
(a Ramanujan sum): reindexing by the unit turns the sum into `∑_{s ∈ (ZMod p)ˣ} ψ(s)`, which is
`(∑_{x} ψ x) − ψ(0) = 0 − 1`. Handles the CRT-degenerate fibre where a `b`-projection vanishes. -/
theorem kloosterman_zero_right {p : ℕ} [Fact p.Prime] {a : ZMod p} (ha : IsUnit a) :
    kloosterman a 0 = -1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have split : ∀ f : ZMod p → ℂ,
      ∑ s : (ZMod p)ˣ, f (s : ZMod p) = ∑ x ∈ Finset.univ.erase (0 : ZMod p), f x := by
    intro f
    have himg : (Finset.univ : Finset (ZMod p)ˣ).image (Units.val)
        = Finset.univ.erase (0 : ZMod p) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      constructor
      · rintro ⟨s, rfl⟩; exact Units.ne_zero s
      · intro hx; exact ⟨(isUnit_iff_ne_zero.mpr hx).unit, IsUnit.unit_spec _⟩
    rw [← himg]
    exact (Finset.sum_image (fun s _ s' _ h => Units.ext h)).symm
  have h0 : kloosterman a 0 = ∑ t : (ZMod p)ˣ, ZMod.stdAddChar (a * (t : ZMod p)) := by
    unfold kloosterman
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [zero_mul, add_zero]
  rw [h0]
  obtain ⟨u, rfl⟩ := ha
  have hre : ∑ t : (ZMod p)ˣ, ZMod.stdAddChar ((u : ZMod p) * (t : ZMod p))
      = ∑ s : (ZMod p)ˣ, ZMod.stdAddChar (s : ZMod p) := by
    rw [← Equiv.sum_comp (Equiv.mulLeft u) (fun s : (ZMod p)ˣ => ZMod.stdAddChar (s : ZMod p))]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [Equiv.coe_mulLeft, Units.val_mul]
  rw [hre, split]
  have hfull : ∑ x : ZMod p, ZMod.stdAddChar x = 0 := by
    have h := AddChar.sum_mulShift (1 : ZMod p) (ZMod.isPrimitive_stdAddChar p)
    simp only [mul_one] at h
    rw [h, if_neg one_ne_zero, Nat.cast_zero]
  have hsplit2 : ZMod.stdAddChar (0 : ZMod p)
      + ∑ x ∈ Finset.univ.erase (0 : ZMod p), ZMod.stdAddChar x
        = ∑ x : ZMod p, ZMod.stdAddChar x :=
    Finset.add_sum_erase _ _ (Finset.mem_univ 0)
  rw [hfull, AddChar.map_zero_eq_one] at hsplit2
  exact eq_neg_of_add_eq_zero_right hsplit2

/-- **The prime case at a unit.** For any prime `p` and a **unit** `a` (any `b`, including the
degenerate `b = 0`), `‖S(a, b; p)‖ ≤ 2·√p`. The nondegenerate case is Weil
(`norm_kloosterman_le_two_sqrt'`); the `b = 0` case is `‖−1‖ = 1 ≤ 2√p`. This is the per-prime
(`k = 1`) input to the squarefree assembly, holding at every prime (`p = 2` included). -/
theorem norm_kloosterman_prime_unit {p : ℕ} [Fact p.Prime] {a b : ZMod p} (ha : IsUnit a) :
    ‖kloosterman a b‖ ≤ 2 * Real.sqrt p := by
  by_cases hb : b = 0
  · subst hb
    rw [kloosterman_zero_right ha, norm_neg, norm_one]
    have h1 : (1 : ℝ) ≤ Real.sqrt p := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    linarith
  · exact norm_kloosterman_le_two_sqrt' a b (isUnit_iff_ne_zero.mp ha) hb

/-- **The prime case at a unit, exponent-`1` modulus form.** `‖S(a, b; p^1)‖ ≤ 2√p` — the
`k = 1` bound transported to the `ZMod (p^1)` modulus that `Nat.recOnPosPrimePosCoprime` hands the
squarefree assembly. Pure repackaging of `norm_kloosterman_prime_unit`. -/
theorem norm_kloosterman_prime_pow_one_unit {p : ℕ} [Fact p.Prime] {a b : ZMod (p ^ 1)}
    (ha : IsUnit a) : ‖kloosterman a b‖ ≤ 2 * Real.sqrt (p : ℝ) := by
  have key : ∀ N : ℕ, N = p → ∀ [NeZero N] (a b : ZMod N), IsUnit a →
      ‖kloosterman a b‖ ≤ 2 * Real.sqrt (p : ℝ) := by
    intro N h; subst h; intro _ a b ha; exact norm_kloosterman_prime_unit ha
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  exact key (p ^ 1) (pow_one p) a b ha

/-- **The composite `τ(c)√c` Kloosterman bound (squarefree modulus).** For a squarefree modulus
`c` and a **unit** `a` (any `b`), `‖S(a, b; c)‖ ≤ τ(c)·√c`, where `τ(c) = #c.divisors`. This is
the classical Weil bound `‖S(a,b;c)‖ ≤ τ(c)√c√gcd(a,b,c)` with the `gcd` factor collapsed to `1`
on the unit branch (`gcd(a,c) = 1`). The proof iterates the unit-threaded factorization
(`norm_kloosterman_le_mul_of_coprime_unit`) over the coprime prime factors via
`Nat.recOnPosPrimePosCoprime`: each factor is a single prime (`Squarefree` forces exponent `1`),
bounded by Weil `2√p = τ(p)√p` (`norm_kloosterman_prime_pow_one_unit`), and both `τ` and `√·` are
multiplicative over coprime factors. For a general (non-squarefree) modulus the composite bound is
the product of the per-prime-power estimates `2·p^{⌈k/2⌉}`
(`norm_kloosterman_prime_pow_ge_two`), which the sharp `τ(c)√c` needs the odd-`k` Gauss-sum `√p`
to recover (the recorded honest gap; here `k = 1` throughout, so no gap). -/
theorem norm_kloosterman_le_tau_sqrt {c : ℕ} [NeZero c] (hc : Squarefree c) {a b : ZMod c}
    (ha : IsUnit a) : ‖kloosterman a b‖ ≤ (c.divisors.card : ℝ) * Real.sqrt c := by
  have key : ∀ c : ℕ, Squarefree c → ∀ [NeZero c] (a b : ZMod c), IsUnit a →
      ‖kloosterman a b‖ ≤ (c.divisors.card : ℝ) * Real.sqrt c := by
    intro c
    refine Nat.recOnPosPrimePosCoprime
      (motive := fun c => Squarefree c → ∀ [NeZero c] (a b : ZMod c), IsUnit a →
        ‖kloosterman a b‖ ≤ (c.divisors.card : ℝ) * Real.sqrt c) ?_ ?_ ?_ ?_ c
    · intro p n hp hn hsf
      haveI : Fact p.Prime := ⟨hp⟩
      have hn1 : n = 1 := by
        by_contra hne
        have hdd : p * p ∣ p ^ n := by
          have h2 : p ^ 2 ∣ p ^ n := pow_dvd_pow p (by omega)
          simpa [pow_two] using h2
        exact absurd (Nat.isUnit_iff.mp (hsf p hdd)) hp.ne_one
      subst hn1
      intro _ a b ha
      refine (norm_kloosterman_prime_pow_one_unit ha).trans (le_of_eq ?_)
      have hcard : ((Nat.divisors (p ^ 1)).card : ℝ) = 2 := by
        rw [pow_one, Nat.Prime.divisors hp, Finset.card_pair (Ne.symm hp.ne_one)]; norm_num
      have hsqrt : Real.sqrt ((p ^ 1 : ℕ) : ℝ) = Real.sqrt (p : ℝ) := by rw [pow_one]
      rw [hcard, hsqrt]
    · intro hsf
      exact absurd (Nat.isUnit_iff.mp (hsf 0 (by simp))) (by norm_num)
    · intro _ _ a b _
      refine (norm_kloosterman_le_modulus a b).trans (le_of_eq ?_)
      rw [Nat.divisors_one]; simp
    · intro d₁ d₂ hd₁ hd₂ hcop IH₁ IH₂ hsf _ a b ha
      haveI : NeZero d₁ := ⟨by omega⟩
      haveI : NeZero d₂ := ⟨by omega⟩
      have hsf1 : Squarefree d₁ := hsf.squarefree_of_dvd (dvd_mul_right d₁ d₂)
      have hsf2 : Squarefree d₂ := hsf.squarefree_of_dvd (dvd_mul_left d₂ d₁)
      have hM0 : 0 ≤ (d₁.divisors.card : ℝ) * Real.sqrt d₁ := by positivity
      have hbd := norm_kloosterman_le_mul_of_coprime_unit hcop a b ha hM0
        (fun a₁ b₁ hu => IH₁ hsf1 a₁ b₁ hu) (fun a₂ b₂ hu => IH₂ hsf2 a₂ b₂ hu)
      refine hbd.trans (le_of_eq ?_)
      rw [Nat.Coprime.card_divisors_mul hcop]
      push_cast
      rw [Real.sqrt_mul (by positivity)]
      ring
  exact key c hc a b ha

end Salt.Weil
