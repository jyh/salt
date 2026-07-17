/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Weil.Kloosterman
import Salt.Weil.Composite
import Mathlib

/-!
# Weil track, W6.2 — the elementary prime-power Kloosterman bound (even exponent)

For an odd prime `p`, `m ≥ 1`, and a unit `a`, the Kloosterman sum at the modulus
`p ^ (2 * m)` satisfies the square-root bound
`‖S(a, b; p ^ (2m))‖ ≤ 2 · p ^ m = 2 · √(p ^ (2m))`.
This is the Salié / stationary-phase evaluation (Iwaniec–Kowalski §12.3) in the *even*
exponent case, where NO Gauss sum appears: the sum localises to the `≤ 2` critical residues.

The proof is the elementary "averaging + orthogonality" route, entirely inside
`ZMod (p ^ (2m))`, with NO appeal to Weil's Riemann hypothesis for curves:

1. **The `1 + p^m z` shift family** (`ushift`). For `z : ZMod (p ^ (2m))`,
   `u z = 1 + p^m · z` is a unit with inverse `1 − p^m · z` (as `(p^m)² = p^{2m} = 0`).
   Right multiplication by `u z` permutes the units, so `S = ∑_t f(t · u z)` for every `z`.

2. **The summand shift.** `f(t · u z) = f(t) · ψ(z · (p^m · w t))` with `w t = a·t − b·t⁻¹`,
   because `(t · u z)⁻¹ = t⁻¹ (1 − p^m z)` *exactly*.

3. **Averaging + the orthogonality kill.** Summing over all `z : ZMod (p^{2m})`,
   `p^{2m} · S = ∑_t f(t) · ∑_z ψ(z · (p^m · w t))`, and the inner sum is `p^{2m}` if
   `p^m · w t = 0` and `0` otherwise (`AddChar.sum_mulShift`). Cancelling `p^{2m}`,
   `S = ∑_{t : p^m·w t = 0} f(t)`, so `‖S‖ ≤ #{t : p^m·w t = 0}`.

4. **The critical count.** `p^m · w t = 0 ↔ ā·ρ(t)² = b̄` in `ZMod (p^m)` (multiply by the
   unit `t`), a condition on `ρ(t) ∈ (ZMod p^m)ˣ` (`ρ` the reduction). For odd `p`,
   `(ZMod p^m)ˣ` is cyclic, so `x² = c` has `≤ 2` solutions; each pulls back to a full fibre
   of size `p^m`. Hence `#{crit} ≤ 2·p^m`.
-/

namespace Salt.Weil

open scoped BigOperators
open ComplexConjugate Finset

/-- `(p^m)² = 0` in `ZMod (p ^ (2*m))`, since `(p^m)² = p^{2m}` reduces to `0`. This is what
makes `1 ± p^m z` a matched inverse pair. -/
lemma pm_sq_eq_zero (p m : ℕ) : ((p : ZMod (p ^ (2 * m))) ^ m) ^ 2 = 0 := by
  rw [← pow_mul, ← Nat.cast_pow, show m * 2 = 2 * m from by ring, ZMod.natCast_self]

/-- The shift unit `u z = 1 + p^m · z ∈ (ZMod (p^{2m}))ˣ`, with two-sided inverse
`1 − p^m · z`. -/
def ushift {p m : ℕ} (z : ZMod (p ^ (2 * m))) : (ZMod (p ^ (2 * m)))ˣ where
  val := 1 + (p : ZMod (p ^ (2 * m))) ^ m * z
  inv := 1 - (p : ZMod (p ^ (2 * m))) ^ m * z
  val_inv := by
    rw [show (1 + (p : ZMod (p ^ (2 * m))) ^ m * z) * (1 - (p : ZMod (p ^ (2 * m))) ^ m * z)
      = 1 - ((p : ZMod (p ^ (2 * m))) ^ m) ^ 2 * z ^ 2 from by ring, pm_sq_eq_zero, zero_mul,
      sub_zero]
  inv_val := by
    rw [show (1 - (p : ZMod (p ^ (2 * m))) ^ m * z) * (1 + (p : ZMod (p ^ (2 * m))) ^ m * z)
      = 1 - ((p : ZMod (p ^ (2 * m))) ^ m) ^ 2 * z ^ 2 from by ring, pm_sq_eq_zero, zero_mul,
      sub_zero]

@[simp] lemma ushift_val {p m : ℕ} (z : ZMod (p ^ (2 * m))) :
    ((ushift z : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
      = 1 + (p : ZMod (p ^ (2 * m))) ^ m * z := rfl

@[simp] lemma ushift_inv_val {p m : ℕ} (z : ZMod (p ^ (2 * m))) :
    (((ushift z)⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
      = 1 - (p : ZMod (p ^ (2 * m))) ^ m * z := rfl

/-- The phase difference `w t = a·t − b·t⁻¹` whose vanishing mod `p^m` is the critical
condition. Shared between the character sum and the counting lemma so the two filters match. -/
def wexpr {p m : ℕ} (a b : ZMod (p ^ (2 * m))) (t : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)) :=
  a * (t : ZMod (p ^ (2 * m))) - b * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))

/-- **The critical count** (part 4): the number of units `t` with `p^m · w t = 0` is `≤ 2 p^m`.
For an odd prime `p` and a unit `a`, `p^m · w t = 0 ↔ ā ρ(t)² = b̄` in the cyclic group
`(ZMod p^m)ˣ`, whose `≤ 2` roots each pull back to a fibre of size `p^m` under `ZMod.unitsMap`. -/
lemma crit_card_le {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    {a b : ZMod (p ^ (2 * m))} (ha : IsUnit a) :
    (Finset.univ.filter (fun t : (ZMod (p ^ (2 * m)))ˣ =>
      (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0)).card ≤ 2 * p ^ m := by
  classical
  haveI : NeZero (p ^ (2 * m)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  haveI : IsCyclic (ZMod (p ^ m))ˣ := ZMod.isCyclic_units_of_prime_pow p Fact.out hp2 m
  have hdvd : p ^ m ∣ p ^ (2 * m) := pow_dvd_pow p (by omega)
  set ρ : ZMod (p ^ (2 * m)) →+* ZMod (p ^ m) := ZMod.castHom hdvd (ZMod (p ^ m)) with hρ
  set ρᵤ : (ZMod (p ^ (2 * m)))ˣ →* (ZMod (p ^ m))ˣ := ZMod.unitsMap hdvd with hρᵤ
  -- `ρ` on the coercion of a unit agrees with the unit-level reduction `ρᵤ`.
  have hcoe : ∀ t : (ZMod (p ^ (2 * m)))ˣ, ρ ((t : ZMod (p ^ (2 * m)))) = ↑(ρᵤ t) := by
    intro t; rw [hρ, ZMod.castHom_apply, hρᵤ, ZMod.unitsMap_val]
  -- `p^m · x = 0 ↔ ρ x = 0` (both say `p^m ∣ x.val`).
  have hPann : ∀ x : ZMod (p ^ (2 * m)),
      (p : ZMod (p ^ (2 * m))) ^ m * x = 0 ↔ ρ x = 0 := by
    intro x
    have hcast : (p : ZMod (p ^ (2 * m))) ^ m = ((p ^ m : ℕ) : ZMod (p ^ (2 * m))) := by
      push_cast; ring
    have hlhs : ((p ^ m : ℕ) : ZMod (p ^ (2 * m))) * x = 0 ↔ p ^ m ∣ x.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul]
      rw [ZMod.natCast_eq_zero_iff]
      constructor
      · intro h
        have h2 : p ^ m * p ^ m ∣ p ^ m * x.val := by
          rw [← pow_add, show m + m = 2 * m from by ring]; exact h
        exact (Nat.mul_dvd_mul_iff_left (pow_pos (Fact.out : p.Prime).pos m)).mp h2
      · intro h
        have hh : p ^ m * p ^ m ∣ p ^ m * x.val := mul_dvd_mul_left _ h
        have he : p ^ m * p ^ m = p ^ (2 * m) := by rw [← pow_add]; congr 1; omega
        rwa [he] at hh
    have hrhs : ρ x = 0 ↔ p ^ m ∣ x.val := by
      rw [hρ]
      conv_lhs => rw [← ZMod.natCast_zmod_val x, map_natCast]
      rw [ZMod.natCast_eq_zero_iff]
    rw [hcast, hlhs, hrhs]
  -- The critical condition is a square condition on `ρᵤ t`.
  have hcrit : ∀ t : (ZMod (p ^ (2 * m)))ˣ,
      ((p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0)
        ↔ (ρ a * (↑(ρᵤ t) : ZMod (p ^ m)) ^ 2 = ρ b) := by
    intro t
    have htt : ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
        * (t : ZMod (p ^ (2 * m))) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have htt' : (t : ZMod (p ^ (2 * m)))
        * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m))) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hwt : wexpr a b t * (t : ZMod (p ^ (2 * m))) = a * (t : ZMod (p ^ (2 * m))) ^ 2 - b := by
      have e : wexpr a b t * (t : ZMod (p ^ (2 * m)))
          = a * (t : ZMod (p ^ (2 * m))) ^ 2
            - b * (((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
              * (t : ZMod (p ^ (2 * m)))) := by
        simp only [wexpr]; ring
      rw [e, htt, mul_one]
    have hwt' : (a * (t : ZMod (p ^ (2 * m))) ^ 2 - b)
        * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m))) = wexpr a b t := by
      have e : (a * (t : ZMod (p ^ (2 * m))) ^ 2 - b)
          * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
          = a * (t : ZMod (p ^ (2 * m)))
              * ((t : ZMod (p ^ (2 * m))) * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m))))
            - b * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m))) := by ring
      rw [e, htt', mul_one]; simp only [wexpr]
    have hiff : ((p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0)
        ↔ ((p : ZMod (p ^ (2 * m))) ^ m * (a * (t : ZMod (p ^ (2 * m))) ^ 2 - b) = 0) := by
      constructor
      · intro h
        have e2 : (p : ZMod (p ^ (2 * m))) ^ m * (a * (t : ZMod (p ^ (2 * m))) ^ 2 - b)
            = ((p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t) * (t : ZMod (p ^ (2 * m))) := by
          rw [← hwt]; ring
        rw [e2, h, zero_mul]
      · intro h
        have e2 : (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t
            = ((p : ZMod (p ^ (2 * m))) ^ m * (a * (t : ZMod (p ^ (2 * m))) ^ 2 - b))
              * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m))) := by rw [← hwt']; ring
        rw [e2, h, zero_mul]
    rw [hiff, hPann, map_sub, map_mul, map_pow, hcoe t, sub_eq_zero]
  -- The root set in the cyclic units group.
  set RootsU : Finset (ZMod (p ^ m))ˣ :=
    univ.filter (fun x => ρ a * (↑x : ZMod (p ^ m)) ^ 2 = ρ b) with hRoots
  -- `#RootsU ≤ 2`: translate to the 2-torsion of the cyclic units group.
  have hRootscard : RootsU.card ≤ 2 := by
    rcases RootsU.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · simp [he]
    · have hx₀2 : ρ a * (↑x₀ : ZMod (p ^ m)) ^ 2 = ρ b := by
        have h' := hx₀; rw [hRoots, mem_filter] at h'; exact h'.2
      have hle : RootsU.card ≤ (univ.filter (fun y : (ZMod (p ^ m))ˣ => y ^ 2 = 1)).card := by
        apply Finset.card_le_card_of_injOn (fun x => x * x₀⁻¹)
        · intro x hx
          rw [Finset.mem_coe, hRoots, mem_filter] at hx
          rw [Finset.mem_coe, mem_filter]
          refine ⟨mem_univ _, ?_⟩
          have hxeq : ρ a * (↑x : ZMod (p ^ m)) ^ 2 = ρ a * (↑x₀ : ZMod (p ^ m)) ^ 2 := by
            rw [hx.2, hx₀2]
          have hsqcoe : (↑x : ZMod (p ^ m)) ^ 2 = (↑x₀ : ZMod (p ^ m)) ^ 2 :=
            (ha.map ρ).mul_right_injective hxeq
          have hsq : x ^ 2 = x₀ ^ 2 := by
            have hc : ((x ^ 2 : (ZMod (p ^ m))ˣ) : ZMod (p ^ m))
                = ((x₀ ^ 2 : (ZMod (p ^ m))ˣ) : ZMod (p ^ m)) := by push_cast; exact hsqcoe
            exact Units.ext hc
          change (x * x₀⁻¹) ^ 2 = 1
          rw [mul_pow, hsq, inv_pow, mul_inv_cancel]
        · intro x _ y _ hxy
          exact mul_right_cancel hxy
      exact hle.trans (IsCyclic.card_pow_eq_one_le (by norm_num))
  -- Forward inclusion of the critical set into the fibres over `RootsU`.
  have hincl : ∀ t ∈ univ.filter (fun t : (ZMod (p ^ (2 * m)))ˣ =>
      (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0), ρᵤ t ∈ RootsU := by
    intro t ht
    rw [mem_filter] at ht
    rw [hRoots, mem_filter]
    exact ⟨mem_univ _, (hcrit t).mp ht.2⟩
  -- Every fibre of `ρᵤ` has the common cardinality `K`.
  have hsurj : Function.Surjective ρᵤ := by rw [hρᵤ]; exact ZMod.unitsMap_surjective hdvd
  set K := (univ.filter (fun t : (ZMod (p ^ (2 * m)))ˣ => ρᵤ t = 1)).card with hKdef
  have hfib : ∀ x : (ZMod (p ^ m))ˣ, (univ.filter (fun t => ρᵤ t = x)).card = K :=
    fun x => MonoidHom.card_fiber_eq_of_mem_range ρᵤ (Set.mem_range.mpr (hsurj x))
      (Set.mem_range.mpr (hsurj 1))
  -- `K = p^m` from the totient identity `φ(p^{2m}) = φ(p^m) · p^m`.
  have hKeq : Fintype.card (ZMod (p ^ (2 * m)))ˣ = Fintype.card (ZMod (p ^ m))ˣ * K := by
    rw [← Finset.card_univ (α := (ZMod (p ^ (2 * m)))ˣ),
      Finset.card_eq_sum_card_fiberwise (fun t (_ : t ∈ univ) => mem_univ (ρᵤ t)),
      Finset.sum_congr rfl (fun x _ => hfib x), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hKval : K = p ^ m := by
    have hexp : p ^ (m - 1) * p ^ m = p ^ (2 * m - 1) := by rw [← pow_add]; congr 1; omega
    have htot : (p ^ (2 * m)).totient = (p ^ m).totient * p ^ m := by
      rw [Nat.totient_prime_pow (Fact.out) (by omega : 0 < 2 * m),
        Nat.totient_prime_pow (Fact.out) (by omega : 0 < m), mul_right_comm, hexp]
    rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at hKeq
    have hpos : 0 < (p ^ m).totient := Nat.totient_pos.mpr (pow_pos (Fact.out : p.Prime).pos m)
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [← hKeq, htot])
  -- Assemble: fibrewise sum, bound each fibre by `K = p^m`, and `#RootsU ≤ 2`.
  calc (univ.filter (fun t : (ZMod (p ^ (2 * m)))ˣ =>
          (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0)).card
      = ∑ x ∈ RootsU, ((univ.filter (fun t : (ZMod (p ^ (2 * m)))ˣ =>
          (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0)).filter (fun t => ρᵤ t = x)).card :=
        Finset.card_eq_sum_card_fiberwise hincl
    _ ≤ ∑ _x ∈ RootsU, K := by
        refine Finset.sum_le_sum (fun x _ => ?_)
        refine le_trans (Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.filter_subset _ _))) ?_
        rw [hfib x]
    _ = RootsU.card * K := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * p ^ m := by rw [hKval]; exact Nat.mul_le_mul hRootscard le_rfl

/-- **W6.2 — the even prime-power Kloosterman bound.** For an odd prime `p`, `m ≥ 1`, and a unit
`a` (any `b`), `‖S(a, b; p^{2m})‖ ≤ 2 · p^m = 2 · √(p^{2m})`. Elementary averaging +
orthogonality (Salié, even case; no Gauss sum). -/
theorem norm_kloosterman_prime_pow_even {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    {a b : ZMod (p ^ (2 * m))} (ha : IsUnit a) :
    ‖kloosterman a b‖ ≤ 2 * (p : ℝ) ^ m := by
  classical
  haveI : NeZero (p ^ (2 * m)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  -- Local abbreviation for the summand `f`.
  set f : (ZMod (p ^ (2 * m)))ˣ → ℂ :=
    fun t => ZMod.stdAddChar (a * (t : ZMod (p ^ (2 * m)))
      + b * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))) with hf
  have hkf : kloosterman a b = ∑ t, f t := rfl
  -- Step 1+2: for every `z`, reindexing by `t ↦ t · u z` gives the summand shift.
  have hterm : ∀ z : ZMod (p ^ (2 * m)),
      kloosterman a b
        = ∑ t, f t * ZMod.stdAddChar (z * ((p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t)) := by
    intro z
    have hre : ∑ t, f t = ∑ t, f (t * ushift z) :=
      Fintype.sum_bijective (· * (ushift z)⁻¹) (Equiv.mulRight (ushift z)⁻¹).bijective f
        (fun t => f (t * ushift z)) (fun t => by rw [mul_assoc, inv_mul_cancel, mul_one])
    rw [hkf, hre]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have harg : a * ((t * ushift z : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
        + b * (((t * ushift z)⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m)))
        = (a * (t : ZMod (p ^ (2 * m)))
            + b * ((t⁻¹ : (ZMod (p ^ (2 * m)))ˣ) : ZMod (p ^ (2 * m))))
          + z * ((p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t) := by
      rw [Units.val_mul, mul_inv_rev, Units.val_mul, ushift_val, ushift_inv_val]
      simp only [wexpr]; ring
    simp only [hf]
    rw [← AddChar.map_add_eq_mul, harg]
  -- Step 3: average over all `z`, apply orthogonality, cancel `p^{2m}`.
  have hAvg : ((p ^ (2 * m) : ℕ) : ℂ) * kloosterman a b
      = ((p ^ (2 * m) : ℕ) : ℂ)
        * ∑ t, (if (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0 then f t else 0) := by
    have hL : ((p ^ (2 * m) : ℕ) : ℂ) * kloosterman a b
        = ∑ _z : ZMod (p ^ (2 * m)), kloosterman a b := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [hL]
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Finset.mul_sum]
    rw [AddChar.sum_mulShift ((p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t)
      (ZMod.isPrimitive_stdAddChar _)]
    rw [ZMod.card]
    split_ifs with h <;> ring
  -- Cancel the nonzero scalar `p^{2m}`.
  have hNe : ((p ^ (2 * m) : ℕ) : ℂ) ≠ 0 := by
    have : (p : ℕ) ^ (2 * m) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    exact_mod_cast this
  have hS := mul_left_cancel₀ hNe hAvg
  -- Step 3 conclusion → triangle inequality → the critical count.
  calc ‖kloosterman a b‖
      = ‖∑ t, (if (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0 then f t else 0)‖ := by rw [hS]
    _ ≤ ∑ t, ‖(if (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0 then f t else 0)‖ :=
        norm_sum_le _ _
    _ = ∑ t, (if (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        split_ifs with h
        · rw [hf]; exact AddChar.norm_apply _ _
        · exact norm_zero
    _ = ((Finset.univ.filter
          (fun t : (ZMod (p ^ (2 * m)))ˣ =>
            (p : ZMod (p ^ (2 * m))) ^ m * wexpr a b t = 0)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ 2 * (p : ℝ) ^ m := by
        have hcount := crit_card_le hp2 hm (b := b) ha
        have h2 : ((2 * p ^ m : ℕ) : ℝ) = 2 * (p : ℝ) ^ m := by push_cast; ring
        rw [← h2]
        exact_mod_cast hcount

end Salt.Weil
