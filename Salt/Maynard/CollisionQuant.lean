/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.CrossCollision
import Salt.Maynard.Compat
import Salt.Maynard.PhiAtom
import Salt.Brun.SelbergPort

/-!
# N4.4-QUANT — the quantitative collision bound

This file proves the quantitative cross-collision bound
`|s1CollisionForm| ≤ (12k²/D₀k) · yside`, discharging the PORT-BLOCKER
`CrossCollisionControlled` of `CrossCollision.lean` with an explicit,
`R`-free constant.

The route keeps every inner sum **signed** (exact Möbius evaluations) and
takes absolute values only at the outermost layer:

* `T_forced` (P1) — forced-divisor exact evaluation of `∑ λ(d)/∏d` over
  `d` with `v ∣ d` componentwise.
* `inner_exact` (P2) — the constrained diagonalisation: the `(σ,τ)`-guarded
  double `λ`-sum equals a signed `u`-sum of exact `ŷ`-values.
* `inner_abs_le` (P3) — the per-assignment absolute bound
  `≤ 3^{ω(s)} ∏_{p∣s}(p−1)⁻² · yside`, via the φ-splitting and the
  prime-erasure injection.
* `compat_moebius_expansion` / `inner_collision_expand` (P4) — the exact
  Möbius expansion of the compatible form over collision moduli and
  prime-to-slot assignments.
* `euler_tail` (P5) — the `R`-free Euler tail `∑ L^{ω}∏(p−1)⁻² ≤ 12k²/D₀`.
* `collision_lower_order` / `crossCollisionControlled_holds` /
  `compat_le_two_yside` (P6) — the assembled bounds.
-/

open Finset
open scoped ArithmeticFunction.Moebius

namespace Salt.Maynard

/-! ## Support helpers: divisor-closedness, prime bounds, indicators -/

/-- **Divisor-closedness of `𝒟`.** A componentwise divisor of a sieve tuple
is a sieve tuple. -/
theorem mem_kSieveIndex_of_dvd {k R W : ℕ} {r d : Fin k → ℕ}
    (hr : r ∈ kSieveIndex k R W) (h : ∀ i, d i ∣ r i) : d ∈ kSieveIndex k R W := by
  obtain ⟨hrsq, hrcop, hrcopW, hrprod⟩ := (mem_kSieveIndex_iff r).mp hr
  rw [mem_kSieveIndex_iff]
  refine ⟨fun i => (hrsq i).squarefree_of_dvd (h i), ?_,
    fun i => (hrcopW i).coprime_dvd_left (h i), ?_⟩
  · intro i j hij
    exact ((hrcop i j hij).coprime_dvd_left (h i)).coprime_dvd_right (h j)
  · have hdvd : (∏ i, d i) ∣ ∏ i, r i :=
      Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => h i)
    have hpos : 0 < ∏ i, r i := Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hr i)
    exact lt_of_le_of_lt (Nat.le_of_dvd hpos hdvd) hrprod

/-- Every prime dividing a coordinate of a sieve tuple (at modulus `W k`)
exceeds `D₀ k`. -/
theorem D₀_lt_of_prime_dvd_coord {k R : ℕ} {r : Fin k → ℕ}
    (hr : r ∈ kSieveIndex k R (W k)) {p : ℕ} (hp : p.Prime) {i : Fin k}
    (hpi : p ∣ r i) : D₀ k < p :=
  D₀_lt_of_prime_dvd_coprime (((mem_kSieveIndex_iff r).mp hr).2.2.1 i) hp hpi

/-- **P0, uniqueness half.** By pairwise coprimality, a prime divides at
most one coordinate of a sieve tuple. -/
theorem prime_dvd_coord_unique {k R W : ℕ} {d : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) {p : ℕ} (hp : p.Prime) {i i' : Fin k}
    (h1 : p ∣ d i) (h2 : p ∣ d i') : i = i' := by
  by_contra hne
  have hcop : Nat.Coprime (d i) (d i') := ((mem_kSieveIndex_iff d).mp hd).2.1 i i' hne
  have hone : p ∣ 1 := hcop ▸ Nat.dvd_gcd h1 h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

/-- Indicator-product helper: a product of `{0,1}`-indicators over `Fin k`
is the indicator of the conjunction, with the values factored out. -/
private theorem prod_ite_mul {k : ℕ} (P : Fin k → Prop) [DecidablePred P]
    (f : Fin k → ℝ) :
    (∏ i, if P i then f i else 0) = if ∀ i, P i then ∏ i, f i else 0 := by
  by_cases h : ∀ i, P i
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun i _ => if_pos (h i)
  · rw [if_neg h]
    obtain ⟨i, hPi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hPi)

/-- Indicator-product helper over a general `Finset`. -/
private theorem prod_ite_one {ι : Type*} (s : Finset ι) (P : ι → Prop)
    [DecidablePred P] :
    (∏ x ∈ s, if P x then (1 : ℝ) else 0) = if ∀ x ∈ s, P x then 1 else 0 := by
  by_cases h : ∀ x ∈ s, P x
  · rw [if_pos h]
    exact Finset.prod_eq_one fun x hx => if_pos (h x hx)
  · rw [if_neg h]
    obtain ⟨x, hx⟩ := not_forall.mp h
    obtain ⟨hxs, hPx⟩ := Classical.not_imp.mp hx
    exact Finset.prod_eq_zero hxs (if_neg hPx)

/-- Move the innermost of three nested sums to the front (as in
`Diagonal.lean`). -/
private theorem sum_move3 {α β γ δ : Type*} [AddCommMonoid δ]
    (A : Finset α) (B : Finset β) (C : Finset γ) (F : α → β → γ → δ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, F a b c)
      = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, F a b c := by
  rw [← Finset.sum_product']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_product' A B (fun a b => F a b c)

/-- `|μ n| ≤ 1` as a real number. -/
theorem abs_moebius_real_le_one (n : ℕ) : |((μ n : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  have h : |μ n| ≤ 1 := by
    rw [ArithmeticFunction.abs_moebius]
    split_ifs <;> norm_num
  exact_mod_cast h

/-- The classical Möbius identity `∑_{t ∣ n} μ t = [n = 1]`, real-valued. -/
theorem sum_divisors_moebius_eq (n : ℕ) :
    (∑ t ∈ n.divisors, ((μ t : ℤ) : ℝ)) = if n = 1 then 1 else 0 := by
  have h : (∑ t ∈ n.divisors, μ t) = if n = 1 then 1 else 0 := by
    rw [← ArithmeticFunction.one_apply (R := ℤ) (x := n),
      ← ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.coe_mul_zeta_apply]
  calc (∑ t ∈ n.divisors, ((μ t : ℤ) : ℝ))
      = ((∑ t ∈ n.divisors, μ t : ℤ) : ℝ) := by push_cast; ring
    _ = ((if n = 1 then 1 else 0 : ℤ) : ℝ) := by rw [h]
    _ = if n = 1 then 1 else 0 := by split_ifs <;> simp

/-- Rewrite a divisor sum as a guarded sum over an ambient `range`. -/
theorem sum_divisors_eq_sum_range {n M : ℕ} (hn : n ≠ 0) (hnM : n ≤ M)
    (f : ℕ → ℝ) :
    ∑ t ∈ n.divisors, f t
      = ∑ t ∈ Finset.range (M + 1), if t ∣ n then f t else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ fun _ _ => rfl
  ext t
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨htn, -⟩
    exact ⟨Nat.lt_succ_of_le (le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) htn) hnM), htn⟩
  · rintro ⟨-, htn⟩
    exact ⟨htn, hn⟩

/-! ## The collision radical `cRad` and the P0 indicator identity -/

/-- The collision radical of a pair: the product of all off-diagonal
cross-gcds. `cRad d e = 1` iff `(d,e)` is compatible (no collision). -/
def cRad {k : ℕ} (d e : Fin k → ℕ) : ℕ :=
  ∏ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, Nat.gcd (d ij.1) (e ij.2)

theorem cRad_pos {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) (_he : e ∈ kSieveIndex k R W) :
    0 < cRad d e :=
  Finset.prod_pos fun ij _ =>
    Nat.gcd_pos_of_pos_left _ (kSieveIndex_coord_pos hd ij.1)

/-- `cRad d e = 1` iff the pair is compatible. -/
theorem cRad_eq_one_iff {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) (_he : e ∈ kSieveIndex k R W) :
    cRad d e = 1 ↔ ¬ IsCollisionPair d e := by
  have hone : ∀ ij ∈ (Finset.univ : Finset (Fin k)).offDiag,
      1 ≤ Nat.gcd (d ij.1) (e ij.2) := fun ij _ =>
    Nat.gcd_pos_of_pos_left _ (kSieveIndex_coord_pos hd ij.1)
  rw [cRad, Finset.prod_eq_one_iff_of_one_le' hone]
  constructor
  · rintro h ⟨i, j, hij, hnc⟩
    exact hnc (h (i, j) (Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩))
  · intro h ij hij
    rw [Finset.mem_offDiag] at hij
    by_contra hnc
    exact h ⟨ij.1, ij.2, hij.2.2, hnc⟩

/-- A prime divides `cRad` iff it divides some cross-pair. -/
theorem prime_dvd_cRad_iff {k : ℕ} {d e : Fin k → ℕ} {p : ℕ} (hp : p.Prime) :
    p ∣ cRad d e
      ↔ ∃ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, p ∣ d ij.1 ∧ p ∣ e ij.2 := by
  rw [cRad, hp.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨ij, hij, hdvd⟩
    exact ⟨ij, hij, Nat.dvd_gcd_iff.mp hdvd⟩
  · rintro ⟨ij, hij, h1, h2⟩
    exact ⟨ij, hij, Nat.dvd_gcd h1 h2⟩

/-- **P0 — the exact disjoint-sum collision indicator.** For sieve tuples,
the indicator of "`p` collides" is the *sum* (not just bounded by the sum)
of the per-pair indicators: pairwise coprimality makes the witnessing pair
unique. -/
theorem collision_indicator {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) (he : e ∈ kSieveIndex k R W) {p : ℕ}
    (hp : p.Prime) :
    (if p ∣ cRad d e then (1 : ℝ) else 0)
      = ∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag,
          if p ∣ d ij.1 ∧ p ∣ e ij.2 then 1 else 0 := by
  by_cases hcol : p ∣ cRad d e
  · rw [if_pos hcol]
    obtain ⟨ij₀, hij₀, hdvd₀⟩ := (prime_dvd_cRad_iff hp).mp hcol
    rw [Finset.sum_eq_single_of_mem ij₀ hij₀ ?uniq, if_pos hdvd₀]
    case uniq =>
      intro ij _ hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hne (Prod.ext (prime_dvd_coord_unique hd hp h1 hdvd₀.1)
        (prime_dvd_coord_unique he hp h2 hdvd₀.2))
  · rw [if_neg hcol]
    symm
    apply Finset.sum_eq_zero
    intro ij hij
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hcol ((prime_dvd_cRad_iff hp).mpr ⟨ij, hij, h1, h2⟩)

/-! ## P1 — the forced-divisor exact evaluation `T_forced` -/

/-- On the sieve support, `λ(d)/∏ᵢdᵢ = ∏ᵢμ(dᵢ) · wSum d`. -/
theorem lam_div_prod {k R W : ℕ} (y : (Fin k → ℕ) → ℝ) {d : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) :
    lam k R W y d / ∏ i, (d i : ℝ)
      = (∏ i, ((μ (d i) : ℤ) : ℝ)) * wSum k R W y d := by
  have hne : (∏ i, (d i : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by
      exact_mod_cast (kSieveIndex_coord_pos hd i).ne'
  rw [lam, Finset.prod_mul_distrib, div_eq_iff hne]
  ring

/-- **P1 — `T_forced`.** The forced-divisor λ-sum evaluates exactly:
`∑_{d ∈ 𝒟, v ∣ d} λ(d)/∏ᵢdᵢ = ∏ᵢμ(vᵢ) · y(v)/∏ᵢφ(vᵢ)`.
(If `v ∉ 𝒟` both sides vanish: the Möbius delta `[r = v]` never fires on
the support, and `y v = 0`.) -/
theorem T_forced (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W → y r = 0) (v : Fin k → ℕ) :
    ∑ d ∈ (kSieveIndex k R W).filter (fun d => ∀ i, v i ∣ d i),
        lam k R W y d / ∏ i, (d i : ℝ)
      = (∏ i, ((μ (v i) : ℤ) : ℝ)) * y v / ∏ i, (Nat.totient (v i) : ℝ) := by
  rw [Finset.sum_filter]
  calc ∑ d ∈ kSieveIndex k R W,
        (if ∀ i, v i ∣ d i then lam k R W y d / ∏ i, (d i : ℝ) else 0)
      = ∑ d ∈ kSieveIndex k R W, (if ∀ i, v i ∣ d i then
          (∏ i, ((μ (d i) : ℤ) : ℝ)) * wSum k R W y d else 0) := by
        apply Finset.sum_congr rfl; intro d hd
        split_ifs with h
        · exact lam_div_prod y hd
        · rfl
    _ = ∑ d ∈ kSieveIndex k R W, ∑ r ∈ kSieveIndex k R W,
          (if ∀ i, v i ∣ d i then (∏ i, ((μ (d i) : ℤ) : ℝ)) *
            (if ∀ i, d i ∣ r i then y r / ∏ i, (Nat.totient (r i) : ℝ) else 0) else 0) := by
        apply Finset.sum_congr rfl; intro d _
        split_ifs with h
        · rw [wSum, Finset.mul_sum]
        · rw [Finset.sum_const_zero]
    _ = ∑ r ∈ kSieveIndex k R W, ∑ d ∈ kSieveIndex k R W,
          (if ∀ i, d i ∣ r i then
            (if ∀ i, v i ∣ d i then ∏ i, ((μ (d i) : ℤ) : ℝ) else 0)
              * (y r / ∏ i, (Nat.totient (r i) : ℝ)) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro r _
        apply Finset.sum_congr rfl; intro d _
        split_ifs <;> ring
    _ = ∑ r ∈ kSieveIndex k R W,
          ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
            (if ∀ i, v i ∣ d i then ∏ i, ((μ (d i) : ℤ) : ℝ) else 0)
              * (y r / ∏ i, (Nat.totient (r i) : ℝ)) := by
        apply Finset.sum_congr rfl; intro r hr
        exact sum_ksieve_guarded_eq hr (fun d =>
          (if ∀ i, v i ∣ d i then ∏ i, ((μ (d i) : ℤ) : ℝ) else 0)
            * (y r / ∏ i, (Nat.totient (r i) : ℝ)))
    _ = ∑ r ∈ kSieveIndex k R W,
          (if v = r then ∏ i, ((μ (v i) : ℤ) : ℝ) else 0)
            * (y r / ∏ i, (Nat.totient (r i) : ℝ)) := by
        apply Finset.sum_congr rfl; intro r hr
        have hrsq : ∀ i, Squarefree (r i) := fun i =>
          ((mem_kSieveIndex_iff r).mp hr).1 i
        rw [← Finset.sum_mul]
        congr 1
        calc ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
              (if ∀ i, v i ∣ d i then ∏ i, ((μ (d i) : ℤ) : ℝ) else 0)
            = ∑ d ∈ Fintype.piFinset (fun i => (r i).divisors),
                ∏ i, (if v i ∣ d i then ((μ (d i) : ℤ) : ℝ) else 0) := by
              apply Finset.sum_congr rfl; intro d _
              rw [prod_ite_mul]
          _ = ∏ i, ∑ d_i ∈ (r i).divisors,
                (if v i ∣ d_i then ((μ d_i : ℤ) : ℝ) else 0) :=
              (Finset.prod_univ_sum (fun i => (r i).divisors)
                (fun i d_i => if v i ∣ d_i then ((μ d_i : ℤ) : ℝ) else 0)).symm
          _ = ∏ i, (if v i = r i then ((μ (v i) : ℤ) : ℝ) else 0) := by
              apply Finset.prod_congr rfl; intro i _
              exact_mod_cast Salt.SelbergPort.moebius_inv_dvd_lower_bound (v i) (r i) (hrsq i)
          _ = if ∀ i, v i = r i then ∏ i, ((μ (v i) : ℤ) : ℝ) else 0 :=
              prod_ite_mul _ _
          _ = if v = r then ∏ i, ((μ (v i) : ℤ) : ℝ) else 0 := by
              congr 1
              rw [eq_iff_iff, ← funext_iff]
    _ = (∏ i, ((μ (v i) : ℤ) : ℝ)) * y v / ∏ i, (Nat.totient (v i) : ℝ) := by
        have hpt : ∀ r ∈ kSieveIndex k R W,
            (if v = r then ∏ i, ((μ (v i) : ℤ) : ℝ) else 0)
              * (y r / ∏ i, (Nat.totient (r i) : ℝ))
            = if v = r then (∏ i, ((μ (v i) : ℤ) : ℝ))
                * (y r / ∏ i, (Nat.totient (r i) : ℝ)) else 0 := by
          intro r _
          split_ifs <;> ring
        rw [Finset.sum_congr rfl hpt, Finset.sum_ite_eq]
        by_cases hv : v ∈ kSieveIndex k R W
        · rw [if_pos hv, mul_div_assoc]
        · rw [if_neg hv, hy0 v hv, mul_zero, zero_div]

/-! ## P2 — the constrained diagonalisation `inner_exact` -/

/-- The tensor gcd expansion: for `d, e ∈ 𝒟`,
`∏ᵢ gcd(dᵢ,eᵢ) = ∑_{u ∈ 𝒟, u ∣ d, u ∣ e} ∏ᵢ φ(uᵢ)` — exact, with the
`u`-sum ranging over the *whole* sieve set thanks to divisor-closedness. -/
theorem prod_gcd_expand {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) (_he : e ∈ kSieveIndex k R W) :
    (∏ i, (Nat.gcd (d i) (e i) : ℝ))
      = ∑ u ∈ kSieveIndex k R W,
          if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
            ∏ i, (Nat.totient (u i) : ℝ) else 0 := by
  set g : Fin k → ℕ := fun i => Nat.gcd (d i) (e i) with hg
  have hgd : ∀ i, g i ∣ d i := fun i => Nat.gcd_dvd_left _ _
  have hgmem : g ∈ kSieveIndex k R W := mem_kSieveIndex_of_dvd hd hgd
  have hguard : ∀ u : Fin k → ℕ,
      ((∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i)) ↔ (∀ i, u i ∣ g i) := by
    intro u
    constructor
    · rintro ⟨h1, h2⟩ i
      exact Nat.dvd_gcd (h1 i) (h2 i)
    · intro h
      exact ⟨fun i => (h i).trans (Nat.gcd_dvd_left _ _),
        fun i => (h i).trans (Nat.gcd_dvd_right _ _)⟩
  calc (∏ i, (g i : ℝ))
      = ∏ i, ∑ u_i ∈ (g i).divisors, (Nat.totient u_i : ℝ) := by
        apply Finset.prod_congr rfl; intro i _
        symm
        rw [← Nat.cast_sum]
        exact_mod_cast Nat.sum_totient (g i)
    _ = ∑ u ∈ Fintype.piFinset (fun i => (g i).divisors),
          ∏ i, (Nat.totient (u i) : ℝ) :=
        Finset.prod_univ_sum (fun i => (g i).divisors)
          (fun _ u_i => (Nat.totient u_i : ℝ))
    _ = ∑ u ∈ kSieveIndex k R W,
          if ∀ i, u i ∣ g i then ∏ i, (Nat.totient (u i) : ℝ) else 0 :=
        (sum_ksieve_guarded_eq hgmem (fun u => ∏ i, (Nat.totient (u i) : ℝ))).symm
    _ = ∑ u ∈ kSieveIndex k R W,
          if (∀ i, u i ∣ d i) ∧ (∀ i, u i ∣ e i) then
            ∏ i, (Nat.totient (u i) : ℝ) else 0 := by
        apply Finset.sum_congr rfl; intro u _
        congr 1
        rw [eq_iff_iff]
        exact (hguard u).symm

/-- Indicator algebra: `[P]·[Q] = [P ∧ Q]`. -/
private theorem ite_one_mul_ite_one (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then (1 : ℝ) else 0) * (if Q then (1 : ℝ) else 0)
      = if P ∧ Q then (1 : ℝ) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- **P2 — `inner_exact`, the constrained diagonalisation.** The
`(σ,τ)`-forced double λ-sum diagonalises exactly to a signed `u`-sum of
`ŷ`-evaluations at the componentwise lcms. All inner sums stay signed. -/
theorem inner_exact (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    (hy0 : ∀ r, r ∉ kSieveIndex k R W → y r = 0) (σ τ : Fin k → ℕ) :
    ∑ d ∈ (kSieveIndex k R W).filter (fun d => ∀ i, σ i ∣ d i),
      ∑ e ∈ (kSieveIndex k R W).filter (fun e => ∀ i, τ i ∣ e i),
        lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
      = ∑ u ∈ kSieveIndex k R W, (∏ i, (Nat.totient (u i) : ℝ))
          * ((∏ i, ((μ (Nat.lcm (u i) (σ i)) : ℤ) : ℝ))
              * y (fun i => Nat.lcm (u i) (σ i))
              / ∏ i, (Nat.totient (Nat.lcm (u i) (σ i)) : ℝ))
          * ((∏ i, ((μ (Nat.lcm (u i) (τ i)) : ℤ) : ℝ))
              * y (fun i => Nat.lcm (u i) (τ i))
              / ∏ i, (Nat.totient (Nat.lcm (u i) (τ i)) : ℝ)) := by
  classical
  -- Per-pair algebra: `λλ/∏lcm = (λ/∏d)(λ/∏e)·∏gcd`.
  have halg : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
        = (lam k R W y d / ∏ i, (d i : ℝ)) * (lam k R W y e / ∏ i, (e i : ℝ))
            * ∏ i, (Nat.gcd (d i) (e i) : ℝ) := by
    intro d hd e he
    have hdne : (∏ i, (d i : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        exact_mod_cast (kSieveIndex_coord_pos hd i).ne'
    have hene : (∏ i, (e i : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        exact_mod_cast (kSieveIndex_coord_pos he i).ne'
    have hlne : (∏ i, (Nat.lcm (d i) (e i) : ℝ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => by
        have hpos : 0 < Nat.lcm (d i) (e i) := Nat.pos_of_ne_zero
          (Nat.lcm_ne_zero (kSieveIndex_coord_pos hd i).ne'
            (kSieveIndex_coord_pos he i).ne')
        exact_mod_cast hpos.ne'
    have hkey : (∏ i, (Nat.gcd (d i) (e i) : ℝ)) * (∏ i, (Nat.lcm (d i) (e i) : ℝ))
        = (∏ i, (d i : ℝ)) * (∏ i, (e i : ℝ)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro i _
      rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.gcd_mul_lcm]
    rw [div_mul_div_comm, div_mul_eq_mul_div,
      div_eq_div_iff hlne (mul_ne_zero hdne hene)]
    linear_combination (-(lam k R W y d * lam k R W y e)) * hkey
  calc ∑ d ∈ (kSieveIndex k R W).filter (fun d => ∀ i, σ i ∣ d i),
      ∑ e ∈ (kSieveIndex k R W).filter (fun e => ∀ i, τ i ∣ e i),
        lam k R W y d * lam k R W y e / ∏ i, (Nat.lcm (d i) (e i) : ℝ)
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W, ∑ u ∈ kSieveIndex k R W,
          (∏ i, (Nat.totient (u i) : ℝ))
            * ((if ∀ i, Nat.lcm (u i) (σ i) ∣ d i then (1:ℝ) else 0)
                * (lam k R W y d / ∏ i, (d i : ℝ)))
            * ((if ∀ i, Nat.lcm (u i) (τ i) ∣ e i then (1:ℝ) else 0)
                * (lam k R W y e / ∏ i, (e i : ℝ))) := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro d hd
        by_cases hσd : ∀ i, σ i ∣ d i
        · rw [if_pos hσd, Finset.sum_filter]
          apply Finset.sum_congr rfl; intro e he
          by_cases hτe : ∀ i, τ i ∣ e i
          · rw [if_pos hτe, halg d hd e he, prod_gcd_expand hd he, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro u _
            by_cases hud : ∀ i, u i ∣ d i
            · by_cases hue : ∀ i, u i ∣ e i
              · rw [if_pos ⟨hud, hue⟩,
                  if_pos (fun i => Nat.lcm_dvd (hud i) (hσd i)),
                  if_pos (fun i => Nat.lcm_dvd (hue i) (hτe i))]
                ring
              · obtain ⟨i₀, hi₀⟩ := not_forall.mp hue
                rw [if_neg (fun h => hue h.2),
                  if_neg (fun h : ∀ i, Nat.lcm (u i) (τ i) ∣ e i =>
                    hi₀ ((Nat.dvd_lcm_left _ _).trans (h i₀)))]
                ring
            · obtain ⟨i₀, hi₀⟩ := not_forall.mp hud
              rw [if_neg (fun h => hud h.1),
                if_neg (fun h : ∀ i, Nat.lcm (u i) (σ i) ∣ d i =>
                  hi₀ ((Nat.dvd_lcm_left _ _).trans (h i₀)))]
              ring
          · rw [if_neg hτe]
            symm; apply Finset.sum_eq_zero; intro u _
            obtain ⟨i₀, hi₀⟩ := not_forall.mp hτe
            rw [if_neg (fun h : ∀ i, Nat.lcm (u i) (τ i) ∣ e i =>
              hi₀ ((Nat.dvd_lcm_right _ _).trans (h i₀)))]
            ring
        · rw [if_neg hσd]
          symm; apply Finset.sum_eq_zero; intro e _
          apply Finset.sum_eq_zero; intro u _
          obtain ⟨i₀, hi₀⟩ := not_forall.mp hσd
          rw [if_neg (fun h : ∀ i, Nat.lcm (u i) (σ i) ∣ d i =>
            hi₀ ((Nat.dvd_lcm_right _ _).trans (h i₀)))]
          ring
    _ = ∑ u ∈ kSieveIndex k R W, (∏ i, (Nat.totient (u i) : ℝ))
          * (∑ d ∈ kSieveIndex k R W,
              (if ∀ i, Nat.lcm (u i) (σ i) ∣ d i then (1:ℝ) else 0)
                * (lam k R W y d / ∏ i, (d i : ℝ)))
          * (∑ e ∈ kSieveIndex k R W,
              (if ∀ i, Nat.lcm (u i) (τ i) ∣ e i then (1:ℝ) else 0)
                * (lam k R W y e / ∏ i, (e i : ℝ))) := by
        rw [sum_move3]
        apply Finset.sum_congr rfl; intro u _
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        ring
    _ = _ := by
        apply Finset.sum_congr rfl; intro u _
        have hσ_eval := T_forced k R W y hy0 (fun i => Nat.lcm (u i) (σ i))
        have hτ_eval := T_forced k R W y hy0 (fun i => Nat.lcm (u i) (τ i))
        rw [Finset.sum_filter] at hσ_eval hτ_eval
        rw [← hσ_eval, ← hτ_eval]
        congr 1
        · congr 1
          apply Finset.sum_congr rfl; intro d _
          split_ifs <;> ring
        · apply Finset.sum_congr rfl; intro e _
          split_ifs <;> ring

/-! ## P5 — the R-free Euler tail -/

/-- Telescoping tail bound:
`∑_{a < n ≤ b} (n−1)⁻² ≤ (a−1)⁻¹ − (b−1)⁻¹` for `2 ≤ a ≤ b`. -/
private theorem inv_sq_tele (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a ≤ b →
      (∑ n ∈ Finset.Icc (a + 1) b, (((n : ℝ) - 1)⁻¹) ^ 2)
        ≤ ((a : ℝ) - 1)⁻¹ - ((b : ℝ) - 1)⁻¹ := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ b hab ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast le_trans ha hab
      have hstep : (((b + 1 : ℕ) : ℝ) - 1)⁻¹ ^ 2
          ≤ ((b : ℝ) - 1)⁻¹ - (((b + 1 : ℕ) : ℝ) - 1)⁻¹ := by
        push_cast
        have h1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
        have h2 : (0 : ℝ) < (b : ℝ) := by linarith
        rw [show ((b : ℝ) + 1 - 1) = (b : ℝ) by ring, ← sub_nonneg]
        have hexp : ((b : ℝ) - 1)⁻¹ - (b : ℝ)⁻¹ - ((b : ℝ)⁻¹) ^ 2
            = (((b : ℝ)) ^ 2 * ((b : ℝ) - 1))⁻¹ := by
          field_simp
          ring
        rw [hexp]
        have hposm : (0 : ℝ) < ((b : ℝ)) ^ 2 * ((b : ℝ) - 1) := by nlinarith
        exact inv_nonneg.mpr hposm.le
      linarith [ih]

/-- Product-versus-sum: if the `aₓ ≥ 0` sum to at most `1/2`, then
`∏(1 + aₓ) ≤ 1 + 2∑aₓ`. Elementary induction — no logs, no `exp`. -/
private theorem prod_one_add_le {ι : Type*} (s : Finset ι)
    (a : ι → ℝ) (ha : ∀ x ∈ s, 0 ≤ a x) (hs : ∑ x ∈ s, a x ≤ 1 / 2) :
    ∏ x ∈ s, (1 + a x) ≤ 1 + 2 * ∑ x ∈ s, a x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx]
      have hax : 0 ≤ a x := ha x (Finset.mem_insert_self x s)
      have has : ∀ z ∈ s, 0 ≤ a z := fun z hz =>
        ha z (Finset.mem_insert_of_mem hz)
      have hsum_nonneg : 0 ≤ ∑ z ∈ s, a z := Finset.sum_nonneg has
      have hss : ∑ z ∈ s, a z ≤ 1 / 2 := by
        rw [Finset.sum_insert hx] at hs
        linarith
      have hih := ih has hss
      have hprod_nonneg : (0 : ℝ) ≤ ∏ z ∈ s, (1 + a z) :=
        Finset.prod_nonneg fun z hz => by linarith [has z hz]
      nlinarith [hih, hax, hss, hsum_nonneg]

/-- **P5 — `euler_tail`.** The Euler-product tail over squarefree moduli
with all prime factors `> D₀ k`: with per-prime weight `3k²·(p−1)⁻²`, the
total (excluding the trivial modulus `1`) is at most `12k²/D₀ k` —
explicit and `R`-free. `M` is an arbitrary finite range cap. -/
theorem euler_tail (k M : ℕ) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    ∑ t ∈ ((Finset.range M).filter
        (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1,
      (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
        * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
      ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by
  classical
  have hD12 : 12 ≤ D₀ k := le_trans (by nlinarith) hD
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by omega
    exact_mod_cast this
  set L : ℝ := 3 * (k : ℝ) ^ 2 with hL
  have hLpos : 0 < L := by positivity
  set a : ℕ → ℝ := fun p => L * (((p : ℝ) - 1)⁻¹) ^ 2 with haDef
  have ha_nonneg : ∀ p, 0 ≤ a p := fun p => by positivity
  set SF := ((Finset.range M).filter
      (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1 with hSF
  set PP := (Finset.range M).filter (fun p => p.Prime ∧ D₀ k < p) with hPP
  -- Step 1: each term is `∏_{p ∣ t} a p`.
  have hterm : ∀ t ∈ SF,
      (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
          * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
        = ∏ p ∈ t.primeFactors, a p := by
    intro t _
    rw [haDef, Finset.prod_mul_distrib, Finset.prod_const, hL]
  -- Step 2: `primeFactors` injects `SF` into `PP.powerset.erase ∅`.
  have hinj : Set.InjOn Nat.primeFactors ↑SF := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, hSF, Finset.mem_erase, Finset.mem_filter] at hx hy
    have hx' := Nat.prod_primeFactors_of_squarefree hx.2.2.1
    rw [← hx', hxy, Nat.prod_primeFactors_of_squarefree hy.2.2.1]
  have hsub : SF.image Nat.primeFactors ⊆ PP.powerset.erase ∅ := by
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨t, ht, rfl⟩ := hS
    rw [hSF, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨hne1, htM, hsq, hbig⟩ := ht
    rw [Finset.mem_erase, Finset.mem_powerset]
    constructor
    · -- `t.primeFactors ≠ ∅` since `t ≠ 1` and `t` squarefree (so `t ≥ 2`).
      have ht2 : 1 < t := by
        rcases Nat.lt_or_ge t 2 with h | h
        · interval_cases t
          · exact absurd hsq not_squarefree_zero
          · exact absurd rfl hne1
        · omega
      have : t.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr ht2
      exact Finset.nonempty_iff_ne_empty.mp this
    · intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ t := Nat.dvd_of_mem_primeFactors hp
      have ht0 : 0 < t := Nat.pos_of_ne_zero hsq.ne_zero
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd ht0 hpd) htM, hpp, hbig p hp⟩
  -- Step 3: the powerset sum is the Euler product minus 1.
  have hprodadd : ∏ p ∈ PP, (1 + a p)
      = ∑ S ∈ PP.powerset, ∏ p ∈ S, a p := by
    have h := Finset.prod_add (fun p => a p) (fun _ => (1 : ℝ)) PP
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hsplit : ∑ S ∈ PP.powerset.erase ∅, ∏ p ∈ S, a p
      = (∏ p ∈ PP, (1 + a p)) - 1 := by
    have h := Finset.sum_erase_add PP.powerset (fun S => ∏ p ∈ S, a p)
      (Finset.empty_mem_powerset PP)
    rw [Finset.prod_empty] at h
    rw [hprodadd]
    linarith
  -- Step 4: the prime sum is at most `L · 2/D₀ ≤ 1/2`.
  have htailsum : ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 ≤ 2 / (D₀ k : ℝ) := by
    have hPPsub : PP ⊆ Finset.Icc (D₀ k + 1) M := by
      intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
    have hmono : ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2
        ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) M, (((n : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hPPsub fun n _ _ => by positivity
    rcases Nat.lt_or_ge M (D₀ k) with hM | hM
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hmono
      exact le_trans hmono (by positivity)
    · have htele := inv_sq_tele (D₀ k) (by omega) M hM
      have hlast : (0 : ℝ) < (M : ℝ) - 1 ∨ ((M : ℝ) - 1)⁻¹ = ((M : ℝ) - 1)⁻¹ :=
        Or.inr rfl
      have hMinv : 0 ≤ ((M : ℝ) - 1)⁻¹ := by
        have hM2 : (2 : ℝ) ≤ (M : ℝ) := by
          have : 12 ≤ M := by omega
          exact_mod_cast (by omega : 2 ≤ M)
        rw [inv_nonneg]
        linarith
      have hfrac : ((D₀ k : ℝ) - 1)⁻¹ ≤ 2 / (D₀ k : ℝ) := by
        have h1 : (0 : ℝ) < (D₀ k : ℝ) - 1 := by
          have : (12 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD12
          linarith
        rw [inv_eq_one_div, div_le_div_iff₀ h1 hDpos]
        have : (12 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD12
        linarith
      linarith
  have hasum : ∑ p ∈ PP, a p ≤ 1 / 2 := by
    have h1 : ∑ p ∈ PP, a p = L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 := by
      simp only [haDef, Finset.mul_sum]
    rw [h1]
    have h2 : L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 ≤ L * (2 / (D₀ k : ℝ)) :=
      mul_le_mul_of_nonneg_left htailsum hLpos.le
    have h3 : L * (2 / (D₀ k : ℝ)) ≤ 1 / 2 := by
      have hcast : (12 : ℝ) * (k : ℝ) ^ 2 ≤ (D₀ k : ℝ) := by exact_mod_cast hD
      have heq : L * (2 / (D₀ k : ℝ)) = 6 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by
        rw [hL]; ring
      rw [heq, div_le_div_iff₀ hDpos (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  -- Assemble.
  calc ∑ t ∈ SF, (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
          * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2
      = ∑ t ∈ SF, ∏ p ∈ t.primeFactors, a p := Finset.sum_congr rfl hterm
    _ = ∑ S ∈ SF.image Nat.primeFactors, ∏ p ∈ S, a p := by
        have himg : ∑ S ∈ SF.image Nat.primeFactors, ∏ p ∈ S, a p
            = ∑ t ∈ SF, ∏ p ∈ t.primeFactors, a p := Finset.sum_image hinj
        rw [himg]
    _ ≤ ∑ S ∈ PP.powerset.erase ∅, ∏ p ∈ S, a p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun S _ _ =>
          Finset.prod_nonneg fun p _ => ha_nonneg p
    _ = (∏ p ∈ PP, (1 + a p)) - 1 := hsplit
    _ ≤ (1 + 2 * ∑ p ∈ PP, a p) - 1 := by
        have := prod_one_add_le PP a (fun p _ => ha_nonneg p) hasum
        linarith
    _ = 2 * ∑ p ∈ PP, a p := by ring
    _ ≤ 2 * (L * (2 / (D₀ k : ℝ))) := by
        have h1 : ∑ p ∈ PP, a p = L * ∑ p ∈ PP, (((p : ℝ) - 1)⁻¹) ^ 2 := by
          simp only [haDef, Finset.mul_sum]
        rw [h1]
        have h2 := mul_le_mul_of_nonneg_left htailsum hLpos.le
        linarith
    _ = 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by
        rw [hL]
        field_simp
        ring

/-! ## P3 helpers — lcm splitting, assignments, the erasure machinery -/

/-- For squarefree `a`: `lcm b a = b · (a/gcd(a,b))` with coprime factors. -/
theorem lcm_split {a b : ℕ} (ha : Squarefree a) :
    Nat.lcm b a = b * (a / Nat.gcd a b) ∧ Nat.Coprime b (a / Nat.gcd a b) := by
  have hga : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  constructor
  · rw [Nat.lcm, Nat.gcd_comm b a, Nat.mul_div_assoc b hga]
  · -- a common prime of `b` and `a/g` would divide `g`, hence square into `a`.
    have hsq_split : Squarefree (Nat.gcd a b * (a / Nat.gcd a b)) := by
      rwa [Nat.mul_div_cancel' hga]
    have hcop_g : Nat.Coprime (Nat.gcd a b) (a / Nat.gcd a b) :=
      Nat.coprime_of_squarefree_mul hsq_split
    have h1 : Nat.gcd (a / Nat.gcd a b) b ∣ Nat.gcd a b :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.div_dvd_of_dvd hga))
        (Nat.gcd_dvd_right _ _)
    have h2 : Nat.gcd (a / Nat.gcd a b) b ∣
        Nat.gcd (Nat.gcd a b) (a / Nat.gcd a b) :=
      Nat.dvd_gcd h1 (Nat.gcd_dvd_left _ _)
    rw [hcop_g] at h2
    exact Nat.Coprime.symm (Nat.dvd_one.mp h2)

/-- Totient splitting at the lcm: for squarefree `a` and `b > 0`,
`φ(lcm b a) = φ(b) · ∏_{p ∣ a, p ∤ b} (p−1)` (real-valued). -/
theorem totient_lcm_split {a b : ℕ} (ha : Squarefree a) (_hb : 0 < b) :
    (Nat.totient (Nat.lcm b a) : ℝ)
      = (Nat.totient b : ℝ)
          * ∏ p ∈ (a / Nat.gcd a b).primeFactors, ((p : ℝ) - 1) := by
  obtain ⟨heq, hcop⟩ := lcm_split (a := a) (b := b) ha
  have hcsq : Squarefree (a / Nat.gcd a b) :=
    ha.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left a b))
  rw [heq, Nat.totient_mul hcop, Nat.cast_mul, totient_squarefree_cast hcsq]

/-- Prime membership in the lcm cofactor: `p ∣ a/gcd(a,b) ↔ p ∣ a ∧ p ∤ b`
for squarefree `a`. -/
theorem prime_dvd_cofactor_iff {a b : ℕ} (ha : Squarefree a) {p : ℕ}
    (hp : p.Prime) :
    p ∣ a / Nat.gcd a b ↔ p ∣ a ∧ ¬ p ∣ b := by
  have hga : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
  have heq : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' hga
  constructor
  · intro hpc
    have hpa : p ∣ a := hpc.trans (Nat.div_dvd_of_dvd hga)
    refine ⟨hpa, fun hpb => ?_⟩
    have hpg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    have hsq : p * p ∣ a := heq ▸ mul_dvd_mul hpg hpc
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (ha p hsq))
  · rintro ⟨hpa, hpb⟩
    have hpg : ¬ p ∣ Nat.gcd a b := fun h => hpb (h.trans (Nat.gcd_dvd_right a b))
    have hpm : p ∣ Nat.gcd a b * (a / Nat.gcd a b) := by rw [heq]; exact hpa
    rcases (Nat.Prime.dvd_mul hp).mp hpm with h | h
    · exact absurd h hpg
    · exact h

/-- The finite set of prime-to-slot assignments for a modulus `s`: one
off-diagonal pair `(i,j)` per prime of `s`. -/
def assignments (k s : ℕ) :
    Finset ((p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k) :=
  s.primeFactors.pi (fun _ => (Finset.univ : Finset (Fin k)).offDiag)

/-- The slot-selected forced tuple of an assignment: coordinate `i` gets the
product of the primes of `s` assigned (by `sel ∘ α`) to slot `i`. -/
def slotProd {k : ℕ} (s : ℕ)
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k)
    (sel : Fin k × Fin k → Fin k) (i : Fin k) : ℕ :=
  ∏ q ∈ s.primeFactors.attach.filter (fun q => sel (α q.1 q.2) = i), (q : ℕ)

/-- Each slot product divides `s`. -/
theorem slotProd_dvd {k s : ℕ} (hs : Squarefree s)
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k)
    (sel : Fin k × Fin k → Fin k) (i : Fin k) : slotProd s α sel i ∣ s := by
  have h1 : slotProd s α sel i ∣ ∏ q ∈ s.primeFactors.attach, (q : ℕ) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  rwa [Finset.prod_attach s.primeFactors (fun p => p),
    Nat.prod_primeFactors_of_squarefree hs] at h1

/-- Prime divisibility of a slot product: exactly the primes of `s`
assigned to that slot. -/
theorem prime_dvd_slotProd_iff {k s : ℕ}
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k)
    (sel : Fin k × Fin k → Fin k) {p : ℕ} (hp : p.Prime) (i : Fin k) :
    p ∣ slotProd s α sel i ↔ ∃ h : p ∈ s.primeFactors, sel (α p h) = i := by
  constructor
  · intro hdvd
    rw [slotProd] at hdvd
    obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
    rw [Finset.mem_filter] at hq
    have hqprime : (q : ℕ).Prime := Nat.prime_of_mem_primeFactors q.2
    have hpe : p = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    subst hpe
    exact ⟨q.2, hq.2⟩
  · rintro ⟨h, hsel⟩
    exact Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_attach _ ⟨p, h⟩, hsel⟩)

/-- The y-tensor summand `F u = (∏f₀(uᵢ))²/∏φ(uᵢ)` is nonnegative. -/
private theorem yterm_nonneg {k : ℕ} (f₀ : ℕ → ℝ) (u : Fin k → ℕ) :
    0 ≤ (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) :=
  div_nonneg (sq_nonneg _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
/-- **Single-prime erasure (P3(e), one step).** Dividing the forced prime
`q₀` out of coordinate `i₀` contracts the constrained y-tensor sum by
`(q₀−1)⁻¹`, for any erasure-stable side condition `C`. -/
private theorem erase_branch {k R W : ℕ} {f₀ : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f₀ n)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    {q₀ : ℕ} (hq₀ : q₀.Prime) (i₀ : Fin k)
    (C : (Fin k → ℕ) → Prop) [DecidablePred C]
    (hC : ∀ u ∈ kSieveIndex k R W, q₀ ∣ u i₀ → C u →
      C (Function.update u i₀ (u i₀ / q₀))) :
    ∑ u ∈ (kSieveIndex k R W).filter (fun u => q₀ ∣ u i₀ ∧ C u),
        (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ ((q₀ : ℝ) - 1)⁻¹
          * ∑ u ∈ (kSieveIndex k R W).filter C,
              (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
  classical
  have hq₀R : (1 : ℝ) < (q₀ : ℝ) := by exact_mod_cast hq₀.one_lt
  have hq₀inv : (0 : ℝ) ≤ ((q₀ : ℝ) - 1)⁻¹ := by
    rw [inv_nonneg]; linarith
  set A := (kSieveIndex k R W).filter (fun u => q₀ ∣ u i₀ ∧ C u) with hA
  -- The erased tuple divides the original componentwise.
  have hgdvd : ∀ u : Fin k → ℕ, q₀ ∣ u i₀ →
      ∀ i, Function.update u i₀ (u i₀ / q₀) i ∣ u i := by
    intro u hq i
    rcases eq_or_ne i i₀ with rfl | hne
    · rw [Function.update_self]
      exact Nat.div_dvd_of_dvd hq
    · rw [Function.update_of_ne hne]
  -- (i) the erasure maps `A` into the `C`-filter.
  have hgmem : ∀ u ∈ A, Function.update u i₀ (u i₀ / q₀)
      ∈ (kSieveIndex k R W).filter C := by
    intro u hu
    rw [hA, Finset.mem_filter] at hu
    obtain ⟨hu𝒟, hq, hCu⟩ := hu
    rw [Finset.mem_filter]
    exact ⟨mem_kSieveIndex_of_dvd hu𝒟 (hgdvd u hq), hC u hu𝒟 hq hCu⟩
  -- (ii) termwise contraction.
  have hterm : ∀ u ∈ A,
      (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
        ≤ ((q₀ : ℝ) - 1)⁻¹
            * ((∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2
                / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) := by
    intro u hu
    rw [hA, Finset.mem_filter] at hu
    obtain ⟨hu𝒟, hq, _hCu⟩ := hu
    have hupos : 0 < u i₀ := kSieveIndex_coord_pos hu𝒟 i₀
    have husq : Squarefree (u i₀) := ((mem_kSieveIndex_iff u).mp hu𝒟).1 i₀
    have hmpos : 0 < u i₀ / q₀ := Nat.div_pos (Nat.le_of_dvd hupos hq) hq₀.pos
    have hsplit : u i₀ = q₀ * (u i₀ / q₀) := (Nat.mul_div_cancel' hq).symm
    have hcop : Nat.Coprime q₀ (u i₀ / q₀) :=
      Nat.coprime_of_squarefree_mul (hsplit ▸ husq)
    have hgu𝒟 : Function.update u i₀ (u i₀ / q₀) ∈ kSieveIndex k R W :=
      mem_kSieveIndex_of_dvd hu𝒟 (hgdvd u hq)
    -- totient product splits off `(q₀ − 1)`.
    have hφeq : (∏ i, (Nat.totient (u i) : ℝ))
        = ((q₀ : ℝ) - 1)
            * ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ
          (fun i => (Nat.totient (u i) : ℝ)) (Finset.mem_univ i₀),
        ← Finset.mul_prod_erase Finset.univ
          (fun i => (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ))
          (Finset.mem_univ i₀)]
      have h1 : (Nat.totient (u i₀) : ℝ)
          = ((q₀ : ℝ) - 1)
              * (Nat.totient (Function.update u i₀ (u i₀ / q₀) i₀) : ℝ) := by
        rw [Function.update_self]
        conv_lhs => rw [hsplit]
        rw [Nat.totient_mul hcop, Nat.totient_prime hq₀, Nat.cast_mul,
          Nat.cast_sub hq₀.one_lt.le, Nat.cast_one]
      have h2 : ∀ i ∈ Finset.univ.erase i₀,
          (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)
            = (Nat.totient (u i) : ℝ) := by
        intro i hi
        rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
      rw [h1, Finset.prod_congr rfl h2]
      ring
    -- numerator is monotone under the erasure.
    have hfle : (∏ i, f₀ (u i))
        ≤ ∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i) := by
      apply Finset.prod_le_prod (fun i _ => hf0 _)
      intro i _
      rcases eq_or_ne i i₀ with rfl | hne
      · rw [Function.update_self]
        exact hfmono _ _ (Nat.div_dvd_of_dvd hq) hmpos
      · rw [Function.update_of_ne hne]
    have hf0u : 0 ≤ ∏ i, f₀ (u i) := Finset.prod_nonneg fun i _ => hf0 _
    have hφgpos : 0 < ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) := by
      apply Finset.prod_pos
      intro i _
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos hgu𝒟 i)
    have hsq : (∏ i, f₀ (u i)) ^ 2
        ≤ (∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2 :=
      pow_le_pow_left₀ hf0u hfle 2
    calc (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
        = (∏ i, f₀ (u i)) ^ 2
            / (((q₀ : ℝ) - 1)
                * ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) := by
          rw [hφeq]
      _ ≤ (∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2
            / (((q₀ : ℝ) - 1)
                * ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) :=
          div_le_div₀ (sq_nonneg _) hsq
            (by nlinarith) (le_refl _)
      _ = ((q₀ : ℝ) - 1)⁻¹
            * ((∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2
                / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) := by
          rw [inv_mul_eq_div, div_div]
          ring_nf
  -- (iii) injectivity of the erasure on `A`.
  have hginj : ∀ x ∈ A, ∀ y ∈ A,
      Function.update x i₀ (x i₀ / q₀) = Function.update y i₀ (y i₀ / q₀)
        → x = y := by
    intro x hx y hy hxy
    rw [hA, Finset.mem_filter] at hx hy
    funext i
    rcases eq_or_ne i i₀ with hii | hne
    · rw [hii]
      have h3 : x i₀ / q₀ = y i₀ / q₀ := by
        have := congrFun hxy i₀
        rwa [Function.update_self, Function.update_self] at this
      have h1 : x i₀ = q₀ * (x i₀ / q₀) := (Nat.mul_div_cancel' hx.2.1).symm
      have h2 : y i₀ = q₀ * (y i₀ / q₀) := (Nat.mul_div_cancel' hy.2.1).symm
      rw [h1, h3, ← h2]
    · have := congrFun hxy i
      rwa [Function.update_of_ne hne, Function.update_of_ne hne] at this
  -- assemble
  calc ∑ u ∈ A, (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ ∑ u ∈ A, ((q₀ : ℝ) - 1)⁻¹
          * ((∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2
              / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((q₀ : ℝ) - 1)⁻¹
          * ∑ u ∈ A, (∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2
              / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) := by
        rw [Finset.mul_sum]
    _ = ((q₀ : ℝ) - 1)⁻¹
          * ∑ v ∈ A.image (fun u => Function.update u i₀ (u i₀ / q₀)),
              (∏ i, f₀ (v i)) ^ 2 / ∏ i, (Nat.totient (v i) : ℝ) := by
        have himg : ∑ v ∈ A.image (fun u => Function.update u i₀ (u i₀ / q₀)),
            (∏ i, f₀ (v i)) ^ 2 / ∏ i, (Nat.totient (v i) : ℝ)
            = ∑ u ∈ A, (∏ i, f₀ (Function.update u i₀ (u i₀ / q₀) i)) ^ 2
                / ∏ i, (Nat.totient (Function.update u i₀ (u i₀ / q₀) i) : ℝ) :=
          Finset.sum_image hginj
        rw [himg]
    _ ≤ ((q₀ : ℝ) - 1)⁻¹
          * ∑ v ∈ (kSieveIndex k R W).filter C,
              (∏ i, f₀ (v i)) ^ 2 / ∏ i, (Nat.totient (v i) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hq₀inv
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro v hv
          rw [Finset.mem_image] at hv
          obtain ⟨u, hu, rfl⟩ := hv
          exact hgmem u hu
        · intro v _ _
          exact yterm_nonneg f₀ v

/-- **P3(e) — the iterated erasure bound.** For a finite set `P` of primes
with two slot maps, the y-tensor sum constrained to "every `q ∈ Q` divides
one of its two slots" contracts by `2^{|Q|}·∏_{q∈Q}(q−1)⁻¹` relative to the
unconstrained sum. -/
private theorem erasure_bound {k R W : ℕ} {f₀ : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f₀ n)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (sl1 sl2 : {x // x ∈ P} → Fin k) (Q : Finset {x // x ∈ P}) :
    ∑ u ∈ (kSieveIndex k R W).filter
        (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
      (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
      ≤ 2 ^ Q.card * (∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)⁻¹)
          * ∑ u ∈ kSieveIndex k R W,
              (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
  induction Q using Finset.induction with
  | empty =>
      have hfilter : (kSieveIndex k R W).filter
          (fun u => ∀ q ∈ (∅ : Finset {x // x ∈ P}),
            (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
          = kSieveIndex k R W :=
        Finset.filter_true_of_mem (fun u _ => fun q hq =>
          absurd hq (Finset.notMem_empty q))
      rw [hfilter, Finset.card_empty, pow_zero, Finset.prod_empty, one_mul,
        one_mul]
  | insert q₀ Q hq₀Q ih =>
      have hq₀prime : (q₀ : ℕ).Prime := hP _ q₀.2
      have hq₀R : (1 : ℝ) < ((q₀ : ℕ) : ℝ) := by exact_mod_cast hq₀prime.one_lt
      have hq₀inv : (0 : ℝ) ≤ (((q₀ : ℕ) : ℝ) - 1)⁻¹ := by
        rw [inv_nonneg]; linarith
      -- stability of the Q-condition under erasing `q₀` anywhere
      have hstable : ∀ i₀ : Fin k, ∀ u ∈ kSieveIndex k R W, (q₀ : ℕ) ∣ u i₀ →
          (∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)) →
          (∀ q ∈ Q, (q : ℕ) ∣ (Function.update u i₀ (u i₀ / (q₀ : ℕ))) (sl1 q)
            ∨ (q : ℕ) ∣ (Function.update u i₀ (u i₀ / (q₀ : ℕ))) (sl2 q)) := by
        intro i₀ u _hu hdvd hCu q hq
        have hqne : (q : ℕ) ≠ (q₀ : ℕ) := by
          intro h
          exact hq₀Q (by rwa [Subtype.ext h] at hq)
        have hqprime : (q : ℕ).Prime := hP _ q.2
        have hpres : ∀ j, (q : ℕ) ∣ u j →
            (q : ℕ) ∣ Function.update u i₀ (u i₀ / (q₀ : ℕ)) j := by
          intro j hj
          rcases eq_or_ne j i₀ with hji | hne
          · rw [hji, Function.update_self]
            have hsplit : u i₀ = (q₀ : ℕ) * (u i₀ / (q₀ : ℕ)) :=
              (Nat.mul_div_cancel' hdvd).symm
            have hcop : Nat.Coprime (q : ℕ) (q₀ : ℕ) :=
              (Nat.coprime_primes hqprime hq₀prime).mpr hqne
            have hqm : (q : ℕ) ∣ (q₀ : ℕ) * (u i₀ / (q₀ : ℕ)) := by
              rw [← hsplit, ← hji]
              exact hj
            exact hcop.dvd_of_dvd_mul_left hqm
          · rw [Function.update_of_ne hne]
            exact hj
        rcases hCu q hq with h | h
        · exact Or.inl (hpres _ h)
        · exact Or.inr (hpres _ h)
      -- split the insert-condition filter into the two branch filters
      have hsub : (kSieveIndex k R W).filter
          (fun u => ∀ q ∈ insert q₀ Q,
            (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
          ⊆ ((kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
            ∪ ((kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        obtain ⟨hu𝒟, hcondu⟩ := hu
        rw [Finset.forall_mem_insert] at hcondu
        obtain ⟨h0, hQ⟩ := hcondu
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases h0 with h | h
        · exact Or.inl ⟨hu𝒟, h, hQ⟩
        · exact Or.inr ⟨hu𝒟, h, hQ⟩
      have hbr1 := erase_branch (R := R) (W := W) hf0 hfmono hq₀prime (sl1 q₀)
        (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
        (hstable (sl1 q₀))
      have hbr2 := erase_branch (R := R) (W := W) hf0 hfmono hq₀prime (sl2 q₀)
        (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))
        (hstable (sl2 q₀))
      calc ∑ u ∈ (kSieveIndex k R W).filter
            (fun u => ∀ q ∈ insert q₀ Q,
              (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
            (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
          ≤ ∑ u ∈ ((kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
              ∪ ((kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))),
              (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun u _ _ => yterm_nonneg f₀ u)
        _ ≤ (∑ u ∈ (kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              + ∑ u ∈ (kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
            have hui := Finset.sum_union_inter
              (s₁ := (kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
              (s₂ := (kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
              (f := fun u => (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            have hint : 0 ≤ ∑ u ∈ ((kSieveIndex k R W).filter
                (fun u => (q₀ : ℕ) ∣ u (sl1 q₀)
                  ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)))
                ∩ ((kSieveIndex k R W).filter (fun u => (q₀ : ℕ) ∣ u (sl2 q₀)
                  ∧ ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q))),
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) :=
              Finset.sum_nonneg (fun u _ => yterm_nonneg f₀ u)
            linarith
        _ ≤ ((((q₀ : ℕ) : ℝ) - 1)⁻¹
              * ∑ u ∈ (kSieveIndex k R W).filter
                  (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              + (((q₀ : ℕ) : ℝ) - 1)⁻¹
              * ∑ u ∈ (kSieveIndex k R W).filter
                  (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u (sl1 q) ∨ (q : ℕ) ∣ u (sl2 q)),
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) :=
            add_le_add hbr1 hbr2
        _ ≤ 2 * ((((q₀ : ℕ) : ℝ) - 1)⁻¹
              * (2 ^ Q.card * (∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)⁻¹)
                  * ∑ u ∈ kSieveIndex k R W,
                      (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))) := by
            have hstep := mul_le_mul_of_nonneg_left ih hq₀inv
            linarith
        _ = 2 ^ (insert q₀ Q).card
              * (∏ q ∈ insert q₀ Q, (((q : ℕ) : ℝ) - 1)⁻¹)
              * ∑ u ∈ kSieveIndex k R W,
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
            rw [Finset.card_insert_of_notMem hq₀Q, Finset.prod_insert hq₀Q,
              pow_succ]
            ring

/-- **P3(b) — one side's ŷ bound.** For a squarefree forced tuple `σv`,
`ŷ(u ∨ σv) ≤ ∏f₀(uᵢ) / (∏φ(uᵢ) · ∏ᵢ ∏_{p ∣ cᵢ}(p−1))`, where
`cᵢ = σvᵢ/gcd(σvᵢ,uᵢ)` carries exactly the non-absorbed primes. -/
private theorem yhat_side_le {k R W : ℕ} {y : (Fin k → ℕ) → ℝ} {f₀ : ℕ → ℝ}
    (hf0 : ∀ n, 0 ≤ f₀ n)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W then ∏ i, f₀ (r i) else 0)
    {σv : Fin k → ℕ} (hσsq : ∀ i, Squarefree (σv i))
    {u : Fin k → ℕ} (hu : u ∈ kSieveIndex k R W) :
    y (fun i => Nat.lcm (u i) (σv i))
        / ∏ i, (Nat.totient (Nat.lcm (u i) (σv i)) : ℝ)
      ≤ (∏ i, f₀ (u i))
          / ((∏ i, (Nat.totient (u i) : ℝ))
              * ∏ i, ∏ p ∈ (σv i / Nat.gcd (σv i) (u i)).primeFactors,
                  ((p : ℝ) - 1)) := by
  have hden : (∏ i, (Nat.totient (Nat.lcm (u i) (σv i)) : ℝ))
      = (∏ i, (Nat.totient (u i) : ℝ))
          * ∏ i, ∏ p ∈ (σv i / Nat.gcd (σv i) (u i)).primeFactors,
              ((p : ℝ) - 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact totient_lcm_split (hσsq i) (kSieveIndex_coord_pos hu i)
  have hdpos : 0 < (∏ i, (Nat.totient (u i) : ℝ))
      * ∏ i, ∏ p ∈ (σv i / Nat.gcd (σv i) (u i)).primeFactors, ((p : ℝ) - 1) := by
    apply mul_pos
    · apply Finset.prod_pos; intro i _
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos hu i)
    · apply Finset.prod_pos; intro i _
      apply Finset.prod_pos
      intro p hp
      have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
      linarith
  have hnum : y (fun i => Nat.lcm (u i) (σv i)) ≤ ∏ i, f₀ (u i) := by
    rw [hy]
    split_ifs with hmem
    · apply Finset.prod_le_prod (fun i _ => hf0 _)
      intro i _
      exact hfmono _ _ (Nat.dvd_lcm_left _ _) (kSieveIndex_coord_pos hu i)
    · exact Finset.prod_nonneg fun i _ => hf0 _
  rw [hden]
  exact div_le_div₀ (Finset.prod_nonneg fun i _ => hf0 _) hnum hdpos (le_refl _)

/-- **P3 — `inner_abs_le`, the per-assignment collision bound.** For a
squarefree modulus `s` and any prime-to-slot assignment `α`, the signed
`u`-sum produced by `inner_exact` at `(σ,τ) = (slotProd fst, slotProd snd)`
is bounded by `3^{ω(s)} · ∏_{p∣s}(p−1)⁻² · yside` — the per-prime
`(p−1)⁻²`, `R`-free bound. -/
theorem inner_abs_le (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf0 : ∀ n, 0 ≤ f₀ n)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W then ∏ i, f₀ (r i) else 0)
    {s : ℕ} (hs : Squarefree s)
    (α : (p : ℕ) → p ∈ s.primeFactors → Fin k × Fin k)
    (hα : α ∈ assignments k s) :
    |∑ u ∈ kSieveIndex k R W, (∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  classical
  have hPprime : ∀ p ∈ s.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hslots : ∀ (q : {x // x ∈ s.primeFactors}),
      (α q.1 q.2).1 ≠ (α q.1 q.2).2 := by
    intro q
    have hmem := (Finset.mem_pi.mp hα) q.1 q.2
    rw [Finset.mem_offDiag] at hmem
    exact hmem.2.2
  have hqR : ∀ q : {x // x ∈ s.primeFactors}, (1 : ℝ) < ((q : ℕ) : ℝ) := by
    intro q
    exact_mod_cast (hPprime _ q.2).one_lt
  have hqne0 : ∀ q : {x // x ∈ s.primeFactors}, (((q : ℕ) : ℝ) - 1) ≠ 0 := by
    intro q
    have := hqR q
    intro h
    linarith
  have hσsq : ∀ (sel : Fin k × Fin k → Fin k) i,
      Squarefree (slotProd s α sel i) :=
    fun sel i => hs.squarefree_of_dvd (slotProd_dvd hs α sel i)
  -- the y-value is nonnegative
  have hynn : ∀ v : Fin k → ℕ, 0 ≤ y v := by
    intro v
    rw [hy]
    split_ifs
    · exact Finset.prod_nonneg fun i _ => hf0 _
    · exact le_refl 0
  -- shared products
  have hT : (0 : ℝ) < ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
    apply Finset.prod_pos
    intro q _
    have := hqR q
    linarith
  -- reindexing of the non-absorbed-prime product
  have hreindex : ∀ (sel : Fin k × Fin k → Fin k), ∀ u : Fin k → ℕ,
      (∏ i, ∏ p ∈ (slotProd s α sel i
            / Nat.gcd (slotProd s α sel i) (u i)).primeFactors, ((p : ℝ) - 1))
        = ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u (sel (α q.1 q.2))),
            (((q : ℕ) : ℝ) - 1) := by
    intro sel u
    rw [← Finset.prod_fiberwise_of_maps_to
      (g := fun q : {x // x ∈ s.primeFactors} => sel (α q.1 q.2))
      (t := (Finset.univ : Finset (Fin k)))
      (fun q _ => Finset.mem_univ _)
      (fun q : {x // x ∈ s.primeFactors} => (((q : ℕ) : ℝ) - 1))]
    apply Finset.prod_congr rfl
    intro i _
    have hcne : slotProd s α sel i / Nat.gcd (slotProd s α sel i) (u i) ≠ 0 := by
      have hσpos : 0 < slotProd s α sel i := Squarefree.pos (hσsq sel i)
      have hgpos : 0 < Nat.gcd (slotProd s α sel i) (u i) :=
        Nat.gcd_pos_of_pos_left _ hσpos
      have hgle : Nat.gcd (slotProd s α sel i) (u i) ≤ slotProd s α sel i :=
        Nat.le_of_dvd hσpos (Nat.gcd_dvd_left _ _)
      exact (Nat.div_pos hgle hgpos).ne'
    have hset : (slotProd s α sel i
          / Nat.gcd (slotProd s α sel i) (u i)).primeFactors
        = ((s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u (sel (α q.1 q.2)))).filter
            (fun q => sel (α q.1 q.2) = i)).image
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ)) := by
      ext p
      simp only [Nat.mem_primeFactors, Finset.mem_image, Finset.mem_filter,
        Finset.mem_attach, true_and]
      constructor
      · rintro ⟨hp, hpc, -⟩
        obtain ⟨hpσ, hpu⟩ := (prime_dvd_cofactor_iff (hσsq sel i) hp).mp hpc
        obtain ⟨hmem, hsel⟩ := (prime_dvd_slotProd_iff α sel hp i).mp hpσ
        refine ⟨⟨p, hmem⟩, ⟨?_, hsel⟩, rfl⟩
        simp only
        rw [hsel]
        exact hpu
      · rintro ⟨q, ⟨hqnot, hqsel⟩, rfl⟩
        have hqp : (q : ℕ).Prime := hPprime _ q.2
        refine ⟨hqp, ?_, hcne⟩
        apply (prime_dvd_cofactor_iff (hσsq sel i) hqp).mpr
        refine ⟨(prime_dvd_slotProd_iff α sel hqp i).mpr ⟨q.2, hqsel⟩, ?_⟩
        rw [← hqsel]
        exact hqnot
    rw [hset, Finset.prod_image]
    intro q₁ _ q₂ _ h
    exact Subtype.ext h
  -- termwise absolute bound
  have hterm : ∀ u ∈ kSieveIndex k R W,
      |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * (((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1)) := by
    intro u hu
    have hΦu_pos : 0 < ∏ i, (Nat.totient (u i) : ℝ) := by
      apply Finset.prod_pos; intro i _
      exact_mod_cast Nat.totient_pos.mpr (kSieveIndex_coord_pos hu i)
    have hΦcast : ∀ v : Fin k → ℕ, 0 ≤ ∏ i, (Nat.totient (v i) : ℝ) :=
      fun v => Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
    have habsμ : ∀ v : Fin k → ℕ, |∏ i, ((μ (v i) : ℤ) : ℝ)| ≤ 1 := by
      intro v
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _)
        (fun i _ => abs_moebius_real_le_one _)
    have hΦlcm_pos : ∀ (sel : Fin k × Fin k → Fin k),
        0 < ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α sel i)) : ℝ) := by
      intro sel
      apply Finset.prod_pos; intro i _
      have hpos : 0 < Nat.lcm (u i) (slotProd s α sel i) :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero
          (kSieveIndex_coord_pos hu i).ne' (Squarefree.pos (hσsq sel i)).ne')
      exact_mod_cast Nat.totient_pos.mpr hpos
    -- strip signs on one side
    have hside : ∀ (sel : Fin k × Fin k → Fin k),
        |(∏ i, ((μ (Nat.lcm (u i) (slotProd s α sel i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α sel i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α sel i)) : ℝ)|
          ≤ y (fun i => Nat.lcm (u i) (slotProd s α sel i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α sel i)) : ℝ) := by
      intro sel
      rw [abs_div, abs_mul, abs_of_nonneg (hynn _),
        abs_of_nonneg (hΦcast _)]
      exact div_le_div₀ (hynn _)
        (mul_le_of_le_one_left (hynn _) (habsμ _)) (hΦlcm_pos sel) (le_refl _)
    -- the ŷ bounds from `yhat_side_le`
    have hyhatσ := yhat_side_le hf0 hfmono hy (hσsq Prod.fst) hu
    have hyhatτ := yhat_side_le hf0 hfmono hy (hσsq Prod.snd) hu
    -- notation for the W-products
    set Wσ : ℝ := ∏ i, ∏ p ∈ (slotProd s α Prod.fst i
        / Nat.gcd (slotProd s α Prod.fst i) (u i)).primeFactors,
        ((p : ℝ) - 1) with hWσ
    set Wτ : ℝ := ∏ i, ∏ p ∈ (slotProd s α Prod.snd i
        / Nat.gcd (slotProd s α Prod.snd i) (u i)).primeFactors,
        ((p : ℝ) - 1) with hWτ
    have hWpos : ∀ (sel : Fin k × Fin k → Fin k),
        (0:ℝ) < ∏ i, ∏ p ∈ (slotProd s α sel i
          / Nat.gcd (slotProd s α sel i) (u i)).primeFactors, ((p : ℝ) - 1) := by
      intro sel
      apply Finset.prod_pos; intro i _
      apply Finset.prod_pos; intro p hp
      have h2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
      have h2R : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
      linarith
    have hWσ_pos : 0 < Wσ := hWpos Prod.fst
    have hWτ_pos : 0 < Wτ := hWpos Prod.snd
    -- chain: strip signs, apply the ŷ bounds, do the algebra
    have hchain : |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ (∏ i, (Nat.totient (u i) : ℝ))
          * ((∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ))
          * ((∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hΦcast u)]
      have hNσ_nonneg : 0 ≤ (∏ i, f₀ (u i))
          / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ) :=
        div_nonneg (Finset.prod_nonneg fun i _ => hf0 _)
          (mul_nonneg (hΦcast u) hWσ_pos.le)
      have hbσ : |(∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ)|
          ≤ (∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ) :=
        le_trans (hside Prod.fst) hyhatσ
      have hbτ : |(∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ)|
          ≤ (∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ) :=
        le_trans (hside Prod.snd) hyhatτ
      apply mul_le_mul _ hbτ (abs_nonneg _)
        (mul_nonneg (hΦcast u) hNσ_nonneg)
      exact mul_le_mul_of_nonneg_left hbσ (hΦcast u)
    -- the algebra + reindex + complementation
    have halg : (∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ))
        * ((∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ))
        = ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * (Wσ⁻¹ * Wτ⁻¹) := by
      field_simp
    -- complementation identity
    set Bσ := s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)) with hBσ
    set Bτ := s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).2)) with hBτ
    have hWσ_eq : Wσ = ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u ((α q.1 q.2).1)), (((q : ℕ) : ℝ) - 1) :=
      hreindex Prod.fst u
    have hWτ_eq : Wτ = ∏ q ∈ s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => ¬ (q : ℕ) ∣ u ((α q.1 q.2).2)), (((q : ℕ) : ℝ) - 1) :=
      hreindex Prod.snd u
    have hsplitσ : (∏ q ∈ Bσ, (((q : ℕ) : ℝ) - 1)) * Wσ
        = ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
      rw [hWσ_eq, hBσ]
      exact Finset.prod_filter_mul_prod_filter_not _ _ _
    have hsplitτ : (∏ q ∈ Bτ, (((q : ℕ) : ℝ) - 1)) * Wτ
        = ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
      rw [hWτ_eq, hBτ]
      exact Finset.prod_filter_mul_prod_filter_not _ _ _
    have hdisj : Disjoint Bσ Bτ := by
      rw [Finset.disjoint_left]
      intro q hqσ hqτ
      rw [hBσ, Finset.mem_filter] at hqσ
      rw [hBτ, Finset.mem_filter] at hqτ
      exact hslots q (prime_dvd_coord_unique hu (hPprime _ q.2) hqσ.2 hqτ.2)
    have hunion : s.primeFactors.attach.filter
        (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
          ∨ (q : ℕ) ∣ u ((α q.1 q.2).2))
        = Bσ ∪ Bτ := by
      rw [hBσ, hBτ, Finset.filter_or]
    have hcompl : Wσ⁻¹ * Wτ⁻¹
        = (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1) := by
      have hKinv : (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          = ((∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1))⁻¹) ^ 2 := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]
      rw [hunion, Finset.prod_union hdisj, hKinv]
      have h1 : Wσ⁻¹ = (∏ q ∈ Bσ, (((q : ℕ) : ℝ) - 1))
          / ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
        rw [eq_div_iff hT.ne', ← hsplitσ]
        field_simp
      have h2 : Wτ⁻¹ = (∏ q ∈ Bτ, (((q : ℕ) : ℝ) - 1))
          / ∏ q ∈ s.primeFactors.attach, (((q : ℕ) : ℝ) - 1) := by
        rw [eq_div_iff hT.ne', ← hsplitτ]
        field_simp
      rw [h1, h2]
      ring
    calc |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
        ≤ (∏ i, (Nat.totient (u i) : ℝ))
            * ((∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wσ))
            * ((∏ i, f₀ (u i)) / ((∏ i, (Nat.totient (u i) : ℝ)) * Wτ)) := hchain
      _ = ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * (Wσ⁻¹ * Wτ⁻¹) := halg
      _ = ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * ((∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 1)) := by rw [hcompl]
      _ = (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
            * (((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 1)) := by ring
  -- the partitioned sum bound
  have hpart : ∑ u ∈ kSieveIndex k R W,
      (((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
        * ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
            (((q : ℕ) : ℝ) - 1))
      ≤ 3 ^ s.primeFactors.card
          * ∑ u ∈ kSieveIndex k R W,
              (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
    have hmaps : ∀ u ∈ kSieveIndex k R W,
        s.primeFactors.attach.filter
          (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
            ∨ (q : ℕ) ∣ u ((α q.1 q.2).2))
          ∈ s.primeFactors.attach.powerset :=
      fun u _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun u => ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
        * ∏ q ∈ s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
            (((q : ℕ) : ℝ) - 1))]
    have hQterm : ∀ Q ∈ s.primeFactors.attach.powerset,
        (∑ u ∈ (kSieveIndex k R W).filter
            (fun u => s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
          ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1))
        ≤ (2 : ℝ) ^ Q.card
            * ∑ u ∈ kSieveIndex k R W,
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
      intro Q hQ
      have hQprim : 0 ≤ ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) := by
        apply Finset.prod_nonneg
        intro q _
        have := hqR q
        linarith
      have hcongr : ∀ u ∈ (kSieveIndex k R W).filter
          (fun u => s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
          ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1)
          = ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) := by
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [hu.2]
      rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul]
      have hsub2 : (kSieveIndex k R W).filter
          (fun u => s.primeFactors.attach.filter
            (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q)
          ⊆ (kSieveIndex k R W).filter
            (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u ((α q.1 q.2).1)
              ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) := by
        intro u hu
        rw [Finset.mem_filter] at hu ⊢
        refine ⟨hu.1, fun q hq => ?_⟩
        rw [← hu.2, Finset.mem_filter] at hq
        exact hq.2
      have herasure := erasure_bound (R := R) (W := W) hf0 hfmono hPprime
        (fun q => (α q.1 q.2).1) (fun q => (α q.1 q.2).2) Q
      have hQpair : (∏ q ∈ Q, ((((q : ℕ) : ℝ) - 1)⁻¹))
          * (∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)) = 1 := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_eq_one
        intro q _
        exact inv_mul_cancel₀ (hqne0 q)
      calc (∑ u ∈ (kSieveIndex k R W).filter
            (fun u => s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
            (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1)
          ≤ (∑ u ∈ (kSieveIndex k R W).filter
              (fun u => ∀ q ∈ Q, (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
              (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right
              (Finset.sum_le_sum_of_subset_of_nonneg hsub2
                (fun u _ _ => yterm_nonneg f₀ u)) hQprim
        _ ≤ (2 ^ Q.card * (∏ q ∈ Q, ((((q : ℕ) : ℝ) - 1)⁻¹))
              * ∑ u ∈ kSieveIndex k R W,
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ Q, (((q : ℕ) : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right herasure hQprim
        _ = (2 : ℝ) ^ Q.card
              * ∑ u ∈ kSieveIndex k R W,
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
            linear_combination (2 ^ Q.card
              * ∑ u ∈ kSieveIndex k R W,
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)) * hQpair
    have hbinom : ∑ Q ∈ s.primeFactors.attach.powerset, (2 : ℝ) ^ Q.card
        = 3 ^ s.primeFactors.card := by
      have h := Finset.prod_add (fun _ => (2 : ℝ)) (fun _ => (1 : ℝ))
        s.primeFactors.attach
      simp only [Finset.prod_const_one, mul_one, Finset.prod_const] at h
      rw [Finset.card_attach] at h
      norm_num at h
      rw [← h]
    calc ∑ Q ∈ s.primeFactors.attach.powerset,
          ∑ u ∈ (kSieveIndex k R W).filter
            (fun u => s.primeFactors.attach.filter
              (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)) = Q),
            ((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
              * ∏ q ∈ s.primeFactors.attach.filter
                  (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                    ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                  (((q : ℕ) : ℝ) - 1)
        ≤ ∑ Q ∈ s.primeFactors.attach.powerset, (2 : ℝ) ^ Q.card
            * ∑ u ∈ kSieveIndex k R W,
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) :=
          Finset.sum_le_sum hQterm
      _ = (∑ Q ∈ s.primeFactors.attach.powerset, (2 : ℝ) ^ Q.card)
            * ∑ u ∈ kSieveIndex k R W,
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) :=
          (Finset.sum_mul _ _ _).symm
      _ = 3 ^ s.primeFactors.card
            * ∑ u ∈ kSieveIndex k R W,
                (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ) := by
          rw [hbinom]
  -- identify the y-side and the attach product, then conclude
  have hSy : ∑ u ∈ kSieveIndex k R W,
      (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)
      = ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [hy r, if_pos hr]
  have hKattach : (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
      = ∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
    Finset.prod_attach s.primeFactors (fun p => (((p : ℝ) - 1)⁻¹) ^ 2)
  have hKnonneg : 0 ≤ ∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2 :=
    Finset.prod_nonneg fun q _ => sq_nonneg _
  calc |∑ u ∈ kSieveIndex k R W, (∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))|
      ≤ ∑ u ∈ kSieveIndex k R W, |(∏ i, (Nat.totient (u i) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.fst i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.fst i)) : ℝ))
        * ((∏ i, ((μ (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℤ) : ℝ))
            * y (fun i => Nat.lcm (u i) (slotProd s α Prod.snd i))
            / ∏ i, (Nat.totient (Nat.lcm (u i) (slotProd s α Prod.snd i)) : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ kSieveIndex k R W,
          (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * (((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
            * ∏ q ∈ s.primeFactors.attach.filter
                (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                  ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                (((q : ℕ) : ℝ) - 1)) :=
      Finset.sum_le_sum hterm
    _ = (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * ∑ u ∈ kSieveIndex k R W,
              (((∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ))
                * ∏ q ∈ s.primeFactors.attach.filter
                    (fun q : {x // x ∈ s.primeFactors} => (q : ℕ) ∣ u ((α q.1 q.2).1)
                      ∨ (q : ℕ) ∣ u ((α q.1 q.2).2)),
                    (((q : ℕ) : ℝ) - 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (∏ q ∈ s.primeFactors.attach, ((((q : ℕ) : ℝ) - 1)⁻¹) ^ 2)
          * (3 ^ s.primeFactors.card
              * ∑ u ∈ kSieveIndex k R W,
                  (∏ i, f₀ (u i)) ^ 2 / ∏ i, (Nat.totient (u i) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpart hKnonneg
    _ = 3 ^ s.primeFactors.card
          * (∏ p ∈ s.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ kSieveIndex k R W, (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [hKattach, hSy]
        ring


/-! ## P4 — the Möbius collision expansion -/

/-- The finite index set of collision moduli: all `t ≤ R^k`. It contains
every divisor of every `cRad d e` (`d, e ∈ 𝒟`). -/
def collisionModuli (k R : ℕ) : Finset ℕ := Finset.range (R ^ k + 1)

/-- A squarefree number divides `n` iff each of its primes does. -/
theorem squarefree_dvd_iff_primes {t n : ℕ} (ht : Squarefree t) :
    t ∣ n ↔ ∀ p ∈ t.primeFactors, p ∣ n := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    rw [← Nat.prod_primeFactors_of_squarefree ht]
    exact Finset.prod_primes_dvd n
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) h

/-- `cRad d e ≤ R^k` on the sieve support. -/
theorem cRad_le {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) (_he : e ∈ kSieveIndex k R W) :
    cRad d e ≤ R ^ k := by
  have h1 : cRad d e ≤ ∏ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, d ij.1 := by
    apply Finset.prod_le_prod'
    intro ij _
    exact Nat.gcd_le_left _ (kSieveIndex_coord_pos hd ij.1)
  have h2 : (∏ ij ∈ (Finset.univ : Finset (Fin k)).offDiag, d ij.1)
      ≤ ∏ ij ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
          d ij.1 := by
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro ij _
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    · intro ij _ _
      exact kSieveIndex_coord_pos hd ij.1
  have h3 : (∏ ij ∈ (Finset.univ : Finset (Fin k)) ×ˢ (Finset.univ : Finset (Fin k)),
        d ij.1) = (∏ i, d i) ^ k := by
    rw [Finset.prod_product]
    calc ∏ i, ∏ _j : Fin k, d i
        = ∏ i, (d i) ^ k := by
          apply Finset.prod_congr rfl
          intro i _
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = (∏ i, d i) ^ k := Finset.prod_pow _ _ _
  have h4 : (∏ i, d i) ^ k ≤ R ^ k := by
    apply Nat.pow_le_pow_left
    exact le_of_lt ((mem_kSieveIndex_iff d).mp hd).2.2.2
  omega
  
/-- Every divisor of a `cRad` lies in `collisionModuli`. -/
theorem dvd_cRad_mem {k R W : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W) (he : e ∈ kSieveIndex k R W)
    {t : ℕ} (ht : t ∣ cRad d e) : t ∈ collisionModuli k R := by
  rw [collisionModuli, Finset.mem_range]
  have h1 : t ≤ cRad d e := Nat.le_of_dvd (cRad_pos hd he) ht
  have h2 := cRad_le hd he
  omega

/-- **P4(i)+(ii) — `compat_moebius_expansion`.** The compatible form
expands exactly over collision moduli with signed Möbius weights:
`s1CompatForm = ∑_{t ∈ CM} μ(t) · ∑_{(d,e) : t ∣ cRad} s1Summand`. -/
theorem compat_moebius_expansion (k R W : ℕ) (y : (Fin k → ℕ) → ℝ) :
    s1CompatForm k R W y
      = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
              (if t ∣ cRad d e then s1Summand k R W y d e else 0) := by
  unfold s1CompatForm
  have hpt : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      (if IsCollisionPair d e then 0 else s1Summand k R W y d e)
        = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s1Summand k R W y d e else 0) := by
    intro d hd e he
    have hmoeb : (∑ t ∈ collisionModuli k R,
        if t ∣ cRad d e then ((μ t : ℤ) : ℝ) else 0)
        = if cRad d e = 1 then 1 else 0 := by
      rw [← sum_divisors_moebius_eq (cRad d e), collisionModuli]
      exact (sum_divisors_eq_sum_range (cRad_pos hd he).ne' (cRad_le hd he)
        (fun t => ((μ t : ℤ) : ℝ))).symm
    calc (if IsCollisionPair d e then 0 else s1Summand k R W y d e)
        = (if cRad d e = 1 then 1 else 0) * s1Summand k R W y d e := by
          by_cases hc : IsCollisionPair d e
          · rw [if_pos hc,
              if_neg (fun h1 => ((cRad_eq_one_iff hd he).mp h1) hc), zero_mul]
          · rw [if_neg hc, if_pos ((cRad_eq_one_iff hd he).mpr hc), one_mul]
      _ = (∑ t ∈ collisionModuli k R,
            if t ∣ cRad d e then ((μ t : ℤ) : ℝ) else 0)
            * s1Summand k R W y d e := by rw [hmoeb]
      _ = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s1Summand k R W y d e else 0) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro u _
          split_ifs <;> ring
  calc ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        (if IsCollisionPair d e then 0 else s1Summand k R W y d e)
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s1Summand k R W y d e else 0) := by
        apply Finset.sum_congr rfl; intro d hd
        apply Finset.sum_congr rfl; intro e he
        exact hpt d hd e he
    _ = ∑ t ∈ collisionModuli k R, ∑ d ∈ kSieveIndex k R W,
          ∑ e ∈ kSieveIndex k R W, ((μ t : ℤ) : ℝ)
            * (if t ∣ cRad d e then s1Summand k R W y d e else 0) :=
        sum_move3 _ _ _ _
    _ = ∑ t ∈ collisionModuli k R, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
              (if t ∣ cRad d e then s1Summand k R W y d e else 0) := by
        apply Finset.sum_congr rfl; intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.mul_sum]

/-- The slot products of an assignment force exactly the per-prime slot
divisibilities. -/
theorem slotProd_dvd_iff {k t : ℕ} (ht : Squarefree t)
    (α : (p : ℕ) → p ∈ t.primeFactors → Fin k × Fin k)
    (sel : Fin k × Fin k → Fin k) (d : Fin k → ℕ) :
    (∀ i, slotProd t α sel i ∣ d i)
      ↔ ∀ q : {x // x ∈ t.primeFactors}, (q : ℕ) ∣ d (sel (α q.1 q.2)) := by
  constructor
  · intro h q
    have hmem : q ∈ t.primeFactors.attach.filter
        (fun q' => sel (α q'.1 q'.2) = sel (α q.1 q.2)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach _ q, rfl⟩
    have hdvd : (q : ℕ) ∣ slotProd t α sel (sel (α q.1 q.2)) := by
      rw [slotProd]
      exact Finset.dvd_prod_of_mem
        (fun q' : {x // x ∈ t.primeFactors} => (q' : ℕ)) hmem
    exact hdvd.trans (h (sel (α q.1 q.2)))
  · intro h i
    have hsq : Squarefree (slotProd t α sel i) :=
      ht.squarefree_of_dvd (slotProd_dvd ht α sel i)
    rw [squarefree_dvd_iff_primes hsq]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    obtain ⟨hmem, hsel⟩ := (prime_dvd_slotProd_iff α sel hpp i).mp
      (Nat.dvd_of_mem_primeFactors hp)
    have hq := h ⟨p, hmem⟩
    rwa [hsel] at hq

/-- **P4(iii) — `inner_collision_expand`.** For squarefree `t`, the
`t ∣ cRad`-guarded double sum expands **exactly** (disjointness — no
over-counting) as a sum over prime-to-slot assignments of doubly-forced
sums. -/
theorem inner_collision_expand (k R W : ℕ) (y : (Fin k → ℕ) → ℝ)
    {t : ℕ} (ht : Squarefree t) :
    (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        if t ∣ cRad d e then s1Summand k R W y d e else 0)
      = ∑ α ∈ assignments k t,
          ∑ d ∈ (kSieveIndex k R W).filter
              (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
            ∑ e ∈ (kSieveIndex k R W).filter
              (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
              s1Summand k R W y d e := by
  classical
  -- the per-pair indicator identity
  have hind : ∀ d ∈ kSieveIndex k R W, ∀ e ∈ kSieveIndex k R W,
      (if t ∣ cRad d e then (1 : ℝ) else 0)
        = ∑ α ∈ assignments k t,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0) := by
    intro d hd e he
    calc (if t ∣ cRad d e then (1 : ℝ) else 0)
        = if ∀ p ∈ t.primeFactors, p ∣ cRad d e then (1 : ℝ) else 0 := by
          congr 1
          rw [eq_iff_iff]
          exact squarefree_dvd_iff_primes ht
      _ = ∏ p ∈ t.primeFactors, (if p ∣ cRad d e then (1 : ℝ) else 0) :=
          (prod_ite_one _ _).symm
      _ = ∏ p ∈ t.primeFactors, ∑ ij ∈ (Finset.univ : Finset (Fin k)).offDiag,
            (if p ∣ d ij.1 ∧ p ∣ e ij.2 then (1 : ℝ) else 0) := by
          apply Finset.prod_congr rfl; intro p hp
          exact collision_indicator hd he (Nat.prime_of_mem_primeFactors hp)
      _ = ∑ α ∈ assignments k t, ∏ q ∈ t.primeFactors.attach,
            (if (q : ℕ) ∣ d ((α q.1 q.2).1) ∧ (q : ℕ) ∣ e ((α q.1 q.2).2)
              then (1 : ℝ) else 0) := by
          rw [assignments]
          exact Finset.prod_sum _ _ _
      _ = ∑ α ∈ assignments k t,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl; intro α _
          have hsplit : ∀ q ∈ t.primeFactors.attach,
              (if (q : ℕ) ∣ d ((α q.1 q.2).1) ∧ (q : ℕ) ∣ e ((α q.1 q.2).2)
                then (1 : ℝ) else 0)
              = (if (q : ℕ) ∣ d ((α q.1 q.2).1) then (1 : ℝ) else 0)
                  * (if (q : ℕ) ∣ e ((α q.1 q.2).2) then (1 : ℝ) else 0) := by
            intro q _
            rw [ite_one_mul_ite_one]
          rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib,
            prod_ite_one, prod_ite_one]
          have h1 : (∀ q ∈ t.primeFactors.attach, (q : ℕ) ∣ d ((α q.1 q.2).1))
              ↔ ∀ i, slotProd t α Prod.fst i ∣ d i := by
            constructor
            · intro h
              apply (slotProd_dvd_iff ht α Prod.fst d).mpr
              intro q
              exact h q (Finset.mem_attach _ q)
            · intro h q _
              exact (slotProd_dvd_iff ht α Prod.fst d).mp h q
          have h2 : (∀ q ∈ t.primeFactors.attach, (q : ℕ) ∣ e ((α q.1 q.2).2))
              ↔ ∀ i, slotProd t α Prod.snd i ∣ e i := by
            constructor
            · intro h
              apply (slotProd_dvd_iff ht α Prod.snd e).mpr
              intro q
              exact h q (Finset.mem_attach _ q)
            · intro h q _
              exact (slotProd_dvd_iff ht α Prod.snd e).mp h q
          congr 1
          · congr 1
            rw [eq_iff_iff]
            exact h1
          · congr 1
            rw [eq_iff_iff]
            exact h2
  -- substitute the identity and swap the sums
  calc (∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
        if t ∣ cRad d e then s1Summand k R W y d e else 0)
      = ∑ d ∈ kSieveIndex k R W, ∑ e ∈ kSieveIndex k R W,
          ∑ α ∈ assignments k t,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0)
              * s1Summand k R W y d e := by
        apply Finset.sum_congr rfl; intro d hd
        apply Finset.sum_congr rfl; intro e he
        have hstep : (if t ∣ cRad d e then s1Summand k R W y d e else 0)
            = (if t ∣ cRad d e then (1 : ℝ) else 0) * s1Summand k R W y d e := by
          split_ifs <;> ring
        rw [hstep, hind d hd e he, Finset.sum_mul]
    _ = ∑ α ∈ assignments k t, ∑ d ∈ kSieveIndex k R W,
          ∑ e ∈ kSieveIndex k R W,
            (if ∀ i, slotProd t α Prod.fst i ∣ d i then (1 : ℝ) else 0)
              * (if ∀ i, slotProd t α Prod.snd i ∣ e i then (1 : ℝ) else 0)
              * s1Summand k R W y d e :=
        sum_move3 _ _ _ _
    _ = ∑ α ∈ assignments k t,
          ∑ d ∈ (kSieveIndex k R W).filter
              (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
            ∑ e ∈ (kSieveIndex k R W).filter
              (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
              s1Summand k R W y d e := by
        apply Finset.sum_congr rfl; intro α _
        symm
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.sum_filter]
        by_cases h1 : ∀ i, slotProd t α Prod.fst i ∣ d i
        · rw [if_pos h1]
          apply Finset.sum_congr rfl; intro e _
          by_cases h2 : ∀ i, slotProd t α Prod.snd i ∣ e i
          · rw [if_pos h2, if_pos h1, if_pos h2]
            ring
          · rw [if_neg h2, if_neg h2]
            ring
        · rw [if_neg h1]
          symm
          apply Finset.sum_eq_zero; intro e _
          rw [if_neg h1]
          ring

/-- Collision moduli with a small prime factor contribute nothing: their
guarded double sum is empty (every prime of a `cRad` exceeds `D₀ k`). -/
theorem inner_collision_zero (k R : ℕ) (y : (Fin k → ℕ) → ℝ)
    {t p : ℕ} (hp : p.Prime) (hpt : p ∣ t) (hpD : p ≤ D₀ k) :
    (∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
        if t ∣ cRad d e then s1Summand k R (W k) y d e else 0) = 0 := by
  apply Finset.sum_eq_zero; intro d hd
  apply Finset.sum_eq_zero; intro e he
  rw [if_neg]
  intro hdvd
  have hpc : p ∣ cRad d e := hpt.trans hdvd
  obtain ⟨ij, _, h1, _⟩ := (prime_dvd_cRad_iff hp).mp hpc
  exact absurd (D₀_lt_of_prime_dvd_coord hd hp h1) (not_lt.mpr hpD)


/-! ## P6 — assembly: the quantitative collision bound -/

/-- `12k² ≤ D₀ k` holds as soon as `12 ≤ k` (since `D₀ k ≥ k³`). -/
theorem twelve_k_sq_le_D₀ {k : ℕ} (hk : 12 ≤ k) : 12 * k ^ 2 ≤ D₀ k := by
  have h1 : 12 * k ^ 2 ≤ k ^ 3 := by nlinarith
  have h2 : k ^ 3 ≤ D₀ k := le_max_left _ _
  omega

/-- **P6 — `collision_lower_order` (N4.4-QUANT).** For the tensor weights
`y(r) = ∏ᵢ f₀(rᵢ)` with `0 ≤ f₀ ≤ 1` divisor-antitone, at the Maynard
modulus `W k` with `12k² ≤ D₀ k`:
`|s1CollisionForm| ≤ (12k²/D₀ k) · ∑_r y(r)²/∏φ(rᵢ)` — an explicit,
`R`-free constant. -/
theorem collision_lower_order (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    |s1CollisionForm k R W' y|
      ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
          * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  classical
  subst hW
  have hf0 : ∀ n, 0 ≤ f₀ n := fun n => (hf01 n).1
  have hy0 : ∀ r, r ∉ kSieveIndex k R (W k) → y r = 0 := by
    intro r hr
    rw [hy r, if_neg hr]
  have hyside : 0 ≤ ∑ r ∈ kSieveIndex k R (W k),
      (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := s1_yside_nonneg k R (W k) y
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D₀ k := by omega
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hDposN
  have hκ : (0 : ℝ) ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    have hempty : kSieveIndex k 0 (W k) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro r hr
      exact absurd ((mem_kSieveIndex_iff r).mp hr).2.2.2 (Nat.not_lt_zero _)
    unfold s1CollisionForm
    rw [hempty]
    simp
  -- main case: `R ≥ 1`
  have h1mem : (1 : ℕ) ∈ collisionModuli k R := by
    rw [collisionModuli, Finset.mem_range]
    have := Nat.one_le_pow k R hRpos
    omega
  have hcompat := compat_moebius_expansion k R (W k) y
  have herase := Finset.add_sum_erase (collisionModuli k R)
    (fun t => ((μ t : ℤ) : ℝ)
      * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)) h1mem
  have hG1 : (∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
      (if (1 : ℕ) ∣ cRad d e then s1Summand k R (W k) y d e else 0))
      = s1FullForm k R (W k) y := by
    unfold s1FullForm
    apply Finset.sum_congr rfl; intro d _
    apply Finset.sum_congr rfl; intro e _
    rw [if_pos (one_dvd _)]
  have hμ1 : ((μ 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]
    norm_num
  have hkey : s1CollisionForm k R (W k) y
      = - ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
              (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0) := by
    have hsplit0 := s1_full_split k R (W k) y
    have hfull := s1_full_eq_yside k R (W k) y hy0
    simp only [hμ1, one_mul, hG1] at herase
    -- herase : full + Σ_erase = Σ_CM ; hcompat : compat = Σ_CM
    have e1 : s1CompatForm k R (W k) y
        = s1FullForm k R (W k) y
          + ∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
              * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
                  (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0) := by
      rw [hcompat, ← herase]
    linarith
  -- per-modulus bound
  have hbound : ∀ t ∈ (collisionModuli k R).erase 1,
      |((μ t : ℤ) : ℝ)
        * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
            (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)|
      ≤ (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p then
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * ∑ r ∈ kSieveIndex k R (W k),
                (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
        else 0) := by
    intro t _
    by_cases hgood : Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p
    · rw [if_pos hgood]
      obtain ⟨hsq, _⟩ := hgood
      have hcard : (assignments k t).card
          = (k * k - k) ^ t.primeFactors.card := by
        rw [assignments, Finset.card_pi, Finset.prod_const,
          Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      have hinvsq_nonneg : 0 ≤ ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2 :=
        Finset.prod_nonneg fun p _ => sq_nonneg _
      have hGabs : |∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
          (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)|
          ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ kSieveIndex k R (W k),
                    (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by
        rw [inner_collision_expand k R (W k) y hsq]
        calc |∑ α ∈ assignments k t,
              ∑ d ∈ (kSieveIndex k R (W k)).filter
                  (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                ∑ e ∈ (kSieveIndex k R (W k)).filter
                    (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                  s1Summand k R (W k) y d e|
            ≤ ∑ α ∈ assignments k t,
                |∑ d ∈ (kSieveIndex k R (W k)).filter
                    (fun d => ∀ i, slotProd t α Prod.fst i ∣ d i),
                  ∑ e ∈ (kSieveIndex k R (W k)).filter
                      (fun e => ∀ i, slotProd t α Prod.snd i ∣ e i),
                    s1Summand k R (W k) y d e| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _α ∈ assignments k t,
                ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * ∑ r ∈ kSieveIndex k R (W k),
                      (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by
              apply Finset.sum_le_sum
              intro α hα
              have hinner := inner_exact k R (W k) y hy0
                (slotProd t α Prod.fst) (slotProd t α Prod.snd)
              unfold s1Summand
              rw [hinner]
              exact inner_abs_le k R (W k) y f₀ hf0 hfmono hy hsq α hα
          _ = ((assignments k t).card : ℝ)
                * ((3 : ℝ) ^ t.primeFactors.card
                  * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                  * ∑ r ∈ kSieveIndex k R (W k),
                      (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcast : ((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card
          ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card := by
        rw [hcard]
        push_cast
        rw [← mul_pow]
        apply pow_le_pow_left₀
        · positivity
        · have hle : ((k * k - k : ℕ) : ℝ) ≤ (k : ℝ) * (k : ℝ) := by
            have h1 : (k * k - k : ℕ) ≤ k * k := Nat.sub_le _ _
            calc ((k * k - k : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast h1
              _ = (k : ℝ) * (k : ℝ) := by push_cast; ring
          nlinarith
      calc |((μ t : ℤ) : ℝ)
            * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
                (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)|
          ≤ |∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
              (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)| := by
            rw [abs_mul]
            have h1 := abs_moebius_real_le_one t
            have h2 := abs_nonneg (∑ d ∈ kSieveIndex k R (W k),
              ∑ e ∈ kSieveIndex k R (W k),
                (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0))
            nlinarith
        _ ≤ ((assignments k t).card : ℝ)
              * ((3 : ℝ) ^ t.primeFactors.card
                * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ kSieveIndex k R (W k),
                    (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := hGabs
        _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * ∑ r ∈ kSieveIndex k R (W k),
                  (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
            have hrest : 0 ≤ (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                * ∑ r ∈ kSieveIndex k R (W k),
                    (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) :=
              mul_nonneg hinvsq_nonneg hyside
            calc ((assignments k t).card : ℝ)
                  * ((3 : ℝ) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * ∑ r ∈ kSieveIndex k R (W k),
                        (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ))
                = (((assignments k t).card : ℝ) * (3 : ℝ) ^ t.primeFactors.card)
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * ∑ r ∈ kSieveIndex k R (W k),
                          (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) := by ring
              _ ≤ (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * ((∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                      * ∑ r ∈ kSieveIndex k R (W k),
                          (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)) :=
                  mul_le_mul_of_nonneg_right hcast hrest
              _ = (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
                    * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
                    * ∑ r ∈ kSieveIndex k R (W k),
                        (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by ring
    · rw [if_neg hgood]
      by_cases hsq : Squarefree t
      · have hsmall : ∃ p ∈ t.primeFactors, ¬ D₀ k < p := by
          by_contra hall
          push Not at hall
          exact hgood ⟨hsq, hall⟩
        obtain ⟨p, hp, hple⟩ := hsmall
        have hzero := inner_collision_zero k R y
          (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) (not_lt.mp hple)
        rw [hzero, mul_zero, abs_zero]
      · have hμ0 : ((μ t : ℤ) : ℝ) = 0 := by
          rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
          norm_num
        rw [hμ0, zero_mul, abs_zero]
  -- assemble via the Euler tail
  have htail := euler_tail k (R ^ k + 1) hk hD
  calc |s1CollisionForm k R (W k) y|
      = |∑ t ∈ (collisionModuli k R).erase 1, ((μ t : ℤ) : ℝ)
          * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
              (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)| := by
        rw [hkey, abs_neg]
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          |((μ t : ℤ) : ℝ)
            * ∑ d ∈ kSieveIndex k R (W k), ∑ e ∈ kSieveIndex k R (W k),
                (if t ∣ cRad d e then s1Summand k R (W k) y d e else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ (collisionModuli k R).erase 1,
          (if Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p then
            (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
              * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
              * ∑ r ∈ kSieveIndex k R (W k),
                  (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ)
          else 0) :=
        Finset.sum_le_sum hbound
    _ = ∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * (∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
            * ∑ r ∈ kSieveIndex k R (W k),
                (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [← Finset.sum_filter, Finset.filter_erase]
    _ = (∑ t ∈ (((collisionModuli k R).filter
          (fun t => Squarefree t ∧ ∀ p ∈ t.primeFactors, D₀ k < p)).erase 1),
          (3 * (k : ℝ) ^ 2) ^ t.primeFactors.card
            * ∏ p ∈ t.primeFactors, (((p : ℝ) - 1)⁻¹) ^ 2)
          * ∑ r ∈ kSieveIndex k R (W k),
              (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
          * ∑ r ∈ kSieveIndex k R (W k),
              (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) :=
        mul_le_mul_of_nonneg_right htail hyside

/-- **P6 — the PORT-BLOCKER of `CrossCollision.lean`, discharged.** The
collision form is controlled relative to the y-side with the explicit,
`R`-free constant `κ = 12k²/D₀ k`. -/
theorem crossCollisionControlled_holds (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ)
    (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    CrossCollisionControlled k R W' y := by
  refine ⟨12 * (k : ℝ) ^ 2 / (D₀ k : ℝ), ?_, ?_⟩
  · have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
    have hDposN : 0 < D₀ k := by omega
    have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hDposN
    positivity
  · exact collision_lower_order k R W' y f₀ hf01 hfmono hy hW hk hD

/-- **P6 — the compatible form is at most twice the y-side.** With
`12k² ≤ D₀ k` the collision correction is dominated by the main term:
`s1CompatForm ≤ 2·∑_r y(r)²/∏φ(rᵢ)`. -/
theorem compat_le_two_yside (k R W' : ℕ) (y : (Fin k → ℕ) → ℝ) (f₀ : ℕ → ℝ)
    (hf01 : ∀ n, 0 ≤ f₀ n ∧ f₀ n ≤ 1)
    (hfmono : ∀ d m : ℕ, d ∣ m → 0 < d → f₀ m ≤ f₀ d)
    (hy : ∀ r, y r = if r ∈ kSieveIndex k R W' then ∏ i, f₀ (r i) else 0)
    (hW : W' = W k) (hk : 1 ≤ k) (hD : 12 * k ^ 2 ≤ D₀ k) :
    s1CompatForm k R W' y
      ≤ 2 * ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
  have hy0 : ∀ r, r ∉ kSieveIndex k R W' → y r = 0 := by
    intro r hr
    rw [hy r, if_neg hr]
  have hcoll := collision_lower_order k R W' y f₀ hf01 hfmono hy hW hk hD
  have hyside := s1_yside_nonneg k R W' y
  have heq := s1_compat_eq k R W' y hy0
  have hk2 : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ hk
  have hDposN : 0 < D₀ k := by omega
  have hDpos : (0 : ℝ) < (D₀ k : ℝ) := by exact_mod_cast hDposN
  have hratio : 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ) ≤ 1 := by
    rw [div_le_one hDpos]
    exact_mod_cast hD
  have habs := neg_le_abs (s1CollisionForm k R W' y)
  have hcoll2 : |s1CollisionForm k R W' y|
      ≤ ∑ r ∈ kSieveIndex k R W', (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := by
    calc |s1CollisionForm k R W' y|
        ≤ 12 * (k : ℝ) ^ 2 / (D₀ k : ℝ)
            * ∑ r ∈ kSieveIndex k R W',
                (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := hcoll
      _ ≤ 1 * ∑ r ∈ kSieveIndex k R W',
            (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) :=
          mul_le_mul_of_nonneg_right hratio hyside
      _ = ∑ r ∈ kSieveIndex k R W',
            (y r) ^ 2 / ∏ i, (Nat.totient (r i) : ℝ) := one_mul _
  linarith


end Salt.Maynard
