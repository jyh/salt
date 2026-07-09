/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Eh
import Salt.Maynard.VAbs
import Salt.Maynard.CrossCollision
import Salt.Maynard.Compat
import Salt.Maynard.DivisorCount
import Salt.Maynard.CollisionQuant

/-!
# C4 item 4 — the pair fiber count

A nonnegative function `F` summed over compatible pairs `(d,e)` (both in the
sieve index, pinned at `dₘ = eₘ = 1`, non-collision), regrouped by their
combined modulus `q = qMod k d e = W k · ∏ᵢ lcm(dᵢ,eᵢ)`, is dominated by a
`(3k)^{ω(q)}`-weighted sum over squarefree moduli `q < W k · R² + 1`:

  `∑_{(d,e) compat} F(qMod k d e) ≤ ∑_{q < W·R²+1, sqfree} (3k)^{ω(q)}·F(q)`.

Route (the PAIR analog of `VAbs.lean`'s single-tuple `fiber_count_le`):

* **qMod lands in the squarefree range** (`qMod_squarefree`, `qMod_mem_range`):
  each `lcm(dᵢ,eᵢ)` is squarefree, the lcms are pairwise coprime
  (`lcm_pairwise_coprime`, via `pair_coord_unique`) and coprime to `W`, so
  `q` is squarefree; `∏ lcm ≤ (∏dᵢ)(∏eᵢ) < R²` bounds it.
* **Each fiber injects into per-prime assignments** `θ : q.primeFactors →
  Fin k × Fin 3` (coordinate × side ∈ {d-only, e-only, both}); the pair is
  recovered from `(q, θ)` by `pair_recover_d`/`pair_recover_e`, so the fiber
  card is `≤ card (pairAssignSet) = (3k)^{ω(q)}`.
* **Assemble** by `Finset.sum_fiberwise_of_maps_to`; `F ≥ 0` absorbs the
  overcount from assignments to coordinate `m`.
-/

open Finset

namespace Salt.Maynard

/-! ## Basic combinatorial facts about a compatible pair -/

/-- `lcm a b ∣ a * b` for naturals (cofactor `gcd a b`). -/
private theorem lcm_dvd_mul (a b : ℕ) : Nat.lcm a b ∣ a * b :=
  ⟨Nat.gcd a b, by rw [← Nat.gcd_mul_lcm]; ring⟩

/-- The lcm of two squarefrees is squarefree. -/
private theorem lcm_squarefree {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (ha.natFactorization_le_one p) (hb.natFactorization_le_one p)

/-- Each combined lcm coordinate is coprime to `W k` (both `dᵢ, eᵢ` are). -/
private theorem lcm_coprime_W {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k)) (i : Fin k) :
    Nat.Coprime (W k) (Nat.lcm (d i) (e i)) := by
  have hdW : Nat.Coprime (d i) (W k) := ((mem_kSieveIndex_iff d).mp hd).2.2.1 i
  have heW : Nat.Coprime (e i) (W k) := ((mem_kSieveIndex_iff e).mp he).2.2.1 i
  exact ((hdW.symm).mul_right (heW.symm)).coprime_dvd_right (lcm_dvd_mul _ _)

/-- **Coordinate uniqueness for a compatible pair.**  A prime dividing some
coordinate of `d` or `e` at index `i`, and again at index `j`, forces `i = j`:
same-side clashes contradict pairwise coprimality (`prime_dvd_coord_unique`),
cross-side clashes are collisions (contradicting `¬ IsCollisionPair`). -/
private theorem pair_coord_unique {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) {p : ℕ} (hp : p.Prime) {i j : Fin k}
    (hi : p ∣ d i ∨ p ∣ e i) (hj : p ∣ d j ∨ p ∣ e j) : i = j := by
  by_contra hne
  rcases hi with hdi | hei <;> rcases hj with hdj | hej
  · exact hne (prime_dvd_coord_unique hd hp hdi hdj)
  · exact hcompat ⟨i, j, hne, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdi, hej⟩⟩
  · exact hcompat ⟨j, i, Ne.symm hne, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdj, hei⟩⟩
  · exact hne (prime_dvd_coord_unique he hp hei hej)

/-- The combined lcms are pairwise coprime (`i ≠ j`): a shared prime would
divide a coordinate at both `i` and `j`, contradicting `pair_coord_unique`. -/
private theorem lcm_pairwise_coprime {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hi : p ∣ d i ∨ p ∣ e i := (Nat.Prime.dvd_mul hp).mp (hpi.trans (lcm_dvd_mul _ _))
  have hj : p ∣ d j ∨ p ∣ e j := (Nat.Prime.dvd_mul hp).mp (hpj.trans (lcm_dvd_mul _ _))
  exact hij (pair_coord_unique hd he hcompat hp hi hj)

/-- `q = qMod k d e` is squarefree for a compatible pair: `W k` squarefree,
`∏ᵢ lcm(dᵢ,eᵢ)` squarefree (pairwise-coprime squarefrees), and `W` coprime to
the product. -/
private theorem qMod_squarefree {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) : Squarefree (qMod k d e) := by
  have hdsq := ((mem_kSieveIndex_iff d).mp hd).1
  have hesq := ((mem_kSieveIndex_iff e).mp he).1
  have hprodsq : Squarefree (∏ i, Nat.lcm (d i) (e i)) :=
    squarefree_prod_coprime _ _ (fun i _ => lcm_squarefree (hdsq i) (hesq i))
      (fun i _ j _ hij => lcm_pairwise_coprime hd he hcompat hij)
  have hcopW : Nat.Coprime (W k) (∏ i, Nat.lcm (d i) (e i)) :=
    Nat.Coprime.prod_right (fun i _ => lcm_coprime_W hd he i)
  unfold qMod
  rw [Nat.squarefree_mul hcopW]
  exact ⟨W_squarefree k, hprodsq⟩

/-- `qMod k d e < W k · R² + 1`: `∏ᵢ lcm(dᵢ,eᵢ) ∣ (∏dᵢ)(∏eᵢ) ≤ R·R`. -/
private theorem qMod_mem_range {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k)) :
    qMod k d e ∈ Finset.range (W k * R ^ 2 + 1) := by
  rw [Finset.mem_range]
  have hdprod : ∏ i, d i < R := ((mem_kSieveIndex_iff d).mp hd).2.2.2
  have heprod : ∏ i, e i < R := ((mem_kSieveIndex_iff e).mp he).2.2.2
  have hlcmdvd : (∏ i, Nat.lcm (d i) (e i)) ∣ (∏ i, d i) * (∏ i, e i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => lcm_dvd_mul _ _)
  have hprodpos : 0 < (∏ i, d i) * (∏ i, e i) :=
    Nat.mul_pos (Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hd i))
      (Finset.prod_pos (fun i _ => kSieveIndex_coord_pos he i))
  have hlcmle : ∏ i, Nat.lcm (d i) (e i) ≤ (∏ i, d i) * (∏ i, e i) :=
    Nat.le_of_dvd hprodpos hlcmdvd
  have hbound : (∏ i, d i) * (∏ i, e i) ≤ R * R :=
    Nat.mul_le_mul (Nat.le_of_lt hdprod) (Nat.le_of_lt heprod)
  have hq : qMod k d e ≤ W k * (R * R) := by
    unfold qMod
    exact Nat.mul_le_mul (le_refl (W k)) (le_trans hlcmle hbound)
  rw [pow_two]
  exact Nat.lt_succ_of_le hq

/-- `p ∣ lcm(dᵢ,eᵢ)` implies `p ∣ qMod k d e`. -/
private theorem dvd_qMod_of_dvd_lcm {k : ℕ} {d e : Fin k → ℕ} {p : ℕ} {i : Fin k}
    (h : p ∣ Nat.lcm (d i) (e i)) : p ∣ qMod k d e := by
  unfold qMod
  exact (h.trans (Finset.dvd_prod_of_mem (fun j => Nat.lcm (d j) (e j))
    (Finset.mem_univ i))).trans (dvd_mul_left _ _)

/-! ## Prime-to-(coordinate × side) assignments -/

/-- The finite set of prime-to-`(coordinate × side)` assignments for `q`.
`card = (Fin k × Fin 3)^{ω(q)} = (3k)^{ω(q)}`. -/
private def pairAssignSet (k q : ℕ) :
    Finset ((p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) :=
  q.primeFactors.pi (fun _ => (Finset.univ : Finset (Fin k × Fin 3)))

private theorem pairAssignSet_card (k q : ℕ) :
    (pairAssignSet k q).card = (3 * k) ^ q.primeFactors.card := by
  rw [pairAssignSet, Finset.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]

/-- The side reconstruction at coordinate `i`: the product of primes of `q`
assigned to `(i, s)` with `s ≠ excl` (`excl = 1` recovers the `d`-side,
`excl = 0` the `e`-side). -/
private def sideProd {k : ℕ} (q : ℕ)
    (θ : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) (i : Fin k)
    (excl : Fin 3) : ℕ :=
  ∏ p ∈ q.primeFactors.attach.filter
      (fun p => (θ p.1 p.2).1 = i ∧ (θ p.1 p.2).2 ≠ excl), (p : ℕ)

/-- Each side reconstruction divides `q` (product over a subset of its primes). -/
private theorem sideProd_dvd {k q : ℕ} (hq : Squarefree q)
    (θ : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) (i : Fin k) (excl : Fin 3) :
    sideProd q θ i excl ∣ q := by
  have h1 : sideProd q θ i excl ∣ ∏ p ∈ q.primeFactors.attach, (p : ℕ) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  rwa [Finset.prod_attach q.primeFactors (fun p => p),
    Nat.prod_primeFactors_of_squarefree hq] at h1

/-- Prime divisibility of a side reconstruction: exactly the primes of `q`
assigned to `(i, s)` with `s ≠ excl`. -/
private theorem prime_dvd_sideProd_iff {k q : ℕ}
    (θ : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) {p : ℕ} (hp : p.Prime)
    (i : Fin k) (excl : Fin 3) :
    p ∣ sideProd q θ i excl ↔
      ∃ h : p ∈ q.primeFactors, (θ p h).1 = i ∧ (θ p h).2 ≠ excl := by
  constructor
  · intro hdvd
    rw [sideProd] at hdvd
    obtain ⟨qp, hqp, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hdvd
    rw [Finset.mem_filter] at hqp
    have hqprime : (qp : ℕ).Prime := Nat.prime_of_mem_primeFactors qp.2
    have hpe : p = (qp : ℕ) := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
    subst hpe
    exact ⟨qp.2, hqp.2⟩
  · rintro ⟨h, hθ⟩
    exact Finset.dvd_prod_of_mem _
      (Finset.mem_filter.mpr ⟨Finset.mem_attach _ ⟨p, h⟩, hθ⟩)

open Classical in
/-- The canonical assignment of a compatible pair: `p` goes to the coordinate
it divides (in `d` or `e`, unique by `pair_coord_unique`), with side `0`
(`d`-only), `1` (`e`-only), or `2` (both); primes dividing no coordinate (the
`W`-primes) default to `(m, 0)`. -/
private noncomputable def pairTheta {k : ℕ} (m : Fin k) (d e : Fin k → ℕ)
    (p : ℕ) : Fin k × Fin 3 :=
  if h : ∃ j, p ∣ d j ∨ p ∣ e j then
    (h.choose, if p ∣ d h.choose then (if p ∣ e h.choose then 2 else 0) else 1)
  else (m, 0)

/-- On a compatible pair, `pairTheta` picks the coordinate divided by `p`. -/
private theorem pairTheta_coord {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairTheta m d e p).1 = i := by
  have hex : ∃ j, p ∣ d j ∨ p ∣ e j := ⟨i, hi⟩
  unfold pairTheta
  rw [dif_pos hex]
  exact pair_coord_unique hd he hcompat hp hex.choose_spec hi

/-- The side value of `pairTheta` at the divided coordinate. -/
private theorem pairTheta_snd {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairTheta m d e p).2 = if p ∣ d i then (if p ∣ e i then 2 else 0) else 1 := by
  have hex : ∃ j, p ∣ d j ∨ p ∣ e j := ⟨i, hi⟩
  have hci : hex.choose = i := pair_coord_unique hd he hcompat hp hex.choose_spec hi
  unfold pairTheta
  rw [dif_pos hex]
  dsimp only
  rw [hci]

/-- `d`-side test: `p` divides `dᵢ` iff its side is not `1`. -/
private theorem pairTheta_dvd_d {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairTheta m d e p).2 ≠ 1 ↔ p ∣ d i := by
  rw [pairTheta_snd hd he hcompat m hp hi]
  by_cases hpd : p ∣ d i
  · rw [if_pos hpd]
    exact ⟨fun _ => hpd, fun _ => by split_ifs <;> decide⟩
  · rw [if_neg hpd]
    exact ⟨fun h => absurd rfl h, fun h => absurd h hpd⟩

/-- `e`-side test: `p` divides `eᵢ` iff its side is not `0`. -/
private theorem pairTheta_dvd_e {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairTheta m d e p).2 ≠ 0 ↔ p ∣ e i := by
  rw [pairTheta_snd hd he hcompat m hp hi]
  by_cases hpe : p ∣ e i
  · refine ⟨fun _ => hpe, fun _ => ?_⟩
    rw [if_pos hpe]; split_ifs <;> decide
  · have hpd : p ∣ d i := hi.resolve_right hpe
    rw [if_pos hpd, if_neg hpe]
    exact ⟨fun h => absurd rfl h, fun h => absurd h hpe⟩

/-- A prime factor of `q = qMod k d e` at a coordinate `i ≠ m` genuinely
divides `dᵢ` or `eᵢ`: it cannot divide `W` (that would force the default
coordinate `m`), so it divides some `lcm(dⱼ,eⱼ)`, and `j = i` by uniqueness. -/
private theorem prime_of_qMod_coord {k R : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    (hpq : p ∈ (qMod k d e).primeFactors) {i : Fin k} (him : i ≠ m)
    (hcoord : (pairTheta m d e p).1 = i) : p ∣ d i ∨ p ∣ e i := by
  have hpdvd : p ∣ qMod k d e := Nat.dvd_of_mem_primeFactors hpq
  unfold qMod at hpdvd
  rcases (Nat.Prime.dvd_mul hp).mp hpdvd with hpW | hpprod
  · exfalso
    have hnex : ¬ ∃ j, p ∣ d j ∨ p ∣ e j := by
      rintro ⟨j, hjd | hje⟩
      · have h1 : p ∣ 1 :=
          ((mem_kSieveIndex_iff d).mp hd).2.2.1 j ▸ Nat.dvd_gcd hjd hpW
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
      · have h1 : p ∣ 1 :=
          ((mem_kSieveIndex_iff e).mp he).2.2.1 j ▸ Nat.dvd_gcd hje hpW
        exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
    have hcm : (pairTheta m d e p).1 = m := by unfold pairTheta; rw [dif_neg hnex]
    exact him (hcoord.symm.trans hcm)
  · obtain ⟨j, -, hpj⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpprod
    have hj : p ∣ d j ∨ p ∣ e j :=
      (Nat.Prime.dvd_mul hp).mp (hpj.trans (lcm_dvd_mul _ _))
    have hcj : (pairTheta m d e p).1 = j := pairTheta_coord hd he hcompat m hp hj
    have hji : j = i := hcj.symm.trans hcoord
    rw [← hji]; exact hj

/-! ## Recovery: the pair is determined by `(q, θ)` -/

/-- **Side recovery.**  For a compatible pair and `i ≠ m`, the side product at
`(i, excl)` reconstructs the coordinate `f i` (`f = d, excl = 1` or
`f = e, excl = 0`): both are squarefree with the same prime factors. -/
private theorem pair_recover_side {k R : ℕ} (m : Fin k) {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) {i : Fin k} (him : i ≠ m)
    (f : Fin k → ℕ) (excl : Fin 3) (hfsq : Squarefree (f i))
    (hfdvd : ∀ p, p.Prime → p ∣ f i → p ∣ d i ∨ p ∣ e i)
    (hside : ∀ p, p.Prime → (p ∣ d i ∨ p ∣ e i) →
        ((pairTheta m d e p).2 ≠ excl ↔ p ∣ f i)) :
    sideProd (qMod k d e) (fun p _ => pairTheta m d e p) i excl = f i := by
  set θ : (p : ℕ) → p ∈ (qMod k d e).primeFactors → Fin k × Fin 3 :=
    fun p _ => pairTheta m d e p with hθ
  have hqsq : Squarefree (qMod k d e) := qMod_squarefree hd he hcompat
  have hqne : qMod k d e ≠ 0 := hqsq.ne_zero
  have hXsq : Squarefree (sideProd (qMod k d e) θ i excl) :=
    hqsq.squarefree_of_dvd (sideProd_dvd hqsq θ i excl)
  have d1 : f i ∣ sideProd (qMod k d e) θ i excl := by
    rw [squarefree_dvd_iff_primes hfsq]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpfi : p ∣ f i := Nat.dvd_of_mem_primeFactors hp
    have hor : p ∣ d i ∨ p ∣ e i := hfdvd p hpp hpfi
    have hcoord : (pairTheta m d e p).1 = i := pairTheta_coord hd he hcompat m hpp hor
    have hsd : (pairTheta m d e p).2 ≠ excl := (hside p hpp hor).mpr hpfi
    have hplcm : p ∣ Nat.lcm (d i) (e i) :=
      hor.elim (fun h => h.trans (Nat.dvd_lcm_left _ _))
        (fun h => h.trans (Nat.dvd_lcm_right _ _))
    have hpq : p ∈ (qMod k d e).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, dvd_qMod_of_dvd_lcm hplcm, hqne⟩
    exact (prime_dvd_sideProd_iff θ hpp i excl).mpr ⟨hpq, hcoord, hsd⟩
  have d2 : sideProd (qMod k d e) θ i excl ∣ f i := by
    rw [squarefree_dvd_iff_primes hXsq]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpX : p ∣ sideProd (qMod k d e) θ i excl := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨hpq, hcoord, hsd⟩ := (prime_dvd_sideProd_iff θ hpp i excl).mp hpX
    have hor : p ∣ d i ∨ p ∣ e i :=
      prime_of_qMod_coord hd he hcompat m hpp hpq him hcoord
    exact (hside p hpp hor).mp hsd
  exact Nat.dvd_antisymm d2 d1

/-- `d`-coordinate recovery (`excl = 1`). -/
private theorem pair_recover_d {k R : ℕ} (m : Fin k) {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) {i : Fin k} (him : i ≠ m) :
    sideProd (qMod k d e) (fun p _ => pairTheta m d e p) i 1 = d i :=
  pair_recover_side m hd he hcompat him d 1 (((mem_kSieveIndex_iff d).mp hd).1 i)
    (fun _ _ h => Or.inl h)
    (fun _p hp hor => pairTheta_dvd_d hd he hcompat m hp hor)

/-- `e`-coordinate recovery (`excl = 0`). -/
private theorem pair_recover_e {k R : ℕ} (m : Fin k) {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R (W k)) (he : e ∈ kSieveIndex k R (W k))
    (hcompat : ¬ IsCollisionPair d e) {i : Fin k} (him : i ≠ m) :
    sideProd (qMod k d e) (fun p _ => pairTheta m d e p) i 0 = e i :=
  pair_recover_side m hd he hcompat him e 0 (((mem_kSieveIndex_iff e).mp he).1 i)
    (fun _ _ h => Or.inr h)
    (fun _p hp hor => pairTheta_dvd_e hd he hcompat m hp hor)

/-- `sideProd` depends only on the values of `θ` on `q.primeFactors`. -/
private theorem sideProd_congr {k q : ℕ}
    {θ θ' : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3}
    (h : ∀ r (hr : r ∈ q.primeFactors), θ r hr = θ' r hr) (i : Fin k) (excl : Fin 3) :
    sideProd q θ i excl = sideProd q θ' i excl := by
  unfold sideProd
  refine Finset.prod_congr (Finset.filter_congr (fun r _ => ?_)) (fun _ _ => rfl)
  rw [h r.1 r.2]

/-! ## The per-fiber count -/

/-- **Fiber count.**  Any set `S` of compatible pairs with a fixed combined
modulus `q` has at most `(3k)^{ω(q)}` elements: the assignment
`(d,e) ↦ (p ↦ pairTheta)` injects `S` into `pairAssignSet k q`, since each pair
is recovered from `(q, θ)` by `pair_recover_d`/`pair_recover_e`. -/
private theorem fiber_card_le {k R : ℕ} (m : Fin k) (q : ℕ)
    (S : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hS : ∀ p ∈ S,
        p.1 ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1)
      ∧ p.2 ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1)
      ∧ ¬ IsCollisionPair p.1 p.2 ∧ qMod k p.1 p.2 = q) :
    S.card ≤ (3 * k) ^ q.primeFactors.card := by
  classical
  have hmap : ∀ p ∈ S,
      (fun (r : ℕ) (_ : r ∈ q.primeFactors) => pairTheta m p.1 p.2 r) ∈ pairAssignSet k q :=
    fun p _ => Finset.mem_pi.mpr (fun r _ => Finset.mem_univ _)
  have hinj : Set.InjOn
      (fun p : (Fin k → ℕ) × (Fin k → ℕ) =>
        (fun (r : ℕ) (_ : r ∈ q.primeFactors) => pairTheta m p.1 p.2 r)) ↑S := by
    intro a ha b hb hab
    obtain ⟨haf1, haf2, hacompat, haq⟩ := hS a (Finset.mem_coe.mp ha)
    obtain ⟨hbf1, hbf2, hbcompat, hbq⟩ := hS b (Finset.mem_coe.mp hb)
    rw [Finset.mem_filter] at haf1 haf2 hbf1 hbf2
    have hthetaeq : ∀ r (hr : r ∈ q.primeFactors),
        pairTheta m a.1 a.2 r = pairTheta m b.1 b.2 r :=
      fun r hr => congrFun (congrFun hab r) hr
    have key1 : a.1 = b.1 := by
      funext i
      by_cases him : i = m
      · rw [him, haf1.2, hbf1.2]
      · have ra : a.1 i = sideProd q (fun p _ => pairTheta m a.1 a.2 p) i 1 := by
          rw [← haq]; exact (pair_recover_d m haf1.1 haf2.1 hacompat him).symm
        have rb : b.1 i = sideProd q (fun p _ => pairTheta m b.1 b.2 p) i 1 := by
          rw [← hbq]; exact (pair_recover_d m hbf1.1 hbf2.1 hbcompat him).symm
        rw [ra, rb]
        exact sideProd_congr hthetaeq i 1
    have key2 : a.2 = b.2 := by
      funext i
      by_cases him : i = m
      · rw [him, haf2.2, hbf2.2]
      · have ra : a.2 i = sideProd q (fun p _ => pairTheta m a.1 a.2 p) i 0 := by
          rw [← haq]; exact (pair_recover_e m haf1.1 haf2.1 hacompat him).symm
        have rb : b.2 i = sideProd q (fun p _ => pairTheta m b.1 b.2 p) i 0 := by
          rw [← hbq]; exact (pair_recover_e m hbf1.1 hbf2.1 hbcompat him).symm
        rw [ra, rb]
        exact sideProd_congr hthetaeq i 0
    exact Prod.ext key1 key2
  calc S.card ≤ (pairAssignSet k q).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = (3 * k) ^ q.primeFactors.card := pairAssignSet_card k q

/-! ## The headline: the pair fiber bound -/

/-- **C4 item 4 — the pair fiber count.**  A nonnegative `F` summed over
compatible pairs (both in the sieve index, `dₘ = eₘ = 1`, non-collision),
regrouped by their combined modulus `q = qMod k d e`, is dominated by the
`(3k)^{ω(q)}`-weighted sum over squarefree `q < W·R² + 1`.  Fold the double sum
to a product sum over compatible pairs, group by `qMod` (lands squarefree in
range by `qMod_squarefree`/`qMod_mem_range`), count each fiber by
`(3k)^{ω(q)}` (`fiber_card_le`), and use `F ≥ 0`. -/
theorem compat_pair_fiber_le (k R : ℕ) (m : Fin k) (F : ℕ → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ∑ d ∈ (kSieveIndex k R (W k)).filter (fun d => d m = 1),
      ∑ e ∈ (kSieveIndex k R (W k)).filter (fun e => e m = 1),
        (if IsCollisionPair d e then 0 else F (qMod k d e))
      ≤ ∑ q ∈ (Finset.range (W k * R ^ 2 + 1)).filter Squarefree,
          (3 * k : ℝ) ^ q.primeFactors.card * F q := by
  classical
  set Dm := (kSieveIndex k R (W k)).filter (fun d => d m = 1) with hDm
  set SF := (Finset.range (W k * R ^ 2 + 1)).filter Squarefree with hSF
  set compatSet := (Dm ×ˢ Dm).filter (fun p => ¬ IsCollisionPair p.1 p.2) with hCS
  -- Step 1: fold to a product sum over compatible pairs
  have hstep1 : (∑ d ∈ Dm, ∑ e ∈ Dm, (if IsCollisionPair d e then 0 else F (qMod k d e)))
      = ∑ p ∈ compatSet, F (qMod k p.1 p.2) := by
    rw [← Finset.sum_product']
    conv_rhs => rw [hCS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : IsCollisionPair p.1 p.2
    · rw [if_pos h, if_neg (not_not_intro h)]
    · rw [if_neg h, if_pos h]
  rw [hstep1]
  -- Step 2: qMod maps compatible pairs into the squarefree range
  have hmaps : ∀ p ∈ compatSet, qMod k p.1 p.2 ∈ SF := by
    intro p hp
    rw [hCS] at hp
    obtain ⟨hprod, hpcol⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
    rw [hDm, Finset.mem_filter] at hp1 hp2
    rw [hSF, Finset.mem_filter]
    exact ⟨qMod_mem_range hp1.1 hp2.1, qMod_squarefree hp1.1 hp2.1 hpcol⟩
  -- Step 3: fiber by qMod and count
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => F (qMod k p.1 p.2))]
  refine Finset.sum_le_sum (fun q hq => ?_)
  have hqsf : Squarefree q := (Finset.mem_filter.mp hq).2
  set fiberq := compatSet.filter (fun p => qMod k p.1 p.2 = q) with hfib
  have hcongr : ∀ p ∈ fiberq, F (qMod k p.1 p.2) = F q :=
    fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  have hcard : fiberq.card ≤ (3 * k) ^ q.primeFactors.card := by
    apply fiber_card_le (R := R) m q fiberq
    intro p hp
    rw [hfib] at hp
    obtain ⟨hpc, hpq⟩ := Finset.mem_filter.mp hp
    rw [hCS] at hpc
    obtain ⟨hprod, hpcol⟩ := Finset.mem_filter.mp hpc
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
    rw [hDm] at hp1 hp2
    exact ⟨hp1, hp2, hpcol, hpq⟩
  apply mul_le_mul_of_nonneg_right _ (hF q)
  calc (fiberq.card : ℝ) ≤ (((3 * k) ^ q.primeFactors.card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (3 * k : ℝ) ^ q.primeFactors.card := by push_cast; ring

end Salt.Maynard
