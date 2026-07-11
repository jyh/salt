/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Eh
import Salt.Maynard.FrontierDischarge
import Salt.Maynard.S2FiberCount

/-!
# W5-3 — free-`W'` mirrors of the S₂ discrepancy (`herr`) chain

The free-modulus `S2mW_lower` (`S2Eh.lean`) discharges its `herr` hypothesis
from exactly the same discrepancy assembly that `S2CompatEH.lean`/
`FrontierDischarge.lean` built at the hardwired modulus `W k`.  This file lands
the free-`W'` mirrors so a follow-on (W5-6) can assemble `herr` and close
`S2mW_ge_compatMain_theta_uniform`:

* `abs_S2mW_sub_compatMainW_le` — the algebraic core (mirror of
  `abs_S2m_sub_compatMain_le`): `S2mW` rewrites to a compat-guarded sum
  (collision ⟹ `s2PrimeCountW = 0` via `s2PrimeCountW_collision`), and its
  difference from the compat main is a single compat sum of
  `λλ·(count − density)`, triangle-bounded per pair.
* `abs_S2mW_sub_compatMainW_le_disc_R_uniform` — the `R`-uniform disc bound
  (mirror of `abs_S2m_sub_compatMain_le_disc_R_uniform`), stated for a general
  weight `y` with `|y| ≤ 1`, reusing the free-`W`/free-`y`
  `lam_abs_le_sharp_uniform` and the landed `s2PrimeCountW_approx'`.
* `compat_pair_fiber_leW` — the free-`W'` CRT `(3k)^{ω(q)}` fiber count (mirror
  of `compat_pair_fiber_le`): the entire fiber machinery of `S2FiberCount.lean`,
  reproduced at modulus `qModW k W' d e = W'·∏lcm` over `q < W'·R²+1`.

Everything is additive (`*W`-suffixed); no landed statement is touched.
-/

namespace Salt.Maynard

open Finset

/-! ## The base algebraic discrepancy bound (mirror of `abs_S2m_sub_compatMain_le`) -/

/-- **Free-`W'` C4 core (algebraic).** `S2mW` minus its compat main term is
controlled, pair by pair, by `|λ_d||λ_e|·|count − density|` over compat pairs.
Collision pairs drop out on both sides (`s2PrimeCountW_collision` on the left,
the `IsCollisionPair` guard on the right).  Free `y`; needs `hD`/`hlt`. -/
theorem abs_S2mW_sub_compatMainW_le (k K₀ N R ν₀ W' D : ℕ) (m : Fin k)
    (y : (Fin k → ℕ) → ℝ) (hRN : R ≤ N)
    (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D ≤ p) (hlt : ∀ i : Fin k, hSeq k i < D) :
    |S2mW k K₀ N R ν₀ W' m y
        - deltaPi k K₀ N m / (Nat.totient W' : ℝ)
            * s2CompatFormM k R W' m y|
      ≤ ∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else |lam k R W' y d| * |lam k R W' y e|
                    * |(s2PrimeCountW k K₀ N ν₀ W' m d e : ℝ)
                        - deltaPi k K₀ N m / ((Nat.totient W' : ℝ)
                            * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))|) := by
  classical
  -- `S2mW` as a compat-guarded sum: on collision pairs the count is `0`.
  have hS2m : S2mW k K₀ N R ν₀ W' m y
      = ∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else lam k R W' y d * lam k R W' y e
                    * (s2PrimeCountW k K₀ N ν₀ W' m d e : ℝ)) := by
    rw [S2mW_eq_guarded k K₀ N R ν₀ W' m y hRN, guarded_double_sum]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.mem_filter] at hd
    by_cases hcol : IsCollisionPair d e
    · rw [if_pos hcol]
      obtain ⟨i, j, hij, hcolij⟩ := hcol
      have hdcop : ∀ i, Nat.Coprime (d i) W' := ((mem_kSieveIndex_iff d).mp hd.1).2.2.1
      rw [s2PrimeCountW_collision k K₀ N ν₀ W' D m d e hD hlt hdcop hij hcolij]
      simp
    · rw [if_neg hcol]
  -- the difference is a single compat-guarded sum of `λλ·(count − density)`.
  have hcombine : S2mW k K₀ N R ν₀ W' m y
        - deltaPi k K₀ N m / (Nat.totient W' : ℝ)
            * s2CompatFormM k R W' m y
      = ∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else lam k R W' y d * lam k R W' y e
                    * ((s2PrimeCountW k K₀ N ν₀ W' m d e : ℝ)
                        - deltaPi k K₀ N m / ((Nat.totient W' : ℝ)
                            * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)))) := by
    rw [hS2m, s2CompatMainW_eq k K₀ N R W' m y, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hcol : IsCollisionPair d e
    · simp only [if_pos hcol, sub_zero]
    · rw [if_neg hcol, if_neg hcol, if_neg hcol]; ring
  rw [hcombine]
  -- triangle inequality, twice, then per-pair `|λλΔ| = |λ||λ||Δ|`.
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun d _ => ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => ?_))
  by_cases hcol : IsCollisionPair d e
  · rw [if_pos hcol, if_pos hcol, abs_zero]
  · rw [if_neg hcol, if_neg hcol, abs_mul, abs_mul]

/-! ## Fiber-count helpers, free-`W'` (mirrors of `S2FiberCount.lean`'s
private chain, which is file-local and thus reproduced here). -/

/-- The lcm of two squarefrees is squarefree. -/
private theorem lcmSquarefreeW {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (ha.natFactorization_le_one p) (hb.natFactorization_le_one p)

/-- Each combined lcm coordinate is coprime to `W'` (both `dᵢ, eᵢ` are). -/
private theorem lcmCoprimeWW {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W') (i : Fin k) :
    Nat.Coprime W' (Nat.lcm (d i) (e i)) := by
  have hdW : Nat.Coprime (d i) W' := ((mem_kSieveIndex_iff d).mp hd).2.2.1 i
  have heW : Nat.Coprime (e i) W' := ((mem_kSieveIndex_iff e).mp he).2.2.1 i
  exact ((hdW.symm).mul_right (heW.symm)).coprime_dvd_right (Nat.lcm_dvd_mul _ _)

/-- **Coordinate uniqueness for a compatible pair** (free `W'`).  A prime
dividing some coordinate of `d` or `e` at index `i`, and again at index `j`,
forces `i = j`. -/
private theorem pairCoordUniqueW {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) {p : ℕ} (hp : p.Prime) {i j : Fin k}
    (hi : p ∣ d i ∨ p ∣ e i) (hj : p ∣ d j ∨ p ∣ e j) : i = j := by
  by_contra hne
  rcases hi with hdi | hei <;> rcases hj with hdj | hej
  · exact hne (prime_dvd_coord_unique hd hp hdi hdj)
  · exact hcompat ⟨i, j, hne, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdi, hej⟩⟩
  · exact hcompat ⟨j, i, Ne.symm hne, Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hdj, hei⟩⟩
  · exact hne (prime_dvd_coord_unique he hp hei hej)

/-- The combined lcms are pairwise coprime (`i ≠ j`), free `W'`. -/
private theorem lcmPairwiseCoprimeW {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) := by
  apply Nat.coprime_of_dvd
  intro p hp hpi hpj
  have hi : p ∣ d i ∨ p ∣ e i := (Nat.Prime.dvd_mul hp).mp (hpi.trans (Nat.lcm_dvd_mul _ _))
  have hj : p ∣ d j ∨ p ∣ e j := (Nat.Prime.dvd_mul hp).mp (hpj.trans (Nat.lcm_dvd_mul _ _))
  exact hij (pairCoordUniqueW hd he hcompat hp hi hj)

/-- `qModW k W' d e = W'·∏lcm` is squarefree for a compatible pair (`Squarefree
W'`, squarefree pairwise-coprime lcms, `W'` coprime to the product). -/
private theorem qModWSquarefreeW {k R W' : ℕ} (hW' : Squarefree W') {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) : Squarefree (qModW k W' d e) := by
  have hdsq := ((mem_kSieveIndex_iff d).mp hd).1
  have hesq := ((mem_kSieveIndex_iff e).mp he).1
  have hprodsq : Squarefree (∏ i, Nat.lcm (d i) (e i)) :=
    squarefree_prod_coprime _ _ (fun i _ => lcmSquarefreeW (hdsq i) (hesq i))
      (fun i _ j _ hij => lcmPairwiseCoprimeW hd he hcompat hij)
  have hcopW : Nat.Coprime W' (∏ i, Nat.lcm (d i) (e i)) :=
    Nat.Coprime.prod_right (fun i _ => lcmCoprimeWW hd he i)
  unfold qModW
  rw [Nat.squarefree_mul hcopW]
  exact ⟨hW', hprodsq⟩

/-- `qModW k W' d e < W'·R² + 1`. -/
private theorem qModWMemRangeW {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W') :
    qModW k W' d e ∈ Finset.range (W' * R ^ 2 + 1) := by
  rw [Finset.mem_range]
  have hdprod : ∏ i, d i < R := ((mem_kSieveIndex_iff d).mp hd).2.2.2
  have heprod : ∏ i, e i < R := ((mem_kSieveIndex_iff e).mp he).2.2.2
  have hlcmdvd : (∏ i, Nat.lcm (d i) (e i)) ∣ (∏ i, d i) * (∏ i, e i) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => Nat.lcm_dvd_mul _ _)
  have hprodpos : 0 < (∏ i, d i) * (∏ i, e i) :=
    Nat.mul_pos (Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hd i))
      (Finset.prod_pos (fun i _ => kSieveIndex_coord_pos he i))
  have hlcmle : ∏ i, Nat.lcm (d i) (e i) ≤ (∏ i, d i) * (∏ i, e i) :=
    Nat.le_of_dvd hprodpos hlcmdvd
  have hbound : (∏ i, d i) * (∏ i, e i) ≤ R * R :=
    Nat.mul_le_mul (Nat.le_of_lt hdprod) (Nat.le_of_lt heprod)
  have hq : qModW k W' d e ≤ W' * (R * R) := by
    unfold qModW
    exact Nat.mul_le_mul (le_refl W') (le_trans hlcmle hbound)
  rw [pow_two]
  exact Nat.lt_succ_of_le hq

/-- `p ∣ lcm(dᵢ,eᵢ)` implies `p ∣ qModW k W' d e`. -/
private theorem dvdQModWOfDvdLcm {k W' : ℕ} {d e : Fin k → ℕ} {p : ℕ} {i : Fin k}
    (h : p ∣ Nat.lcm (d i) (e i)) : p ∣ qModW k W' d e := by
  unfold qModW
  exact (h.trans (Finset.dvd_prod_of_mem (fun j => Nat.lcm (d j) (e j))
    (Finset.mem_univ i))).trans (dvd_mul_left _ _)

/-- The finite set of prime-to-`(coordinate × side)` assignments for `q`. -/
private def pairAssignSetW (k q : ℕ) :
    Finset ((p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) :=
  q.primeFactors.pi (fun _ => (Finset.univ : Finset (Fin k × Fin 3)))

private theorem pairAssignSetW_card (k q : ℕ) :
    (pairAssignSetW k q).card = (3 * k) ^ q.primeFactors.card := by
  rw [pairAssignSetW, Finset.card_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.mul_comm]

/-- The side reconstruction at coordinate `i`. -/
private def sideProdW {k : ℕ} (q : ℕ)
    (θ : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) (i : Fin k)
    (excl : Fin 3) : ℕ :=
  ∏ p ∈ q.primeFactors.attach.filter
      (fun p => (θ p.1 p.2).1 = i ∧ (θ p.1 p.2).2 ≠ excl), (p : ℕ)

/-- Each side reconstruction divides `q`. -/
private theorem sideProdW_dvd {k q : ℕ} (hq : Squarefree q)
    (θ : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) (i : Fin k) (excl : Fin 3) :
    sideProdW q θ i excl ∣ q := by
  have h1 : sideProdW q θ i excl ∣ ∏ p ∈ q.primeFactors.attach, (p : ℕ) :=
    Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  rwa [Finset.prod_attach q.primeFactors (fun p => p),
    Nat.prod_primeFactors_of_squarefree hq] at h1

/-- Prime divisibility of a side reconstruction. -/
private theorem primeDvdSideProdWIff {k q : ℕ}
    (θ : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3) {p : ℕ} (hp : p.Prime)
    (i : Fin k) (excl : Fin 3) :
    p ∣ sideProdW q θ i excl ↔
      ∃ h : p ∈ q.primeFactors, (θ p h).1 = i ∧ (θ p h).2 ≠ excl := by
  constructor
  · intro hdvd
    rw [sideProdW] at hdvd
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
/-- The canonical assignment of a compatible pair (side `0` = d-only, `1` =
e-only, `2` = both; `W'`-primes default to `(m, 0)`). -/
private noncomputable def pairThetaW {k : ℕ} (m : Fin k) (d e : Fin k → ℕ)
    (p : ℕ) : Fin k × Fin 3 :=
  if h : ∃ j, p ∣ d j ∨ p ∣ e j then
    (h.choose, if p ∣ d h.choose then (if p ∣ e h.choose then 2 else 0) else 1)
  else (m, 0)

/-- On a compatible pair, `pairThetaW` picks the coordinate divided by `p`. -/
private theorem pairThetaW_coord {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairThetaW m d e p).1 = i := by
  have hex : ∃ j, p ∣ d j ∨ p ∣ e j := ⟨i, hi⟩
  unfold pairThetaW
  rw [dif_pos hex]
  exact pairCoordUniqueW hd he hcompat hp hex.choose_spec hi

/-- The side value of `pairThetaW` at the divided coordinate. -/
private theorem pairThetaW_snd {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairThetaW m d e p).2 = if p ∣ d i then (if p ∣ e i then 2 else 0) else 1 := by
  have hex : ∃ j, p ∣ d j ∨ p ∣ e j := ⟨i, hi⟩
  have hci : hex.choose = i := pairCoordUniqueW hd he hcompat hp hex.choose_spec hi
  unfold pairThetaW
  rw [dif_pos hex]
  dsimp only
  rw [hci]

/-- `d`-side test: `p` divides `dᵢ` iff its side is not `1`. -/
private theorem pairThetaW_dvd_d {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairThetaW m d e p).2 ≠ 1 ↔ p ∣ d i := by
  rw [pairThetaW_snd hd he hcompat m hp hi]
  by_cases hpd : p ∣ d i
  · rw [if_pos hpd]
    exact ⟨fun _ => hpd, fun _ => by split_ifs <;> decide⟩
  · rw [if_neg hpd]
    exact ⟨fun h => absurd rfl h, fun h => absurd h hpd⟩

/-- `e`-side test: `p` divides `eᵢ` iff its side is not `0`. -/
private theorem pairThetaW_dvd_e {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    {i : Fin k} (hi : p ∣ d i ∨ p ∣ e i) :
    (pairThetaW m d e p).2 ≠ 0 ↔ p ∣ e i := by
  rw [pairThetaW_snd hd he hcompat m hp hi]
  by_cases hpe : p ∣ e i
  · refine ⟨fun _ => hpe, fun _ => ?_⟩
    rw [if_pos hpe]; split_ifs <;> decide
  · have hpd : p ∣ d i := hi.resolve_right hpe
    rw [if_pos hpd, if_neg hpe]
    exact ⟨fun h => absurd rfl h, fun h => absurd h hpe⟩

/-- A prime factor of `q = qModW k W' d e` at a coordinate `i ≠ m` genuinely
divides `dᵢ` or `eᵢ`. -/
private theorem primeOfQModWCoord {k R W' : ℕ} {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) (m : Fin k) {p : ℕ} (hp : p.Prime)
    (hpq : p ∈ (qModW k W' d e).primeFactors) {i : Fin k} (him : i ≠ m)
    (hcoord : (pairThetaW m d e p).1 = i) : p ∣ d i ∨ p ∣ e i := by
  have hpdvd : p ∣ qModW k W' d e := Nat.dvd_of_mem_primeFactors hpq
  unfold qModW at hpdvd
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
    have hcm : (pairThetaW m d e p).1 = m := by unfold pairThetaW; rw [dif_neg hnex]
    exact him (hcoord.symm.trans hcm)
  · obtain ⟨j, -, hpj⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpprod
    have hj : p ∣ d j ∨ p ∣ e j :=
      (Nat.Prime.dvd_mul hp).mp (hpj.trans (Nat.lcm_dvd_mul _ _))
    have hcj : (pairThetaW m d e p).1 = j := pairThetaW_coord hd he hcompat m hp hj
    have hji : j = i := hcj.symm.trans hcoord
    rw [← hji]; exact hj

/-- **Side recovery** (free `W'`). -/
private theorem pairRecoverSideW {k R W' : ℕ} (hW' : Squarefree W') (m : Fin k)
    {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) {i : Fin k} (him : i ≠ m)
    (f : Fin k → ℕ) (excl : Fin 3) (hfsq : Squarefree (f i))
    (hfdvd : ∀ p, p.Prime → p ∣ f i → p ∣ d i ∨ p ∣ e i)
    (hside : ∀ p, p.Prime → (p ∣ d i ∨ p ∣ e i) →
        ((pairThetaW m d e p).2 ≠ excl ↔ p ∣ f i)) :
    sideProdW (qModW k W' d e) (fun p _ => pairThetaW m d e p) i excl = f i := by
  set θ : (p : ℕ) → p ∈ (qModW k W' d e).primeFactors → Fin k × Fin 3 :=
    fun p _ => pairThetaW m d e p with hθ
  have hqsq : Squarefree (qModW k W' d e) := qModWSquarefreeW hW' hd he hcompat
  have hqne : qModW k W' d e ≠ 0 := hqsq.ne_zero
  have hXsq : Squarefree (sideProdW (qModW k W' d e) θ i excl) :=
    hqsq.squarefree_of_dvd (sideProdW_dvd hqsq θ i excl)
  have d1 : f i ∣ sideProdW (qModW k W' d e) θ i excl := by
    rw [squarefree_dvd_iff_primes hfsq]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpfi : p ∣ f i := Nat.dvd_of_mem_primeFactors hp
    have hor : p ∣ d i ∨ p ∣ e i := hfdvd p hpp hpfi
    have hcoord : (pairThetaW m d e p).1 = i := pairThetaW_coord hd he hcompat m hpp hor
    have hsd : (pairThetaW m d e p).2 ≠ excl := (hside p hpp hor).mpr hpfi
    have hplcm : p ∣ Nat.lcm (d i) (e i) :=
      hor.elim (fun h => h.trans (Nat.dvd_lcm_left _ _))
        (fun h => h.trans (Nat.dvd_lcm_right _ _))
    have hpq : p ∈ (qModW k W' d e).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, dvdQModWOfDvdLcm hplcm, hqne⟩
    exact (primeDvdSideProdWIff θ hpp i excl).mpr ⟨hpq, hcoord, hsd⟩
  have d2 : sideProdW (qModW k W' d e) θ i excl ∣ f i := by
    rw [squarefree_dvd_iff_primes hXsq]
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpX : p ∣ sideProdW (qModW k W' d e) θ i excl := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨hpq, hcoord, hsd⟩ := (primeDvdSideProdWIff θ hpp i excl).mp hpX
    have hor : p ∣ d i ∨ p ∣ e i :=
      primeOfQModWCoord hd he hcompat m hpp hpq him hcoord
    exact (hside p hpp hor).mp hsd
  exact Nat.dvd_antisymm d2 d1

/-- `d`-coordinate recovery (`excl = 1`). -/
private theorem pairRecoverDW {k R W' : ℕ} (hW' : Squarefree W') (m : Fin k)
    {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) {i : Fin k} (him : i ≠ m) :
    sideProdW (qModW k W' d e) (fun p _ => pairThetaW m d e p) i 1 = d i :=
  pairRecoverSideW hW' m hd he hcompat him d 1 (((mem_kSieveIndex_iff d).mp hd).1 i)
    (fun _ _ h => Or.inl h)
    (fun _p hp hor => pairThetaW_dvd_d hd he hcompat m hp hor)

/-- `e`-coordinate recovery (`excl = 0`). -/
private theorem pairRecoverEW {k R W' : ℕ} (hW' : Squarefree W') (m : Fin k)
    {d e : Fin k → ℕ}
    (hd : d ∈ kSieveIndex k R W') (he : e ∈ kSieveIndex k R W')
    (hcompat : ¬ IsCollisionPair d e) {i : Fin k} (him : i ≠ m) :
    sideProdW (qModW k W' d e) (fun p _ => pairThetaW m d e p) i 0 = e i :=
  pairRecoverSideW hW' m hd he hcompat him e 0 (((mem_kSieveIndex_iff e).mp he).1 i)
    (fun _ _ h => Or.inr h)
    (fun _p hp hor => pairThetaW_dvd_e hd he hcompat m hp hor)

/-- `sideProdW` depends only on the values of `θ` on `q.primeFactors`. -/
private theorem sideProdWCongr {k q : ℕ}
    {θ θ' : (p : ℕ) → p ∈ q.primeFactors → Fin k × Fin 3}
    (h : ∀ r (hr : r ∈ q.primeFactors), θ r hr = θ' r hr) (i : Fin k) (excl : Fin 3) :
    sideProdW q θ i excl = sideProdW q θ' i excl := by
  unfold sideProdW
  refine Finset.prod_congr (Finset.filter_congr (fun r _ => ?_)) (fun _ _ => rfl)
  rw [h r.1 r.2]

/-- **Fiber count** (free `W'`).  Any set `S` of compatible pairs with a fixed
combined modulus `q` has at most `(3k)^{ω(q)}` elements. -/
private theorem fiberCardLeW {k R W' : ℕ} (hW' : Squarefree W') (m : Fin k) (q : ℕ)
    (S : Finset ((Fin k → ℕ) × (Fin k → ℕ)))
    (hS : ∀ p ∈ S,
        p.1 ∈ (kSieveIndex k R W').filter (fun d => d m = 1)
      ∧ p.2 ∈ (kSieveIndex k R W').filter (fun e => e m = 1)
      ∧ ¬ IsCollisionPair p.1 p.2 ∧ qModW k W' p.1 p.2 = q) :
    S.card ≤ (3 * k) ^ q.primeFactors.card := by
  classical
  have hmap : ∀ p ∈ S,
      (fun (r : ℕ) (_ : r ∈ q.primeFactors) => pairThetaW m p.1 p.2 r) ∈ pairAssignSetW k q :=
    fun p _ => Finset.mem_pi.mpr (fun r _ => Finset.mem_univ _)
  have hinj : Set.InjOn
      (fun p : (Fin k → ℕ) × (Fin k → ℕ) =>
        (fun (r : ℕ) (_ : r ∈ q.primeFactors) => pairThetaW m p.1 p.2 r)) ↑S := by
    intro a ha b hb hab
    obtain ⟨haf1, haf2, hacompat, haq⟩ := hS a (Finset.mem_coe.mp ha)
    obtain ⟨hbf1, hbf2, hbcompat, hbq⟩ := hS b (Finset.mem_coe.mp hb)
    rw [Finset.mem_filter] at haf1 haf2 hbf1 hbf2
    have hthetaeq : ∀ r (hr : r ∈ q.primeFactors),
        pairThetaW m a.1 a.2 r = pairThetaW m b.1 b.2 r :=
      fun r hr => congrFun (congrFun hab r) hr
    have key1 : a.1 = b.1 := by
      funext i
      by_cases him : i = m
      · rw [him, haf1.2, hbf1.2]
      · have ra : a.1 i = sideProdW q (fun p _ => pairThetaW m a.1 a.2 p) i 1 := by
          rw [← haq]; exact (pairRecoverDW hW' m haf1.1 haf2.1 hacompat him).symm
        have rb : b.1 i = sideProdW q (fun p _ => pairThetaW m b.1 b.2 p) i 1 := by
          rw [← hbq]; exact (pairRecoverDW hW' m hbf1.1 hbf2.1 hbcompat him).symm
        rw [ra, rb]
        exact sideProdWCongr hthetaeq i 1
    have key2 : a.2 = b.2 := by
      funext i
      by_cases him : i = m
      · rw [him, haf2.2, hbf2.2]
      · have ra : a.2 i = sideProdW q (fun p _ => pairThetaW m a.1 a.2 p) i 0 := by
          rw [← haq]; exact (pairRecoverEW hW' m haf1.1 haf2.1 hacompat him).symm
        have rb : b.2 i = sideProdW q (fun p _ => pairThetaW m b.1 b.2 p) i 0 := by
          rw [← hbq]; exact (pairRecoverEW hW' m hbf1.1 hbf2.1 hbcompat him).symm
        rw [ra, rb]
        exact sideProdWCongr hthetaeq i 0
    exact Prod.ext key1 key2
  calc S.card ≤ (pairAssignSetW k q).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = (3 * k) ^ q.primeFactors.card := pairAssignSetW_card k q

/-! ## The headline free-`W'` fiber bound (mirror of `compat_pair_fiber_le`) -/

/-- **W5-3 item 3 — the free-`W'` pair fiber count.**  A nonnegative `F` summed
over compatible pairs (both in `kSieveIndex k R W'`, `dₘ = eₘ = 1`,
non-collision), regrouped by their combined modulus `q = qModW k W' d e`, is
dominated by the `(3k)^{ω(q)}`-weighted sum over squarefree `q < W'·R² + 1`. -/
theorem compat_pair_fiber_leW (k R W' : ℕ) (hW' : Squarefree W') (m : Fin k)
    (F : ℕ → ℝ) (hF : ∀ q, 0 ≤ F q) :
    ∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
      ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
        (if IsCollisionPair d e then 0 else F (qModW k W' d e))
      ≤ ∑ q ∈ (Finset.range (W' * R ^ 2 + 1)).filter Squarefree,
          (3 * k : ℝ) ^ q.primeFactors.card * F q := by
  classical
  set Dm := (kSieveIndex k R W').filter (fun d => d m = 1) with hDm
  set SF := (Finset.range (W' * R ^ 2 + 1)).filter Squarefree with hSF
  set compatSet := (Dm ×ˢ Dm).filter (fun p => ¬ IsCollisionPair p.1 p.2) with hCS
  -- Step 1: fold to a product sum over compatible pairs
  have hstep1 : (∑ d ∈ Dm, ∑ e ∈ Dm, (if IsCollisionPair d e then 0 else F (qModW k W' d e)))
      = ∑ p ∈ compatSet, F (qModW k W' p.1 p.2) := by
    rw [← Finset.sum_product']
    conv_rhs => rw [hCS, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : IsCollisionPair p.1 p.2
    · rw [if_pos h, if_neg (not_not_intro h)]
    · rw [if_neg h, if_pos h]
  rw [hstep1]
  -- Step 2: qModW maps compatible pairs into the squarefree range
  have hmaps : ∀ p ∈ compatSet, qModW k W' p.1 p.2 ∈ SF := by
    intro p hp
    rw [hCS] at hp
    obtain ⟨hprod, hpcol⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
    rw [hDm, Finset.mem_filter] at hp1 hp2
    rw [hSF, Finset.mem_filter]
    exact ⟨qModWMemRangeW hp1.1 hp2.1, qModWSquarefreeW hW' hp1.1 hp2.1 hpcol⟩
  -- Step 3: fiber by qModW and count
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => F (qModW k W' p.1 p.2))]
  refine Finset.sum_le_sum (fun q hq => ?_)
  set fiberq := compatSet.filter (fun p => qModW k W' p.1 p.2 = q) with hfib
  have hcongr : ∀ p ∈ fiberq, F (qModW k W' p.1 p.2) = F q :=
    fun p hp => by rw [(Finset.mem_filter.mp hp).2]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul]
  have hcard : fiberq.card ≤ (3 * k) ^ q.primeFactors.card := by
    apply fiberCardLeW (R := R) hW' m q fiberq
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

/-! ## The `R`-uniform disc bound (mirror of
`abs_S2m_sub_compatMain_le_disc_R_uniform`), general `y` under `|y| ≤ 1` -/

/-- **Free-`W'` `R`-uniform disc bound.**  The sharp `λ`-constant `Clam` (from
the free-`W`/free-`y` `lam_abs_le_sharp_uniform`, `R`-free) is pulled out before
`R`; the body is the landed disc-bound proof at modulus `qModW k W' d e`.  Stated
for a general weight `y` with `|y r| ≤ 1` so `yF … Fstar1` slots in later. -/
theorem abs_S2mW_sub_compatMainW_le_disc_R_uniform (k K₀ W' D : ℕ) (hK₀ : 1 ≤ K₀)
    (hW' : Squarefree W') (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D ≤ p)
    (hlt : ∀ i : Fin k, hSeq k i < D) :
    ∃ Clam : ℝ, 0 ≤ Clam ∧ ∀ (R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ), 2 ≤ R →
      (∀ r, |y r| ≤ 1) →
      (∀ h ∈ H k, Nat.Coprime (ν₀ + h) W') →
      ∀ (m : Fin k) (N : ℕ), R ≤ N →
        |S2mW k K₀ N R ν₀ W' m y
            - deltaPi k K₀ N m / (Nat.totient W' : ℝ)
                * s2CompatFormM k R W' m y|
          ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
              * ∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
                  ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
                    (if IsCollisionPair d e then 0
                     else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                          + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)) := by
  classical
  obtain ⟨Clam, hClam1, hClam⟩ := lam_abs_le_sharp_uniform k W'
  refine ⟨Clam, le_trans zero_le_one hClam1, fun R ν₀ y hR hy1 hν₀ m N hRN => ?_⟩
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  set B := Clam * (1 + Real.log R) ^ (k + 1) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hcoef : Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) = B ^ 2 := by
    have he : (2 * k + 2) = (k + 1) * 2 := by omega
    rw [hBdef, mul_pow, ← pow_mul, he]
  rw [hcoef]
  refine le_trans (abs_S2mW_sub_compatMainW_le k K₀ N R ν₀ W' D m y hRN hD hlt) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun d hd => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun e he => ?_)
  by_cases hcol : IsCollisionPair d e
  · rw [if_pos hcol, if_pos hcol, mul_zero]
  · rw [if_neg hcol, if_neg hcol]
    rw [Finset.mem_filter] at hd he
    obtain ⟨hdmem, hdm⟩ := hd
    obtain ⟨hemem, hem⟩ := he
    obtain ⟨hdsq, -, hdcopW, -⟩ := (mem_kSieveIndex_iff d).mp hdmem
    obtain ⟨hesq, -, hecopW, -⟩ := (mem_kSieveIndex_iff e).mp hemem
    have hlcmpos : ∀ i, 0 < Nat.lcm (d i) (e i) := fun i =>
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero (hdsq i).ne_zero (hesq i).ne_zero)
    have hcopW : ∀ i, Nat.Coprime W' (Nat.lcm (d i) (e i)) := fun i =>
      ((hdcopW i).symm.mul_right (hecopW i).symm).coprime_dvd_right
        (Nat.lcm_dvd_mul (d i) (e i))
    have hcoplcm : ∀ i j, i ≠ j →
        Nat.Coprime (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j)) :=
      fun i j hij => lcmPairwiseCoprimeW hdmem hemem hcol hij
    have happrox := s2PrimeCountW_approx' k K₀ N ν₀ W' D m d e hdm hem hW' hD hlt
      hlcmpos hcopW hcoplcm hν₀ hK₀
    simp only [phiLcmProd] at happrox
    set M := maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
      + maxDiscrepancy (N + hSeq k m) (qModW k W' d e) with hMdef
    calc |lam k R W' y d| * |lam k R W' y e|
            * |(s2PrimeCountW k K₀ N ν₀ W' m d e : ℝ)
                - deltaPi k K₀ N m / ((Nat.totient W' : ℝ)
                    * ∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ))|
          ≤ B * B * M := by
            refine mul_le_mul ?_ happrox (abs_nonneg _) (mul_nonneg hBnn hBnn)
            exact mul_le_mul
              (hClam R hR y hy1 d hdmem)
              (hClam R hR y hy1 e hemem)
              (abs_nonneg _) hBnn
      _ = B ^ 2 * M := by ring

end Salt.Maynard
