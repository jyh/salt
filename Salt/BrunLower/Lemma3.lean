/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.BrunLower.Defs
import Salt.BrunLower.Pointwise
import Salt.BrunLower.BlockDecomp
import Salt.BrunLower.WRatio

/-!
# H-R Lemma 3 + Corollary + (2.10): discharging `hcorr` (blueprint `p0`, node B3a′)

Skeleton: the two `hcorr` endpoints, plugged into `mainSum_le/ge_blockForm`.
-/

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace Salt.BrunLower

open BoundingSieve

/-- The "above-`p`" part of `d`: the product of the prime factors of `d` exceeding `p`. -/
noncomputable def pAbove (p d : ℕ) : ℕ := ∏ q ∈ d.primeFactors.filter (fun q => p < q), q

@[simp] lemma pAbove_one (p : ℕ) : pAbove p 1 = 1 := by
  simp [pAbove, Nat.primeFactors_one]

/-- For a set `S` of primes, `pAbove p (∏ S) = ∏ (S.filter (p<·))`. -/
lemma pAbove_prod {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime) (p : ℕ) :
    pAbove p (∏ q ∈ S, q) = ∏ q ∈ S.filter (fun q => p < q), q := by
  unfold pAbove
  rw [Nat.primeFactors_prod hS]

/-- The block indicator `[χ_ν(∏S)]` as a function of the prime set `S`. -/
noncomputable def chiN (Lam z : ℝ) (side b : ℕ) (S : Finset ℕ) : ℝ :=
  if chi Lam z side b (∏ q ∈ S, q) then 1 else 0

/-! ## Layer 2 — the telescoping identity (H-R Lemma 3's `χ(d) = 1 − Σ_{p∣d}{…}`) -/

/-- **The χ-telescoping identity** (H-R Lemma 3, opening line): for any real-valued `F` and
squarefree `d`, summing the boundary brackets `F(pAbove p d) − F(p·pAbove p d)` over the prime
factors `p` of `d` telescopes to `F(1) − F(d)`.  With `F = [χ_ν(·)]` and `F(1) = 1` this becomes
`[χ_ν(d)] = 1 − Σ_{p∣d}{…}`.  Proved by peeling the smallest prime (`q(d)`, all other primes of
`d` exceed it), exactly as H-R order the telescoping. -/
lemma telescope_sum (F : ℕ → ℝ) :
    ∀ d, Squarefree d →
      ∑ p ∈ d.primeFactors, (F (pAbove p d) - F (p * pAbove p d)) = F 1 - F d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro hd
  rcases eq_or_ne d 1 with rfl | hd1
  · simp
  · -- peel the smallest prime `q = q(d)`; every other prime of `d` exceeds it
    set q := d.minFac with hq
    have hq_prime : q.Prime := Nat.minFac_prime hd1
    have hqd : q ∣ d := Nat.minFac_dvd d
    set m := d / q with hm
    have hqm_eq : q * m = d := Nat.mul_div_cancel' hqd
    have hd0 : d ≠ 0 := hd.ne_zero
    have hm0 : m ≠ 0 := by
      intro h; rw [h, mul_zero] at hqm_eq; exact hd0 hqm_eq.symm
    have hmdvd : m ∣ d := ⟨q, by rw [← hqm_eq]; ring⟩
    have hqnm : ¬ q ∣ m := by
      intro hdvd
      have hqq : q * q ∣ d := by rw [← hqm_eq]; exact mul_dvd_mul_left q hdvd
      exact hq_prime.ne_one (Nat.isUnit_iff.mp (hd q hqq))
    have hmsf : Squarefree m := hd.squarefree_of_dvd hmdvd
    have hlt : ∀ r ∈ m.primeFactors, q < r := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrm : r ∣ m := Nat.dvd_of_mem_primeFactors hr
      have hle : q ≤ r := Nat.minFac_le_of_dvd hrp.two_le (hrm.trans hmdvd)
      have hne : r ≠ q := by rintro rfl; exact hqnm hrm
      omega
    have hpf : d.primeFactors = insert q m.primeFactors := by
      rw [← hqm_eq, Nat.primeFactors_mul hq_prime.ne_zero hm0, hq_prime.primeFactors,
        Finset.insert_eq]
    have hqnmpf : q ∉ m.primeFactors := fun h => hqnm (Nat.dvd_of_mem_primeFactors h)
    -- `pAbove q d = m`: dropping `q` from the `>q`-filter leaves all of `m`'s primes
    have hAq : pAbove q d = m := by
      unfold pAbove
      rw [hpf, Finset.filter_insert, if_neg (lt_irrefl q),
        Finset.filter_true_of_mem (fun r hr => hlt r hr),
        Nat.prod_primeFactors_of_squarefree hmsf]
    -- for `p ∈ m.pf` (so `p > q`), the `>p`-filter is unaffected by `q`
    have hApm : ∀ p ∈ m.primeFactors, pAbove p d = pAbove p m := by
      intro p hp
      have hpq : q < p := hlt p hp
      unfold pAbove
      rw [hpf, Finset.filter_insert, if_neg (by omega : ¬ p < q)]
    rw [hpf, Finset.sum_insert hqnmpf, hAq, hqm_eq,
      Finset.sum_congr rfl (fun p hp => by rw [hApm p hp]),
      ih m (Nat.div_lt_self (Nat.pos_of_ne_zero hd0) hq_prime.one_lt) hmsf]
    ring

/-! ## Layer 3 — divisors ↔ subsets of the prime set; Euler products

For squarefree `N`, divisors of `N` correspond to subsets of `N.primeFactors` via `S ↦ ∏_{q∈S}q`.
Working with subsets keeps the reindexing and Euler products purely combinatorial (`Finset`),
matching the target's `powersetCard`/`∏_{p∈T} s.nu p` shape. -/

/-- Reindex a divisor sum over squarefree `N` as a sum over subsets of its prime set. -/
lemma sum_divisors_eq_sum_powerset {N : ℕ} (hN : Squarefree N) (H : ℕ → ℝ) :
    ∑ d ∈ N.divisors, H d = ∑ S ∈ N.primeFactors.powerset, H (∏ q ∈ S, q) := by
  refine Finset.sum_nbij' (fun d => d.primeFactors) (fun S => ∏ q ∈ S, q) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Finset.mem_powerset.mpr (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hd) hN.ne_zero)
  · intro S hS
    rw [Finset.mem_powerset] at hS
    refine Nat.mem_divisors.mpr ⟨?_, hN.ne_zero⟩
    calc (∏ q ∈ S, q) ∣ ∏ q ∈ N.primeFactors, q := Finset.prod_dvd_prod_of_subset _ _ _ hS
      _ = N := Nat.prod_primeFactors_of_squarefree hN
  · intro d hd
    exact Nat.prod_primeFactors_of_squarefree (hN.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
  · intro S hS
    rw [Finset.mem_powerset] at hS
    exact Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))
  · intro d hd
    rw [Nat.prod_primeFactors_of_squarefree (hN.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]

/-- `∏_{q∈S}q` divides `prodPrimes` for `S ⊆ prodPrimes.primeFactors`, hence is squarefree. -/
lemma prod_subset_dvd (s : BoundingSieve) {S : Finset ℕ} (hS : S ⊆ s.prodPrimes.primeFactors) :
    (∏ q ∈ S, q) ∣ s.prodPrimes := by
  rw [← Nat.prod_primeFactors_of_squarefree s.prodPrimes_squarefree]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hS

lemma prod_subset_squarefree (s : BoundingSieve) {S : Finset ℕ}
    (hS : S ⊆ s.prodPrimes.primeFactors) : Squarefree (∏ q ∈ S, q) :=
  s.prodPrimes_squarefree.squarefree_of_dvd (prod_subset_dvd s hS)

/-- `ν(∏_{q∈S}q) = ∏_{q∈S} ν(q)` for `S` a set of sifting primes (multiplicativity). -/
lemma nu_prod_eq (s : BoundingSieve) {S : Finset ℕ} (hS : S ⊆ s.prodPrimes.primeFactors) :
    s.nu (∏ q ∈ S, q) = ∏ q ∈ S, s.nu q :=
  s.nu_mult.map_prod_of_subset_primeFactors _ _ hS

/-- `μ(∏S)·ν(∏S) = ∏_{q∈S}(−ν q)`: the sign of `μ` folded into the density product. -/
lemma moebius_nu_prod_eq (s : BoundingSieve) {S : Finset ℕ}
    (hS : S ⊆ s.prodPrimes.primeFactors) :
    (μ (∏ q ∈ S, q) : ℝ) * s.nu (∏ q ∈ S, q) = ∏ q ∈ S, (- s.nu q) := by
  have hpf : (∏ q ∈ S, q).primeFactors = S :=
    Nat.primeFactors_prod (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))
  rw [moebius_real_of_squarefree (prod_subset_squarefree s hS), hpf, nu_prod_eq s hS]
  rw [show (∏ q ∈ S, (- s.nu q)) = ∏ q ∈ S, ((-1 : ℝ) * s.nu q) from
    Finset.prod_congr rfl (fun q _ => by ring), Finset.prod_mul_distrib, Finset.prod_const]

/-- **The leading Euler term** `Σ_{S⊆P} ∏_{q∈S}(−ν q) = W(z)`. -/
lemma sum_powerset_prod_neg_nu (s : BoundingSieve) :
    ∑ S ∈ s.prodPrimes.primeFactors.powerset, ∏ q ∈ S, (- s.nu q) = W s := by
  rw [← Finset.prod_one_add]
  exact Finset.prod_congr rfl (fun q _ => by ring)

/-! ## Layer 4 — the fixed-prime reindex (H-R's `d = δ·p·t`, powerset form) -/

/-- **Step 4: the fixed-prime reindex** (H-R's `d = δpt` split, `Σ_{δ∣P(p)}μ(δ)ω(δ)/δ = W(p)`).
A summand over `{S ⊆ P : p ∈ S}` whose non-`∏(−ν)` part depends only on the `>p`-slice
`S.filter(p<·)` (captured as `Φ`) factors: the `<p`-slice sums to `W(p) = ∏_{q<p}(1−ν q)`,
leaving the `>p`-sum. -/
lemma reindex_fixed_prime (s : BoundingSieve) {p : ℕ}
    (hp : p ∈ s.prodPrimes.primeFactors) (Φ : Finset ℕ → ℝ) :
    ∑ S ∈ s.prodPrimes.primeFactors.powerset.filter (fun S => p ∈ S),
        (∏ q ∈ S, (- s.nu q)) * Φ (S.filter (fun q => p < q))
      = (- s.nu p) * (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
          * ∑ U ∈ (s.prodPrimes.primeFactors.filter (fun q => p < q)).powerset,
              (∏ q ∈ U, (- s.nu q)) * Φ U := by
  classical
  set P := s.prodPrimes.primeFactors with hP
  set Plt := P.filter (fun q => q < p) with hPlt
  set Pgt := P.filter (fun q => p < q) with hPgt
  have key : ∑ S ∈ P.powerset.filter (fun S => p ∈ S),
        (∏ q ∈ S, (- s.nu q)) * Φ (S.filter (fun q => p < q))
      = ∑ AU ∈ Plt.powerset ×ˢ Pgt.powerset,
          (- s.nu p) * ((∏ q ∈ AU.1, (- s.nu q)) * ((∏ q ∈ AU.2, (- s.nu q)) * Φ AU.2)) := by
    refine Finset.sum_nbij'
      (fun S => (S.filter (fun q => q < p), S.filter (fun q => p < q)))
      (fun AU => insert p (AU.1 ∪ AU.2)) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hS.1 hx.1, hx.2⟩
      · intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hS.1 hx.1, hx.2⟩
    · intro AU hAU
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hAU
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, Finset.mem_insert_self _ _⟩
      intro x hx
      rw [Finset.mem_insert, Finset.mem_union] at hx
      rcases hx with rfl | hx | hx
      · exact hp
      · exact (Finset.mem_filter.mp (hAU.1 hx)).1
      · exact (Finset.mem_filter.mp (hAU.2 hx)).1
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      ext x
      rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      constructor
      · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
        · exact hS.2
        · exact hx
        · exact hx
      · intro hx
        rcases lt_trichotomy x p with h | h | h
        · exact Or.inr (Or.inl ⟨hx, h⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inr ⟨hx, h⟩)
    · intro AU hAU
      rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hAU
      ext1
      · ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ⟨rfl | hx | hx, hlt⟩
          · omega
          · exact hx
          · exact absurd (Finset.mem_filter.mp (hAU.2 hx)).2 (by omega)
        · intro hx
          exact ⟨Or.inr (Or.inl hx), (Finset.mem_filter.mp (hAU.1 hx)).2⟩
      · ext x
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
        constructor
        · rintro ⟨rfl | hx | hx, hlt⟩
          · omega
          · exact absurd (Finset.mem_filter.mp (hAU.1 hx)).2 (by omega)
          · exact hx
        · intro hx
          exact ⟨Or.inr (Or.inr hx), (Finset.mem_filter.mp (hAU.2 hx)).2⟩
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      have hrec : insert p (S.filter (fun q => q < p) ∪ S.filter (fun q => p < q)) = S := by
        ext x
        rw [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        constructor
        · rintro (rfl | ⟨hx, _⟩ | ⟨hx, _⟩)
          · exact hS.2
          · exact hx
          · exact hx
        · intro hx
          rcases lt_trichotomy x p with h | h | h
          · exact Or.inr (Or.inl ⟨hx, h⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨hx, h⟩)
      have hpA : p ∉ S.filter (fun q => q < p) := fun h =>
        (by omega : ¬ p < p) (Finset.mem_filter.mp h).2
      have hpU : p ∉ S.filter (fun q => p < q) := fun h =>
        (by omega : ¬ p < p) (Finset.mem_filter.mp h).2
      have hdisjAU : Disjoint (S.filter (fun q => q < p)) (S.filter (fun q => p < q)) := by
        rw [Finset.disjoint_left]; intro x hx hx'
        rw [Finset.mem_filter] at hx hx'; omega
      calc (∏ q ∈ S, (- s.nu q)) * Φ (S.filter (fun q => p < q))
          = (∏ q ∈ insert p (S.filter (fun q => q < p) ∪ S.filter (fun q => p < q)), (- s.nu q))
              * Φ (S.filter (fun q => p < q)) := by rw [hrec]
        _ = (- s.nu p) * ((∏ q ∈ S.filter (fun q => q < p), (- s.nu q))
              * ((∏ q ∈ S.filter (fun q => p < q), (- s.nu q))
                  * Φ (S.filter (fun q => p < q)))) := by
            rw [Finset.prod_insert (by rw [Finset.mem_union]; exact fun h => h.elim hpA hpU),
              Finset.prod_union hdisjAU]; ring
  rw [key, Finset.sum_product]
  have hEuler : (∏ q ∈ Plt, (1 - s.nu q)) = ∑ x ∈ Plt.powerset, ∏ q ∈ x, (- s.nu q) := by
    rw [← Finset.prod_one_add]; exact Finset.prod_congr rfl (fun q _ => by ring)
  rw [hEuler, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [Finset.mul_sum]

/-! ## Layer 5 — the peel identity, telescoping in set form, and the powerset main sum -/

/-- The peel IDENTITY (B2's `peel_term_nonneg`, sharpened to equality): for `t` squarefree
with all primes exceeding `p`, `(−1)^{ν−1}·μ(t)([χt]−[χpt]) = [χt](1−[χpt])`. -/
lemma peel_term_eq {Lam z : ℝ} {b side : ℕ} (hside : side = 1 ∨ side = 2)
    {p t : ℕ} (hp : p.Prime) (ht : Squarefree t)
    (hlt : ∀ q ∈ t.primeFactors, p < q) :
    (-1 : ℝ) ^ (side - 1) *
        ((μ t : ℝ) * ((if chi Lam z side b t then (1 : ℝ) else 0)
                      - (if chi Lam z side b (p * t) then (1 : ℝ) else 0)))
      = (if chi Lam z side b t then (1 : ℝ) else 0)
          * (1 - (if chi Lam z side b (p * t) then (1 : ℝ) else 0)) := by
  by_cases hC : chi Lam z side b (p * t)
  · have hpt0 : p * t ≠ 0 := Nat.mul_ne_zero hp.ne_zero ht.ne_zero
    have hA : chi Lam z side b t := chi_dvd_closed Lam z hpt0 (dvd_mul_left t p) hC
    rw [if_pos hA, if_pos hC]; ring
  · rw [if_neg hC]
    by_cases hA : chi Lam z side b t
    · rw [if_pos hA]
      have hpar_ne : ¬ (t.primeFactors.card % 2 = side % 2) := fun hpar =>
        hC (chi_add_smaller_prime Lam z hp ht.ne_zero hlt hpar hA)
      have hmu : (μ t : ℝ) = (-1 : ℝ) ^ t.primeFactors.card := moebius_real_of_squarefree ht
      have hsign : (μ t : ℝ) = (-1 : ℝ) ^ (side - 1) := by
        rcases hside with rfl | rfl
        · rw [hmu, (Nat.even_iff.mpr (by omega : t.primeFactors.card % 2 = 0)).neg_one_pow]
          norm_num
        · rw [hmu, (Nat.odd_iff.mpr (by omega : t.primeFactors.card % 2 = 1)).neg_one_pow]
          norm_num
      rw [hsign]
      rcases hside with rfl | rfl <;> norm_num
    · rw [if_neg hA]; ring

/-- The telescoping identity in prime-set form: `[χ_ν(∏S)] = 1 − Σ_{p∈S}{…}`. -/
lemma chiN_telescope (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b) (hs : side ≤ 2)
    {S : Finset ℕ} (hS : S ⊆ s.prodPrimes.primeFactors) :
    chiN Lam z side b S
      = 1 - ∑ p ∈ S, (chiN Lam z side b (S.filter (fun q => p < q))
                        - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) := by
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (hS hq)
  have hsf : Squarefree (∏ q ∈ S, q) := prod_subset_squarefree s hS
  have htel := telescope_sum (fun d => if chi Lam z side b d then (1 : ℝ) else 0) _ hsf
  rw [Nat.primeFactors_prod hSp] at htel
  have hFone : (if chi Lam z side b 1 then (1 : ℝ) else 0) = 1 :=
    if_pos (chi_one Lam z hb hs)
  have hcongr : ∀ p ∈ S,
      ((if chi Lam z side b (pAbove p (∏ q ∈ S, q)) then (1 : ℝ) else 0)
        - (if chi Lam z side b (p * pAbove p (∏ q ∈ S, q)) then (1 : ℝ) else 0))
      = (chiN Lam z side b (S.filter (fun q => p < q))
          - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) := by
    intro p hp
    have hpnotmem : p ∉ S.filter (fun q => p < q) := fun h =>
      (by omega : ¬ p < p) (Finset.mem_filter.mp h).2
    simp only [chiN]
    rw [pAbove_prod hSp p, Finset.prod_insert hpnotmem]
  rw [Finset.sum_congr rfl hcongr] at htel
  simp only [hFone] at htel
  have hFprod : (if chi Lam z side b (∏ q ∈ S, q) then (1 : ℝ) else 0) = chiN Lam z side b S := rfl
  rw [hFprod] at htel
  linarith [htel]

/-- `mainSum(μ·[χ_ν])` in prime-set (`H-R (2.7)`) form: `Σ_{S⊆P} ∏_{q∈S}(−ν q)·[χ_ν(∏S)]`. -/
lemma mainSum_eq_powerset (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ} :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0))
      = ∑ S ∈ s.prodPrimes.primeFactors.powerset,
          (∏ q ∈ S, (- s.nu q)) * chiN Lam z side b S := by
  unfold BoundingSieve.mainSum
  rw [sum_divisors_eq_sum_powerset s.prodPrimes_squarefree
    (fun d => (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0) * s.nu d)]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.mem_powerset] at hS
  simp only [chiN]
  rw [show (μ (∏ q ∈ S, q) : ℝ) * (if chi Lam z side b (∏ q ∈ S, q) then (1 : ℝ) else 0)
        * s.nu (∏ q ∈ S, q)
      = ((μ (∏ q ∈ S, q) : ℝ) * s.nu (∏ q ∈ S, q))
        * (if chi Lam z side b (∏ q ∈ S, q) then (1 : ℝ) else 0) by ring,
    moebius_nu_prod_eq s hS]

/-! ## Layer 6 — the signed master identity (H-R Lemma 3 + the peel sign) -/

/-- The nonnegative inner block sum `Σ_{U ⊆ (>p)} ∏_{q∈U} ν(q)·[χ_ν(∏U)]·(1−[χ_ν(p∏U)])` —
H-R's `Σ_{t∣P(p⁺,z)} χ_ν(t){1−χ_ν(pt)} ω(t)/t`, in prime-set form. -/
noncomputable def blockInner (s : BoundingSieve) (Lam z : ℝ) (side b p : ℕ) : ℝ :=
  ∑ U ∈ (s.prodPrimes.primeFactors.filter (fun q => p < q)).powerset,
    (∏ q ∈ U, s.nu q) * chiN Lam z side b U * (1 - chiN Lam z side b (insert p U))

/-- The peel sign, summed: `Σ_U ∏_U(−ν)([χ∏U]−[χp∏U]) = (−1)^{ν−1}·blockInner`. -/
lemma Bsum_sign (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ} (hside : side = 1 ∨ side = 2)
    {p : ℕ} (hp : p ∈ s.prodPrimes.primeFactors) :
    ∑ U ∈ (s.prodPrimes.primeFactors.filter (fun q => p < q)).powerset,
        (∏ q ∈ U, (- s.nu q)) * (chiN Lam z side b U - chiN Lam z side b (insert p U))
      = (-1 : ℝ) ^ (side - 1) * blockInner s Lam z side b p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  unfold blockInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  rw [Finset.mem_powerset] at hU
  have hUP : U ⊆ s.prodPrimes.primeFactors := hU.trans (Finset.filter_subset _ _)
  have hUp : ∀ q ∈ U, p < q := fun q hq => (Finset.mem_filter.mp (hU hq)).2
  have hUprime : ∀ q ∈ U, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (hUP hq)
  have ht : Squarefree (∏ q ∈ U, q) := prod_subset_squarefree s hUP
  have hpf : (∏ q ∈ U, q).primeFactors = U := Nat.primeFactors_prod hUprime
  have hlt : ∀ q ∈ (∏ q ∈ U, q).primeFactors, p < q := by rw [hpf]; exact hUp
  have hpnU : p ∉ U := fun h => (lt_irrefl p) (hUp p h)
  have hchiU : chiN Lam z side b U = (if chi Lam z side b (∏ q ∈ U, q) then (1 : ℝ) else 0) := rfl
  have hchiins : chiN Lam z side b (insert p U)
      = (if chi Lam z side b (p * ∏ q ∈ U, q) then (1 : ℝ) else 0) := by
    simp only [chiN, Finset.prod_insert hpnU]
  rw [hchiU, hchiins, ← moebius_nu_prod_eq s hUP, ← nu_prod_eq s hUP]
  have hpe := peel_term_eq (Lam := Lam) (z := z) (b := b) hside hpp ht hlt
  rcases hside with rfl | rfl
  · simp only [Nat.sub_self, pow_zero, one_mul] at hpe ⊢
    linear_combination (s.nu (∏ q ∈ U, q)) * hpe
  · rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hpe ⊢
    linear_combination (- s.nu (∏ q ∈ U, q)) * hpe

/-- **H-R Lemma 3 (signed master identity)**: `mainSum(μ[χ_ν]) = W(z) + (−1)^{ν−1}·Σ_{p<z}
ν(p)·W(p)·blockInner(p)`, with each `blockInner(p) ≥ 0`.  This is the exact Lemma 3, the peel
sign folded in. -/
lemma master_signed (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ}
    (hb : 1 ≤ b) (hside : side = 1 ∨ side = 2) :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z side b d then (1 : ℝ) else 0))
      = W s + (-1 : ℝ) ^ (side - 1) * ∑ p ∈ s.prodPrimes.primeFactors,
          s.nu p * (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
            * blockInner s Lam z side b p := by
  classical
  set P := s.prodPrimes.primeFactors with hP
  have hs2 : side ≤ 2 := by rcases hside with rfl | rfl <;> norm_num
  rw [mainSum_eq_powerset s]
  -- substitute the telescope into each chiN
  have hsub : ∀ S ∈ P.powerset, (∏ q ∈ S, (- s.nu q)) * chiN Lam z side b S
      = (∏ q ∈ S, (- s.nu q))
        - ∑ p ∈ S, (∏ q ∈ S, (- s.nu q))
            * (chiN Lam z side b (S.filter (fun q => p < q))
                - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    rw [chiN_telescope s hb hs2 hS, mul_sub, mul_one, Finset.mul_sum]
  rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib, sum_powerset_prod_neg_nu s]
  -- swap the (S, p∈S) sum, then reindex each p
  have hswap : ∑ S ∈ P.powerset, ∑ p ∈ S, (∏ q ∈ S, (- s.nu q))
        * (chiN Lam z side b (S.filter (fun q => p < q))
            - chiN Lam z side b (insert p (S.filter (fun q => p < q))))
      = ∑ p ∈ P, ∑ S ∈ P.powerset.filter (fun S => p ∈ S), (∏ q ∈ S, (- s.nu q))
          * (chiN Lam z side b (S.filter (fun q => p < q))
              - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) := by
    calc ∑ S ∈ P.powerset, ∑ p ∈ S, (∏ q ∈ S, (- s.nu q))
            * (chiN Lam z side b (S.filter (fun q => p < q))
                - chiN Lam z side b (insert p (S.filter (fun q => p < q))))
        = ∑ S ∈ P.powerset, ∑ p ∈ P, (if p ∈ S then (∏ q ∈ S, (- s.nu q))
            * (chiN Lam z side b (S.filter (fun q => p < q))
                - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) else 0) := by
          apply Finset.sum_congr rfl; intro S hS
          rw [Finset.mem_powerset] at hS
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]
      _ = ∑ p ∈ P, ∑ S ∈ P.powerset, (if p ∈ S then (∏ q ∈ S, (- s.nu q))
            * (chiN Lam z side b (S.filter (fun q => p < q))
                - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) else 0) :=
          Finset.sum_comm
      _ = ∑ p ∈ P, ∑ S ∈ P.powerset.filter (fun S => p ∈ S), (∏ q ∈ S, (- s.nu q))
            * (chiN Lam z side b (S.filter (fun q => p < q))
                - chiN Lam z side b (insert p (S.filter (fun q => p < q)))) := by
          apply Finset.sum_congr rfl; intro p _; rw [Finset.sum_filter]
  have hSS : ∑ S ∈ P.powerset, ∑ p ∈ S, (∏ q ∈ S, (- s.nu q))
        * (chiN Lam z side b (S.filter (fun q => p < q))
            - chiN Lam z side b (insert p (S.filter (fun q => p < q))))
      = ∑ p ∈ P, (- s.nu p)
          * (∏ q ∈ P.filter (fun q => q < p), (1 - s.nu q))
          * ((-1 : ℝ) ^ (side - 1) * blockInner s Lam z side b p) := by
    rw [hswap]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [hP] at hp ⊢
    rw [reindex_fixed_prime s hp (fun U => chiN Lam z side b U - chiN Lam z side b (insert p U)),
      Bsum_sign s hside hp]
  have heq : ∑ p ∈ P, (- s.nu p) * (∏ q ∈ P.filter (fun q => q < p), (1 - s.nu q))
          * ((-1 : ℝ) ^ (side - 1) * blockInner s Lam z side b p)
      = - ∑ p ∈ P, (-1 : ℝ) ^ (side - 1)
          * (s.nu p * (∏ q ∈ P.filter (fun q => q < p), (1 - s.nu q))
              * blockInner s Lam z side b p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro p _; ring
  rw [hSS, heq, Finset.mul_sum]
  ring

/-! ## Layer 7 — the (2.10) forcing -/

/-- `bigOmegaGe` of a product of primes = the count of those primes in the window `[z_m, ∞)`. -/
lemma bigOmegaGe_prod {Lam z : ℝ} {S : Finset ℕ} (hSp : ∀ q ∈ S, q.Prime) (m : ℕ) :
    bigOmegaGe Lam z m (∏ q ∈ S, q) = (S.filter (fun q : ℕ => zLev Lam z m ≤ (q : ℝ))).card := by
  unfold bigOmegaGe
  rw [Nat.primeFactors_prod hSp]

lemma blockBound_mono {side b : ℕ} {n n' : ℕ} (h : n ≤ n') :
    blockBound side b n ≤ blockBound side b n' := by
  unfold blockBound; omega

/-- **The (2.10) forcing** (H-R p.103): if `[χ_ν(∏U)]=1` but `[χ_ν(p∏U)]=0`, with `p` the
smallest prime and `z_n ≤ p < z_{n-1}`, then `Ω(p∏U) = 2b−ν+2n` (i.e. `|insert p U| = k_n`). -/
lemma forcing {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b) (hs : side ≤ 2)
    {p : ℕ} (hp : p.Prime) {U : Finset ℕ} {n : ℕ} (hn : 1 ≤ n)
    (hUprime : ∀ q ∈ U, q.Prime) (hUp : ∀ q ∈ U, p < q)
    (hLam : 0 ≤ Lam) (hz : 1 ≤ z)
    (hpzn : zLev Lam z n ≤ (p : ℝ)) (hpzn1 : (p : ℝ) < zLev Lam z (n - 1))
    (hchiU : chi Lam z side b (∏ q ∈ U, q))
    (hnotchi : ¬ chi Lam z side b (∏ q ∈ insert p U, q)) :
    (insert p U).card = 2 * b - side + 2 * n := by
  have hpnU : p ∉ U := fun h => (lt_irrefl p) (hUp p h)
  have hins_prime : ∀ q ∈ insert p U, q.Prime := by
    intro q hq; rw [Finset.mem_insert] at hq; rcases hq with rfl | hq
    · exact hp
    · exact hUprime q hq
  -- all primes of `insert p U` are `≥ p ≥ z_m` for `m ≥ n`, so they all count at level `m ≥ n`
  have hall_ge : ∀ q ∈ insert p U, (p : ℝ) ≤ (q : ℝ) := by
    intro q hq; rw [Finset.mem_insert] at hq; rcases hq with rfl | hq
    · exact le_refl _
    · exact (by exact_mod_cast (hUp q hq).le : (p : ℝ) ≤ (q : ℝ))
  -- filter at level `m ≥ n` keeps everything
  have hfilter_all : ∀ m, n ≤ m →
      (insert p U).filter (fun q : ℕ => zLev Lam z m ≤ (q : ℝ)) = insert p U := by
    intro m hm
    apply Finset.filter_true_of_mem
    intro q hq
    have h1 : zLev Lam z m ≤ zLev Lam z n := zLev_antitone hLam hz hm
    exact le_trans h1 (le_trans hpzn (hall_ge q hq))
  have hUfilter_all : ∀ m, n ≤ m → U.filter (fun q : ℕ => zLev Lam z m ≤ (q : ℝ)) = U := by
    intro m hm
    apply Finset.filter_true_of_mem
    intro q hq
    have h1 : zLev Lam z m ≤ zLev Lam z n := zLev_antitone hLam hz hm
    exact le_trans h1 (le_trans hpzn (hall_ge q (Finset.mem_insert_of_mem hq)))
  -- (A) upper bound |U| ≤ blockBound n, from χ(∏U) at level n
  have hA : (U.card : ℤ) ≤ blockBound side b n := by
    have h := hchiU n hn
    rw [bigOmegaGe_prod hUprime n, hUfilter_all n (le_refl n)] at h
    exact h
  -- (B) lower bound: extract the violating level m ≥ n
  unfold chi at hnotchi
  simp only [not_forall, not_le, exists_prop] at hnotchi
  obtain ⟨m, hm1, hmviol⟩ := hnotchi
  rw [bigOmegaGe_prod hins_prime m] at hmviol
  -- the violation cannot be at m < n (there `insert p U` and `U` agree)
  have hmn : n ≤ m := by
    by_contra hlt
    rw [not_le] at hlt  -- m < n
    -- p does not count at level m < n: z_m ≥ z_{n-1} > p
    have hpnotcount : ¬ zLev Lam z m ≤ (p : ℝ) := by
      have hle : zLev Lam z (n - 1) ≤ zLev Lam z m := zLev_antitone hLam hz (by omega)
      linarith
    have hfeq : (insert p U).filter (fun q : ℕ => zLev Lam z m ≤ (q : ℝ))
        = U.filter (fun q : ℕ => zLev Lam z m ≤ (q : ℝ)) := by
      rw [Finset.filter_insert, if_neg hpnotcount]
    rw [hfeq] at hmviol
    have hchi := hchiU m hm1
    rw [bigOmegaGe_prod hUprime m] at hchi
    omega
  -- at m ≥ n, |insert p U| = |U| + 1 counts fully, and blockBound n ≤ blockBound m < |insert p U|
  rw [hfilter_all m hmn] at hmviol
  have hcardins : (insert p U).card = U.card + 1 := Finset.card_insert_of_notMem hpnU
  have hmono : blockBound side b n ≤ blockBound side b m := blockBound_mono hmn
  -- conclude |U| = blockBound n, hence |insert p U| = 2b - side + 2n
  have hbb : blockBound side b n = 2 * (b : ℤ) - side + 2 * n - 1 := rfl
  rw [hcardins]
  rw [hcardins] at hmviol
  omega

/-! ## Layer 8 — the over-count (Corollary + (2.11)) -/

theorem windowPrimes_subset (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) :
    windowPrimes s Lam z n ⊆ s.prodPrimes.primeFactors := Finset.filter_subset _ _

/-- **The over-count** (H-R Corollary + (2.11)): the block sum `Σ_{p∈blk} ν(p)·blockInner(p)`,
each surviving `(p,U)` mapping to the prime set `T = {p}∪U ⊆ window_n` of size `k = 2b−ν+2n`,
is bounded by the full `k`-th elementary symmetric family over `window_n`. -/
lemma overcount (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ} (hb : 1 ≤ b) (hs : side ≤ 2)
    (hLam : 0 ≤ Lam) (hz1 : 1 ≤ z) {n : ℕ} (hn : 1 ≤ n) (blk : Finset ℕ)
    (hblkP : blk ⊆ s.prodPrimes.primeFactors)
    (hblk : ∀ p ∈ blk, zLev Lam z n ≤ (p : ℝ) ∧ (p : ℝ) < zLev Lam z (n - 1)) :
    ∑ p ∈ blk, s.nu p * blockInner s Lam z side b p
      ≤ ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - side + 2 * n), ∏ q ∈ T, s.nu q := by
  classical
  set P := s.prodPrimes.primeFactors with hP
  -- flatten the double sum over pairs (p, U)
  set D := blk.sigma (fun p => (P.filter (fun q => p < q)).powerset) with hD
  set w : (Σ _ : ℕ, Finset ℕ) → ℝ := fun x =>
    s.nu x.1 * (∏ q ∈ x.2, s.nu q) * chiN Lam z side b x.2
      * (1 - chiN Lam z side b (insert x.1 x.2)) with hw
  have hflat : ∑ p ∈ blk, s.nu p * blockInner s Lam z side b p = ∑ x ∈ D, w x := by
    rw [hD, Finset.sum_sigma]
    apply Finset.sum_congr rfl; intro p _
    unfold blockInner
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro U _; simp only [hw]; ring
  rw [hflat]
  -- restrict to surviving pairs; off them w = 0
  set ψ : (Σ _ : ℕ, Finset ℕ) → Finset ℕ := fun x => insert x.1 x.2 with hψ
  have hDsurv : ∀ x ∈ D, w x = if (chi Lam z side b (∏ q ∈ x.2, q)
      ∧ ¬ chi Lam z side b (∏ q ∈ insert x.1 x.2, q)) then (∏ q ∈ ψ x, s.nu q) else 0 := by
    intro x hx
    rw [hD, Finset.mem_sigma, Finset.mem_powerset] at hx
    have hUP : x.2 ⊆ P := hx.2.trans (Finset.filter_subset _ _)
    have hUp : ∀ q ∈ x.2, x.1 < q := fun q hq => (Finset.mem_filter.mp (hx.2 hq)).2
    have hpnU : x.1 ∉ x.2 := fun h => (lt_irrefl x.1) (hUp x.1 h)
    have hchiU : chiN Lam z side b x.2 = if chi Lam z side b (∏ q ∈ x.2, q) then (1:ℝ) else 0 := rfl
    have hchiins : chiN Lam z side b (insert x.1 x.2)
        = if chi Lam z side b (∏ q ∈ insert x.1 x.2, q) then (1:ℝ) else 0 := rfl
    have hnu : (∏ q ∈ ψ x, s.nu q) = s.nu x.1 * ∏ q ∈ x.2, s.nu q := by
      rw [hψ, Finset.prod_insert hpnU]
    have hind : chiN Lam z side b x.2 * (1 - chiN Lam z side b (insert x.1 x.2))
        = if (chi Lam z side b (∏ q ∈ x.2, q)
              ∧ ¬ chi Lam z side b (∏ q ∈ insert x.1 x.2, q)) then (1 : ℝ) else 0 := by
      simp only [chiN]
      by_cases h1 : chi Lam z side b (∏ q ∈ x.2, q) <;>
        by_cases h2 : chi Lam z side b (∏ q ∈ insert x.1 x.2, q) <;> simp [h1, h2]
    simp only [hw]
    rw [show s.nu x.1 * (∏ q ∈ x.2, s.nu q) * chiN Lam z side b x.2
            * (1 - chiN Lam z side b (insert x.1 x.2))
          = (s.nu x.1 * ∏ q ∈ x.2, s.nu q)
            * (chiN Lam z side b x.2 * (1 - chiN Lam z side b (insert x.1 x.2))) by ring,
      hind, ← hnu, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hDsurv]
  rw [← Finset.sum_filter]
  -- ψ is injective on the surviving set and lands in the powersetCard family
  set Dsurv := D.filter (fun x => chi Lam z side b (∏ q ∈ x.2, q)
      ∧ ¬ chi Lam z side b (∏ q ∈ insert x.1 x.2, q)) with hDsurvdef
  have hmem : ∀ x ∈ Dsurv, x.1.Prime ∧ x.2 ⊆ P ∧ (∀ q ∈ x.2, x.1 < q) := by
    intro x hx
    rw [hDsurvdef, Finset.mem_filter, hD, Finset.mem_sigma, Finset.mem_powerset] at hx
    have hUP : x.2 ⊆ P := hx.1.2.trans (Finset.filter_subset _ _)
    exact ⟨Nat.prime_of_mem_primeFactors (hblkP hx.1.1), hUP,
      fun q hq => (Finset.mem_filter.mp (hx.1.2 hq)).2⟩
  have hinj : Set.InjOn ψ Dsurv := by
    intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    simp only [hψ] at hxy
    obtain ⟨_, hxU, hxUp⟩ := hmem x hx
    obtain ⟨_, hyU, hyUp⟩ := hmem y hy
    have hpx : ∀ r ∈ insert x.1 x.2, x.1 ≤ r := by
      intro r hr; rw [Finset.mem_insert] at hr
      rcases hr with rfl | hr
      · exact le_refl _
      · exact (hxUp r hr).le
    have hpy : ∀ r ∈ insert y.1 y.2, y.1 ≤ r := by
      intro r hr; rw [Finset.mem_insert] at hr
      rcases hr with rfl | hr
      · exact le_refl _
      · exact (hyUp r hr).le
    have hpxnU : x.1 ∉ x.2 := fun h => (lt_irrefl x.1) (hxUp x.1 h)
    have hpynU : y.1 ∉ y.2 := fun h => (lt_irrefl y.1) (hyUp y.1 h)
    have hp1 : x.1 = y.1 := by
      have hx1 : x.1 ∈ insert y.1 y.2 := hxy ▸ Finset.mem_insert_self x.1 x.2
      have hy1 : y.1 ∈ insert x.1 x.2 := hxy.symm ▸ Finset.mem_insert_self y.1 y.2
      exact le_antisymm (hpx y.1 hy1) (hpy x.1 hx1)
    have hU : x.2 = y.2 := by
      have he : (insert x.1 x.2).erase x.1 = (insert y.1 y.2).erase y.1 := by rw [hxy, hp1]
      rw [Finset.erase_insert hpxnU, Finset.erase_insert hpynU] at he
      exact he
    obtain ⟨x1, x2⟩ := x
    obtain ⟨y1, y2⟩ := y
    simp only at hp1 hU
    subst hp1; subst hU; rfl
  have himage : ∀ x ∈ Dsurv,
      ψ x ∈ (windowPrimes s Lam z n).powersetCard (2 * b - side + 2 * n) := by
    intro x hx
    rw [hDsurvdef, Finset.mem_filter] at hx
    obtain ⟨hxD, hchi, hnotchi⟩ := hx
    obtain ⟨hxp, hxU, hxUp⟩ := hmem x (Finset.mem_filter.mpr ⟨hxD, hchi, hnotchi⟩)
    have hblkx : zLev Lam z n ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) < zLev Lam z (n - 1) := by
      have hx1blk : x.1 ∈ blk := by
        rw [hD, Finset.mem_sigma] at hxD; exact hxD.1
      exact hblk x.1 hx1blk
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · -- ψ x ⊆ windowPrimes
      intro r hr
      rw [hψ, Finset.mem_insert] at hr
      rw [windowPrimes, Finset.mem_filter]
      rcases hr with rfl | hr
      · exact ⟨hblkP (by rw [hD, Finset.mem_sigma] at hxD; exact hxD.1), hblkx.1⟩
      · refine ⟨hxU hr, ?_⟩
        have : (x.1 : ℝ) < (r : ℝ) := by exact_mod_cast hxUp r hr
        linarith [hblkx.1]
    · -- card via forcing
      have hUprime : ∀ q ∈ x.2, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (hxU hq)
      exact forcing hb hs hxp hn hUprime hxUp hLam hz1 hblkx.1 hblkx.2 hchi hnotchi
  -- put it together
  have hsumimg : ∑ T ∈ Dsurv.image ψ, ∏ q ∈ T, s.nu q = ∑ x ∈ Dsurv, ∏ q ∈ ψ x, s.nu q :=
    Finset.sum_image (fun x hx y hy h =>
      hinj (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) h)
  calc ∑ x ∈ Dsurv, (∏ q ∈ ψ x, s.nu q)
      = ∑ T ∈ Dsurv.image ψ, ∏ q ∈ T, s.nu q := hsumimg.symm
    _ ≤ ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - side + 2 * n), ∏ q ∈ T, s.nu q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro T hT
          rw [Finset.mem_image] at hT
          obtain ⟨x, hx, rfl⟩ := hT
          exact himage x hx
        · intro T hT _
          rw [Finset.mem_powersetCard] at hT
          exact Finset.prod_nonneg (fun q hq =>
            nu_nonneg_of_mem_primeFactors s (windowPrimes_subset s Lam z n (hT.1 hq)))

/-! ## Layer 9 — block grouping and the density-ratio (W antitone) -/

/-- The block index of a sifting prime `p`: the least level `n ≥ 1` with `z_n ≤ p`. -/
noncomputable def blockOf (Lam z : ℝ) (p : ℕ) : ℕ := sInf {n : ℕ | 1 ≤ n ∧ zLev Lam z n ≤ (p : ℝ)}

lemma blockOf_set_nonempty {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) {p : ℕ} (hp2 : (2 : ℝ) ≤ p) :
    {n : ℕ | 1 ≤ n ∧ zLev Lam z n ≤ (p : ℝ)}.Nonempty :=
  ⟨minLevel Lam z, (minLevel_mem hLam hz).1, le_trans (zLev_minLevel_le_two hLam hz) hp2⟩

lemma blockOf_mem {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) {p : ℕ} (hp2 : (2 : ℝ) ≤ p) :
    1 ≤ blockOf Lam z p ∧ zLev Lam z (blockOf Lam z p) ≤ (p : ℝ) :=
  Nat.sInf_mem (blockOf_set_nonempty hLam hz hp2)

lemma blockOf_le_minLevel {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) {p : ℕ} (hp2 : (2 : ℝ) ≤ p) :
    blockOf Lam z p ≤ minLevel Lam z :=
  Nat.sInf_le ⟨(minLevel_mem hLam hz).1, le_trans (zLev_minLevel_le_two hLam hz) hp2⟩

lemma blockOf_pred {Lam z : ℝ} (hLam : 0 < Lam) (hz : 1 < z) {p : ℕ} (hp2 : (2 : ℝ) ≤ p)
    (hpz : (p : ℝ) < z) : (p : ℝ) < zLev Lam z (blockOf Lam z p - 1) := by
  set k := blockOf Lam z p with hk
  have hk1 : 1 ≤ k := (blockOf_mem hLam hz hp2).1
  rcases eq_or_lt_of_le hk1 with h1 | h1
  · -- k = 1, so k - 1 = 0, z_0 = z
    rw [← h1]
    simp only [Nat.sub_self]
    rwa [zLev_zero Lam z (by linarith)]
  · -- k ≥ 2, so k - 1 ≥ 1 is not in the set, hence z_{k-1} > p
    have hnotmem : (k - 1) ∉ {n : ℕ | 1 ≤ n ∧ zLev Lam z n ≤ (p : ℝ)} := by
      intro hmem
      have hle : k ≤ k - 1 := Nat.sInf_le hmem
      omega
    simp only [Set.mem_setOf_eq, not_and, not_le] at hnotmem
    exact hnotmem (by omega)

/-- Each summand of `blockInner` is nonnegative, hence `blockInner ≥ 0`. -/
lemma blockInner_nonneg (s : BoundingSieve) {Lam z : ℝ} {side b p : ℕ} :
    0 ≤ blockInner s Lam z side b p := by
  unfold blockInner
  apply Finset.sum_nonneg
  intro U hU
  rw [Finset.mem_powerset] at hU
  have hchiU : (0 : ℝ) ≤ chiN Lam z side b U := by unfold chiN; split <;> norm_num
  have hchiins : chiN Lam z side b (insert p U) ≤ 1 := by unfold chiN; split <;> norm_num
  have hprod : (0 : ℝ) ≤ ∏ q ∈ U, s.nu q := by
    apply Finset.prod_nonneg
    intro q hq
    exact nu_nonneg_of_mem_primeFactors s
      ((Finset.filter_subset _ _) (hU hq))
  have : (0 : ℝ) ≤ 1 - chiN Lam z side b (insert p U) := by linarith
  positivity

/-! ## W below a threshold -/

/-- `W(x) = ∏_{p < x}(1 − ν p)`, the density product below a real threshold. -/
noncomputable def Wbelow (s : BoundingSieve) (x : ℝ) : ℝ :=
  ∏ q ∈ s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < x), (1 - s.nu q)

lemma Wbelow_nonneg (s : BoundingSieve) (x : ℝ) : 0 ≤ Wbelow s x := by
  unfold Wbelow
  apply Finset.prod_nonneg
  intro q hq
  have := nu_nonneg_of_mem_primeFactors s ((Finset.filter_subset _ _) hq)
  have hlt := s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors ((Finset.filter_subset _ _) hq))
    (Nat.dvd_of_mem_primeFactors ((Finset.filter_subset _ _) hq))
  linarith

/-- `W` decreases as the threshold increases (more factors in `(0,1)`). -/
lemma Wbelow_anti (s : BoundingSieve) {x y : ℝ} (hxy : x ≤ y) : Wbelow s y ≤ Wbelow s x := by
  unfold Wbelow
  have hAB : s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < x)
      ⊆ s.prodPrimes.primeFactors.filter (fun q : ℕ => (q : ℝ) < y) := by
    intro q hq; rw [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, lt_of_lt_of_le hq.2 hxy⟩
  rw [← Finset.prod_sdiff hAB]
  apply mul_le_of_le_one_left
  · apply Finset.prod_nonneg
    intro q hq
    have hqP := (Finset.filter_subset _ _) hq
    have := nu_nonneg_of_mem_primeFactors s hqP
    have hlt := s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors hqP)
      (Nat.dvd_of_mem_primeFactors hqP)
    linarith
  · apply Finset.prod_le_one
    · intro q hq
      have hqP := (Finset.filter_subset _ _) (Finset.sdiff_subset hq)
      have := nu_nonneg_of_mem_primeFactors s hqP
      have hlt := s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors hqP)
        (Nat.dvd_of_mem_primeFactors hqP)
      linarith
    · intro q hq
      have hqP := (Finset.filter_subset _ _) (Finset.sdiff_subset hq)
      have := nu_nonneg_of_mem_primeFactors s hqP
      linarith

lemma Wlt_eq (s : BoundingSieve) (p : ℕ) :
    (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q)) = Wbelow s (p : ℝ) := by
  unfold Wbelow
  apply Finset.prod_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro q _
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

lemma Wzn_eq (s : BoundingSieve) (Lam z : ℝ) (n : ℕ) :
    W s * Wratio s Lam z n = Wbelow s (zLev Lam z n) := by
  unfold W Wratio Wbelow windowPrimes
  rw [← Finset.prod_filter_mul_prod_filter_not s.prodPrimes.primeFactors
    (fun q : ℕ => zLev Lam z n ≤ (q : ℝ))]
  have hpos : (0 : ℝ) < ∏ q ∈ s.prodPrimes.primeFactors.filter
      (fun q : ℕ => zLev Lam z n ≤ (q : ℝ)), (1 - s.nu q) := by
    apply Finset.prod_pos
    intro q hq
    have hqP := (Finset.filter_subset _ _) hq
    have hlt := s.nu_lt_one_of_prime q (Nat.prime_of_mem_primeFactors hqP)
      (Nat.dvd_of_mem_primeFactors hqP)
    linarith
  rw [mul_comm _ (∏ q ∈ _, _), mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), mul_one]
  apply Finset.prod_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro q _
  rw [not_le]

/-! ## Layer 10 — the correction bound (Corollary → p.104 display) -/

/-- **The correction bound** (H-R Corollary → p.104 display): the whole correction
`Σ_{p<z} ν(p)·W(p)·blockInner(p)`, grouped into blocks and over-counted, is `≤ W(z)·Σ_n
(W(z_n)/W(z))·e_{k_n}`. -/
lemma corr_bound (s : BoundingSieve) {Lam z : ℝ} {side b : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b) (hs : side ≤ 2)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    ∑ p ∈ s.prodPrimes.primeFactors,
        s.nu p * (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
          * blockInner s Lam z side b p
      ≤ W s * ∑ n ∈ Finset.Icc 1 (minLevel Lam z), Wratio s Lam z n
          * ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - side + 2 * n),
              ∏ q ∈ T, s.nu q := by
  classical
  have hmaps : ∀ p ∈ s.prodPrimes.primeFactors,
      blockOf Lam z p ∈ Finset.Icc 1 (minLevel Lam z) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    rw [Finset.mem_Icc]
    exact ⟨(blockOf_mem hLam hz hp2).1, blockOf_le_minLevel hLam hz hp2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Icc] at hn
  set blk := s.prodPrimes.primeFactors.filter (fun p => blockOf Lam z p = n) with hblkdef
  have hblkP : blk ⊆ s.prodPrimes.primeFactors := Finset.filter_subset _ _
  have hblkfacts : ∀ p ∈ blk, zLev Lam z n ≤ (p : ℝ) ∧ (p : ℝ) < zLev Lam z (n - 1) := by
    intro p hp
    rw [hblkdef, Finset.mem_filter] at hp
    obtain ⟨hpP, hpn⟩ := hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hpP).two_le
    refine ⟨?_, ?_⟩
    · have := (blockOf_mem hLam hz hp2).2; rwa [hpn] at this
    · have := blockOf_pred hLam hz hp2 (hzprimes p hpP); rwa [hpn] at this
  calc ∑ p ∈ blk, s.nu p
          * (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
          * blockInner s Lam z side b p
      ≤ ∑ p ∈ blk, Wbelow s (zLev Lam z n) * (s.nu p * blockInner s Lam z side b p) := by
        apply Finset.sum_le_sum
        intro p hp
        have hWle : (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
            ≤ Wbelow s (zLev Lam z n) := by
          rw [Wlt_eq s p]; exact Wbelow_anti s (hblkfacts p hp).1
        have hnubi : 0 ≤ s.nu p * blockInner s Lam z side b p :=
          mul_nonneg (nu_nonneg_of_mem_primeFactors s (hblkP hp)) (blockInner_nonneg s)
        calc s.nu p
                * (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
                * blockInner s Lam z side b p
            = (∏ q ∈ s.prodPrimes.primeFactors.filter (fun q => q < p), (1 - s.nu q))
                * (s.nu p * blockInner s Lam z side b p) := by ring
          _ ≤ Wbelow s (zLev Lam z n) * (s.nu p * blockInner s Lam z side b p) :=
              mul_le_mul_of_nonneg_right hWle hnubi
    _ = Wbelow s (zLev Lam z n) * ∑ p ∈ blk, s.nu p * blockInner s Lam z side b p := by
        rw [Finset.mul_sum]
    _ ≤ Wbelow s (zLev Lam z n)
          * ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - side + 2 * n),
              ∏ q ∈ T, s.nu q := by
        apply mul_le_mul_of_nonneg_left _ (Wbelow_nonneg s _)
        exact overcount s hb hs hLam.le hz.le hn.1 blk hblkP hblkfacts
    _ = W s * (Wratio s Lam z n
          * ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - side + 2 * n),
              ∏ q ∈ T, s.nu q) := by
        rw [← Wzn_eq s Lam z n]; ring

/-! ## The two `hcorr` endpoints (frozen shapes from `BlockDecomp.lean`) -/

theorem hcorr_upper (s : BoundingSieve) {Lam z : ℝ} {b : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
      ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 (minLevel Lam z), Wratio s Lam z n *
          ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - 1 + 2 * n), ∏ p ∈ T, s.nu p) := by
  rw [master_signed s hb (Or.inl rfl)]
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hcb := corr_bound (s := s) (Lam := Lam) (z := z) (side := 1) (b := b)
    hLam hz hb (by norm_num) hzprimes
  rw [mul_add, mul_one]
  linarith [hcb]

theorem hcorr_lower (s : BoundingSieve) {Lam z : ℝ} {b : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    W s * (1 - ∑ n ∈ Finset.Icc 1 (minLevel Lam z), Wratio s Lam z n *
          ∑ T ∈ (windowPrimes s Lam z n).powersetCard (2 * b - 2 + 2 * n), ∏ p ∈ T, s.nu p)
      ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0)) := by
  rw [master_signed s hb (Or.inr rfl)]
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have hcb := corr_bound (s := s) (Lam := Lam) (z := z) (side := 2) (b := b)
    hLam hz hb (by norm_num) hzprimes
  rw [mul_sub, mul_one]
  linarith [hcb]

/-! ## The composed endpoints (drop-in for B5, discharging `hcorr` in `BlockDecomp`) -/

/-- **Upper block form, `hcorr` discharged** — the concrete-carrier instantiation of
`mainSum_le_blockForm`. -/
theorem mainSum_le_blockForm' (s : BoundingSieve) {Lam z : ℝ} {b : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 1 b d then (1 : ℝ) else 0))
      ≤ W s * (1 + ∑ n ∈ Finset.Icc 1 (minLevel Lam z),
          Wratio s Lam z n * (∑ p ∈ windowPrimes s Lam z n, s.nu p) ^ (2 * b - 1 + 2 * n)
            / ((2 * b - 1 + 2 * n)! : ℝ)) :=
  mainSum_le_blockForm s (windowPrimes s Lam z) (windowPrimes_subset s Lam z)
    (Wratio s Lam z) (fun n _ => (Wratio_pos s Lam z n).le) (hcorr_upper s hLam hz hb hzprimes)

/-- **Lower block form, `hcorr` discharged** — the load-bearing side. -/
theorem mainSum_ge_blockForm' (s : BoundingSieve) {Lam z : ℝ} {b : ℕ}
    (hLam : 0 < Lam) (hz : 1 < z) (hb : 1 ≤ b)
    (hzprimes : ∀ p ∈ s.prodPrimes.primeFactors, (p : ℝ) < z) :
    W s * (1 - ∑ n ∈ Finset.Icc 1 (minLevel Lam z),
          Wratio s Lam z n * (∑ p ∈ windowPrimes s Lam z n, s.nu p) ^ (2 * b - 2 + 2 * n)
            / ((2 * b - 2 + 2 * n)! : ℝ))
      ≤ s.mainSum (fun d => (μ d : ℝ) * (if chi Lam z 2 b d then (1 : ℝ) else 0)) :=
  mainSum_ge_blockForm s (windowPrimes s Lam z) (windowPrimes_subset s Lam z)
    (Wratio s Lam z) (fun n _ => (Wratio_pos s Lam z n).le) (hcorr_lower s hLam hz hb hzprimes)

end Salt.BrunLower
