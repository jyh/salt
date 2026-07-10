/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.W3Prep
import Salt.Twelve.MomentAtom
import Salt.Maynard.GFunction
import Salt.Maynard.CollisionQuant

/-!
# W3-2 (g-engine) — `marked_sqf_g` and `budget_moment_g`

Card W3-2 of the `explicit12` wave-3 dispatch
(`docs/blueprints/explicit12-design.md`).  Both lemmas are powerset-swap
machinery over the `g`-weight `gMult r = ∏_{p ∣ r} (p − 2)`.

The core identity (for squarefree `r` with all prime factors `> D ≥ 3`) is the
Möbius-style expansion
`1/g(r) = (1/φ(r)) · ∑_{u ∣ r} h(u)`, `h(u) = ∏_{p ∣ u} 1/(p−2)`,
mirroring `Salt.Maynard.EulerTailL`'s `inv_gMult_expand` (whose lemmas are
`private`, so the divisor-sum chain is re-derived here).

* `marked_sqf_g` — the `g`-weighted marked-sqf sum: substitute the identity,
  factor `r = s·b` (so `g(r) = g(s)·g(b)`), bound `(log r)^a ≤ (log z)^a`, then
  swap and apply `marked_sqf_phi` at each divisor `v`.  The residual tail
  `∑_v h(v)/φ(v) = ∏_{D<p<z}(1 + 1/((p−1)(p−2))) ≤ 2`.  Net constant `c = 2·c_φ`.
* `budget_moment_g` — the two-sided sandwich `φ-sum ≤ g-sum ≤ φ-sum + Cg·log R/D`.
  LOWER is termwise (`0 < g(r) ≤ φ(r)`, weights `≥ 0`); UPPER swaps the
  `u ≠ 1` divisor tail into `marked_sqf_phi` and bounds it by
  `(∏−1)·c_φ·log R ≤ (2/(D−1))·c_φ·log R ≤ (4/D)·c_φ·log R`.  `Cg = 4·c_φ`.
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-! ## `box_g_pos` and per-prime facts on the box -/

/-- Any prime dividing a number coprime to `W'` exceeds `D`. -/
private lemma box_prime_gt {W' D r : ℕ} (hrcop : r.Coprime W')
    (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) {p : ℕ}
    (hpp : p.Prime) (hpr : p ∣ r) : D < p := by
  refine hD p hpp (fun hpW => ?_)
  have : p ∣ 1 := hrcop ▸ Nat.dvd_gcd hpr hpW
  exact hpp.one_lt.ne' (Nat.dvd_one.mp this)

/-- **`box_g_pos` (reusable helper).** On the box `r` — squarefree, coprime to
`W'`, with `D ≥ 3` and every prime not dividing `W'` exceeding `D` — the
`g`-weight is strictly positive.  This is load-bearing for the sandwich's LOWER
half: a `g(r) = 0` term would flip the inequality under `x/0 = 0`. -/
theorem box_g_pos {W' D r : ℕ} (_hr : Squarefree r) (hrcop : r.Coprime W')
    (hD3 : 3 ≤ D) (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) :
    0 < gMult r := by
  rw [gMult]
  refine Finset.prod_pos (fun p hp => ?_)
  have := box_prime_gt hrcop hD (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp)
  omega

/-- `g` is multiplicative on a coprime factorization. -/
private lemma gMult_mul_coprime {s b : ℕ} (hcop : Nat.Coprime s b) :
    gMult (s * b) = gMult s * gMult b := by
  rw [gMult, gMult, gMult, Nat.Coprime.primeFactors_mul hcop,
    Finset.prod_union hcop.disjoint_primeFactors]

/-! ## Divisor-sum expansion of `1/g` (re-derived; `EulerTailL`'s are private) -/

/-- Divisors of a squarefree `r` are the products of subsets of its prime
factors. -/
private lemma divisors_eq_powerset_image {r : ℕ} (hr : Squarefree r) :
    r.divisors = r.primeFactors.powerset.image (fun S => ∏ p ∈ S, p) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hdvd, -⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hdvd hr.ne_zero,
      Nat.prod_primeFactors_of_squarefree (hr.squarefree_of_dvd hdvd)⟩
  · rintro ⟨S, hS, rfl⟩
    refine ⟨?_, hr.ne_zero⟩
    calc ∏ p ∈ S, p ∣ ∏ p ∈ r.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset _ _ _ hS
      _ = r := Nat.prod_primeFactors_of_squarefree hr

/-- Divisor sums over a squarefree `r` are powerset sums over its prime
factors. -/
private lemma sum_divisors_eq_sum_powerset {r : ℕ} (hr : Squarefree r)
    (f : ℕ → ℝ) :
    ∑ d ∈ r.divisors, f d
      = ∑ S ∈ r.primeFactors.powerset, f (∏ p ∈ S, p) := by
  have hinj : Set.InjOn (fun S : Finset ℕ => ∏ p ∈ S, p)
      ↑r.primeFactors.powerset := by
    intro X hX Y hY hXY
    rw [Finset.mem_coe, Finset.mem_powerset] at hX hY
    have hXp : ∀ p ∈ X, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hX hp)
    have hYp : ∀ p ∈ Y, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactors (hY hp)
    calc X = (∏ p ∈ X, p).primeFactors := (Nat.primeFactors_prod hXp).symm
      _ = (∏ p ∈ Y, p).primeFactors := congrArg Nat.primeFactors hXY
      _ = Y := Nat.primeFactors_prod hYp
  rw [divisors_eq_powerset_image hr, Finset.sum_image hinj]

/-- **The `h`-expansion.** For squarefree `r` with all prime factors `≥ 3`,
`1/g(r) = (∑_{d ∣ r} ∏_{p ∣ d} (p−2)⁻¹) · (1/φ(r))`. -/
private lemma inv_gMult_expand {r : ℕ} (hrsq : Squarefree r)
    (hp3 : ∀ p ∈ r.primeFactors, 3 ≤ p) :
    ((gMult r : ℝ))⁻¹
      = (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * ((Nat.totient r : ℝ))⁻¹ := by
  have hsum : (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
      = ∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, ((p : ℝ) - 2)⁻¹ := by
    rw [sum_divisors_eq_sum_powerset hrsq]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [Finset.mem_powerset] at hS
    rw [Nat.primeFactors_prod
      (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))]
  have hpow : (∑ S ∈ r.primeFactors.powerset, ∏ p ∈ S, ((p : ℝ) - 2)⁻¹)
      = ∏ p ∈ r.primeFactors, (1 + ((p : ℝ) - 2)⁻¹) := by
    have h := Finset.prod_add (fun p : ℕ => ((p : ℝ) - 2)⁻¹)
      (fun _ => (1 : ℝ)) r.primeFactors
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hsum, hpow, gMult_cast hp3, totient_squarefree_cast hrsq,
    ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3 p hp
  have h2 : ((p : ℝ) - 2) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  have h1 : ((p : ℝ) - 1) ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
  field_simp
  ring

/-- For squarefree `d`, `h(d)·(1/φ(d)) = ∏_{p ∣ d} ((p−1)(p−2))⁻¹`. -/
private lemma h_over_phi {d : ℕ} (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹) * ((Nat.totient d : ℝ))⁻¹
      = ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ := by
  rw [totient_squarefree_cast hd, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← mul_inv, mul_comm ((p : ℝ) - 2) ((p : ℝ) - 1)]

/-! ## Elementary inequalities and the telescoping Euler tail -/

/-- Product-versus-sum: if the `aₓ ≥ 0` sum to at most `1/2`, then
`∏(1 + aₓ) ≤ 1 + 2∑aₓ`.  (Copy of `EulerTailL.prod_one_add_le`, which is
private.) -/
private lemma prod_one_add_le {ι : Type*} (s : Finset ι)
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

/-- Telescoping tail bound:
`∑_{D < n ≤ M} ((n−1)(n−2))⁻¹ ≤ (D−1)⁻¹` for `2 ≤ D`. -/
private lemma inv_prod_tele (D : ℕ) (hD : 2 ≤ D) :
    ∀ M : ℕ, D ≤ M →
      (∑ n ∈ Finset.Icc (D + 1) M, (((n : ℝ) - 1) * ((n : ℝ) - 2))⁻¹)
        ≤ ((D : ℝ) - 1)⁻¹ - ((M : ℝ) - 1)⁻¹ := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ M hDM ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_trans hD hDM
      have h1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
      have h2 : (0 : ℝ) < (M : ℝ) := by linarith
      have hstep : ((((M + 1 : ℕ) : ℝ) - 1) * (((M + 1 : ℕ) : ℝ) - 2))⁻¹
          = ((M : ℝ) - 1)⁻¹ - (((M + 1 : ℕ) : ℝ) - 1)⁻¹ := by
        push_cast
        rw [show ((M : ℝ) + 1 - 1) = (M : ℝ) by ring,
          show ((M : ℝ) + 1 - 2) = (M : ℝ) - 1 by ring]
        field_simp
        ring
      rw [hstep]
      linarith [ih]

/-- **The Euler tail.** For `D ≥ 3`, the sum of `h(d)/φ(d) = ∏_{p∣d}((p−1)(p−2))⁻¹`
over nontrivial squarefree moduli `< M` with all prime factors `> D` is at most
`2/(D−1)`.  (Powerset expansion + `prod_one_add_le` + telescoping tail.) -/
private lemma tail_erase_le (D M : ℕ) (hD : 3 ≤ D) :
    ∑ d ∈ ((Finset.range M).filter
        (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
      ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹
      ≤ 2 / ((D : ℝ) - 1) := by
  classical
  have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) - 1 := by linarith
  set SF := ((Finset.range M).filter
      (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1 with hSF
  set PP := (Finset.range M).filter (fun p => p.Prime ∧ D < p) with hPP
  have ha_nonneg : ∀ p ∈ PP, (0 : ℝ) ≤ (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ := by
    intro p hp
    rw [hPP, Finset.mem_filter] at hp
    have hp3 : 3 ≤ p := by have := hp.2.2; omega
    have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    exact (inv_pos.mpr (mul_pos (by linarith) (by linarith))).le
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
    refine ⟨?_, ?_⟩
    · have ht2 : 1 < t := by
        rcases Nat.lt_or_ge t 2 with h | h
        · interval_cases t
          · exact absurd hsq not_squarefree_zero
          · exact absurd rfl hne1
        · omega
      exact Finset.nonempty_iff_ne_empty.mp (Nat.nonempty_primeFactors.mpr ht2)
    · intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range]
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ t := Nat.dvd_of_mem_primeFactors hp
      have ht0 : 0 < t := Nat.pos_of_ne_zero hsq.ne_zero
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd ht0 hpd) htM, hpp, hbig p hp⟩
  have hprodadd : ∏ p ∈ PP, (1 + (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
      = ∑ S ∈ PP.powerset, ∏ p ∈ S, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ := by
    have h := Finset.prod_add (fun p : ℕ => (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
      (fun _ : ℕ => (1 : ℝ)) PP
    simp only [Finset.prod_const_one, mul_one] at h
    rw [← h]
    exact Finset.prod_congr rfl fun p _ => by ring
  have hsplit : ∑ S ∈ PP.powerset.erase ∅,
        ∏ p ∈ S, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹
      = (∏ p ∈ PP, (1 + (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)) - 1 := by
    have h := Finset.sum_erase_add PP.powerset
      (fun S => ∏ p ∈ S, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
      (Finset.empty_mem_powerset PP)
    rw [Finset.prod_empty] at h
    rw [hprodadd]; linarith
  have htailsum : ∑ p ∈ PP, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ ≤ ((D : ℝ) - 1)⁻¹ := by
    have hPPsub : PP ⊆ Finset.Icc (D + 1) M := by
      intro p hp
      rw [hPP, Finset.mem_filter, Finset.mem_range] at hp
      rw [Finset.mem_Icc]; omega
    have hmono : ∑ p ∈ PP, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹
        ≤ ∑ n ∈ Finset.Icc (D + 1) M, (((n : ℝ) - 1) * ((n : ℝ) - 2))⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hPPsub
      intro n hn _
      rw [Finset.mem_Icc] at hn
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
      exact (inv_pos.mpr (mul_pos (by linarith) (by linarith))).le
    rcases Nat.lt_or_ge M D with hM | hM
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hmono
      have : (0 : ℝ) ≤ ((D : ℝ) - 1)⁻¹ := inv_nonneg.mpr hDpos.le
      linarith
    · have htele := inv_prod_tele D (by omega) M hM
      have hMinv : (0 : ℝ) ≤ ((M : ℝ) - 1)⁻¹ := by
        have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 2 ≤ M)
        exact inv_nonneg.mpr (by linarith)
      linarith [htele]
  have hasum : ∑ p ∈ PP, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ ≤ 1 / 2 := by
    have hle : (2 : ℝ) ≤ (D : ℝ) - 1 := by linarith
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hle
    rw [one_div] at h
    linarith [htailsum, h]
  have himg : ∑ S ∈ SF.image Nat.primeFactors,
        ∏ p ∈ S, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹
      = ∑ d ∈ SF, ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ :=
    Finset.sum_image hinj
  calc ∑ d ∈ SF, ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹
      = ∑ S ∈ SF.image Nat.primeFactors,
          ∏ p ∈ S, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ := himg.symm
    _ ≤ ∑ S ∈ PP.powerset.erase ∅, ∏ p ∈ S, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro S hSt _
        have hSsub : S ⊆ PP := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hSt)
        exact Finset.prod_nonneg fun p hp => ha_nonneg p (hSsub hp)
    _ = (∏ p ∈ PP, (1 + (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)) - 1 := hsplit
    _ ≤ (1 + 2 * ∑ p ∈ PP, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) - 1 := by
        have := prod_one_add_le PP _ ha_nonneg hasum
        linarith
    _ = 2 * ∑ p ∈ PP, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ := by ring
    _ ≤ 2 / ((D : ℝ) - 1) := by
        rw [div_eq_mul_inv]
        have := htailsum
        nlinarith [htailsum, inv_nonneg.mpr hDpos.le]

/-- **The full Euler tail (including `d = 1`).** For `D ≥ 3` and `2 ≤ M`,
`∑_{d < M, nice} ∏_{p∣d}((p−1)(p−2))⁻¹ ≤ 2`.  This is `1 + tail_erase ≤ 1 + 2/(D−1) ≤ 2`. -/
private lemma tail_full_le (D M : ℕ) (hD : 3 ≤ D) (hM : 2 ≤ M) :
    ∑ d ∈ (Finset.range M).filter
        (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
      ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹ ≤ 2 := by
  have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) - 1 := by linarith
  have h1mem : (1 : ℕ) ∈ (Finset.range M).filter
      (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, squarefree_one, ?_⟩
    simp
  have hsplit := Finset.add_sum_erase
    ((Finset.range M).filter
      (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p))
    (fun d : ℕ => ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) h1mem
  simp only [Nat.primeFactors_one, Finset.prod_empty] at hsplit
  have htail := tail_erase_le D M hD
  have hle : 2 / ((D : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hDpos]; linarith
  linarith [hsplit, htail, hle]

/-! ## `marked_sqf_g` -/

/-- **Frozen theorem 1.** The `g`-weighted marked-sqf sum: for an arbitrary
divisor `s`, the sub-sum over multiples of `s` is at most `(1/g(s))` times a
`(W', a)`-uniform constant times `(log z)^{a+1}`.  No case split on `s` is
needed: `g` is multiplicative on the factorization `r = s·b`, and `x/0 = 0`
makes the even-`s` degeneracy self-consistent. -/
theorem marked_sqf_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W') (a : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D s z : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter
          (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
          (Real.log r) ^ a / (gMult r : ℝ))
        ≤ (1 / (gMult s : ℝ)) * c * (Real.log z) ^ (a + 1) := by
  obtain ⟨cφ, hcφ0, hcφ⟩ := marked_sqf_phi W' hW' hpos 0
  refine ⟨2 * cφ, by positivity, ?_⟩
  intro D s z hD3 hD hs hz
  classical
  set Fs := (Finset.range z).filter
    (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r) with hFs
  set B := (Finset.range z).filter
    (fun b => Squarefree b ∧ b.Coprime W' ∧ b.Coprime s) with hB
  have hlogz0 : (0 : ℝ) ≤ Real.log z :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  -- Step A: reindex `r = s·b`, factor `g(r) = g(s)·g(b)`, bound `(log r)^a ≤ (log z)^a`.
  have hStepA : ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
      ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := by
    have hmap_inj : Set.InjOn (fun r => r / s) (Fs : Set ℕ) := by
      intro r1 h1 r2 h2 heq
      rw [Finset.mem_coe, hFs, Finset.mem_filter, Finset.mem_range] at h1 h2
      obtain ⟨_, _, _, hsr1⟩ := h1
      obtain ⟨_, _, _, hsr2⟩ := h2
      have e1 : s * (r1 / s) = r1 := Nat.mul_div_cancel' hsr1
      have e2 : s * (r2 / s) = r2 := Nat.mul_div_cancel' hsr2
      have hh : r1 / s = r2 / s := heq
      rw [← e1, ← e2, hh]
    have himg_sub : Fs.image (fun r => r / s) ⊆ B := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨r, hr, rfl⟩ := hb
      rw [hFs, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrz, hrsf, hrW', hsr⟩ := hr
      have hrsb : r = s * (r / s) := (Nat.mul_div_cancel' hsr).symm
      have hbdvd : (r / s) ∣ r :=
        ⟨s, by rw [mul_comm]; exact (Nat.mul_div_cancel' hsr).symm⟩
      rw [hB, Finset.mem_filter, Finset.mem_range]
      refine ⟨lt_of_le_of_lt (Nat.div_le_self r s) hrz,
        hrsf.squarefree_of_dvd hbdvd, hrW'.coprime_dvd_left hbdvd, ?_⟩
      have hsqsb : Squarefree (s * (r / s)) := hrsb ▸ hrsf
      exact (Nat.coprime_of_squarefree_mul hsqsb).symm
    have hper : ∀ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
        ≤ (Real.log z) ^ a * ((gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹) := by
      intro r hr
      rw [hFs, Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨hrz, hrsf, _hrW', hsr⟩ := hr
      have hrsb : r = s * (r / s) := (Nat.mul_div_cancel' hsr).symm
      have hcop_s_b : Nat.Coprime s (r / s) := by
        have hsqsb : Squarefree (s * (r / s)) := hrsb ▸ hrsf
        exact Nat.coprime_of_squarefree_mul hsqsb
      have hgmul : gMult r = gMult s * gMult (r / s) := by
        have h := gMult_mul_coprime hcop_s_b
        rwa [← hrsb] at h
      have hinv : (gMult r : ℝ)⁻¹ = (gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹ := by
        rw [hgmul, Nat.cast_mul, mul_inv]
      rw [div_eq_mul_inv, hinv]
      have hr1 : (1 : ℕ) ≤ r := Nat.pos_of_ne_zero hrsf.ne_zero
      have hlogr0 : (0 : ℝ) ≤ Real.log r :=
        Real.log_nonneg (by exact_mod_cast hr1)
      have hlogrz : Real.log r ≤ Real.log z :=
        Real.log_le_log (by exact_mod_cast hr1) (by exact_mod_cast hrz.le)
      have hpow : (Real.log r) ^ a ≤ (Real.log z) ^ a :=
        pow_le_pow_left₀ hlogr0 hlogrz a
      have hK0 : (0 : ℝ) ≤ (gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹ :=
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact mul_le_mul_of_nonneg_right hpow hK0
    have himg : ∑ b ∈ Fs.image (fun r => r / s), (gMult b : ℝ)⁻¹
        = ∑ r ∈ Fs, (gMult (r / s) : ℝ)⁻¹ := Finset.sum_image hmap_inj
    calc ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
        ≤ ∑ r ∈ Fs, (Real.log z) ^ a * ((gMult s : ℝ)⁻¹ * (gMult (r / s) : ℝ)⁻¹) :=
          Finset.sum_le_sum hper
      _ = (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ r ∈ Fs, (gMult (r / s) : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = (gMult s : ℝ)⁻¹ * (Real.log z) ^ a
            * ∑ b ∈ Fs.image (fun r => r / s), (gMult b : ℝ)⁻¹ := by rw [himg]
      _ ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hlogz0 a))
          exact Finset.sum_le_sum_of_subset_of_nonneg himg_sub
            (fun b _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  -- Step B: `∑_{b∈B} 1/g(b) ≤ 2·cφ·log z`.
  have hStepB : ∑ b ∈ B, (gMult b : ℝ)⁻¹ ≤ 2 * cφ * Real.log z := by
    have hexp : ∀ b ∈ B, (gMult b : ℝ)⁻¹
        = ∑ d ∈ Finset.range (z + 1),
            if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ else 0 := by
      intro b hb
      rw [hB, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hbz, hbsf, hbW', _⟩ := hb
      have hp3 : ∀ p ∈ b.primeFactors, 3 ≤ p := by
        intro p hp
        have := box_prime_gt hbW' hD (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)
        omega
      calc (gMult b : ℝ)⁻¹
          = (∑ d ∈ b.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ := inv_gMult_expand hbsf hp3
        _ = ∑ d ∈ b.divisors,
              (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹) * (Nat.totient b : ℝ)⁻¹ := by
            rw [Finset.sum_mul]
        _ = _ := sum_divisors_eq_sum_range hbsf.ne_zero (by omega) _
    have hswap : ∑ b ∈ B, (gMult b : ℝ)⁻¹
        = ∑ d ∈ Finset.range (z + 1), ∑ b ∈ B,
            if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ else 0 := by
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    rw [hswap]
    have hvanish : ∀ d ∈ Finset.range (z + 1),
        (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (Nat.totient b : ℝ)⁻¹ else 0) ≠ 0 →
        (Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p) := by
      intro d _ hne
      by_contra hnot
      apply hne
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [if_neg]
      intro hdb
      rw [hB, Finset.mem_filter] at hb
      obtain ⟨_, hbsf, hbW', _⟩ := hb
      exact hnot ⟨hbsf.squarefree_of_dvd hdb, fun p hp =>
        box_prime_gt hbW' hD (Nat.prime_of_mem_primeFactors hp)
          (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdb)⟩
    rw [← Finset.sum_filter_of_ne hvanish]
    have hbound : ∀ d ∈ (Finset.range (z + 1)).filter
        (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
        (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) := by
      intro d hd
      rw [Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨_hdz1, hdsf, hdbig⟩ := hd
      have hpull : (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (Nat.totient b : ℝ)⁻¹ else 0)
          = (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by rw [mul_ite, mul_zero])
      rw [hpull]
      have hHnn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹ := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hpD : (D : ℝ) < (p : ℝ) := by exact_mod_cast hdbig p hp
        have hD3R : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD3
        exact inv_nonneg.mpr (by linarith)
      have hmarked : ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (Nat.totient d : ℝ)⁻¹ * cφ * Real.log z := by
        have hd0 : 0 < d := Nat.pos_of_ne_zero hdsf.ne_zero
        rw [← Finset.sum_filter]
        have hsub : B.filter (fun b => d ∣ b) ⊆ (Finset.range z).filter
            (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r) := by
          intro b hb
          rw [Finset.mem_filter, hB, Finset.mem_filter, Finset.mem_range] at hb
          obtain ⟨⟨hbz, hbsf, hbW', _⟩, hdb⟩ := hb
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hbz, hbsf, hbW', hdb⟩
        calc ∑ b ∈ B.filter (fun b => d ∣ b), (Nat.totient b : ℝ)⁻¹
            ≤ ∑ r ∈ (Finset.range z).filter
                (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r), (Nat.totient r : ℝ)⁻¹ := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun r _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          _ = ∑ r ∈ (Finset.range z).filter
                (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r),
                (Real.log r) ^ 0 / (Nat.totient r : ℝ) := by
              exact Finset.sum_congr rfl (fun r _ => by rw [pow_zero, one_div])
          _ ≤ (1 / (Nat.totient d : ℝ)) * cφ * (Real.log z) ^ (0 + 1) := hcφ d z hd0 hz
          _ = (Nat.totient d : ℝ)⁻¹ * cφ * Real.log z := by rw [one_div, zero_add, pow_one]
      calc (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((Nat.totient d : ℝ)⁻¹ * cφ * Real.log z) :=
            mul_le_mul_of_nonneg_left hmarked hHnn
        _ = (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) := by
            rw [← h_over_phi hdsf]; ring
    calc ∑ d ∈ (Finset.range (z + 1)).filter
          (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
          (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (Nat.totient b : ℝ)⁻¹ else 0)
        ≤ ∑ d ∈ (Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
            (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) :=
          Finset.sum_le_sum hbound
      _ = (∑ d ∈ (Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
            ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * (cφ * Real.log z) := by
          exact mul_le_mul_of_nonneg_right (tail_full_le D (z + 1) hD3 (by omega))
            (mul_nonneg hcφ0 hlogz0)
      _ = 2 * cφ * Real.log z := by ring
  calc ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
      ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := hStepA
    _ ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * (2 * cφ * Real.log z) := by
        exact mul_le_mul_of_nonneg_left hStepB
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hlogz0 a))
    _ = 1 / (gMult s : ℝ) * (2 * cφ) * (Real.log z) ^ (a + 1) := by
        rw [one_div, pow_succ]; ring

/-! ## `budget_moment_g` -/

/-- **Frozen theorem 2 (two-sided sandwich).** The `φ`-weighted budget moment is
bounded below by its `g`-weighted analogue (LOWER, termwise from `0 < g ≤ φ`),
and above by it plus an `O(log R / D)` correction (UPPER, the `d ≠ 1` divisor
tail fed into `marked_sqf_phi`).  `Cg = 4·c_φ`. -/
theorem budget_moment_g (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (c b : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ D z R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (Nat.totient r : ℝ))
        ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
            (Real.log r / Real.log R) ^ c
              * ((Real.log z - Real.log r) / Real.log R) ^ b
              / (gMult r : ℝ)) ∧
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (gMult r : ℝ))
        ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
            (Real.log r / Real.log R) ^ c
              * ((Real.log z - Real.log r) / Real.log R) ^ b
              / (Nat.totient r : ℝ))
          + Cg / D * Real.log R := by
  have _hUpper := hUpper
  obtain ⟨cφ, hcφ0, hcφ⟩ := marked_sqf_phi W' hW' hpos 0
  refine ⟨4 * cφ, by positivity, ?_⟩
  intro D z R hD3 hD hz hzR hR
  classical
  set F := (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W') with hF
  -- abbreviation for the (nonnegative, ≤ 1) budget weight
  set w : ℕ → ℝ := fun r => (Real.log r / Real.log R) ^ c
    * ((Real.log z - Real.log r) / Real.log R) ^ b with hw
  have hLpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le zero_lt_one hR
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hZnn : (0 : ℝ) ≤ Real.log z := Real.log_nonneg hz1
  have hZL : Real.log z ≤ Real.log R :=
    Real.log_le_log (by linarith) (by exact_mod_cast hzR)
  have hmemF : ∀ r ∈ F, r < z ∧ Squarefree r ∧ r.Coprime W' := by
    intro r hr; rw [hF, Finset.mem_filter, Finset.mem_range] at hr; exact hr
  have hlogr_facts : ∀ r ∈ F, 0 ≤ Real.log r ∧ Real.log r ≤ Real.log z := by
    intro r hr
    obtain ⟨hrz, hrsf, _⟩ := hmemF r hr
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hrsf.ne_zero)
    exact ⟨Real.log_nonneg hr1, Real.log_le_log (by linarith) (by exact_mod_cast hrz.le)⟩
  have hw_nonneg : ∀ r ∈ F, 0 ≤ w r := by
    intro r hr
    obtain ⟨hlr0, hlrz⟩ := hlogr_facts r hr
    rw [hw]
    exact mul_nonneg (pow_nonneg (div_nonneg hlr0 hLpos.le) c)
      (pow_nonneg (div_nonneg (by linarith) hLpos.le) b)
  have hw_le1 : ∀ r ∈ F, w r ≤ 1 := by
    intro r hr
    obtain ⟨hlr0, hlrz⟩ := hlogr_facts r hr
    rw [hw]
    refine mul_le_one₀ ?_ (pow_nonneg (div_nonneg (by linarith) hLpos.le) b) ?_
    · exact pow_le_one₀ (div_nonneg hlr0 hLpos.le) ((div_le_one hLpos).mpr (by linarith))
    · exact pow_le_one₀ (div_nonneg (by linarith) hLpos.le)
        ((div_le_one hLpos).mpr (by linarith))
  -- LOWER: `φ-sum ≤ g-sum`, termwise from `0 < g(r) ≤ φ(r)` and `w(r) ≥ 0`.
  have hLower : ∑ r ∈ F, w r / (Nat.totient r : ℝ) ≤ ∑ r ∈ F, w r / (gMult r : ℝ) := by
    refine Finset.sum_le_sum fun r hr => ?_
    obtain ⟨_hrz, hrsf, hrW'⟩ := hmemF r hr
    have hgpos : 0 < gMult r := box_g_pos hrsf hrW' hD3 hD
    have hgposR : (0 : ℝ) < (gMult r : ℝ) := by exact_mod_cast hgpos
    have hgφ : (gMult r : ℝ) ≤ (Nat.totient r : ℝ) :=
      gMult_le_totient hrsf (fun p hp => by
        have := box_prime_gt hrW' hD (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)
        omega)
    exact div_le_div_of_nonneg_left (hw_nonneg r hr) hgposR hgφ
  -- UPPER: `g-sum = φ-sum + tail`, `tail ≤ Cg·log R / D`.
  have hUpperB : ∑ r ∈ F, w r / (gMult r : ℝ)
      ≤ ∑ r ∈ F, w r / (Nat.totient r : ℝ) + (4 * cφ) / D * Real.log R := by
    have hexp : ∀ r ∈ F, w r / (gMult r : ℝ)
        = ∑ d ∈ Finset.range (z + 1),
            if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
      intro r hr
      obtain ⟨_hrz, hrsf, hrW'⟩ := hmemF r hr
      have hp3 : ∀ p ∈ r.primeFactors, 3 ≤ p := by
        intro p hp
        have := box_prime_gt hrW' hD (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp)
        omega
      calc w r / (gMult r : ℝ)
          = w r * (gMult r : ℝ)⁻¹ := div_eq_mul_inv _ _
        _ = (∑ d ∈ r.divisors, ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (w r * (Nat.totient r : ℝ)⁻¹) := by rw [inv_gMult_expand hrsf hp3]; ring
        _ = ∑ d ∈ r.divisors,
              (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹) * (w r * (Nat.totient r : ℝ)⁻¹) := by
            rw [Finset.sum_mul]
        _ = _ := sum_divisors_eq_sum_range hrsf.ne_zero (by omega) _
    have hswap : ∑ r ∈ F, w r / (gMult r : ℝ)
        = ∑ d ∈ Finset.range (z + 1), ∑ r ∈ F,
            if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
      rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
    -- split off `d = 1` (the `φ`-sum) from the divisor sum.
    have h1mem : (1 : ℕ) ∈ Finset.range (z + 1) := by
      rw [Finset.mem_range]; omega
    have hd1 : (∑ r ∈ F, if (1 : ℕ) ∣ r then
          (∏ p ∈ (1 : ℕ).primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
        = ∑ r ∈ F, w r / (Nat.totient r : ℝ) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [if_pos (one_dvd r), Nat.primeFactors_one, Finset.prod_empty, one_mul,
        div_eq_mul_inv]
    have hsplit := Finset.add_sum_erase (Finset.range (z + 1))
      (fun d => ∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
        * (w r * (Nat.totient r : ℝ)⁻¹) else 0) h1mem
    rw [hd1] at hsplit
    -- restrict the tail to the nice moduli
    have hvanish : ∀ d ∈ (Finset.range (z + 1)).erase 1,
        (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (w r * (Nat.totient r : ℝ)⁻¹) else 0) ≠ 0 →
        (Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p) := by
      intro d _ hne
      by_contra hnot
      apply hne
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [if_neg]
      intro hdr
      obtain ⟨_, hrsf, hrW'⟩ := hmemF r hr
      exact hnot ⟨hrsf.squarefree_of_dvd hdr, fun p hp =>
        box_prime_gt hrW' hD (Nat.prime_of_mem_primeFactors hp)
          (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdr)⟩
    have hbound : ∀ d ∈ ((Finset.range (z + 1)).filter
        (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
        (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
          ≤ (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) := by
      intro d hd
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨_hd1, _hdz1, hdsf, hdbig⟩ := hd
      have hpull : (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
          = (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ => by rw [mul_ite, mul_zero])
      rw [hpull]
      have hHnn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹ := by
        refine Finset.prod_nonneg fun p hp => ?_
        have hpD : (D : ℝ) < (p : ℝ) := by exact_mod_cast hdbig p hp
        have hD3R : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD3
        exact inv_nonneg.mpr (by linarith)
      have hmarked : ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0)
          ≤ (Nat.totient d : ℝ)⁻¹ * cφ * Real.log z := by
        have hd0 : 0 < d := Nat.pos_of_ne_zero hdsf.ne_zero
        rw [← Finset.sum_filter]
        have hsub : F.filter (fun r => d ∣ r) ⊆ (Finset.range z).filter
            (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r) := by
          intro r hr
          rw [Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_range] at hr
          obtain ⟨⟨hrz, hrsf, hrW'⟩, hdr⟩ := hr
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨hrz, hrsf, hrW', hdr⟩
        calc ∑ r ∈ F.filter (fun r => d ∣ r), w r * (Nat.totient r : ℝ)⁻¹
            ≤ ∑ r ∈ F.filter (fun r => d ∣ r), (Nat.totient r : ℝ)⁻¹ := by
              refine Finset.sum_le_sum fun r hr => ?_
              rw [Finset.mem_filter] at hr
              have hwr := hw_le1 r hr.1
              have hφnn : (0 : ℝ) ≤ (Nat.totient r : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
              calc w r * (Nat.totient r : ℝ)⁻¹
                  ≤ 1 * (Nat.totient r : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hwr hφnn
                _ = (Nat.totient r : ℝ)⁻¹ := one_mul _
          _ ≤ ∑ r ∈ (Finset.range z).filter
                (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r), (Nat.totient r : ℝ)⁻¹ :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun r _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
          _ = ∑ r ∈ (Finset.range z).filter
                (fun r => Squarefree r ∧ r.Coprime W' ∧ d ∣ r),
                (Real.log r) ^ 0 / (Nat.totient r : ℝ) :=
              Finset.sum_congr rfl (fun r _ => by rw [pow_zero, one_div])
          _ ≤ (1 / (Nat.totient d : ℝ)) * cφ * (Real.log z) ^ (0 + 1) := hcφ d z hd0 hz
          _ = (Nat.totient d : ℝ)⁻¹ * cφ * Real.log z := by rw [one_div, zero_add, pow_one]
      calc (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((Nat.totient d : ℝ)⁻¹ * cφ * Real.log z) :=
            mul_le_mul_of_nonneg_left hmarked hHnn
        _ = (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) := by
            rw [← h_over_phi hdsf]; ring
    -- assemble the tail bound
    have htail :
        (∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
          if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
        ≤ (4 * cφ) / D * Real.log R := by
      have hcφlogz : (0 : ℝ) ≤ cφ * Real.log z := mul_nonneg hcφ0 hZnn
      have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD3
      have hDpos : (0 : ℝ) < (D : ℝ) := by linarith
      have hDm1 : (0 : ℝ) < (D : ℝ) - 1 := by linarith
      calc (∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
              if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
                * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
          = ∑ d ∈ ((Finset.range (z + 1)).filter
              (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
              ∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
                * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
            rw [← Finset.filter_erase, Finset.sum_filter_of_ne hvanish]
        _ ≤ ∑ d ∈ ((Finset.range (z + 1)).filter
              (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
              (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) :=
            Finset.sum_le_sum hbound
        _ = (∑ d ∈ ((Finset.range (z + 1)).filter
              (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
              ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹) * (cφ * Real.log z) := by
            rw [Finset.sum_mul]
        _ ≤ (2 / ((D : ℝ) - 1)) * (cφ * Real.log z) :=
            mul_le_mul_of_nonneg_right (tail_erase_le D (z + 1) hD3) hcφlogz
        _ ≤ (4 * cφ) / D * Real.log R := by
            have hcR : (0 : ℝ) ≤ cφ * Real.log R := mul_nonneg hcφ0 hLpos.le
            have hfrac : (2 : ℝ) / ((D : ℝ) - 1) ≤ 4 / (D : ℝ) := by
              rw [div_le_div_iff₀ hDm1 hDpos]; linarith
            have hb1 : (2 / ((D : ℝ) - 1)) * (cφ * Real.log z)
                ≤ (2 / ((D : ℝ) - 1)) * (cφ * Real.log R) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZL hcφ0)
                (div_nonneg (by norm_num) hDm1.le)
            have hb2 : (2 / ((D : ℝ) - 1)) * (cφ * Real.log R)
                ≤ (4 / (D : ℝ)) * (cφ * Real.log R) :=
              mul_le_mul_of_nonneg_right hfrac hcR
            have hb3 : (4 / (D : ℝ)) * (cφ * Real.log R)
                = (4 * cφ) / D * Real.log R := by ring
            linarith [hb1, hb2, hb3]
    -- combine: `g-sum = φ-sum + tail`
    have heq : ∑ r ∈ F, w r / (gMult r : ℝ)
        = (∑ r ∈ F, w r / (Nat.totient r : ℝ))
          + ∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
            if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
      rw [hswap, ← hsplit]
    rw [heq]
    linarith [htail]
  exact ⟨hLower, hUpperB⟩

end Salt.Twelve
