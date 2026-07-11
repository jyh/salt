/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Twelve.W3Prep
import Salt.Twelve.BudgetMomentG
import Salt.Maynard.PhiAtom
import Salt.Maynard.GFunction

/-!
# W4-1 (RelEngines) — constant-FREE relative engines

Card W4-1 of the `explicit12` wave-4 dispatch
(`docs/blueprints/explicit12-design.md`). Each of the three theorems below is
a TRUNCATION of an already-landed proof (`Salt.Twelve.marked_sqf_phi` in
`W3Prep.lean`, and `Salt.Twelve.marked_sqf_g` / `Salt.Twelve.budget_moment_g`
in `BudgetMomentG.lean`), stopping BEFORE the atom-constant step
(`Salt.Maynard.phiAtom_upper_lossy`) so that the bound is stated relative to
the a=0 crude atom `Salt.Maynard.phiAtomSum z W'` instead of an opaque
`∃ c, ...` constant. No `∃` appears anywhere; every coefficient is a literal
(`1`, `2`, `4/D`).

Because the helper lemmas used by the landed proofs are `private` to their
own files, the small amount of shared machinery (log/reindex facts, the
`1/g` divisor expansion, the Euler tail bound) is re-derived here verbatim.
-/

open Finset

namespace Salt.Twelve

open Salt.Maynard

/-! ## Local helpers, re-derived from `Salt.Twelve.W3Prep` (there: `private`) -/

private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma log_nat_mono_le {m n : ℕ} (h : m ≤ n) :
    Real.log (m : ℝ) ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simpa using log_nat_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast h)

private lemma reindex_coprime {s r : ℕ} (hrsf : Squarefree r) (hsr : s ∣ r) :
    r = s * (r / s) ∧ Nat.Coprime s (r / s) := by
  have hrs : r = s * (r / s) := by
    rw [mul_comm]; exact (Nat.div_mul_cancel hsr).symm
  have hsf : Squarefree (s * (r / s)) := hrs ▸ hrsf
  exact ⟨hrs, (Nat.squarefree_mul_iff.mp hsf).1⟩

private lemma totient_reindex {s r : ℕ} (hrsf : Squarefree r) (hsr : s ∣ r) :
    (Nat.totient r : ℝ) = (Nat.totient s : ℝ) * (Nat.totient (r / s) : ℝ) := by
  obtain ⟨hrs, hcop⟩ := reindex_coprime hrsf hsr
  have heq : Nat.totient r = Nat.totient s * Nat.totient (r / s) := by
    conv_lhs => rw [hrs]
    exact Nat.totient_mul hcop
  exact_mod_cast heq

/-! ## Local helpers, re-derived from `Salt.Twelve.BudgetMomentG` (there: `private`) -/

/-- Any prime dividing a number coprime to `W'` exceeds `D`. -/
private lemma box_prime_gt {W' D r : ℕ} (hrcop : r.Coprime W')
    (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) {p : ℕ}
    (hpp : p.Prime) (hpr : p ∣ r) : D < p := by
  refine hD p hpp (fun hpW => ?_)
  have : p ∣ 1 := hrcop ▸ Nat.dvd_gcd hpr hpW
  exact hpp.one_lt.ne' (Nat.dvd_one.mp this)

/-- `g` is multiplicative on a coprime factorization. -/
private lemma gMult_mul_coprime {s b : ℕ} (hcop : Nat.Coprime s b) :
    gMult (s * b) = gMult s * gMult b := by
  rw [gMult, gMult, gMult, Nat.Coprime.primeFactors_mul hcop,
    Finset.prod_union hcop.disjoint_primeFactors]

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

/-- Product-versus-sum: if the `aₓ ≥ 0` sum to at most `1/2`, then
`∏(1 + aₓ) ≤ 1 + 2∑aₓ`. -/
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

/-- **The Euler tail (nontrivial moduli).** For `D ≥ 3`, the sum of
`h(d)/φ(d) = ∏_{p∣d}((p−1)(p−2))⁻¹` over nontrivial squarefree moduli `< M`
with all prime factors `> D` is at most `2/(D−1)`. -/
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
`∑_{d < M, nice} ∏_{p∣d}((p−1)(p−2))⁻¹ ≤ 2`. -/
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

/-- `phiAtomSum` is nonnegative (a sum of nonnegative terms). -/
private lemma phiAtomSum_nonneg (z W' : ℕ) : 0 ≤ Salt.Maynard.phiAtomSum z W' := by
  unfold Salt.Maynard.phiAtomSum
  exact Finset.sum_nonneg fun r _ => by positivity

/-! ## `marked_sqf_phi_rel`

Truncation of `Salt.Twelve.marked_sqf_phi`'s proof (`W3Prep.lean`): steps 1–6
(bound `(log r)^a` by `(log z)^a`, factor it out, apply the exact reindex
identity `1/φ(r) = (1/φ(s))·(1/φ(r/s))`, reindex `r ↦ r/s` injectively, and
extend the image to `sqfCop z W'`), STOPPING there instead of continuing on
to invoke `Salt.Maynard.phiAtom_upper_lossy` for an opaque `(W',a)`-constant. -/

theorem marked_sqf_phi_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (a : ℕ) (s z : ℕ) (hs : 0 < s) (hz : 2 ≤ z) :
    (∑ r ∈ (Finset.range z).filter
        (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ a / (Nat.totient r : ℝ))
      ≤ (1 / (Nat.totient s : ℝ)) * (Real.log z) ^ a
          * Salt.Maynard.phiAtomSum z W' := by
  -- `hW'`, `hpos`, `hs`, `hz` are not needed once the atom-constant step is
  -- dropped; keep them referenced (frozen signature) to silence the linter.
  have _hW' := hW'
  have _hpos := hpos
  have _hs := hs
  have _hz := hz
  classical
  set S : Finset ℕ :=
    (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r) with hSdef
  have hsinv0 : 0 ≤ (1 / (Nat.totient s : ℝ)) := by positivity
  -- Step 1: bound `(log r)^a` by `(log z)^a` termwise.
  have step1 : ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ) := by
    apply Finset.sum_le_sum
    intro r hr
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrz, _hrsf, _hrW', _hsr⟩ := hr
    have hlogr0 : 0 ≤ Real.log (r : ℝ) := log_nat_nonneg r
    have hlogrz : Real.log (r : ℝ) ≤ Real.log (z : ℝ) := log_nat_mono_le hrz.le
    have hpow : (Real.log r) ^ a ≤ (Real.log z) ^ a := pow_le_pow_left₀ hlogr0 hlogrz a
    exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  -- Step 2: factor out the (constant, over `S`) `(log z)^a`.
  have step2 : ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ)
      = (Real.log z) ^ a * ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => by ring)
  -- Step 3: the exact reindex identity `1/φ(r) = (1/φ(s)) * (1/φ(r/s))`.
  have step3 : ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ)
      = (1 / (Nat.totient s : ℝ)) * ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / s) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨_hrz, hrsf, _hrW', hsr⟩ := hr
    rw [totient_reindex hrsf hsr, ← one_div_mul_one_div]
  -- Step 4: reindex the sum over `S` (via `r ↦ r / s`) as a sum over its image.
  have hinj : Set.InjOn (fun r => r / s) (S : Set ℕ) := by
    intro r1 hr1 r2 hr2 heq
    rw [Finset.mem_coe, hSdef, Finset.mem_filter, Finset.mem_range] at hr1 hr2
    obtain ⟨hr1z, hr1sf, hr1W', hsr1⟩ := hr1
    obtain ⟨hr2z, hr2sf, hr2W', hsr2⟩ := hr2
    have e1 : r1 = s * (r1 / s) := (reindex_coprime hr1sf hsr1).1
    have e2 : r2 = s * (r2 / s) := (reindex_coprime hr2sf hsr2).1
    have heq' : r1 / s = r2 / s := heq
    rw [e1, e2, heq']
  have step4 : ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / s) : ℝ)
      = ∑ u ∈ S.image (fun r => r / s), (1:ℝ) / (Nat.totient u : ℝ) :=
    (Finset.sum_image (f := fun u => (1:ℝ) / (Nat.totient u : ℝ)) hinj).symm
  -- Step 5: extend the sum to `sqfCop z W'` (a superset, nonnegative summands).
  have hsub : S.image (fun r => r / s) ⊆ Salt.Maynard.sqfCop z W' := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨r, hr, hru⟩ := hu
    rw [hSdef, Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrz, hrsf, hrW', hsr⟩ := hr
    obtain ⟨hreq, -⟩ := reindex_coprime hrsf hsr
    have hru' : r / s = u := hru
    have hudvd : u ∣ r := by
      refine ⟨s, ?_⟩
      rw [hreq, hru']
      ring
    have hult : u < z := by
      have hle : u ≤ r := by
        rw [← hru']; exact Nat.div_le_self r s
      omega
    have husf : Squarefree u := hrsf.squarefree_of_dvd hudvd
    have huW' : u.Coprime W' := hrW'.coprime_dvd_left hudvd
    unfold Salt.Maynard.sqfCop
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hult, husf, huW'⟩
  have step5 : ∑ u ∈ S.image (fun r => r / s), (1:ℝ) / (Nat.totient u : ℝ)
      ≤ ∑ u ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient u : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro u _ _
    positivity
  -- Step 6: `sqfCop`-sum is `phiAtomSum` by definition.
  have step6 : ∑ u ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient u : ℝ)
      = Salt.Maynard.phiAtomSum z W' := rfl
  have hlogz0 : 0 ≤ (Real.log z : ℝ) ^ a := pow_nonneg (log_nat_nonneg z) a
  have main : ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := by
    calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
        ≤ ∑ r ∈ S, (Real.log z) ^ a / (Nat.totient r : ℝ) := step1
      _ = (Real.log z) ^ a * ∑ r ∈ S, (1:ℝ) / (Nat.totient r : ℝ) := step2
      _ = (Real.log z) ^ a
            * ((1 / (Nat.totient s : ℝ)) * ∑ r ∈ S, (1:ℝ) / (Nat.totient (r / s) : ℝ)) := by
          rw [step3]
      _ = (Real.log z) ^ a
            * ((1 / (Nat.totient s : ℝ))
                * ∑ u ∈ S.image (fun r => r / s), (1:ℝ) / (Nat.totient u : ℝ)) := by
          rw [step4]
      _ ≤ (Real.log z) ^ a
            * ((1 / (Nat.totient s : ℝ))
                * ∑ u ∈ Salt.Maynard.sqfCop z W', (1:ℝ) / (Nat.totient u : ℝ)) := by
          have := mul_le_mul_of_nonneg_left step5 hsinv0
          exact mul_le_mul_of_nonneg_left this hlogz0
      _ = (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := by
          rw [step6]
  calc ∑ r ∈ S, (Real.log r) ^ a / (Nat.totient r : ℝ)
      ≤ (Real.log z) ^ a * ((1 / (Nat.totient s : ℝ)) * Salt.Maynard.phiAtomSum z W') := main
    _ = (1 / (Nat.totient s : ℝ)) * (Real.log z) ^ a * Salt.Maynard.phiAtomSum z W' := by ring

/-! ## `marked_sqf_g_rel`

Truncation of `Salt.Twelve.marked_sqf_g`'s proof (`BudgetMomentG.lean`): the
`r = s·b` reindex/multiplicativity step (Step A, unchanged) followed by the
divisor-swap bound on `∑_{b} 1/g(b)` (Step B), with the constant-bearing
`marked_sqf_phi` call replaced by `marked_sqf_phi_rel`, landing the tail at
`2 · phiAtomSum z W'` (the `2` is the same `exp(2/D) ≤ 2`-shaped Euler-tail
factor as the landed proof, from `tail_full_le`). -/

theorem marked_sqf_g_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (a : ℕ) (D s z : ℕ) (hD : 3 ≤ D)
    (hDp : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) (hs : 0 < s) (hz : 2 ≤ z) :
    (∑ r ∈ (Finset.range z).filter
        (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ a / (gMult r : ℝ))
      ≤ (1 / (gMult s : ℝ)) * 2 * (Real.log z) ^ a
          * Salt.Maynard.phiAtomSum z W' := by
  -- `hs` is not needed (the reindex/divisor-swap argument is `s`-uniform,
  -- with the even-`s` degeneracy self-consistent via `x/0 = 0`); keep it
  -- referenced (frozen signature) to silence the linter.
  have _hs := hs
  classical
  set Fs := (Finset.range z).filter
    (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r) with hFs
  set B := (Finset.range z).filter
    (fun b => Squarefree b ∧ b.Coprime W' ∧ b.Coprime s) with hB
  have hlogz0 : (0 : ℝ) ≤ Real.log z :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  -- Step A (unchanged from `marked_sqf_g`): reindex `r = s·b`, factor
  -- `g(r) = g(s)·g(b)`, bound `(log r)^a ≤ (log z)^a`.
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
  -- Step B (relative): `∑_{b∈B} 1/g(b) ≤ 2 · phiAtomSum z W'`.
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum z W' := phiAtomSum_nonneg z W'
  have hStepB : ∑ b ∈ B, (gMult b : ℝ)⁻¹ ≤ 2 * Salt.Maynard.phiAtomSum z W' := by
    have hexp : ∀ b ∈ B, (gMult b : ℝ)⁻¹
        = ∑ d ∈ Finset.range (z + 1),
            if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * (Nat.totient b : ℝ)⁻¹ else 0 := by
      intro b hb
      rw [hB, Finset.mem_filter, Finset.mem_range] at hb
      obtain ⟨hbz, hbsf, hbW', _⟩ := hb
      have hp3 : ∀ p ∈ b.primeFactors, 3 ≤ p := by
        intro p hp
        have := box_prime_gt hbW' hDp (Nat.prime_of_mem_primeFactors hp)
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
        box_prime_gt hbW' hDp (Nat.prime_of_mem_primeFactors hp)
          (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdb)⟩
    rw [← Finset.sum_filter_of_ne hvanish]
    have hbound : ∀ d ∈ (Finset.range (z + 1)).filter
        (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
        (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
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
        have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
        exact inv_nonneg.mpr (by linarith)
      have hmarked : ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
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
          _ ≤ (1 / (Nat.totient d : ℝ)) * (Real.log z) ^ 0
                * Salt.Maynard.phiAtomSum z W' :=
              marked_sqf_phi_rel W' hW' hpos 0 d z hd0 hz
          _ = (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
              rw [one_div, pow_zero, mul_one]
      calc (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ∑ b ∈ B, (if d ∣ b then (Nat.totient b : ℝ)⁻¹ else 0)
          ≤ (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
              * ((Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W') :=
            mul_le_mul_of_nonneg_left hmarked hHnn
        _ = (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
            rw [← h_over_phi hdsf]; ring
    calc ∑ d ∈ (Finset.range (z + 1)).filter
          (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
          (∑ b ∈ B, if d ∣ b then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (Nat.totient b : ℝ)⁻¹ else 0)
        ≤ ∑ d ∈ (Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
            (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' :=
          Finset.sum_le_sum hbound
      _ = (∑ d ∈ (Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p),
            ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
          rw [Finset.sum_mul]
      _ ≤ 2 * Salt.Maynard.phiAtomSum z W' :=
          mul_le_mul_of_nonneg_right (tail_full_le D (z + 1) hD (by omega)) hPASnn
  calc ∑ r ∈ Fs, (Real.log r) ^ a / (gMult r : ℝ)
      ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * ∑ b ∈ B, (gMult b : ℝ)⁻¹ := hStepA
    _ ≤ (gMult s : ℝ)⁻¹ * (Real.log z) ^ a * (2 * Salt.Maynard.phiAtomSum z W') := by
        exact mul_le_mul_of_nonneg_left hStepB
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hlogz0 a))
    _ = 1 / (gMult s : ℝ) * 2 * (Real.log z) ^ a * Salt.Maynard.phiAtomSum z W' := by
        rw [one_div]; ring

/-! ## `g_gap_rel`

Truncation of `Salt.Twelve.budget_moment_g`'s proof (`BudgetMomentG.lean`):
only the UPPER half of the two-sided sandwich (the `LOWER` half, `φ-sum ≤
g-sum`, needs `box_g_pos`/`gMult_le_totient` positivity and is not part of
this frozen deliverable). The `d ≠ 1` divisor tail is bounded via
`marked_sqf_phi_rel` instead of the constant-bearing `marked_sqf_phi`, and
since `marked_sqf_phi_rel` at `a = 0` carries no `log z`/`log R` factor at
all, the tail lands directly at `(4/D)·phiAtomSum z W'` with no `log R`
multiplier (unlike the landed `Cg/D · log R` correction). -/

theorem g_gap_rel (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (c b : ℕ) (D z R : ℕ) (hD : 3 ≤ D)
    (hDp : ∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p)
    (hz : 2 ≤ z) (hzR : z ≤ R) (hlR : 1 ≤ Real.log R) :
    (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
        (Real.log r / Real.log R) ^ c
          * ((Real.log z - Real.log r) / Real.log R) ^ b / (gMult r : ℝ))
      ≤ (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W'),
          (Real.log r / Real.log R) ^ c
            * ((Real.log z - Real.log r) / Real.log R) ^ b
            / (Nat.totient r : ℝ))
        + (4 / (D : ℝ)) * Salt.Maynard.phiAtomSum z W' := by
  classical
  set F := (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W') with hF
  set w : ℕ → ℝ := fun r => (Real.log r / Real.log R) ^ c
    * ((Real.log z - Real.log r) / Real.log R) ^ b with hw
  have hLpos : (0 : ℝ) < Real.log R := lt_of_lt_of_le zero_lt_one hlR
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
  have hPASnn : 0 ≤ Salt.Maynard.phiAtomSum z W' := phiAtomSum_nonneg z W'
  -- `w r / g(r) = w r / φ(r) + tail`, `tail ≤ (4/D) · phiAtomSum z W'`.
  have hexp : ∀ r ∈ F, w r / (gMult r : ℝ)
      = ∑ d ∈ Finset.range (z + 1),
          if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
    intro r hr
    obtain ⟨_hrz, hrsf, hrW'⟩ := hmemF r hr
    have hp3 : ∀ p ∈ r.primeFactors, 3 ≤ p := by
      intro p hp
      have := box_prime_gt hrW' hDp (Nat.prime_of_mem_primeFactors hp)
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
      box_prime_gt hrW' hDp (Nat.prime_of_mem_primeFactors hp)
        (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdr)⟩
  have hbound : ∀ d ∈ ((Finset.range (z + 1)).filter
      (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
      (∑ r ∈ F, if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
        * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
        ≤ (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
            * Salt.Maynard.phiAtomSum z W' := by
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
      have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
      exact inv_nonneg.mpr (by linarith)
    have hmarked : ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0)
        ≤ (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
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
        _ ≤ (1 / (Nat.totient d : ℝ)) * (Real.log z) ^ 0 * Salt.Maynard.phiAtomSum z W' :=
            marked_sqf_phi_rel W' hW' hpos 0 d z hd0 hz
        _ = (Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W' := by
            rw [one_div, pow_zero, mul_one]
    calc (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * ∑ r ∈ F, (if d ∣ r then w r * (Nat.totient r : ℝ)⁻¹ else 0)
        ≤ (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * ((Nat.totient d : ℝ)⁻¹ * Salt.Maynard.phiAtomSum z W') :=
          mul_le_mul_of_nonneg_left hmarked hHnn
      _ = (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
            * Salt.Maynard.phiAtomSum z W' := by
          rw [← h_over_phi hdsf]; ring
  have htail :
      (∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
        if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
          * (w r * (Nat.totient r : ℝ)⁻¹) else 0)
      ≤ (4 : ℝ) / D * Salt.Maynard.phiAtomSum z W' := by
    have hDR : (3 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
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
            (∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' :=
          Finset.sum_le_sum hbound
      _ = (∑ d ∈ ((Finset.range (z + 1)).filter
            (fun d => Squarefree d ∧ ∀ p ∈ d.primeFactors, D < p)).erase 1,
            ∏ p ∈ d.primeFactors, (((p : ℝ) - 1) * ((p : ℝ) - 2))⁻¹)
              * Salt.Maynard.phiAtomSum z W' := by
          rw [Finset.sum_mul]
      _ ≤ (2 / ((D : ℝ) - 1)) * Salt.Maynard.phiAtomSum z W' :=
          mul_le_mul_of_nonneg_right (tail_erase_le D (z + 1) hD) hPASnn
      _ ≤ (4 : ℝ) / D * Salt.Maynard.phiAtomSum z W' := by
          have hfrac : (2 : ℝ) / ((D : ℝ) - 1) ≤ 4 / (D : ℝ) := by
            rw [div_le_div_iff₀ hDm1 hDpos]; linarith
          exact mul_le_mul_of_nonneg_right hfrac hPASnn
  have heq : ∑ r ∈ F, w r / (gMult r : ℝ)
      = (∑ r ∈ F, w r / (Nat.totient r : ℝ))
        + ∑ d ∈ (Finset.range (z + 1)).erase 1, ∑ r ∈ F,
          if d ∣ r then (∏ p ∈ d.primeFactors, ((p : ℝ) - 2)⁻¹)
            * (w r * (Nat.totient r : ℝ)⁻¹) else 0 := by
    rw [hswap, ← hsplit]
  rw [heq]
  linarith [htail]

end Salt.Twelve
