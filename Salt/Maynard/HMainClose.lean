/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Tensor
import Salt.Maynard.Overshoot
import Salt.Maynard.HMain
import Salt.Maynard.HOmit

/-!
# C3b — closing `H_main` (re-threaded overshoot 3/8 + coprimality 1/8)

The committed `H_main_bound` (`Salt/Maynard/HMain.lean`) leaves the two analytic
loss fractions `hOver`, `hCop` as `(1/4)`-hypotheses.  The `(1/4, 1/4)` split is
too tight: the genuine overshoot is `(k−1)/(k−T)·(A₁⁽¹⁾/A₁)·A₁^{k-1} > (1/4)·A₁^{k-1}`.
Here we re-thread to `(3/8, 1/8)` (sum still `1/2`) and close *both* leaves:

* `hOver_bound` — dim-`(k-1)` first-moment Markov (mirror of `Overshoot.overshoot_le`
  over `univ.erase m`, threshold `k−T`) `≤ (3/8)·A₁^{k-1}`, given `A₁⁽¹⁾ ≤ (1/4)·A₁`
  (`hA11`, carried as a narrow transfer atom) and `3T ≤ k` (`hTk`).
* `hCop_bound` — pairwise-coprimality mass `≤ (1/8)·A₁^{k-1}`, via a genuine
  two-coordinate box factorization + the per-prime reindex `sqfCop_dvd_reindex`,
  union-bounded over the `k(k-1)` ordered off-`m` pairs and the primes `p > D₀`,
  with `∑_{p>D₀}(p−1)⁻² ≤ 2/D₀` (`inv_sq_tele`).  Fully concrete.
* `H_main_bound_closed` — re-runs the `sum_sdiff` assembly of `H_main_bound` with
  the `(3/8, 1/8)` fractions; plugs into the `H_main` slot of `s2_tensor_lower`.

This module lives downstream of both `HMain` and `HOmit` (the reindex kit is in
`HOmit`, which already imports `HMain`, so it cannot be re-imported into `HMain`).
-/

open Finset

namespace Salt.Maynard

/-- Re-declared private copy of `CollisionQuant.inv_sq_tele` / `HOmit.inv_sq_tele`
(both `private`): telescoping tail `∑_{a < n ≤ b} (n−1)⁻² ≤ (a−1)⁻¹ − (b−1)⁻¹`. -/
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

/-- The prime set carrying the coprimality collisions: prime factors of `sqfCop`
elements.  All exceed `D₀ k` and are `≤ D₀ k + R0 k R T`, so `∑ (p−1)⁻² ≤ 2/D₀`. -/
private noncomputable def PScop (k R : ℕ) (T : ℝ) : Finset ℕ :=
  (sqfCop (R0 k R T) (W k)).biUnion (fun am => am.primeFactors)

/-- The telescoping tail bound `∑_{p ∈ PScop} (p−1)⁻² ≤ 2/D₀` (mirror of the
`H_omit_bound` step-6 computation). -/
private lemma PScop_tail (k R : ℕ) (T : ℝ) (hD2 : 2 ≤ D₀ k) :
    (∑ p ∈ PScop k R T, (((p : ℝ) - 1)⁻¹) ^ 2) ≤ 2 / (D₀ k : ℝ) := by
  have hDk_pos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by omega
    exact_mod_cast this
  have hsub : PScop k R T ⊆ Finset.Icc (D₀ k + 1) (D₀ k + R0 k R T) := by
    intro p hp
    rw [PScop, Finset.mem_biUnion] at hp
    obtain ⟨am, hamS, hpf⟩ := hp
    have hpp := Nat.prime_of_mem_primeFactors hpf
    have hpam := Nat.dvd_of_mem_primeFactors hpf
    have hcop : Nat.Coprime am (W k) := by
      rw [sqfCop, Finset.mem_filter] at hamS; exact hamS.2.2
    have hpD : D₀ k < p := D₀_lt_of_prime_dvd_coprime hcop hpp hpam
    have hamlt : am < R0 k R T := by
      rw [sqfCop, Finset.mem_filter, Finset.mem_range] at hamS; exact hamS.1
    have ham0 : 0 < am := by
      rw [sqfCop, Finset.mem_filter] at hamS; exact Nat.pos_of_ne_zero hamS.2.1.ne_zero
    have hple : p ≤ am := Nat.le_of_dvd ham0 hpam
    rw [Finset.mem_Icc]; omega
  have hmono : (∑ p ∈ PScop k R T, (((p : ℝ) - 1)⁻¹) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) (D₀ k + R0 k R T), (((n : ℝ) - 1)⁻¹) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
  have htel := inv_sq_tele (D₀ k) hD2 (D₀ k + R0 k R T) (Nat.le_add_right _ _)
  have hbpos : (0 : ℝ) ≤ (((D₀ k + R0 k R T : ℕ) : ℝ) - 1)⁻¹ := by
    apply inv_nonneg.mpr
    have : (1 : ℝ) ≤ ((D₀ k + R0 k R T : ℕ) : ℝ) := by
      have : 1 ≤ D₀ k + R0 k R T := by omega
      exact_mod_cast this
    linarith
  have hfin : ((D₀ k : ℝ) - 1)⁻¹ ≤ 2 / (D₀ k : ℝ) := by
    have h1 : (0 : ℝ) < (D₀ k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD2
      linarith
    have key : 2 / (D₀ k : ℝ) - ((D₀ k : ℝ) - 1)⁻¹
        = ((D₀ k : ℝ) - 2) / ((D₀ k : ℝ) * ((D₀ k : ℝ) - 1)) := by
      field_simp; ring
    have hnn : 0 ≤ 2 / (D₀ k : ℝ) - ((D₀ k : ℝ) - 1)⁻¹ := by
      rw [key]
      apply div_nonneg _ (mul_pos hDk_pos h1).le
      have : (2 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD2
      linarith
    linarith
  calc (∑ p ∈ PScop k R T, (((p : ℝ) - 1)⁻¹) ^ 2)
      ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) (D₀ k + R0 k R T), (((n : ℝ) - 1)⁻¹) ^ 2 := hmono
    _ ≤ ((D₀ k : ℝ) - 1)⁻¹ - (((D₀ k + R0 k R T : ℕ) : ℝ) - 1)⁻¹ := htel
    _ ≤ ((D₀ k : ℝ) - 1)⁻¹ := by linarith
    _ ≤ 2 / (D₀ k : ℝ) := hfin

/-- On `hmBox`, the off-`m` weight `hmW` equals the full `univ`-product (the
`m`-fiber `= {1}` contributes `1`). -/
private lemma hmW_prod_univ (k R : ℕ) (m : Fin k) (T : ℝ) {u : Fin k → ℕ}
    (hu : u ∈ hmBox k R m T) :
    hmW k R m T u = ∏ j, (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) := by
  have hg1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  simp only [hmBox, Fintype.mem_piFinset] at hu
  have hum : u m = 1 := by have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
  rw [hmW, ← Finset.mul_prod_erase Finset.univ
        (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ m),
      hum, hg1, one_mul]

/-! ## Leaf `hCop` — pairwise-coprimality mass (two-coordinate reindex) -/

/-- **Two-restricted-coordinate box factorization.**  Summing the box weight over
`hmBox` with two distinct off-`m` coordinates `i₀, j₀` both restricted to multiples
of `p` factors as `Q(p)·Q(p)·A₁^{k-3}`, where `Q(p) = ∑_{x∈sqfCop, p∣x} fWt²/φ`.
Mirror of `HOmit.hmBox_restrict_coord` with two guarded fibers. -/
private lemma hmBox_restrict_two (k R : ℕ) (m : Fin k) (T : ℝ) (p : ℕ)
    (i₀ j₀ : Fin k) (hi₀ : i₀ ≠ m) (hj₀ : j₀ ≠ m) (hij : i₀ ≠ j₀) :
    (∑ u ∈ hmBox k R m T, if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0)
      = (∑ x ∈ sqfCop (R0 k R T) (W k),
            if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
        * (∑ x ∈ sqfCop (R0 k R T) (W k),
            if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
        * (A1 k R (W k) T) ^ (k - 3) := by
  classical
  have hG1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  have hsummand : ∀ u ∈ hmBox k R m T,
      (if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0)
        = ∏ j, (if j = i₀ then
                  (if p ∣ u j then (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) else 0)
                else if j = j₀ then
                  (if p ∣ u j then (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) else 0)
                else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) := by
    intro u hu
    by_cases hdi : p ∣ u i₀
    · by_cases hdj : p ∣ u j₀
      · rw [if_pos ⟨hdi, hdj⟩, hmW_prod_univ k R m T hu]
        apply Finset.prod_congr rfl
        intro j _
        by_cases h1 : j = i₀
        · subst h1; rw [if_pos rfl, if_pos hdi]
        · rw [if_neg h1]
          by_cases h2 : j = j₀
          · subst h2; rw [if_pos rfl, if_pos hdj]
          · rw [if_neg h2]
      · rw [if_neg (fun h => hdj h.2)]
        exact (Finset.prod_eq_zero (Finset.mem_univ j₀) (by
          rw [if_neg (Ne.symm hij), if_pos rfl, if_neg hdj])).symm
    · rw [if_neg (fun h => hdi h.1)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (by
        rw [if_pos rfl, if_neg hdi])).symm
  rw [Finset.sum_congr rfl hsummand]
  simp only [hmBox]
  rw [← Finset.prod_univ_sum
        (fun i : Fin k => if i = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
        (fun j x => if j = i₀ then
                      (if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
                    else if j = j₀ then
                      (if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
                    else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
  have hfac : ∀ j : Fin k,
      (∑ x ∈ (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k)),
          if j = i₀ then (if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
          else if j = j₀ then (if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
          else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
        = if j = i₀ then
            (∑ x ∈ sqfCop (R0 k R T) (W k),
                if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
          else if j = j₀ then
            (∑ x ∈ sqfCop (R0 k R T) (W k),
                if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
          else (if j = m then (1 : ℝ) else A1 k R (W k) T) := by
    intro j
    by_cases h1 : j = i₀
    · have hjm : j ≠ m := by rw [h1]; exact hi₀
      rw [if_neg hjm, if_pos h1]
      exact Finset.sum_congr rfl (fun x _ => by rw [if_pos h1])
    · rw [if_neg h1]
      by_cases h2 : j = j₀
      · have hjm : j ≠ m := by rw [h2]; exact hj₀
        rw [if_neg hjm, if_pos h2]
        exact Finset.sum_congr rfl (fun x _ => by rw [if_neg h1, if_pos h2])
      · rw [if_neg h2]
        by_cases hjm : j = m
        · rw [if_pos hjm, if_pos hjm, Finset.sum_singleton, if_neg h1, if_neg h2]; exact hG1
        · rw [if_neg hjm, if_neg hjm, A1]
          exact Finset.sum_congr rfl (fun x _ => by rw [if_neg h1, if_neg h2])
  rw [Finset.prod_congr rfl (fun j _ => hfac j)]
  set Qs : ℝ := ∑ x ∈ sqfCop (R0 k R T) (W k),
      if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0 with hQs
  -- evaluate the product: pull out `i₀`, `j₀`, `m`, rest is `A₁^{k-3}`.
  rw [← Finset.mul_prod_erase Finset.univ
        (fun j => if j = i₀ then Qs else if j = j₀ then Qs
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) (Finset.mem_univ i₀),
      if_pos rfl]
  have hj₀_mem : j₀ ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j₀⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i₀)
        (fun j => if j = i₀ then Qs else if j = j₀ then Qs
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) hj₀_mem,
      if_neg (Ne.symm hij), if_pos rfl]
  have hm_mem : m ∈ (Finset.univ.erase i₀).erase j₀ :=
    Finset.mem_erase.mpr ⟨Ne.symm hj₀,
      Finset.mem_erase.mpr ⟨Ne.symm hi₀, Finset.mem_univ m⟩⟩
  rw [← Finset.mul_prod_erase ((Finset.univ.erase i₀).erase j₀)
        (fun j => if j = i₀ then Qs else if j = j₀ then Qs
                  else (if j = m then (1 : ℝ) else A1 k R (W k) T)) hm_mem,
      if_neg (Ne.symm hi₀), if_neg (Ne.symm hj₀), if_pos rfl]
  rw [Finset.prod_congr rfl (fun j hj => by
        have hjm := Finset.ne_of_mem_erase hj
        have hj' := Finset.mem_of_mem_erase hj
        have hjj₀ := Finset.ne_of_mem_erase hj'
        have hji₀ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj')
        rw [if_neg hji₀, if_neg hjj₀, if_neg hjm]),
      Finset.prod_const,
      Finset.card_erase_of_mem hm_mem, Finset.card_erase_of_mem hj₀_mem,
      Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin,
      show k - 1 - 1 - 1 = k - 3 from by omega]
  ring

/-- Per-prime two-coordinate collision bound: `Q(p)·Q(p)·A₁^{k-3} ≤ (p−1)⁻²·A₁^{k-1}`
(via the two-coordinate factorization and `sqfCop_dvd_reindex` with `g = fWt²`). -/
private lemma pair_prime_bound (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 3 ≤ k)
    (p : ℕ) (hp : p.Prime) (i₀ j₀ : Fin k) (hi₀ : i₀ ≠ m) (hj₀ : j₀ ≠ m) (hij : i₀ ≠ j₀) :
    (∑ u ∈ hmBox k R m T, if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0)
      ≤ (((p : ℝ) - 1)⁻¹) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
  rw [hmBox_restrict_two k R m T p i₀ j₀ hi₀ hj₀ hij]
  have hAnn := A1_nonneg k R (W k) T
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hQ : (∑ x ∈ sqfCop (R0 k R T) (W k),
        if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
      ≤ ((p : ℝ) - 1)⁻¹ * A1 k R (W k) T := by
    have h := sqfCop_dvd_reindex k R T p hp (fun x => (fWt k R x) ^ 2)
        (fun n => sq_nonneg (fWt k R n)) (fWt_sq_anti k R hR)
    simpa only [A1] using h
  have hQnn : 0 ≤ ∑ x ∈ sqfCop (R0 k R T) (W k),
      if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0 :=
    Finset.sum_nonneg (fun x _ => by
      split_ifs
      · exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      · exact le_rfl)
  have hbnn : 0 ≤ ((p : ℝ) - 1)⁻¹ * A1 k R (W k) T := mul_nonneg (inv_nonneg.mpr hp1.le) hAnn
  calc (∑ x ∈ sqfCop (R0 k R T) (W k),
            if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
        * (∑ x ∈ sqfCop (R0 k R T) (W k),
            if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
        * (A1 k R (W k) T) ^ (k - 3)
      ≤ (((p : ℝ) - 1)⁻¹ * A1 k R (W k) T) * (((p : ℝ) - 1)⁻¹ * A1 k R (W k) T)
          * (A1 k R (W k) T) ^ (k - 3) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul hQ hQ hQnn hbnn) (pow_nonneg hAnn _)
    _ = (((p : ℝ) - 1)⁻¹) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
        rw [show k - 1 = (k - 3) + 2 from by omega, pow_add]; ring

/-- Per-pair coprimality-collision bound: the mass of `hmBox` where two distinct
off-`m` coordinates `i₀, j₀` share a common factor is `≤ (2/D₀)·A₁^{k-1}`.  Prime
decomposition + `pair_prime_bound` + `PScop_tail`. -/
private lemma pair_cop_bound (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 3 ≤ k)
    (hD2 : 2 ≤ D₀ k) (i₀ j₀ : Fin k) (hi₀ : i₀ ≠ m) (hj₀ : j₀ ≠ m) (hij : i₀ ≠ j₀) :
    (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u i₀) (u j₀) then hmW k R m T u else 0)
      ≤ (2 / (D₀ k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) := by
  classical
  have hAnn := A1_nonneg k R (W k) T
  have hApow : (0 : ℝ) ≤ (A1 k R (W k) T) ^ (k - 1) := pow_nonneg hAnn _
  have hnn0 : ∀ (q : ℕ) (u : Fin k → ℕ),
      0 ≤ (if q ∣ u i₀ ∧ q ∣ u j₀ then hmW k R m T u else 0) := by
    intro q u
    split_ifs <;> first | exact hmW_nonneg k R m T u | exact le_rfl
  -- Step 1: prime decomposition over `PScop`.
  have decomp : (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u i₀) (u j₀) then hmW k R m T u else 0)
      ≤ ∑ p ∈ PScop k R T,
          (∑ u ∈ hmBox k R m T, if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0) := by
    calc (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u i₀) (u j₀) then hmW k R m T u else 0)
        ≤ ∑ u ∈ hmBox k R m T,
            ∑ p ∈ PScop k R T, (if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0) := by
          apply Finset.sum_le_sum
          intro u hu
          by_cases hc : ¬ Nat.Coprime (u i₀) (u j₀)
          · rw [if_pos hc]
            have hgcd : Nat.gcd (u i₀) (u j₀) ≠ 1 := hc
            obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hgcd
            have hpi : p ∣ u i₀ := hpg.trans (Nat.gcd_dvd_left _ _)
            have hpj : p ∣ u j₀ := hpg.trans (Nat.gcd_dvd_right _ _)
            have hui₀S : u i₀ ∈ sqfCop (R0 k R T) (W k) := by
              simp only [hmBox, Fintype.mem_piFinset] at hu
              have := hu i₀; rwa [if_neg hi₀] at this
            have hui₀0 : u i₀ ≠ 0 := by
              rw [sqfCop, Finset.mem_filter] at hui₀S; exact hui₀S.2.1.ne_zero
            have hpmem : p ∈ PScop k R T := by
              rw [PScop, Finset.mem_biUnion]
              exact ⟨u i₀, hui₀S, Nat.mem_primeFactors.mpr ⟨hpp, hpi, hui₀0⟩⟩
            calc hmW k R m T u
                = (if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0) := (if_pos ⟨hpi, hpj⟩).symm
              _ ≤ ∑ q ∈ PScop k R T, (if q ∣ u i₀ ∧ q ∣ u j₀ then hmW k R m T u else 0) :=
                  Finset.single_le_sum (fun q _ => hnn0 q u) hpmem
          · rw [if_neg hc]
            exact Finset.sum_nonneg (fun q _ => hnn0 q u)
      _ = ∑ p ∈ PScop k R T,
            (∑ u ∈ hmBox k R m T, if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0) :=
          Finset.sum_comm
  -- Step 2: bound each prime term and sum.
  calc (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u i₀) (u j₀) then hmW k R m T u else 0)
      ≤ ∑ p ∈ PScop k R T,
          (∑ u ∈ hmBox k R m T, if p ∣ u i₀ ∧ p ∣ u j₀ then hmW k R m T u else 0) := decomp
    _ ≤ ∑ p ∈ PScop k R T, (((p : ℝ) - 1)⁻¹) ^ 2 * (A1 k R (W k) T) ^ (k - 1) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpp : p.Prime := by
          rw [PScop, Finset.mem_biUnion] at hp
          obtain ⟨am, _, hpf⟩ := hp
          exact Nat.prime_of_mem_primeFactors hpf
        exact pair_prime_bound k R m T hR hk p hpp i₀ j₀ hi₀ hj₀ hij
    _ = (∑ p ∈ PScop k R T, (((p : ℝ) - 1)⁻¹) ^ 2) * (A1 k R (W k) T) ^ (k - 1) := by
        rw [Finset.sum_mul]
    _ ≤ (2 / (D₀ k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) :=
        mul_le_mul_of_nonneg_right (PScop_tail k R T hD2) hApow

/-- **Leaf `hCop`.**  The pairwise-coprimality-failure mass over `hmBox` is
`≤ (1/8)·A₁^{k-1}`.  Union bound over the `k(k−1)` ordered coordinate pairs
(`Finset.univ.offDiag`; pairs touching `m` vanish, as `uₘ = 1`), each bounded by
`pair_cop_bound` (`≤ (2/D₀)·A₁^{k-1}`), with `k(k−1)·(2/D₀) ≤ 1/8` for `D₀ ≥ k³`
and `k ≥ 16`. -/
theorem hCop_bound (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 16 ≤ k) :
    (∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j))),
        hmW k R m T u) ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) := by
  classical
  have hk3 : 3 ≤ k := by omega
  have hk3cube : k ^ 3 ≤ D₀ k := le_max_left _ _
  have hk3ge : 2 ≤ k ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) k)
  have hD2 : 2 ≤ D₀ k := le_trans hk3ge hk3cube
  have hAnn := A1_nonneg k R (W k) T
  have hApow : (0 : ℝ) ≤ (A1 k R (W k) T) ^ (k - 1) := pow_nonneg hAnn _
  have hDk_pos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by omega
    exact_mod_cast this
  have hnnW : ∀ (i j : Fin k) (u : Fin k → ℕ),
      0 ≤ (if ¬ Nat.Coprime (u i) (u j) then hmW k R m T u else 0) := by
    intro i j u
    split_ifs <;> first | exact hmW_nonneg k R m T u | exact le_rfl
  -- membership fact `uₘ = 1` on `hmBox`
  have hum : ∀ u ∈ hmBox k R m T, u m = 1 := by
    intro u hu
    simp only [hmBox, Fintype.mem_piFinset] at hu
    have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
  -- per-pair bound (with the `m`-touching pairs contributing `0`)
  have hpair : ∀ q ∈ (Finset.univ : Finset (Fin k)).offDiag,
      (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u q.1) (u q.2) then hmW k R m T u else 0)
        ≤ (2 / (D₀ k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) := by
    intro q hq
    have hij : q.1 ≠ q.2 := (Finset.mem_offDiag.mp hq).2.2
    by_cases hi : q.1 = m
    · have hz : (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u q.1) (u q.2) then hmW k R m T u else 0)
          = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        rw [hi, hum u hu]
        exact if_neg (not_not.mpr (Nat.coprime_one_left _))
      rw [hz]; positivity
    · by_cases hj : q.2 = m
      · have hz : (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u q.1) (u q.2) then hmW k R m T u else 0)
            = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          rw [hj, hum u hu]
          exact if_neg (not_not.mpr (Nat.coprime_one_right _))
        rw [hz]; positivity
      · exact pair_cop_bound k R m T hR hk3 hD2 q.1 q.2 hi hj hij
  -- union bound over ordered pairs
  rw [Finset.sum_filter]
  calc (∑ u ∈ hmBox k R m T,
          if ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j)) then hmW k R m T u else 0)
      ≤ ∑ u ∈ hmBox k R m T,
          ∑ q ∈ (Finset.univ : Finset (Fin k)).offDiag,
            (if ¬ Nat.Coprime (u q.1) (u q.2) then hmW k R m T u else 0) := by
        apply Finset.sum_le_sum
        intro u _
        by_cases hpw : ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j))
        · rw [if_pos hpw]
          push Not at hpw
          obtain ⟨i, j, hijne, hnc⟩ := hpw
          have hmem : (i, j) ∈ (Finset.univ : Finset (Fin k)).offDiag :=
            Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hijne⟩
          calc hmW k R m T u
              = (if ¬ Nat.Coprime (u (i, j).1) (u (i, j).2) then hmW k R m T u else 0) :=
                (if_pos hnc).symm
            _ ≤ ∑ q ∈ (Finset.univ : Finset (Fin k)).offDiag,
                  (if ¬ Nat.Coprime (u q.1) (u q.2) then hmW k R m T u else 0) :=
                Finset.single_le_sum (fun q _ => hnnW q.1 q.2 u) hmem
        · rw [if_neg hpw]
          exact Finset.sum_nonneg (fun q _ => hnnW q.1 q.2 u)
    _ = ∑ q ∈ (Finset.univ : Finset (Fin k)).offDiag,
          (∑ u ∈ hmBox k R m T, if ¬ Nat.Coprime (u q.1) (u q.2) then hmW k R m T u else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (Fin k)).offDiag,
          (2 / (D₀ k : ℝ)) * (A1 k R (W k) T) ^ (k - 1) :=
        Finset.sum_le_sum hpair
    _ = ((Finset.univ : Finset (Fin k)).offDiag.card : ℝ)
          * ((2 / (D₀ k : ℝ)) * (A1 k R (W k) T) ^ (k - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) := by
        rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
        have hcard : ((k * k - k : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
          have : k * k - k ≤ k * k := Nat.sub_le _ _
          calc ((k * k - k : ℕ) : ℝ) ≤ ((k * k : ℕ) : ℝ) := by exact_mod_cast this
            _ = (k : ℝ) ^ 2 := by push_cast; ring
        have hk16 : (16 : ℝ) * (k : ℝ) ^ 2 ≤ (D₀ k : ℝ) := by
          have h1 : (16 : ℝ) * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
            have hkr : (16 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)) 2]
          have h2 : (k : ℝ) ^ 3 ≤ (D₀ k : ℝ) := by exact_mod_cast hk3cube
          linarith
        have hfrac : ((k * k - k : ℕ) : ℝ) * (2 / (D₀ k : ℝ)) ≤ 1 / 8 := by
          have h2Dnn : (0 : ℝ) ≤ 2 / (D₀ k : ℝ) := by positivity
          calc ((k * k - k : ℕ) : ℝ) * (2 / (D₀ k : ℝ))
              ≤ (k : ℝ) ^ 2 * (2 / (D₀ k : ℝ)) := mul_le_mul_of_nonneg_right hcard h2Dnn
            _ ≤ 1 / 8 := by
                rw [show (k : ℝ) ^ 2 * (2 / (D₀ k : ℝ)) = (2 * (k : ℝ) ^ 2) / (D₀ k : ℝ)
                      from by ring, div_le_iff₀ hDk_pos]
                linarith [hk16]
        calc ((k * k - k : ℕ) : ℝ) * ((2 / (D₀ k : ℝ)) * (A1 k R (W k) T) ^ (k - 1))
            = (((k * k - k : ℕ) : ℝ) * (2 / (D₀ k : ℝ))) * (A1 k R (W k) T) ^ (k - 1) := by ring
          _ ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) :=
              mul_le_mul_of_nonneg_right hfrac hApow

/-! ## Leaf `hOver` — dim-`(k-1)` first-moment Markov overshoot -/

/-- **dim-`(k-1)` first-moment identity over `hmBox`.**  Weighting the off-`m` box
mass by `∑_{i≠m} uVal(uᵢ)` and factoring the single special coordinate gives
`(k−1)·A₁⁽¹⁾·A₁^{k-2}` (the `m`-fiber `= {1}` contributes `1`; the special
coordinate carries `A₁⁽¹⁾`, the remaining `k−2` carry `A₁`).  Mirror of
`Overshoot.moment1_box_eq` restricted to `univ.erase m`. -/
theorem hmBox_moment1 (k R : ℕ) (m : Fin k) (T : ℝ) :
    (∑ u ∈ hmBox k R m T,
        (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) * hmW k R m T u)
      = ((k : ℝ) - 1) * A1_1 k R (W k) T * (A1 k R (W k) T) ^ (k - 2) := by
  classical
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact m.elim0)
  have hg1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  -- On `hmBox`, `hmW` is the full `univ`-product (the `m`-factor is `1`).
  have hmWfull : ∀ u ∈ hmBox k R m T,
      hmW k R m T u = ∏ j, (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) := by
    intro u hu
    simp only [hmBox, Fintype.mem_piFinset] at hu
    have hum : u m = 1 := by have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
    rw [hmW, ← Finset.mul_prod_erase Finset.univ
          (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ m),
        hum, hg1, one_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hF : ∀ i ∈ Finset.univ.erase m,
      (∑ u ∈ hmBox k R m T, uVal k R (u i) * hmW k R m T u)
        = A1_1 k R (W k) T * (A1 k R (W k) T) ^ (k - 2) := by
    intro i hi_mem
    have hi : i ≠ m := Finset.ne_of_mem_erase hi_mem
    have hsummand : ∀ u ∈ hmBox k R m T,
        uVal k R (u i) * hmW k R m T u
          = ∏ j, (if j = i then
                    uVal k R (u j) * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
                  else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) := by
      intro u hu
      rw [hmWfull u hu,
          ← Finset.mul_prod_erase Finset.univ
            (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ i),
          ← Finset.mul_prod_erase Finset.univ
            (fun j => if j = i then
                        uVal k R (u j) * ((fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ))
                      else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ i),
          if_pos rfl,
          Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
      ring
    rw [Finset.sum_congr rfl hsummand]
    simp only [hmBox]
    rw [← Finset.prod_univ_sum
          (fun i' : Fin k => if i' = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
          (fun j x => if j = i then uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                      else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
    have hfac : ∀ j : Fin k,
        (∑ x ∈ (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k)),
            if j = i then uVal k R x * ((fWt k R x) ^ 2 / (Nat.totient x : ℝ))
                     else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
          = if j = i then A1_1 k R (W k) T
            else (if j = m then (1 : ℝ) else A1 k R (W k) T) := by
      intro j
      by_cases hji : j = i
      · subst hji
        have hfiber : (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
            = sqfCop (R0 k R T) (W k) := if_neg hi
        rw [hfiber, if_pos rfl, A1_1]
        apply Finset.sum_congr rfl
        intro x _
        rw [if_pos rfl]; ring
      · rw [if_neg hji]
        by_cases hjm : j = m
        · rw [if_pos hjm, if_pos hjm, Finset.sum_singleton, if_neg hji]; exact hg1
        · rw [if_neg hjm, if_neg hjm, A1]
          exact Finset.sum_congr rfl (fun x _ => by rw [if_neg hji])
    rw [Finset.prod_congr rfl (fun j _ => hfac j),
        ← Finset.mul_prod_erase Finset.univ
          (fun j => if j = i then A1_1 k R (W k) T
                    else (if j = m then (1 : ℝ) else A1 k R (W k) T)) (Finset.mem_univ i),
        if_pos rfl]
    congr 1
    rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj))]
    have hm_mem : m ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨fun h => hi h.symm, Finset.mem_univ m⟩
    rw [← Finset.mul_prod_erase (Finset.univ.erase i)
          (fun j => if j = m then (1 : ℝ) else A1 k R (W k) T) hm_mem, if_pos rfl, one_mul,
        Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
        Finset.prod_const, Finset.card_erase_of_mem hm_mem,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        show k - 1 - 1 = k - 2 from by omega]
  rw [Finset.sum_congr rfl hF, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_sub hk, Nat.cast_one]
  ring

/-- **Leaf `hOver`.**  The dim-`(k-1)` overshoot mass over `hmBox` (the region that
fails the `uVal`-threshold `∑_{i≠m} uVal < k−T`) is `≤ (3/8)·A₁^{k-1}`.  First-moment
Markov (`hmBox_moment1`): on `{k−T ≤ ∑ uVal}`, `1 ≤ (∑ uVal)/(k−T)`, so
`overshoot ≤ (1/(k−T))·(k−1)·A₁⁽¹⁾·A₁^{k-2}`; then `(k−1)/(k−T) ≤ 3/2` (from `hTk`)
and `A₁⁽¹⁾ ≤ (1/4)·A₁` (from `hA11`) give the `3/8`. -/
theorem hOver_bound (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 2 ≤ k)
    (hTk : 3 * T ≤ (k : ℝ))
    (hA11 : A1_1 k R (W k) T ≤ (1 / 4 : ℝ) * A1 k R (W k) T) :
    (∑ u ∈ (hmBox k R m T).filter
        (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
        hmW k R m T u) ≤ (3 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) := by
  classical
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hkT : (0 : ℝ) < (k : ℝ) - T := by linarith
  have hAnn : (0 : ℝ) ≤ A1 k R (W k) T := A1_nonneg _ _ _ _
  have hA1_1nn : (0 : ℝ) ≤ A1_1 k R (W k) T := A1_1_nonneg k R (W k) T hR
  have hApow : (0 : ℝ) ≤ (A1 k R (W k) T) ^ (k - 2) := pow_nonneg hAnn _
  -- Every off-`m` box coordinate is `≥ 1`, so `uVal ≥ 0` on the box.
  have hri1 : ∀ u ∈ hmBox k R m T, ∀ i ∈ Finset.univ.erase m, 1 ≤ u i := by
    intro u hu i hi
    simp only [hmBox, Fintype.mem_piFinset] at hu
    have hmem := hu i
    rw [if_neg (Finset.ne_of_mem_erase hi), sqfCop, Finset.mem_filter, Finset.mem_range] at hmem
    exact Nat.one_le_iff_ne_zero.mpr hmem.2.1.ne_zero
  have hsumnn : ∀ u ∈ hmBox k R m T, 0 ≤ ∑ i ∈ Finset.univ.erase m, uVal k R (u i) :=
    fun u hu => Finset.sum_nonneg (fun i hi => uVal_nonneg_nat k R (u i) (hri1 u hu i hi))
  -- Markov step: bound the overshoot by the moment sum / (k−T).
  calc (∑ u ∈ (hmBox k R m T).filter
            (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
            hmW k R m T u)
      ≤ ∑ u ∈ (hmBox k R m T).filter
            (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)),
            ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) / ((k : ℝ) - T)) * hmW k R m T u := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Finset.mem_filter, not_lt] at hu
        have h1 : 1 ≤ (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) / ((k : ℝ) - T) :=
          (one_le_div hkT).mpr hu.2
        exact le_mul_of_one_le_left (hmW_nonneg k R m T u) h1
    _ ≤ ∑ u ∈ hmBox k R m T,
            ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) / ((k : ℝ) - T)) * hmW k R m T u := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro u hu _
        exact mul_nonneg (div_nonneg (hsumnn u hu) hkT.le) (hmW_nonneg k R m T u)
    _ = (∑ u ∈ hmBox k R m T,
            (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) * hmW k R m T u) / ((k : ℝ) - T) := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun u _ => by ring)
    _ = (((k : ℝ) - 1) * A1_1 k R (W k) T * (A1 k R (W k) T) ^ (k - 2)) / ((k : ℝ) - T) := by
        rw [hmBox_moment1]
    _ ≤ (3 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) := by
        -- `(k−1)/(k−T) ≤ 3/2` and `A₁⁽¹⁾ ≤ (1/4)·A₁`; assemble.
        have hkTb : (k : ℝ) - 1 ≤ (3 / 2 : ℝ) * ((k : ℝ) - T) := by linarith
        have hpow : (A1 k R (W k) T) ^ (k - 1) = (A1 k R (W k) T) ^ (k - 2) * A1 k R (W k) T := by
          rw [← pow_succ]; congr 1; omega
        rw [div_le_iff₀ hkT, hpow]
        -- goal: (k−1)·A₁⁽¹⁾·A₁^{k-2} ≤ (3/8)·(A₁^{k-2}·A₁)·(k−T)
        have hmoment_nn : 0 ≤ A1_1 k R (W k) T * (A1 k R (W k) T) ^ (k - 2) :=
          mul_nonneg hA1_1nn hApow
        nlinarith [mul_le_mul_of_nonneg_right hkTb hmoment_nn,
          mul_le_mul_of_nonneg_right hA11 hApow, hApow, hkT.le, hAnn]

/-! ## Assembly — `H_main` fully discharged with the re-threaded `(3/8, 1/8)` split -/

/-- **`H_main` closed.**  Re-runs the `sum_sdiff`/subadditivity assembly of
`HMain.H_main_bound` with the re-threaded loss fractions `hOver_bound` (`3/8`) and
`hCop_bound` (`1/8`); their sum is still `1/2`, so `Σ_Good ≥ A₁^{k-1} − (1/2)·A₁^{k-1}
= (1/2)·A₁^{k-1}`.  Depends only on `hR`, `hk`, `hTk`, and the narrow transfer atom
`hA11 : A₁⁽¹⁾ ≤ (1/4)·A₁` (carried, see module header).  Conclusion matches the
`H_main` slot of `s2_tensor_lower` verbatim. -/
theorem H_main_bound_closed (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 16 ≤ k)
    (hT : 0 ≤ T) (hTk : 3 * T ≤ (k : ℝ))
    (hA11 : A1_1 k R (W k) T ≤ (1 / 4 : ℝ) * A1 k R (W k) T) :
    (1 / 2 : ℝ) * (A1 k R (W k) T) ^ (k - 1)
      ≤ ∑ u ∈ Good k R m T,
          ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ) := by
  classical
  have hk1 : 1 ≤ k := by omega
  -- Convert the `fTilde`-summand to `hmW` (on `Good`, off-`m` coords are in `S`).
  have hconv : ∑ u ∈ Good k R m T,
        ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
      = ∑ u ∈ Good k R m T, hmW k R m T u := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [Good, Finset.mem_filter] at hu
    obtain ⟨_, _, hmemS, _⟩ := hu
    rw [hmW]
    apply Finset.prod_congr rfl
    intro i hi
    rw [fTilde, if_pos (hmemS i (Finset.ne_of_mem_erase hi))]
  rw [hconv]
  have hsub := Good_subset_hmBox k R m T
  have hsd := Finset.sum_sdiff (f := hmW k R m T) hsub
  rw [hmBox_sum] at hsd
  set A := (hmBox k R m T).filter
      (fun u => ¬ ((∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T)) with hA
  set Bset := (hmBox k R m T).filter
      (fun u => ¬ (∀ i j, i ≠ j → Nat.Coprime (u i) (u j))) with hB
  have hsubAB : (hmBox k R m T) \ (Good k R m T) ⊆ A ∪ Bset := by
    intro u hu
    rw [Finset.mem_sdiff] at hu
    obtain ⟨huBox, huG⟩ := hu
    rw [Finset.mem_union, hA, hB, Finset.mem_filter, Finset.mem_filter]
    by_cases hthr : (∑ i ∈ Finset.univ.erase m, uVal k R (u i)) < (k : ℝ) - T
    · by_cases hcop : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)
      · exact absurd (mem_Good_of_hmBox k R m T hR hk1 hT huBox hthr hcop) huG
      · exact Or.inr ⟨huBox, hcop⟩
    · exact Or.inl ⟨huBox, hthr⟩
  have hsdle : ∑ u ∈ (hmBox k R m T) \ (Good k R m T), hmW k R m T u
      ≤ ∑ u ∈ A ∪ Bset, hmW k R m T u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubAB (fun u _ _ => hmW_nonneg k R m T u)
  have hunion : ∑ u ∈ A ∪ Bset, hmW k R m T u
      ≤ ∑ u ∈ A, hmW k R m T u + ∑ u ∈ Bset, hmW k R m T u := by
    have hui := Finset.sum_union_inter (s₁ := A) (s₂ := Bset) (f := hmW k R m T)
    have hinn : 0 ≤ ∑ u ∈ A ∩ Bset, hmW k R m T u :=
      Finset.sum_nonneg (fun u _ => hmW_nonneg k R m T u)
    linarith [hui]
  have hOver : ∑ u ∈ A, hmW k R m T u ≤ (3 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) :=
    hOver_bound k R m T hR (by omega) hTk hA11
  have hCop : ∑ u ∈ Bset, hmW k R m T u ≤ (1 / 8 : ℝ) * (A1 k R (W k) T) ^ (k - 1) :=
    hCop_bound k R m T hR hk
  linarith [hsd, hsdle, hunion, hOver, hCop]

end Salt.Maynard
