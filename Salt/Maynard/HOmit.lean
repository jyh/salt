/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Tensor
import Salt.Maynard.Compat
import Salt.Maynard.HMain

/-!
# C3b — the `H_omit` sum-level atom (Maynard Lemma 6.3, the AVERAGE)

Discharges the `H_omit` hypothesis of `s2_tensor_lower`:
`Σ_{u∈Good} omitMass(u)·owt(u) ≤ (1/8)·B₁·A₁^{k-1}`, where
`owt(u) = ∏_{i≠m} fTilde(uᵢ)²/φ(uᵢ)`.

The reduction (all steps below are proved here) is:

1. **Swap sums** (`am` outer): `Σ_u omitMass·owt = Σ_{am∈sqfCop} (fWt(am)/φ(am))·G(am)`,
   `G(am) = Σ_{u∈Good, ¬(am⊥∏uᵢ)} owt(u)`.
2. **Coprimality decomposition**: `¬(am⊥∏uᵢ) ⟹ ∃p∈primeFactors(am), p∣∏uᵢ`, so
   `G(am) ≤ Σ_{p∈primeFactors am} H(p)`, `H(p) = Σ_{u∈Good, p∣∏uᵢ} owt(u)`.
3. **Swap `am`/`p`** (`Finset.sum_comm'`): the double sum becomes
   `Σ_{p} H(p)·(Σ_{am∈sqfCop, p∣am} fWt(am)/φ(am))`, the primes `p > D₀ k`.
4. Two number-theoretic reindex bounds — the narrow PORT-BLOCKERs, taken as
   named hypotheses `H_box` and `H_reindex`:
   * `H_box`  : `H(p) ≤ (k-1)·(p-1)⁻¹·A₁^{k-1}`  (reindex `uᵢ = p·b`).
   * `H_reindex` : `Σ_{am∈sqfCop, p∣am} fWt/φ ≤ (p-1)⁻¹·B₁`  (reindex `am = p·b`).
5. **`inv_sq_tele`** (re-declared private copy): `Σ_{p>D₀k} (p-1)⁻² ≤ 2/(D₀ k)`.
   The `log R₀` has cancelled; the average converges.  With `16k ≤ D₀ k` and
   `k ≥ 1` this gives `≤ 2(k-1)/(D₀ k)·B₁·A₁^{k-1} ≤ (1/8)·B₁·A₁^{k-1}`.
-/

open Finset

namespace Salt.Maynard

/-- Off-`m` product weight `owt(u) = ∏_{i≠m} fTilde(uᵢ)²/φ(uᵢ)` — the weight
appearing in `H_main`/`H_omit`. -/
private noncomputable def owt (k R : ℕ) (m : Fin k) (T : ℝ) (u : Fin k → ℕ) : ℝ :=
  ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)

/-- Off-`m` product of coordinates `∏_{i≠m} uᵢ`. -/
private def oprod {k : ℕ} (m : Fin k) (u : Fin k → ℕ) : ℕ :=
  ∏ i ∈ Finset.univ.erase m, u i

private lemma owt_eq {k R : ℕ} {m : Fin k} {T : ℝ} (u : Fin k → ℕ) :
    (∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ))
      = owt k R m T u := rfl

private lemma oprod_eq {k : ℕ} {m : Fin k} (u : Fin k → ℕ) :
    (∏ i ∈ Finset.univ.erase m, u i) = oprod m u := rfl

private lemma owt_nonneg (k R : ℕ) (m : Fin k) (T : ℝ) (u : Fin k → ℕ) :
    0 ≤ owt k R m T u :=
  Finset.prod_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- Re-declared private copy of `CollisionQuant.inv_sq_tele` (it is `private`
there, hence not importable): telescoping tail
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

/-- **`H_omit` — the average coprimality-omitted mass (Maynard 6.3).**  Matches the
`H_omit` hypothesis shape of `s2_tensor_lower` exactly (same `Good`, `omitMass`,
`A1`, `B1`, and the explicit off-`m` weight product).  Two narrow reindex bounds
are taken as hypotheses `H_box`/`H_reindex` (PORT-BLOCKERs). -/
theorem H_omit_bound (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 1 ≤ k)
    (hD : 16 * k ≤ D₀ k)
    (H_box : ∀ p : ℕ, p.Prime →
        (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)
          ≤ ((k : ℝ) - 1) * ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1))
    (H_reindex : ∀ p : ℕ, p.Prime →
        (∑ am ∈ sqfCop (R0 k R T) (W k),
            if p ∣ am then fWt k R am / (Nat.totient am : ℝ) else 0)
          ≤ ((p : ℝ) - 1)⁻¹ * B1 k R (W k) T) :
    ∑ u ∈ Good k R m T,
        omitMass k R m T u
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
      ≤ (1 / 8 : ℝ) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) := by
  -- fold the off-`m` weight product into `owt`
  simp only [owt_eq]
  -- nonnegativity facts
  have hAnn : (0 : ℝ) ≤ A1 k R (W k) T := A1_nonneg _ _ _ _
  have hApow : (0 : ℝ) ≤ (A1 k R (W k) T) ^ (k - 1) := pow_nonneg hAnn _
  have hBnn : (0 : ℝ) ≤ B1 k R (W k) T := B1_nonneg k R (W k) T hR
  have hk0 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hf_nonneg : ∀ am ∈ sqfCop (R0 k R T) (W k), 0 ≤ fWt k R am / (Nat.totient am : ℝ) :=
    fun am hmem => div_nonneg (fWt_nonneg (mem_support hmem).1 hR) (Nat.cast_nonneg _)
  have hDk_pos : (0 : ℝ) < (D₀ k : ℝ) := by
    have : 0 < D₀ k := by omega
    exact_mod_cast this
  -- ─────────── Step 1: swap the `u`/`am` sums (`am` outer) ───────────
  have swap1 : (∑ u ∈ Good k R m T, omitMass k R m T u * owt k R m T u)
      = ∑ am ∈ sqfCop (R0 k R T) (W k),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T,
                if ¬ Nat.Coprime am (oprod m u) then owt k R m T u else 0) := by
    have e1 : (∑ u ∈ Good k R m T, omitMass k R m T u * owt k R m T u)
        = ∑ u ∈ Good k R m T, ∑ am ∈ sqfCop (R0 k R T) (W k),
            (if ¬ Nat.Coprime am (oprod m u) then fWt k R am / (Nat.totient am : ℝ) else 0)
              * owt k R m T u := by
      apply Finset.sum_congr rfl; intro u _
      rw [omitMass, Finset.sum_mul]; rfl
    rw [e1, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro am _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro u _
    split_ifs with hc <;> ring
  -- ─────────── Step 2: per-`am` coprimality decomposition ───────────
  have decomp : ∀ am ∈ sqfCop (R0 k R T) (W k),
      (∑ u ∈ Good k R m T, if ¬ Nat.Coprime am (oprod m u) then owt k R m T u else 0)
        ≤ ∑ p ∈ am.primeFactors,
            (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) := by
    intro am hammem
    have ham0 : am ≠ 0 := by
      rw [sqfCop, Finset.mem_filter] at hammem; exact hammem.2.1.ne_zero
    calc (∑ u ∈ Good k R m T, if ¬ Nat.Coprime am (oprod m u) then owt k R m T u else 0)
        ≤ ∑ u ∈ Good k R m T,
            ∑ p ∈ am.primeFactors, (if p ∣ oprod m u then owt k R m T u else 0) := by
          apply Finset.sum_le_sum; intro u _
          have hnn : ∀ q : ℕ, 0 ≤ if q ∣ oprod m u then owt k R m T u else 0 :=
            fun q => by split_ifs <;> first | exact owt_nonneg _ _ _ _ _ | exact le_rfl
          by_cases hc : ¬ Nat.Coprime am (oprod m u)
          · rw [if_pos hc]
            have hgcd : Nat.gcd am (oprod m u) ≠ 1 := hc
            obtain ⟨p, hpp, hpg⟩ := Nat.exists_prime_and_dvd hgcd
            have hpam : p ∣ am := hpg.trans (Nat.gcd_dvd_left _ _)
            have hpo : p ∣ oprod m u := hpg.trans (Nat.gcd_dvd_right _ _)
            have hpmem : p ∈ am.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpam, ham0⟩
            calc owt k R m T u = (if p ∣ oprod m u then owt k R m T u else 0) := (if_pos hpo).symm
              _ ≤ ∑ q ∈ am.primeFactors, (if q ∣ oprod m u then owt k R m T u else 0) :=
                  Finset.single_le_sum (fun q _ => hnn q) hpmem
          · rw [if_neg hc]
            exact Finset.sum_nonneg (fun q _ => hnn q)
      _ = ∑ p ∈ am.primeFactors,
            (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) :=
          Finset.sum_comm
  -- ─────────── Step 3: bound and distribute ───────────
  have step2 : (∑ am ∈ sqfCop (R0 k R T) (W k),
        (fWt k R am / (Nat.totient am : ℝ))
          * (∑ u ∈ Good k R m T, if ¬ Nat.Coprime am (oprod m u) then owt k R m T u else 0))
      ≤ ∑ am ∈ sqfCop (R0 k R T) (W k),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ p ∈ am.primeFactors,
                (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)) := by
    apply Finset.sum_le_sum; intro am hammem
    exact mul_le_mul_of_nonneg_left (decomp am hammem) (hf_nonneg am hammem)
  have step3 : (∑ am ∈ sqfCop (R0 k R T) (W k),
        (fWt k R am / (Nat.totient am : ℝ))
          * (∑ p ∈ am.primeFactors,
              (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)))
      = ∑ am ∈ sqfCop (R0 k R T) (W k), ∑ p ∈ am.primeFactors,
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) := by
    apply Finset.sum_congr rfl; intro am _; rw [Finset.mul_sum]
  -- ─────────── Step 4: swap `am`/`p` ───────────
  set PS : Finset ℕ := (sqfCop (R0 k R T) (W k)).biUnion (fun am => am.primeFactors) with hPS
  have hext : ∀ am ∈ sqfCop (R0 k R T) (W k),
      (∑ p ∈ am.primeFactors,
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0))
        = ∑ p ∈ PS, if p ∈ am.primeFactors then
              (fWt k R am / (Nat.totient am : ℝ))
                * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) else 0 := by
    intro am hamS
    have hsubset : am.primeFactors ⊆ PS := by
      intro p hp; rw [hPS, Finset.mem_biUnion]; exact ⟨am, hamS, hp⟩
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsubset]
  have step4 : (∑ am ∈ sqfCop (R0 k R T) (W k), ∑ p ∈ am.primeFactors,
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0))
      = ∑ p ∈ PS, ∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) := by
    rw [Finset.sum_congr rfl hext, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.sum_filter]
  have step5 : ∀ p,
      (∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0))
        = (∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
              fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) := by
    intro p; rw [Finset.sum_mul]
  -- ─────────── Step 5: per-prime facts ───────────
  have hp_prime : ∀ p ∈ PS, p.Prime := by
    intro p hp
    rw [hPS, Finset.mem_biUnion] at hp
    obtain ⟨am, _, hpf⟩ := hp
    exact Nat.prime_of_mem_primeFactors hpf
  -- `D'(p)` reindex bound (via `H_reindex`)
  have hDp : ∀ p ∈ PS,
      (∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
          fWt k R am / (Nat.totient am : ℝ))
        ≤ ((p : ℝ) - 1)⁻¹ * B1 k R (W k) T := by
    intro p hp
    have hpp := hp_prime p hp
    have hfeq : (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors)
        = (sqfCop (R0 k R T) (W k)).filter (fun am => p ∣ am) := by
      apply Finset.filter_congr
      intro am hammem
      have ham0 : am ≠ 0 := by
        rw [sqfCop, Finset.mem_filter] at hammem; exact hammem.2.1.ne_zero
      exact ⟨fun h => Nat.dvd_of_mem_primeFactors h,
        fun h => Nat.mem_primeFactors.mpr ⟨hpp, h, ham0⟩⟩
    rw [hfeq, Finset.sum_filter]
    exact H_reindex p hpp
  -- per-prime product bound
  have hterm_bound : ∀ p ∈ PS,
      (∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
          fWt k R am / (Nat.totient am : ℝ))
        * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)
      ≤ ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) * (((p : ℝ) - 1)⁻¹) ^ 2 := by
    intro p hp
    have hpp := hp_prime p hp
    have hpge : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hpinv : (0 : ℝ) ≤ ((p : ℝ) - 1)⁻¹ := by
      apply inv_nonneg.mpr; linarith
    have hD1 := hDp p hp
    have hB1 := H_box p hpp
    have hDp_nn : 0 ≤ ∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
        fWt k R am / (Nat.totient am : ℝ) :=
      Finset.sum_nonneg (fun am hh => hf_nonneg am (Finset.mem_filter.mp hh).1)
    have hHp_nn : 0 ≤ ∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0 :=
      Finset.sum_nonneg (fun u _ => by
        split_ifs <;> first | exact owt_nonneg _ _ _ _ _ | exact le_rfl)
    have hbndD_nn : 0 ≤ ((p : ℝ) - 1)⁻¹ * B1 k R (W k) T := mul_nonneg hpinv hBnn
    calc (∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
              fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)
        ≤ (((p : ℝ) - 1)⁻¹ * B1 k R (W k) T)
            * (((k : ℝ) - 1) * ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1)) :=
          mul_le_mul hD1 hB1 hHp_nn hbndD_nn
      _ = ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) * (((p : ℝ) - 1)⁻¹) ^ 2 := by
          ring
  -- ─────────── Step 6: the telescoping tail `∑ (p-1)⁻² ≤ 2/D₀` ───────────
  have ha2 : 2 ≤ D₀ k := by omega
  have hd2 : (2 : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast ha2
  have hPStail : (∑ p ∈ PS, (((p : ℝ) - 1)⁻¹) ^ 2) ≤ 2 / (D₀ k : ℝ) := by
    have hsub : PS ⊆ Finset.Icc (D₀ k + 1) (D₀ k + R0 k R T) := by
      intro p hp
      rw [hPS, Finset.mem_biUnion] at hp
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
    have hmono : (∑ p ∈ PS, (((p : ℝ) - 1)⁻¹) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) (D₀ k + R0 k R T), (((n : ℝ) - 1)⁻¹) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    have htel := inv_sq_tele (D₀ k) ha2 (D₀ k + R0 k R T) (Nat.le_add_right _ _)
    have hbpos : (0 : ℝ) ≤ (((D₀ k + R0 k R T : ℕ) : ℝ) - 1)⁻¹ := by
      apply inv_nonneg.mpr
      have : (1 : ℝ) ≤ ((D₀ k + R0 k R T : ℕ) : ℝ) := by
        have : 1 ≤ D₀ k + R0 k R T := by omega
        exact_mod_cast this
      linarith
    have hfin : ((D₀ k : ℝ) - 1)⁻¹ ≤ 2 / (D₀ k : ℝ) := by
      have h1 : (0 : ℝ) < (D₀ k : ℝ) - 1 := by linarith
      have key : 2 / (D₀ k : ℝ) - ((D₀ k : ℝ) - 1)⁻¹
          = ((D₀ k : ℝ) - 2) / ((D₀ k : ℝ) * ((D₀ k : ℝ) - 1)) := by
        field_simp; ring
      have hnn : 0 ≤ 2 / (D₀ k : ℝ) - ((D₀ k : ℝ) - 1)⁻¹ := by
        rw [key]; exact div_nonneg (by linarith) (mul_pos hDk_pos h1).le
      linarith
    calc (∑ p ∈ PS, (((p : ℝ) - 1)⁻¹) ^ 2)
        ≤ ∑ n ∈ Finset.Icc (D₀ k + 1) (D₀ k + R0 k R T), (((n : ℝ) - 1)⁻¹) ^ 2 := hmono
      _ ≤ ((D₀ k : ℝ) - 1)⁻¹ - (((D₀ k + R0 k R T : ℕ) : ℝ) - 1)⁻¹ := htel
      _ ≤ ((D₀ k : ℝ) - 1)⁻¹ := by linarith
      _ ≤ 2 / (D₀ k : ℝ) := hfin
  -- ─────────── Step 7: final arithmetic ───────────
  have hfinal : ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) * (2 / (D₀ k : ℝ))
      ≤ (1 / 8 : ℝ) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) := by
    have hDk16 : (16 : ℝ) * (k : ℝ) ≤ (D₀ k : ℝ) := by exact_mod_cast hD
    have hBA : 0 ≤ B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) := mul_nonneg hBnn hApow
    have hratio : 2 * ((k : ℝ) - 1) / (D₀ k : ℝ) ≤ 1 / 8 := by
      rw [div_le_iff₀ hDk_pos]; linarith
    calc ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) * (2 / (D₀ k : ℝ))
        = (B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1)) * (2 * ((k : ℝ) - 1) / (D₀ k : ℝ)) := by
          ring
      _ ≤ (B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1)) * (1 / 8) :=
          mul_le_mul_of_nonneg_left hratio hBA
      _ = (1 / 8 : ℝ) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) := by ring
  -- ─────────── Assemble ───────────
  rw [swap1]
  calc (∑ am ∈ sqfCop (R0 k R T) (W k),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if ¬ Nat.Coprime am (oprod m u) then owt k R m T u else 0))
      ≤ ∑ am ∈ sqfCop (R0 k R T) (W k),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ p ∈ am.primeFactors,
                (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)) := step2
    _ = ∑ am ∈ sqfCop (R0 k R T) (W k), ∑ p ∈ am.primeFactors,
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) := step3
    _ = ∑ p ∈ PS, ∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
          (fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) := step4
    _ = ∑ p ∈ PS, (∑ am ∈ (sqfCop (R0 k R T) (W k)).filter (fun am => p ∈ am.primeFactors),
              fWt k R am / (Nat.totient am : ℝ))
            * (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0) :=
          Finset.sum_congr rfl (fun p _ => step5 p)
    _ ≤ ∑ p ∈ PS,
          ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) * (((p : ℝ) - 1)⁻¹) ^ 2 :=
          Finset.sum_le_sum hterm_bound
    _ = ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1)
          * ∑ p ∈ PS, (((p : ℝ) - 1)⁻¹) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ((k : ℝ) - 1) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) * (2 / (D₀ k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hPStail
          exact mul_nonneg (mul_nonneg hk0 hBnn) hApow
    _ ≤ (1 / 8 : ℝ) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) := hfinal

/-! ## Closing the two `H_omit` leaves (concrete per-prime reindexes) -/

/-- `fWt` is nonnegative for *every* natural argument (not just `r ≥ 1`):
`uVal ≥ 0` unconditionally (`log n ≥ 0`), so the denominator `1 + (log k)·uVal ≥ 1`. -/
lemma fWt_nonneg_all (k R n : ℕ) (hR : 2 ≤ R) : 0 ≤ fWt k R n := by
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hu : 0 ≤ uVal k R n := by
    unfold uVal
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) hlogn) hlogR.le
  have hden : (0 : ℝ) ≤ 1 + Real.log (k : ℝ) * uVal k R n := by nlinarith [mul_nonneg hlk hu]
  unfold fWt
  exact div_nonneg zero_le_one hden

/-- **`fWt` antitonicity.** For `a ∣ b` with `b > 0`, `fWt b ≤ fWt a`.  `uVal` is
monotone in its argument (`log` monotone), and `fWt = 1/(1 + (log k)·uVal)` is a
decreasing function of `uVal` (since `log k ≥ 0`). -/
lemma fWt_anti (k R : ℕ) (hR : 2 ≤ R) :
    ∀ a b : ℕ, 0 < b → a ∣ b → fWt k R b ≤ fWt k R a := by
  intro a b hb hab
  have ha : 0 < a := Nat.pos_of_dvd_of_pos hab hb
  have hab_le : a ≤ b := Nat.le_of_dvd hb hab
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hlk : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
  have hloga_le : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab_le)
  have hu_le : uVal k R a ≤ uVal k R b := by
    unfold uVal
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hloga_le (Nat.cast_nonneg k)) (inv_nonneg.mpr hlogR.le)
  have hden_le : 1 + Real.log (k : ℝ) * uVal k R a ≤ 1 + Real.log (k : ℝ) * uVal k R b := by
    have := mul_le_mul_of_nonneg_left hu_le hlk; linarith
  have hua : 0 ≤ uVal k R a := by
    unfold uVal
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) (Real.log_natCast_nonneg a)) hlogR.le
  have hden_a_pos : (0 : ℝ) < 1 + Real.log (k : ℝ) * uVal k R a := by
    nlinarith [mul_nonneg hlk hua]
  unfold fWt
  exact one_div_le_one_div_of_le hden_a_pos hden_le

/-- The square of `fWt` is antitone (square of a nonnegative antitone function). -/
lemma fWt_sq_anti (k R : ℕ) (hR : 2 ≤ R) :
    ∀ a b : ℕ, 0 < b → a ∣ b → (fWt k R b) ^ 2 ≤ (fWt k R a) ^ 2 := by
  intro a b hb hab
  exact pow_le_pow_left₀ (fWt_nonneg_all k R b hR) (fWt_anti k R hR a b hb hab) 2

/-- **Per-prime reindex** (the crux of both `H_omit` leaves).  Reindexing
`r = p·b` over the `p`-divisible part of `sqfCop`, using `φ(pb) = (p-1)·φ(b)`
(squarefree `⇒ p ⊥ b`, `Nat.totient_mul` + `Nat.totient_prime`) and the
antitonicity of the weight `g` (`g(pb) ≤ g(b)`, `b ∣ pb`).  Holds for *every*
prime `p` (if `p` divides no element the filtered sum is `0`). -/
theorem sqfCop_dvd_reindex (k R : ℕ) (T : ℝ) (p : ℕ) (hp : p.Prime)
    (g : ℕ → ℝ) (hg_nonneg : ∀ n, 0 ≤ g n)
    (hg_anti : ∀ a b : ℕ, 0 < b → a ∣ b → g b ≤ g a) :
    (∑ r ∈ sqfCop (R0 k R T) (W k), if p ∣ r then g r / (Nat.totient r : ℝ) else 0)
      ≤ ((p : ℝ) - 1)⁻¹ * ∑ r ∈ sqfCop (R0 k R T) (W k), g r / (Nat.totient r : ℝ) := by
  classical
  set S := sqfCop (R0 k R T) (W k) with hSdef
  set filt := S.filter (fun r => p ∣ r) with hfilt
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hmem : ∀ r ∈ filt, r < R0 k R T ∧ Squarefree r ∧ Nat.Coprime r (W k) ∧ p ∣ r := by
    intro r hr
    rw [hfilt, Finset.mem_filter] at hr
    obtain ⟨hrS, hpr⟩ := hr
    rw [hSdef, sqfCop, Finset.mem_filter, Finset.mem_range] at hrS
    exact ⟨hrS.1, hrS.2.1, hrS.2.2, hpr⟩
  have hLHS : (∑ r ∈ S, if p ∣ r then g r / (Nat.totient r : ℝ) else 0)
      = ∑ r ∈ filt, g r / (Nat.totient r : ℝ) := (Finset.sum_filter _ _).symm
  rw [hLHS]
  have hb_mem : ∀ r ∈ filt, r / p ∈ S := by
    intro r hr
    obtain ⟨hrlt, hsqf, hcw, hpr⟩ := hmem r hr
    have hbdvd : (r / p) ∣ r := ⟨p, by rw [mul_comm]; exact (Nat.mul_div_cancel' hpr).symm⟩
    rw [hSdef, sqfCop, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (Nat.div_le_self r p) hrlt,
      Squarefree.squarefree_of_dvd hbdvd hsqf, Nat.Coprime.coprime_dvd_left hbdvd hcw⟩
  have hterm : ∀ r ∈ filt,
      g r / (Nat.totient r : ℝ) ≤ ((p : ℝ) - 1)⁻¹ * (g (r / p) / (Nat.totient (r / p) : ℝ)) := by
    intro r hr
    obtain ⟨hrlt, hsqf, hcw, hpr⟩ := hmem r hr
    set b := r / p with hbdef
    have hrpb : r = p * b := (Nat.mul_div_cancel' hpr).symm
    have hrpos : 0 < r := Nat.pos_of_ne_zero hsqf.ne_zero
    have hbpos : 0 < b := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · rw [hb0, mul_zero] at hrpb; omega
      · exact hb0
    have hpnb : ¬ p ∣ b := by
      intro hpb
      have hpp : p * p ∣ r := by rw [hrpb]; exact mul_dvd_mul_left p hpb
      have hu : IsUnit p := hsqf p hpp
      rw [Nat.isUnit_iff] at hu
      have := hp.two_le
      omega
    have hcop_pb : Nat.Coprime p b := (hp.coprime_iff_not_dvd).mpr hpnb
    have hφr : (Nat.totient r : ℝ) = ((p : ℝ) - 1) * (Nat.totient b : ℝ) := by
      have h1 : Nat.totient r = (p - 1) * Nat.totient b := by
        rw [hrpb, Nat.totient_mul hcop_pb, Nat.totient_prime hp]
      rw [h1, Nat.cast_mul, Nat.cast_sub hp.one_le, Nat.cast_one]
    have hφb : (0 : ℝ) < (Nat.totient b : ℝ) := by
      have : 0 < Nat.totient b := Nat.totient_pos.mpr hbpos
      exact_mod_cast this
    have hgle : g r ≤ g b := by
      rw [hrpb]
      exact hg_anti b (p * b) (by rw [← hrpb]; exact hrpos) (dvd_mul_left b p)
    rw [hφr, div_le_iff₀ (mul_pos hp1 hφb)]
    have hne1 : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hp1
    have hne2 : (Nat.totient b : ℝ) ≠ 0 := ne_of_gt hφb
    have hrewrite : ((p : ℝ) - 1)⁻¹ * (g b / (Nat.totient b : ℝ))
        * (((p : ℝ) - 1) * (Nat.totient b : ℝ)) = g b := by
      field_simp
    rw [hrewrite]; exact hgle
  calc (∑ r ∈ filt, g r / (Nat.totient r : ℝ))
      ≤ ∑ r ∈ filt, ((p : ℝ) - 1)⁻¹ * (g (r / p) / (Nat.totient (r / p) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = ((p : ℝ) - 1)⁻¹ * ∑ r ∈ filt, g (r / p) / (Nat.totient (r / p) : ℝ) := by
        rw [Finset.mul_sum]
    _ = ((p : ℝ) - 1)⁻¹ * ∑ b ∈ filt.image (fun r => r / p), g b / (Nat.totient b : ℝ) := by
        congr 1
        have hinj : Set.InjOn (fun r => r / p) (filt : Set ℕ) := by
          intro x hx y hy hxy
          simp only [Finset.mem_coe] at hx hy
          obtain ⟨_, _, _, hpx⟩ := hmem x hx
          obtain ⟨_, _, _, hpy⟩ := hmem y hy
          have e1 : p * (x / p) = x := Nat.mul_div_cancel' hpx
          have e2 : p * (y / p) = y := Nat.mul_div_cancel' hpy
          have hxy' : x / p = y / p := hxy
          rw [← e1, ← e2, hxy']
        rw [Finset.sum_image hinj]
    _ ≤ ((p : ℝ) - 1)⁻¹ * ∑ b ∈ S, g b / (Nat.totient b : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp1.le)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro b hb
          rw [Finset.mem_image] at hb
          obtain ⟨r, hr, rfl⟩ := hb
          exact hb_mem r hr
        · intro b _ _
          exact div_nonneg (hg_nonneg b) (Nat.cast_nonneg _)

/-- **Single-restricted-coordinate box factorization.**  Summing the box weight
`hmW` over `hmBox` with the coordinate `i₀ ≠ m` restricted to multiples of `p`
factors as `[∑_{x∈sqfCop, p∣x} fWt(x)²/φ(x)] · A₁^{k-2}` (the `i₀`-fiber carries
the restriction, the `m`-fiber contributes `1`, the remaining `k-2` fibers each
contribute `A₁`).  Mirror of `hmBox_sum` with one fiber guarded. -/
private lemma hmBox_restrict_coord (k R : ℕ) (m : Fin k) (T : ℝ) (p : ℕ)
    (i₀ : Fin k) (hi₀ : i₀ ≠ m) :
    (∑ u ∈ hmBox k R m T, if p ∣ u i₀ then hmW k R m T u else 0)
      = (∑ x ∈ sqfCop (R0 k R T) (W k),
            if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
          * (A1 k R (W k) T) ^ (k - 2) := by
  classical
  have hG1 : (fWt k R 1) ^ 2 / (Nat.totient 1 : ℝ) = 1 := by rw [fWt_one]; simp
  have hsummand : ∀ u ∈ hmBox k R m T,
      (if p ∣ u i₀ then hmW k R m T u else 0)
        = ∏ j, (if j = i₀ then
                  (if p ∣ u j then (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) else 0)
                else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) := by
    intro u hu
    simp only [hmBox, Fintype.mem_piFinset] at hu
    have hum : u m = 1 := by
      have h := hu m; rwa [if_pos rfl, Finset.mem_singleton] at h
    have hmWu : hmW k R m T u = ∏ j, (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) := by
      rw [hmW, ← Finset.mul_prod_erase Finset.univ
            (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ m),
          hum, hG1, one_mul]
    rw [← Finset.mul_prod_erase Finset.univ
          (fun j => if j = i₀ then
                      (if p ∣ u j then (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ) else 0)
                    else (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ i₀),
      if_pos rfl,
      Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])]
    by_cases hd : p ∣ u i₀
    · rw [if_pos hd, if_pos hd, hmWu,
        ← Finset.mul_prod_erase Finset.univ
          (fun j => (fWt k R (u j)) ^ 2 / (Nat.totient (u j) : ℝ)) (Finset.mem_univ i₀)]
    · rw [if_neg hd, if_neg hd, zero_mul]
  rw [Finset.sum_congr rfl hsummand]
  simp only [hmBox]
  rw [← Finset.prod_univ_sum
        (fun i : Fin k => if i = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k))
        (fun j x => if j = i₀ then
                      (if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
                    else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))]
  have hfac : ∀ j : Fin k,
      (∑ x ∈ (if j = m then ({1} : Finset ℕ) else sqfCop (R0 k R T) (W k)),
          if j = i₀ then (if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
                    else (fWt k R x) ^ 2 / (Nat.totient x : ℝ))
        = if j = i₀ then
            (∑ x ∈ sqfCop (R0 k R T) (W k),
                if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
          else (if j = m then (1 : ℝ) else A1 k R (W k) T) := by
    intro j
    by_cases hj : j = i₀
    · have hjm : j ≠ m := by rw [hj]; exact hi₀
      rw [if_pos hj, if_neg hjm]
      exact Finset.sum_congr rfl (fun x _ => if_pos hj)
    · rw [if_neg hj]
      by_cases hjm : j = m
      · rw [if_pos hjm, if_pos hjm, Finset.sum_singleton, if_neg hj]
        exact hG1
      · rw [if_neg hjm, if_neg hjm]
        exact Finset.sum_congr rfl (fun x _ => if_neg hj)
  rw [Finset.prod_congr rfl (fun j _ => hfac j),
    ← Finset.mul_prod_erase Finset.univ
      (fun j => if j = i₀ then
                  (∑ x ∈ sqfCop (R0 k R T) (W k),
                      if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
                else (if j = m then (1 : ℝ) else A1 k R (W k) T)) (Finset.mem_univ i₀),
    if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])]
  have hm_mem : m ∈ Finset.univ.erase i₀ :=
    Finset.mem_erase.mpr ⟨fun h => hi₀ h.symm, Finset.mem_univ m⟩
  rw [← Finset.mul_prod_erase (Finset.univ.erase i₀)
        (fun j => if j = m then (1 : ℝ) else A1 k R (W k) T) hm_mem,
    if_pos rfl, one_mul,
    Finset.prod_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)]),
    Finset.prod_const, Finset.card_erase_of_mem hm_mem,
    Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
  congr 1

/-- **Leaf 1 — `H_reindex`.**  Direct application of `sqfCop_dvd_reindex` with the
weight `g = fWt` (nonnegative and antitone).  Matches the `H_reindex` hypothesis
of `H_omit_bound` for every prime `p`. -/
theorem H_reindex_proof (k R : ℕ) (T : ℝ) (hR : 2 ≤ R) (p : ℕ) (hp : p.Prime) :
    (∑ am ∈ sqfCop (R0 k R T) (W k),
        if p ∣ am then fWt k R am / (Nat.totient am : ℝ) else 0)
      ≤ ((p : ℝ) - 1)⁻¹ * B1 k R (W k) T := by
  have h := sqfCop_dvd_reindex k R T p hp (fun x => fWt k R x)
      (fun n => fWt_nonneg_all k R n hR) (fWt_anti k R hR)
  simpa only [B1] using h

/-- **Leaf 2 — `H_box`.**  The `p`-divisible off-`m` box mass is bounded by
`(k-1)·(p-1)⁻¹·A₁^{k-1}`.  Route: `p ∣ ∏_{i≠m} uᵢ ⇒ ∃ i≠m, p ∣ uᵢ` (prime),
union bound over the `k-1` coordinates, each relaxed `Good ⊆ hmBox`, factored by
`hmBox_restrict_coord`, and reduced by `sqfCop_dvd_reindex` (`g = fWt²`).  Matches
the `H_box` hypothesis of `H_omit_bound` for every prime `p`. -/
theorem H_box_proof (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (p : ℕ) (hp : p.Prime) :
    (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)
      ≤ ((k : ℝ) - 1) * ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1) := by
  classical
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact m.elim0)
  have hAnn : (0 : ℝ) ≤ A1 k R (W k) T := A1_nonneg _ _ _ _
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hconv : (∑ u ∈ Good k R m T, if p ∣ oprod m u then owt k R m T u else 0)
      = ∑ u ∈ Good k R m T, if p ∣ oprod m u then hmW k R m T u else 0 := by
    apply Finset.sum_congr rfl; intro u hu
    have hval : owt k R m T u = hmW k R m T u := by
      rw [owt, hmW]
      rw [Good, Finset.mem_filter] at hu
      apply Finset.prod_congr rfl; intro i hi
      rw [fTilde, if_pos (hu.2.2.1 i (Finset.ne_of_mem_erase hi))]
    rw [hval]
  rw [hconv]
  have hext : (∑ u ∈ Good k R m T, if p ∣ oprod m u then hmW k R m T u else 0)
      ≤ ∑ u ∈ hmBox k R m T, if p ∣ oprod m u then hmW k R m T u else 0 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Good_subset_hmBox k R m T)
    intro u _ _; split_ifs
    · exact hmW_nonneg k R m T u
    · exact le_rfl
  have hunion : (∑ u ∈ hmBox k R m T, if p ∣ oprod m u then hmW k R m T u else 0)
      ≤ ∑ i ∈ Finset.univ.erase m,
          ∑ u ∈ hmBox k R m T, if p ∣ u i then hmW k R m T u else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro u _
    by_cases hd : p ∣ oprod m u
    · rw [if_pos hd]
      have hdvd : p ∣ ∏ i ∈ Finset.univ.erase m, u i := by rw [oprod_eq]; exact hd
      obtain ⟨i, hi_mem, hi_dvd⟩ := hp.prime.exists_mem_finset_dvd hdvd
      have hnn : ∀ j ∈ Finset.univ.erase m, 0 ≤ (if p ∣ u j then hmW k R m T u else 0) := by
        intro j _; split_ifs
        · exact hmW_nonneg k R m T u
        · exact le_rfl
      calc hmW k R m T u = (if p ∣ u i then hmW k R m T u else 0) := (if_pos hi_dvd).symm
        _ ≤ ∑ j ∈ Finset.univ.erase m, if p ∣ u j then hmW k R m T u else 0 :=
            Finset.single_le_sum hnn hi_mem
    · rw [if_neg hd]
      exact Finset.sum_nonneg (fun i _ => by split_ifs; exacts [hmW_nonneg k R m T u, le_rfl])
  have hper : ∀ i ∈ Finset.univ.erase m,
      (∑ u ∈ hmBox k R m T, if p ∣ u i then hmW k R m T u else 0)
        ≤ ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1) := by
    intro i hi_mem
    have hi : i ≠ m := Finset.ne_of_mem_erase hi_mem
    have hk2 : 2 ≤ k := by
      have h1 : 1 ≤ (Finset.univ.erase m).card := Finset.card_pos.mpr ⟨i, hi_mem⟩
      rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin] at h1
      omega
    rw [hmBox_restrict_coord k R m T p i hi]
    have hreindex : (∑ x ∈ sqfCop (R0 k R T) (W k),
          if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
        ≤ ((p : ℝ) - 1)⁻¹ * A1 k R (W k) T := by
      have h := sqfCop_dvd_reindex k R T p hp (fun x => (fWt k R x) ^ 2)
          (fun n => sq_nonneg (fWt k R n)) (fWt_sq_anti k R hR)
      simpa only [A1] using h
    have hpow : (k - 2) + 1 = k - 1 := by omega
    calc (∑ x ∈ sqfCop (R0 k R T) (W k),
              if p ∣ x then (fWt k R x) ^ 2 / (Nat.totient x : ℝ) else 0)
            * (A1 k R (W k) T) ^ (k - 2)
        ≤ (((p : ℝ) - 1)⁻¹ * A1 k R (W k) T) * (A1 k R (W k) T) ^ (k - 2) :=
          mul_le_mul_of_nonneg_right hreindex (pow_nonneg hAnn _)
      _ = ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1) := by
          rw [mul_assoc, ← pow_succ', hpow]
  calc (∑ u ∈ Good k R m T, if p ∣ oprod m u then hmW k R m T u else 0)
      ≤ ∑ u ∈ hmBox k R m T, if p ∣ oprod m u then hmW k R m T u else 0 := hext
    _ ≤ ∑ i ∈ Finset.univ.erase m,
          ∑ u ∈ hmBox k R m T, if p ∣ u i then hmW k R m T u else 0 := hunion
    _ ≤ ∑ i ∈ Finset.univ.erase m, ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1) :=
        Finset.sum_le_sum hper
    _ = ((k : ℝ) - 1) * ((p : ℝ) - 1)⁻¹ * (A1 k R (W k) T) ^ (k - 1) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ m),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hk, Nat.cast_one]
        ring

/-- **`H_omit` fully discharged.**  `H_omit_bound` with both reindex leaves
plugged in; depends only on `hR`, `hk`, `hD`.  Plugs directly into the `H_omit`
slot of `s2_tensor_lower`. -/
theorem H_omit_bound_closed (k R : ℕ) (m : Fin k) (T : ℝ) (hR : 2 ≤ R) (hk : 1 ≤ k)
    (hD : 16 * k ≤ D₀ k) :
    ∑ u ∈ Good k R m T,
        omitMass k R m T u
          * ∏ i ∈ Finset.univ.erase m, (fTilde k R T (u i)) ^ 2 / (Nat.totient (u i) : ℝ)
      ≤ (1 / 8 : ℝ) * B1 k R (W k) T * (A1 k R (W k) T) ^ (k - 1) :=
  H_omit_bound k R m T hR hk hD
    (fun p hp => H_box_proof k R m T hR p hp)
    (fun p hp => H_reindex_proof k R T hR p hp)

end Salt.Maynard
