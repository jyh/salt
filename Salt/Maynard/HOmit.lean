/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Maynard.S2Tensor
import Salt.Maynard.Compat

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

end Salt.Maynard
