/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.MvSplit
import Salt.MaynardK.MvJGen
import Salt.Twelve.DecBoxPair

/-!
# C1 · B4.2b (E2) — `mv_J_main_split` at general `n` (`mv_J_main_split_gen`)

The J-side main moment in MvSplit's split shape (`A` before `W'`), at general `n` for the contracted
budget polynomial `contractB m P`, with its `mjs_*` foundation (gap, bad-pair and drop bounds)
ported off `Fin 4`. Ported by an Opus executor from a frozen brief (2026-10-11).
-/

open Finset

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Twelve Salt.Maynard Salt.MaynardK

/-! ### Relative one-coordinate g-moments (`M0`, `MQ`, `MQ2`) over `sqfCop R W'` -/

/-- a product over `univ.erase m` is the product over `Fin n` through `m.succAbove`. -/
lemma erase_prod_removeNth_g {n : ℕ} {M : Type*} [CommMonoid M] (m : Fin (n + 1)) (F : Fin
        (n + 1) → M) :
    ∏ i ∈ Finset.univ.erase m, F i = ∏ i : Fin n, F (m.succAbove i) := by
  have he : Finset.univ.erase m = ({m}ᶜ : Finset (Fin (n + 1))) := by
    rw [Finset.compl_eq_univ_sdiff, Finset.sdiff_singleton_eq_erase]
  rw [he, ← Fin.image_succAbove_univ m, Finset.prod_image
    (fun i _ j _ h => Fin.succAbove_right_injective h)]



-- factor a single "marked" coordinate over the product box (n = 4)
/-- subadditivity of `Σ_{p ∣ ·} 1/(p − 1)` over a product: for `ρ` with no zero coordinate,
the sum over the prime factors of `Π_i ρ i` is at most `Σ_i` of the sums over the prime
factors of `ρ i`. -/
lemma P_subadd {n : ℕ} (ρ : Fin n → ℕ) (hρ : ∀ i, ρ i ≠ 0) :
    (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
      ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
  classical
  have hsub : (∏ i, ρ i).primeFactors ⊆ Finset.univ.biUnion (fun i => (ρ i).primeFactors) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpdvd := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨i, _, hpi⟩ := (Prime.exists_mem_finset_dvd hpp.prime hpdvd)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Nat.mem_primeFactors.mpr ⟨hpp, hpi, hρ i⟩⟩
  calc (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
      ≤ ∑ p ∈ Finset.univ.biUnion (fun i => (ρ i).primeFactors), (1 / ((p:ℝ) - 1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp _
        rw [Finset.mem_biUnion] at hp
        obtain ⟨i, _, hpi⟩ := hp
        have hpp := Nat.prime_of_mem_primeFactors hpi
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity
    _ ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
        apply mjs_sum_biUnion_le
        intro i _ p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have h2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpp.two_le
        have : (0:ℝ) < (p:ℝ) - 1 := by linarith
        positivity

-- common: enlarge a nonneg per-coordinate weighted sum from kSieveIndex4 (via decBox4)
-- to the product box
/-! ## NEW: the general-`n` relative aggregate moments `T0`, `T1`, `T2` -/

/-- `a^n = a · a^(n − 1)` for `1 ≤ n`. -/
lemma pow_split_g (n : ℕ) (hn : 1 ≤ n) (a : ℝ) : a ^ n = a * a ^ (n - 1) := by
  rw [← pow_succ']; congr 1; omega


/-- B4.2b hypothesis 1: `mv_J_main_split`'s statement, transformed (index set `k = 5 → n + 1`,
`contractAt m F → contractB m P`, `kSieveIndex 5 → kSieveIndex (n+1)`, `^ 4 → ^ n`). -/
def MvJMainSplitGen (n : ℕ) (P : BPoly (n + 1)) (m : Fin (n + 1)) : Prop :=
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
              eval (contractB m P) (fun i => Real.log (r (m.succAbove i)) / Real.log R) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ n
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ n / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ n / D

/-! ## list helpers (copied from MvSplit) -/

/-- for `a i ∈ [0, 1]` on `s`, `1 − Π_{i ∈ s} a i ≤ Σ_{i ∈ s} (1 − a i)`. -/
private lemma one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    have hax := ha x (Finset.mem_insert_self x s)
    have has : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1 := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hih := ih has
    have hsum_nn : 0 ≤ ∑ i ∈ s, (1 - a i) :=
      Finset.sum_nonneg (fun i hi => by have := (has i hi).2; linarith)
    have hprod_nn : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg (fun i hi => (has i hi).1)
    have hprod_le1 : ∏ i ∈ s, a i ≤ 1 :=
      Finset.prod_le_one (fun i hi => (has i hi).1) (fun i hi => (has i hi).2)
    nlinarith only [hax, hsum_nn, hih]


/-- the relative gap at general `n ≥ 1`, under the five hypotheses of `mjs_M0_rel`:
`Σ_{ρ ∈ kSieveIndex n R W'} (1/Π_i gMult (ρ i) − 1/Π_i φ(ρ i))`
`≤ 8n · 2^(n−1) · (phiAtomSum R W')^n / D`. -/
private lemma gap_rel_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W',
        (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)))
      ≤ (8 * (n:ℝ) * 2 ^ (n - 1)) * (Salt.Maynard.phiAtomSum R W') ^ n / (D:ℝ) := by
  classical
  -- per-coordinate: `1 − g(ρᵢ)/φ(ρᵢ) ≤ Q(ρᵢ)`
  have hcoord : ∀ x : ℕ, Squarefree x → x.Coprime W' →
      1 - (gMult x : ℝ) / (Nat.totient x : ℝ) ≤ ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)) := by
    intro x hxsf hxcop
    have hp3 : ∀ p ∈ x.primeFactors, 3 ≤ p := by
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpx := Nat.dvd_of_mem_primeFactors hp
      have hnpW : ¬ p ∣ W' := by
        intro hpW; have h1 : p ∣ 1 := hxcop ▸ Nat.dvd_gcd hpx hpW
        exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
      have := hDW p hpp hnpW; omega
    have hgcast : (gMult x : ℝ) = ∏ p ∈ x.primeFactors, ((p:ℝ) - 2) := gMult_cast hp3
    have hφcast : (Nat.totient x : ℝ) = ∏ p ∈ x.primeFactors, ((p:ℝ) - 1) :=
      totient_squarefree_cast hxsf
    have hφpos : ∀ p ∈ x.primeFactors, (0:ℝ) < (p:ℝ) - 1 := by
      intro p hp
      have hp3p : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp3 p hp
      linarith
    have hratio : (gMult x : ℝ) / (Nat.totient x : ℝ)
        = ∏ p ∈ x.primeFactors, (((p:ℝ) - 2) / ((p:ℝ) - 1)) := by
      rw [hgcast, hφcast, ← Finset.prod_div_distrib]
    rw [hratio]
    have hbnd := one_sub_prod_le_sum x.primeFactors (fun p => ((p:ℝ) - 2) / ((p:ℝ) - 1))
      (fun p hp => by
        have h1 := hφpos p hp
        have h3 : (3:ℝ) ≤ (p:ℝ) := by have := hp3 p hp; exact_mod_cast this
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · rw [div_le_one (by linarith)]; linarith)
    refine le_trans hbnd (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro p hp
    have h1 : ((p:ℝ) - 1) ≠ 0 := (hφpos p hp).ne'
    field_simp
    ring
  -- per-tuple: `1/∏g − 1/∏φ ≤ (∑ᵢ Q(ρᵢ))/∏g`
  have hpertuple : ∀ ρ ∈ kSieveIndex n R W',
      1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)
      ≤ (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) / ∏ i, (gMult (ρ i) : ℝ) := by
    intro ρ hρ
    obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
    have hgpos : ∀ i, (0:ℝ) < (gMult (ρ i) : ℝ) := fun i => by
      have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this
    have hφpos : ∀ i, (0:ℝ) < (Nat.totient (ρ i) : ℝ) := fun i => by
      have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
      exact_mod_cast Nat.totient_pos.mpr this
    have hpg : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => hgpos i)
    have hpφ : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => hφpos i)
    have hgleφ : ∀ i, (gMult (ρ i) : ℝ) ≤ (Nat.totient (ρ i) : ℝ) := fun i => by
      have := gMult_le_totient (hsqf i)
        (fun p hp => by
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpx := Nat.dvd_of_mem_primeFactors hp
          have hnpW : ¬ p ∣ W' := by
            intro hpW; have h1 : p ∣ 1 := (hcop i) ▸ Nat.dvd_gcd hpx hpW
            exact hpp.one_lt.ne' (Nat.dvd_one.mp h1)
          have := hDW p hpp hnpW; omega)
      exact_mod_cast this
    have hprodratio : (∏ i, (gMult (ρ i) : ℝ)) / (∏ i, (Nat.totient (ρ i) : ℝ))
        = ∏ i, ((gMult (ρ i) : ℝ) / (Nat.totient (ρ i) : ℝ)) := by
      rw [← Finset.prod_div_distrib]
    have h1prod : 1 - (∏ i, (gMult (ρ i) : ℝ)) / (∏ i, (Nat.totient (ρ i) : ℝ))
        ≤ ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) := by
      rw [hprodratio]
      refine le_trans (one_sub_prod_le_sum Finset.univ
        (fun i => (gMult (ρ i) : ℝ) / (Nat.totient (ρ i) : ℝ)) (fun i _ => ?_)) ?_
      · exact ⟨div_nonneg (le_of_lt (hgpos i)) (le_of_lt (hφpos i)),
          (div_le_one (hφpos i)).mpr (hgleφ i)⟩
      · exact Finset.sum_le_sum (fun i _ =>
          hcoord (ρ i) (hsqf i) (hcop i))
    have heq : 1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)
        = (1 / ∏ i, (gMult (ρ i) : ℝ))
          * (1 - (∏ i, (gMult (ρ i) : ℝ)) / (∏ i, (Nat.totient (ρ i) : ℝ))) := by
      field_simp
    rw [heq]
    have hrhs : (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) / ∏ i, (gMult (ρ i) : ℝ)
        = (1 / ∏ i, (gMult (ρ i) : ℝ))
          * (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) := by
      rw [one_div, mul_comm, ← div_eq_mul_inv]
    rw [hrhs]
    exact mul_le_mul_of_nonneg_left h1prod (by positivity)
  -- sum + bound via `mjs_T1`-style tail (∑ᵢQ, no `P_subadd`)
  refine le_trans (Finset.sum_le_sum hpertuple) ?_
  -- `∑_{kSieveIndex4} (∑ᵢQ(ρᵢ))/∏g ≤ 8n·2^(n−1) PASⁿ/D`
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) / (gMult x : ℝ) with hMQdef
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQnn : 0 ≤ MQ := Finset.sum_nonneg (fun x _ => div_nonneg (mjs_PFsum_nn _) (by positivity))
  have hMQle : MQ ≤ 8 * PAS / (D:ℝ) := mjs_MQ_rel W' hW' hpos D R hD hDW hR2
  have h1 := enlarge_to_PB (n := n) W' D R hD hDW
    (fun ρ => ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))))
    (fun ρ => Finset.sum_nonneg (fun i _ => mjs_PFsum_nn _))
  refine le_trans h1 ?_
  have hdist : ∀ ρ : Fin n → ℕ,
      (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun ρ => by rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hi : ∀ i : Fin n,
      (∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
        (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ * M0 ^ (n - 1) := by
    intro i
    rw [factor_one F_R i (fun x => ∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1)))]
    congr 1
    rw [hMQdef]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hM0cube : M0 ^ (n - 1) ≤ (2 * PAS) ^ (n - 1) := pow_le_pow_left₀ hM0nn hM0le (n - 1)
  have hMQM0 : MQ * M0 ^ (n - 1) ≤ (8 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1) :=
    mul_le_mul hMQle hM0cube (by positivity) (by positivity)
  calc (n:ℝ) * (MQ * M0 ^ (n - 1)) ≤ (n:ℝ) * ((8 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left hMQM0 (Nat.cast_nonneg _)
    _ = (8 * (n:ℝ) * 2 ^ (n - 1)) * (PAS * PAS ^ (n - 1)) / (D:ℝ) := by rw [mul_pow]; ring
    _ = (8 * (n:ℝ) * 2 ^ (n - 1)) * PAS ^ n / (D:ℝ) := by rw [← pow_split_g n hn PAS]


/-! ### The general-`n` φ pairwise-coprimality drop -/

/-- the relative bad-pair bound: for `W'` squarefree and positive, `2 ≤ R`, coordinates
`i ≠ j` and a prime `p`,
`Σ_{r ∈ decBox n R W', p ∣ r i, p ∣ r j} Π_k 1/φ(r k) ≤ (phiAtomSum R W')^n / (p − 1)²`. -/
private lemma badpair_rel_g (n : ℕ) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (R : ℕ) (hR2 : 2 ≤ R) (i j : Fin n) (hij : i ≠ j) (p : ℕ) (hp : Nat.Prime p) :
    ∑ r ∈ (decBox n R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ (Salt.Maynard.phiAtomSum R W') ^ n / ((p:ℝ) - 1) ^ 2 := by
  classical
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set g : Fin n → ℕ := fun k => if k = i ∨ k = j then p else 1 with hg
  have hp2 : 2 ≤ p := hp.two_le
  have hp1R : (0:ℝ) < (p:ℝ) - 1 := by
    have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    linarith
  have hgpos : ∀ k, 0 < g k := by
    intro k; simp only [hg]; split
    · exact hp.pos
    · exact one_pos
  set coordSet : Fin n → Finset ℕ := fun k =>
    (Finset.range R).filter (fun s => Squarefree s ∧ s.Coprime W' ∧ g k ∣ s) with hcoord
  have hstepA : ∑ r ∈ (decBox n R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ ∏ k, ∑ s ∈ coordSet k, (1 / (Nat.totient s : ℝ)) := by
    exact decBox_filter_pair_le_prod i j (fun s => 1 / (Nat.totient s : ℝ)) (fun s => by positivity)
  set h : Fin n → ℝ := fun k => ∑ s ∈ coordSet k, (1 / (Nat.totient s : ℝ)) with hh
  have hhnn : ∀ k, 0 ≤ h k := fun k => Finset.sum_nonneg (fun s _ => by positivity)
  have hhle : ∀ k, h k ≤ (1 / (Nat.totient (g k) : ℝ)) * PAS := by
    intro k
    have hkey := marked_sqf_phi_rel W' hW' hpos 0 (g k) R (hgpos k) hR2
    have hrw : ∑ s ∈ coordSet k, (Real.log s) ^ 0 / (Nat.totient s : ℝ) = h k := by
      simp only [hh, hcoord, pow_zero]
    rw [hrw, pow_zero, mul_one, ← hPASdef] at hkey
    exact hkey
  have hgi : g i = p := by simp [hg]
  have hgj : g j = p := by simp [hg]
  have hφp : (Nat.totient p : ℝ) = (p:ℝ) - 1 := by
    rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hi_le : h i ≤ PAS / ((p:ℝ) - 1) := by
    have := hhle i; rw [hgi, hφp] at this
    calc h i ≤ 1 / ((p:ℝ) - 1) * PAS := this
      _ = PAS / ((p:ℝ) - 1) := by ring
  have hj_le : h j ≤ PAS / ((p:ℝ) - 1) := by
    have := hhle j; rw [hgj, hφp] at this
    calc h j ≤ 1 / ((p:ℝ) - 1) * PAS := this
      _ = PAS / ((p:ℝ) - 1) := by ring
  have hother : ∀ k ∈ (Finset.univ.erase i).erase j, h k ≤ PAS := by
    intro k hk
    rw [Finset.mem_erase, Finset.mem_erase] at hk
    obtain ⟨hkj, hki, _⟩ := hk
    have hgk : g k = 1 := by simp only [hg]; rw [if_neg (by tauto)]
    have := hhle k; rw [hgk] at this; simpa using this
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  have hsplit : ∏ k, h k = h i * (h j * ∏ k ∈ (Finset.univ.erase i).erase j, h k) := by
    rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i),
        ← Finset.mul_prod_erase (Finset.univ.erase i) h hjmem]
  have hn2 : 2 ≤ n := by
    have hv : (i : ℕ) ≠ (j : ℕ) := fun hv => hij (Fin.ext hv)
    have := i.isLt; have := j.isLt; omega
  have hcard : ((Finset.univ.erase i).erase j).card = n - 2 := by
    rw [Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]; omega
  have hprodrest : ∏ k ∈ (Finset.univ.erase i).erase j, h k ≤ PAS ^ (n - 2) := by
    calc ∏ k ∈ (Finset.univ.erase i).erase j, h k
        ≤ ∏ _k ∈ (Finset.univ.erase i).erase j, PAS :=
          Finset.prod_le_prod (fun k _ => hhnn k) hother
      _ = PAS ^ (n - 2) := by rw [Finset.prod_const, hcard]
  have hbnd : ∏ k, h k
      ≤ (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ (n - 2)) := by
    rw [hsplit]
    apply mul_le_mul hi_le _ (mul_nonneg (hhnn j) (Finset.prod_nonneg (fun k _ => hhnn k)))
      (div_nonneg hPAS0 hp1R.le)
    apply mul_le_mul hj_le hprodrest (Finset.prod_nonneg (fun k _ => hhnn k))
      (div_nonneg hPAS0 hp1R.le)
  have hfinal : (PAS / ((p:ℝ) - 1)) * ((PAS / ((p:ℝ) - 1)) * PAS ^ (n - 2))
      = PAS ^ n / ((p:ℝ) - 1) ^ 2 := by
    have hne : (p:ℝ) - 1 ≠ 0 := ne_of_gt hp1R
    have hpow : PAS ^ n = PAS ^ (n - 2) * PAS ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hn2]
    rw [hpow]; generalize (p:ℝ) - 1 = q; ring
  calc ∑ r ∈ (decBox n R W').filter (fun r => p ∣ r i ∧ p ∣ r j),
        ∏ k, (1 / (Nat.totient (r k) : ℝ))
      ≤ ∏ k, h k := hstepA
    _ ≤ _ := hbnd
    _ = PAS ^ n / ((p:ℝ) - 1) ^ 2 := hfinal

/-- the relative φ pairwise-coprimality drop at general `n`, under the five hypotheses of
`mjs_M0_rel`:
`Σ_{r ∈ decBox n R W' \ kSieveIndex n R W'} Π_i 1/φ(r i) ≤ 2n² · (phiAtomSum R W')^n / D`. -/
private lemma drop_phi_g (n : ℕ) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ r ∈ decBox n R W' \ kSieveIndex n R W', ∏ i, (1 / (Nat.totient (r i) : ℝ)))
      ≤ 2 * (n:ℝ) ^ 2 * (Salt.Maynard.phiAtomSum R W') ^ n / (D : ℝ) := by
  classical
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  set Pairs : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 ≠ q.2) with hPairsdef
  set Primes : Finset ℕ :=
    (Finset.range R).filter (fun p => Nat.Prime p ∧ D < p) with hPrimesdef
  set T : Finset ((Fin n × Fin n) × ℕ) := Pairs ×ˢ Primes with hTdef
  set Bad : (Fin n × Fin n) × ℕ → Finset (Fin n → ℕ) := fun x =>
    (decBox n R W').filter (fun r => x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2) with hBaddef
  set ind : (Fin n × Fin n) × ℕ → (Fin n → ℕ) → ℝ := fun x r =>
    if x.2 ∣ r x.1.1 ∧ x.2 ∣ r x.1.2 then ∏ i, (1 / (Nat.totient (r i) : ℝ)) else 0 with hinddef
  have hindnn : ∀ x r, 0 ≤ ind x r := by
    intro x r; simp only [hinddef]; split_ifs
    · exact Finset.prod_nonneg (fun i _ => by positivity)
    · exact le_refl 0
  have hcover : (∑ r ∈ decBox n R W' \ kSieveIndex n R W', ∏ i, (1 / (Nat.totient (r i) : ℝ)))
      ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
    have hpt : ∀ r ∈ decBox n R W' \ kSieveIndex n R W',
        (∏ i, (1 / (Nat.totient (r i) : ℝ))) ≤ ∑ x ∈ T, ind x r := by
      intro r hr
      obtain ⟨hrdec, hrnk⟩ := Finset.mem_sdiff.mp hr
      have hrdec' := hrdec
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hrdec'
      obtain ⟨hlt, hsqf, hcop, hprod⟩ := hrdec'
      rw [mem_kSieveIndex_iff] at hrnk
      have hpair_neg : ¬ (∀ i j : Fin n, i ≠ j → Nat.Coprime (r i) (r j)) :=
        fun hpair => hrnk ⟨hsqf, hpair, hcop, hprod⟩
      obtain ⟨i, j, p, hij, hp, hpi, hpj, hpW', hpR⟩ :=
        exists_prime_pair_of_not_pairwise_coprime hlt hsqf hcop hpair_neg
      have hDp : D < p := hDW p hp hpW'
      have hpmem : p ∈ Primes := by
        rw [hPrimesdef, Finset.mem_filter, Finset.mem_range]; exact ⟨hpR, hp, hDp⟩
      have hqmem : (i, j) ∈ Pairs := by
        rw [hPairsdef, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩
      have hx0 : ((i, j), p) ∈ T := by rw [hTdef]; exact Finset.mem_product.mpr ⟨hqmem, hpmem⟩
      have hindeq : ind ((i, j), p) r = ∏ i, (1 / (Nat.totient (r i) : ℝ)) := by
        rw [hinddef]; simp only [if_pos (And.intro hpi hpj)]
      rw [← hindeq]
      exact Finset.single_le_sum (fun x _ => hindnn x r) hx0
    calc ∑ r ∈ decBox n R W' \ kSieveIndex n R W', (∏ i, (1 / (Nat.totient (r i) : ℝ)))
        ≤ ∑ r ∈ decBox n R W' \ kSieveIndex n R W', ∑ x ∈ T, ind x r :=
          Finset.sum_le_sum hpt
      _ = ∑ x ∈ T, ∑ r ∈ decBox n R W' \ kSieveIndex n R W', ind x r := Finset.sum_comm
      _ ≤ ∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))) := by
          apply Finset.sum_le_sum
          intro x _
          rw [hinddef, ← Finset.sum_filter]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · rw [hBaddef]
            exact Finset.filter_subset_filter _ Finset.sdiff_subset
          · intro r _ _; exact Finset.prod_nonneg (fun i _ => by positivity)
  have hPairsCard : (Pairs.card : ℝ) ≤ (n:ℝ) ^ 2 := by
    have hc : Pairs.card ≤ n ^ 2 := by
      calc Pairs.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
        _ = n ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]
    exact_mod_cast hc
  have hfinal : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
      ≤ 2 * (n:ℝ) ^ 2 * PAS ^ n / (D : ℝ) := by
    have h1 : (∑ x ∈ T, ∑ r ∈ Bad x, (∏ i, (1 / (Nat.totient (r i) : ℝ))))
        ≤ ∑ x ∈ T, PAS ^ n / ((x.2 : ℝ) - 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [hTdef, Finset.mem_product] at hx
      obtain ⟨hq, hpx⟩ := hx
      rw [hPairsdef, Finset.mem_filter] at hq
      rw [hPrimesdef, Finset.mem_filter] at hpx
      have hbp := badpair_rel_g n W' hW' hpos R hR2 x.1.1 x.1.2 hq.2 x.2 hpx.2.1
      rw [← hPASdef] at hbp
      rw [hBaddef]; exact hbp
    refine le_trans h1 ?_
    rw [hTdef, Finset.sum_product]
    have hPAS4 : 0 ≤ PAS ^ n := pow_nonneg hPAS0 n
    have hinner : ∀ q ∈ Pairs,
        (∑ p ∈ Primes, PAS ^ n / (((q, p).2 : ℝ) - 1) ^ 2) ≤ PAS ^ n * (2 / (D : ℝ)) := by
      intro q _
      have heq : (∑ p ∈ Primes, PAS ^ n / ((p : ℝ) - 1) ^ 2)
          = PAS ^ n * ∑ p ∈ Primes, 1 / ((p : ℝ) - 1) ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun p _ => by ring)
      simp only
      rw [heq]
      exact mul_le_mul_of_nonneg_left (prime_tail D R hD) hPAS4
    calc (∑ q ∈ Pairs, ∑ p ∈ Primes, PAS ^ n / (((q, p).2 : ℝ) - 1) ^ 2)
        ≤ ∑ q ∈ Pairs, PAS ^ n * (2 / (D : ℝ)) := Finset.sum_le_sum hinner
      _ = (Pairs.card : ℝ) * (PAS ^ n * (2 / (D : ℝ))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n:ℝ) ^ 2 * (PAS ^ n * (2 / (D : ℝ))) :=
          mul_le_mul_of_nonneg_right hPairsCard (by positivity)
      _ = 2 * (n:ℝ) ^ 2 * PAS ^ n / (D : ℝ) := by ring
  exact le_trans hcover hfinal

/-! ## `mv_J_main_split_gen` -/

set_option maxHeartbeats 2000000 in
-- the general-`n` square-expansion and absorption calc chains are long; the k = 5 template is too
omit [Salt.Maynard.TupleChoice] in
/-- E2: `MvJMainSplitGen` holds at every `n ≥ 1` (general-`n` port of `MvSplit.mv_J_main_split`). -/
theorem mv_J_main_split_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1)) :
    MvJMainSplitGen n P m := by
  classical
  unfold MvJMainSplitGen
  set Q : BPoly n := sq (contractB m P) with hQdef
  set cF : ℝ := ((contractB m P).map (fun mo => |(mo.2.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _
  refine ⟨(8 * (n:ℝ) * 2 ^ (n - 1) + 2 * (n:ℝ) ^ 2) * cF ^ 2, by positivity, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  -- per-monomial `mv_monomial` constants (φ workhorse, n = 4)
  set Cfun : ((Fin n → ℕ) × ℕ × ℚ) → ℝ :=
    fun mo => Classical.choose (mv_monomial W' hW' hpos hUpper n mo.1 mo.2.1) with hCfundef
  have hCfunspec : ∀ mo, 0 ≤ Cfun mo ∧ ∀ z R : ℕ, 2 ≤ z → z ≤ R → 1 ≤ Real.log R →
      |(∑ ρ ∈ decBox n z W',
            (∏ i, (Real.log (ρ i) / Real.log R) ^ (mo.1 i))
              * ((Real.log z - ∑ i, Real.log (ρ i)) / Real.log R) ^ (mo.2.1)
              / ∏ i, (Nat.totient (ρ i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ n * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)
            * (Real.log z / Real.log R) ^ (n + mo.2.1 + ∑ i, mo.1 i)|
      ≤ Cfun mo * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n - 1) :=
    fun mo => Classical.choose_spec (mv_monomial W' hW' hpos hUpper n mo.1 mo.2.1)
  have hCfun0 : ∀ mo, 0 ≤ Cfun mo := fun mo => (hCfunspec mo).1
  set Cmain : ℝ := (Q.map (fun mo => |(mo.2.2 : ℝ)| * Cfun mo)).sum with hCmaindef
  have hCmain0 : 0 ≤ Cmain := by
    rw [hCmaindef]; apply List.sum_nonneg
    intro x hx; rw [List.mem_map] at hx; obtain ⟨mo, _, rfl⟩ := hx
    exact mul_nonneg (abs_nonneg _) (hCfun0 mo)
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  refine ⟨Cmain / κ, div_nonneg hCmain0 hκpos.le, ?_⟩
  intro R hlogR
  obtain ⟨hRpos, hR2⟩ := Salt.Twelve.nat_pos_two_le_of_one_le_log hlogR
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := (W'.totient : ℝ) / W' * Real.log R with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hXκL : X = κ * L := by rw [hXdef, hκdef, hLdef]
  have hX0 : 0 ≤ X := by rw [hXκL]; exact mul_nonneg hκpos.le hLpos.le
  have hκL1X : κ * L ≤ 1 + X := by rw [← hXκL]; linarith
  have hDpos : (0:ℝ) < (D : ℝ) := by
    have h3 : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  -- the reindexed pieces
  set Ev' : (Fin n → ℕ) → ℝ := fun ρ => eval (contractB m P) (fun i => Real.log (ρ i) / L)
    with hEv'def
  have hEvbd : ∀ ρ ∈ decBox n R W', |Ev' ρ| ≤ cF := by
    intro ρ hr
    simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hr
    obtain ⟨hlt, hsqf, hcop, hprod⟩ := hr
    have hr1 : ∀ i, 1 ≤ ρ i := fun i => Nat.pos_of_ne_zero (hsqf i).ne_zero
    rw [hEv'def, hcFdef]
    apply mjs_eval_bpoly_bound
    · intro i; exact div_nonneg (Real.log_nonneg (by exact_mod_cast hr1 i)) hLpos.le
    · intro i; rw [div_le_one hLpos, hLdef]
      exact Real.log_le_log (by exact_mod_cast hr1 i) (by exact_mod_cast (le_of_lt (hlt i)))
    · rw [← Finset.sum_div, div_le_one hLpos]
      have hSL : ∑ i, Real.log (ρ i) = Real.log ((∏ i, ρ i : ℕ) : ℝ) := by
        rw [Nat.cast_prod]
        exact (Real.log_prod (fun i _ => Nat.cast_ne_zero.mpr (by have := hr1 i; omega))).symm
      rw [hSL, hLdef]
      exact Real.log_le_log (by exact_mod_cast Finset.prod_pos (fun i _ => hr1 i))
        (by exact_mod_cast hprod.le)
  -- reindex the LHS to `∑_{kSieveIndex4} Ev'² / ∏g`
  have hreindex : (∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
        eval (contractB m P) (fun i => Real.log (r (m.succAbove i)) / L) ^ 2
          / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
      = ∑ ρ ∈ kSieveIndex n R W', Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) := by
    rw [← sum_filt_removeNth_g R W' m
      (fun ρ => Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ))]
    apply Finset.sum_congr rfl
    intro r _
    rw [erase_prod_removeNth_g m (fun i => (gMult (r i) : ℝ))]
    simp only [Fin.removeNth_apply, hEv'def]
  rw [hreindex]
  -- the three brackets
  set T_kg : ℝ := ∑ ρ ∈ kSieveIndex n R W', Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) with hTkg
  set T_kφ : ℝ := ∑ ρ ∈ kSieveIndex n R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) with hTkφ
  set T_dφ : ℝ := ∑ ρ ∈ decBox n R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) with hTdφ
  -- bracket 1: gap `T_kg − T_kφ ≤ 8n·2^(n−1) cF² PASⁿ/D`
  have hgap : T_kg - T_kφ ≤ (8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ) := by
    have hkSieve_sub : kSieveIndex n R W' ⊆ decBox n R W' := by
      intro r hr
      obtain ⟨hsqf, _, hcop, hprod⟩ := (mem_kSieveIndex_iff r).mp hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
    have hterm : ∀ ρ ∈ kSieveIndex n R W',
        Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) - Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
        ≤ cF ^ 2 * (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)) := by
      intro ρ hρ
      obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
      have hgpos : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
        have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this)
      have hφpos : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
        have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
        exact_mod_cast Nat.totient_pos.mpr this)
      have hgleφ2 : ∏ i, (gMult (ρ i) : ℝ) ≤ ∏ i, (Nat.totient (ρ i) : ℝ) := by
        apply Finset.prod_le_prod (fun i _ => by positivity)
        intro i _
        have := gMult_le_totient (hsqf i)
          (fun q hq => by
            have hqp := Nat.prime_of_mem_primeFactors hq
            have hqx := Nat.dvd_of_mem_primeFactors hq
            have hnpW : ¬ q ∣ W' := by
              intro hqW; have h1 : q ∣ 1 := (hcop i) ▸ Nat.dvd_gcd hqx hqW
              exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
            have := hDW q hqp hnpW; omega)
        exact_mod_cast this
      have hgapnn : 0 ≤ 1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ) := by
        rw [sub_nonneg]; exact one_div_le_one_div_of_le hgpos hgleφ2
      have hEv2 : Ev' ρ ^ 2 ≤ cF ^ 2 := by
        have := hEvbd ρ (hkSieve_sub hρ)
        nlinarith only [this, hcF0, abs_nonneg (Ev' ρ), sq_abs (Ev' ρ)]
      have hfac : Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) - Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
          = Ev' ρ ^ 2 * (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)) := by
        ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_right hEv2 hgapnn
    have hsum : T_kg - T_kφ ≤ cF ^ 2 * (∑ ρ ∈ kSieveIndex n R W',
        (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ))) := by
      rw [hTkg, hTkφ, ← Finset.sum_sub_distrib, Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    refine le_trans hsum ?_
    have hgr := gap_rel_g n hn W' hW' hpos D R hD hDW hR2
    rw [← hPASdef] at hgr
    calc cF ^ 2 * (∑ ρ ∈ kSieveIndex n R W',
          (1 / ∏ i, (gMult (ρ i) : ℝ) - 1 / ∏ i, (Nat.totient (ρ i) : ℝ)))
        ≤ cF ^ 2 * ((8 * (n:ℝ) * 2 ^ (n - 1)) * PAS ^ n / (D : ℝ))
                := mul_le_mul_of_nonneg_left hgr (by positivity)
      _ = (8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ) := by ring
  -- bracket 2: drop `T_kφ − T_dφ`, `|·| ≤ 2n² cF² PASⁿ/D`
  have hdrop : |T_kφ - T_dφ| ≤ 2 * (n:ℝ) ^ 2 * cF ^ 2 * PAS ^ n / (D : ℝ) := by
    have hkSieve_sub : kSieveIndex n R W' ⊆ decBox n R W' := by
      intro r hr
      obtain ⟨hsqf, _, hcop, hprod⟩ := (mem_kSieveIndex_iff r).mp hr
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      exact ⟨fun i => kSieveIndex_coord_lt hr i, hsqf, hcop, hprod⟩
    have hsdiff : T_dφ - T_kφ = ∑ ρ ∈ decBox n R W' \ kSieveIndex n R W',
        Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) := by
      have h := Finset.sum_sdiff (f := fun ρ => Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ))
        hkSieve_sub
      rw [hTdφ, hTkφ]; linarith [h]
    have hbdd : ∀ ρ ∈ decBox n R W' \ kSieveIndex n R W',
        Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) ≤ cF ^ 2 * ∏ i, (1 / (Nat.totient (ρ i) : ℝ)) := by
      intro ρ hρ
      have hρd := (Finset.mem_sdiff.mp hρ).1
      have hmem := hρd
      simp only [decBox, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hmem
      obtain ⟨hlt, hsqf, hcop, hprod⟩ := hmem
      have hφpos : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
        have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
        exact_mod_cast Nat.totient_pos.mpr this)
      have hEv2 : Ev' ρ ^ 2 ≤ cF ^ 2 := by
        have := hEvbd ρ hρd
        nlinarith only [this, hcF0, abs_nonneg (Ev' ρ), sq_abs (Ev' ρ)]
      have hprodinv : (∏ i, (1 / (Nat.totient (ρ i) : ℝ))) = 1 / ∏ i, (Nat.totient (ρ i) : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_const_one]
      rw [hprodinv, mul_one_div, div_le_div_iff₀ hφpos hφpos]
      nlinarith only [hφpos, hEv2]
    have hnn : 0 ≤ ∑ ρ ∈ decBox n R W' \ kSieveIndex n R W',
        Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ) :=
      Finset.sum_nonneg (fun ρ _ => by positivity)
    have hle : (∑ ρ ∈ decBox n R W' \ kSieveIndex n R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ))
        ≤ 2 * (n:ℝ) ^ 2 * cF ^ 2 * PAS ^ n / (D : ℝ) := by
      calc (∑ ρ ∈ decBox n R W' \ kSieveIndex n R W', Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ))
          ≤ ∑ ρ ∈ decBox n R W' \ kSieveIndex n R W',
              cF ^ 2 * ∏ i, (1 / (Nat.totient (ρ i) : ℝ)) := Finset.sum_le_sum hbdd
        _ = cF ^ 2 * ∑ ρ ∈ decBox n R W' \ kSieveIndex n R W',
              ∏ i, (1 / (Nat.totient (ρ i) : ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ cF ^ 2 * (2 * (n:ℝ) ^ 2 * PAS ^ n / (D : ℝ)) := by
            have hdp := drop_phi_g n W' hW' hpos D R hD hDW hR2
            rw [← hPASdef] at hdp
            exact mul_le_mul_of_nonneg_left hdp (by positivity)
        _ = 2 * (n:ℝ) ^ 2 * cF ^ 2 * PAS ^ n / (D : ℝ) := by ring
    rw [abs_sub_comm, abs_of_nonneg (by rw [hsdiff]; exact hnn)]
    rw [hsdiff]; exact hle
  -- bracket 3: `T_dφ − X⁴J`, `|·| ≤ Cmain (1+X)³`
  have hmain : |T_dφ - X ^ n * ((simplexInt Q : ℚ) : ℝ)| ≤ Cmain * (1 + X) ^ (n - 1) := by
    set MSD : ((Fin n → ℕ) × ℕ × ℚ) → ℝ := fun mo =>
      ∑ ρ ∈ decBox n R W',
        (∏ i, (Real.log (ρ i) / L) ^ (mo.1 i)) * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1)
          / ∏ i, (Nat.totient (ρ i) : ℝ) with hMSDdef
    have hTdφexp : T_dφ = (Q.map (fun mo => (mo.2.2 : ℝ) * MSD mo)).sum := by
      have hbudget : ∀ ρ : Fin n → ℕ,
          (1 : ℝ) - ∑ i, Real.log (ρ i) / L = (L - ∑ i, Real.log (ρ i)) / L := by
        intro ρ; rw [← Finset.sum_div, sub_div, div_self hLne]
      have hper : ∀ ρ ∈ decBox n R W',
          Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
            = (Q.map (fun mo => (mo.2.2 : ℝ) * ((∏ i, (Real.log (ρ i) / L) ^ (mo.1 i))
                * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1)
                / ∏ i, (Nat.totient (ρ i) : ℝ)))).sum := by
        intro ρ _
        rw [hEv'def, ← eval_sq (contractB m P), ← hQdef]
        have hev : eval Q (fun i => Real.log (ρ i) / L)
            = (Q.map (fun mo => (mo.2.2 : ℝ) * (∏ i, (Real.log (ρ i) / L) ^ (mo.1 i))
                * ((L - ∑ i, Real.log (ρ i)) / L) ^ (mo.2.1))).sum := by
          unfold eval
          refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
          dsimp only; rw [hbudget ρ]
        rw [hev, ic_list_sum_div]
        refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
        ring
      rw [hTdφ, Finset.sum_congr rfl hper, ic_sum_finset_list_sum]
      refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
      rw [hMSDdef, ← Finset.mul_sum]
    have hMainSum : X ^ n * ((simplexInt Q : ℚ) : ℝ)
        = (Q.map (fun mo => X ^ n * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))).sum := by
      have hcast : ((simplexInt Q : ℚ) : ℝ)
          = (Q.map (fun mo => (mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))).sum := by
        rw [simplexInt, Rat.cast_list_sum, List.map_map]
        refine congrArg List.sum (List.map_congr_left (fun mo _ => ?_))
        simp only [Function.comp_apply]; push_cast; ring
      rw [hcast, ← List.sum_map_mul_left]
    have hStage3 : ∀ mo : (Fin n → ℕ) × ℕ × ℚ,
        |MSD mo - X ^ n * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)| ≤ Cfun mo * (1 + X) ^ (n - 1) := by
      intro mo
      have hspec := (hCfunspec mo).2 R R hR2 le_rfl hlogR
      rw [← hXdef, ← hLdef, div_self hLne, one_pow, mul_one] at hspec
      exact hspec
    have hPer : ∀ mo ∈ Q,
        |(mo.2.2 : ℝ) * MSD mo - X ^ n * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))|
        ≤ |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ (n - 1) := by
      intro mo _
      have hfac : (mo.2.2 : ℝ) * MSD mo - X ^ n * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))
          = (mo.2.2 : ℝ) * (MSD mo - X ^ n * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)) := by ring
      rw [hfac, abs_mul]
      calc |(mo.2.2 : ℝ)| * |MSD mo - X ^ n * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)|
          ≤ |(mo.2.2 : ℝ)| * (Cfun mo * (1 + X) ^ (n - 1)) :=
            mul_le_mul_of_nonneg_left (hStage3 mo) (abs_nonneg _)
        _ = |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ (n - 1) := by ring
    rw [hTdφexp, hMainSum, ic_list_sum_map_sub]
    calc |(Q.map (fun mo => (mo.2.2 : ℝ) * MSD mo
            - X ^ n * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ)))).sum|
        ≤ (Q.map (fun mo => |(mo.2.2 : ℝ) * MSD mo
            - X ^ n * ((mo.2.2 : ℝ) * ((DInt' mo.1 mo.2.1 : ℚ) : ℝ))|)).sum :=
          ic_list_abs_sum_le _ _
      _ ≤ (Q.map (fun mo => |(mo.2.2 : ℝ)| * Cfun mo * (1 + X) ^ (n - 1))).sum :=
          ic_list_sum_le _ _ _ hPer
      _ = Cmain * (1 + X) ^ (n - 1) := by
          rw [hCmaindef,
            List.sum_map_mul_right Q (fun mo => |(mo.2.2 : ℝ)| * Cfun mo) ((1 + X) ^ (n - 1))]
  -- combine the three brackets and absorb
  have htri : |T_kg - X ^ n * ((simplexInt Q : ℚ) : ℝ)|
      ≤ ((8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ)) + (2 * (n:ℝ) ^ 2 * cF ^ 2
              * PAS ^ n / (D : ℝ))
        + Cmain * (1 + X) ^ (n - 1) := by
    calc |T_kg - X ^ n * ((simplexInt Q : ℚ) : ℝ)|
        ≤ |T_kg - T_kφ| + |T_kφ - T_dφ| + |T_dφ - X ^ n * ((simplexInt Q : ℚ) : ℝ)| := by
          have h1 := abs_sub_le (T_kg) (T_kφ) (X ^ n * ((simplexInt Q : ℚ) : ℝ))
          have h2 := abs_sub_le (T_kφ) (T_dφ) (X ^ n * ((simplexInt Q : ℚ) : ℝ))
          linarith [h1, h2]
      _ ≤ ((8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ)) + (2 * (n:ℝ) ^ 2 * cF ^ 2
              * PAS ^ n / (D : ℝ))
          + Cmain * (1 + X) ^ (n - 1) := by
          have hg2 : |T_kg - T_kφ| ≤ (8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ) := by
            rw [abs_of_nonneg]
            · exact hgap
            · -- `T_kg ≥ T_kφ` since `1/∏g ≥ 1/∏φ`
              rw [hTkg, hTkφ, ← Finset.sum_sub_distrib]
              apply Finset.sum_nonneg
              intro ρ hρ
              obtain ⟨hsqf, _, hcop, _⟩ := (mem_kSieveIndex_iff ρ).mp hρ
              have hgpos : (0:ℝ) < ∏ i, (gMult (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
                have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this)
              have hφpos : (0:ℝ) < ∏ i, (Nat.totient (ρ i) : ℝ) := Finset.prod_pos (fun i _ => by
                have : 0 < ρ i := Nat.pos_of_ne_zero (hsqf i).ne_zero
                exact_mod_cast Nat.totient_pos.mpr this)
              have hgleφ2 : ∏ i, (gMult (ρ i) : ℝ) ≤ ∏ i, (Nat.totient (ρ i) : ℝ) := by
                apply Finset.prod_le_prod (fun i _ => by positivity)
                intro i _
                have := gMult_le_totient (hsqf i)
                  (fun q hq => by
                    have hqp := Nat.prime_of_mem_primeFactors hq
                    have hqx := Nat.dvd_of_mem_primeFactors hq
                    have hnpW : ¬ q ∣ W' := by
                      intro hqW; have h1 : q ∣ 1 := (hcop i) ▸ Nat.dvd_gcd hqx hqW
                      exact hqp.one_lt.ne' (Nat.dvd_one.mp h1)
                    have := hDW q hqp hnpW; omega)
                exact_mod_cast this
              have hEvnn : 0 ≤ Ev' ρ ^ 2 := sq_nonneg _
              have : Ev' ρ ^ 2 / ∏ i, (Nat.totient (ρ i) : ℝ)
                  ≤ Ev' ρ ^ 2 / ∏ i, (gMult (ρ i) : ℝ) :=
                div_le_div_of_nonneg_left hEvnn hgpos hgleφ2
              linarith
          linarith [hg2, hdrop]
  refine le_trans htri ?_
  -- absorb
  have hPAS15 : PAS ^ n ≤ (1 + PAS) ^ n := pow_le_pow_left₀ hPAS0 (by linarith) n
  have hDside : ((8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ)) + (2 * (n:ℝ) ^ 2
          * cF ^ 2 * PAS ^ n / (D : ℝ))
      ≤ ((8 * (n:ℝ) * 2 ^ (n - 1)) + 2 * (n:ℝ) ^ 2) * cF ^ 2 * (1 + PAS) ^ n / (D : ℝ) := by
    have he : ((8 * (n:ℝ) * 2 ^ (n - 1)) * cF ^ 2 * PAS ^ n / (D : ℝ)) + (2 * (n:ℝ) ^ 2 * cF ^ 2
            * PAS ^ n / (D : ℝ))
        = ((8 * (n:ℝ) * 2 ^ (n - 1)) + 2 * (n:ℝ) ^ 2) * cF ^ 2 / (D : ℝ) * PAS ^ n := by ring
    rw [he]
    calc ((8 * (n:ℝ) * 2 ^ (n - 1)) + 2 * (n:ℝ) ^ 2) * cF ^ 2 / (D : ℝ) * PAS ^ n
        ≤ ((8 * (n:ℝ) * 2 ^ (n - 1)) + 2 * (n:ℝ) ^ 2) * cF ^ 2 / (D : ℝ) * (1 + PAS) ^ n :=
          mul_le_mul_of_nonneg_left hPAS15 (div_nonneg (by positivity) hDpos.le)
      _ = ((8 * (n:ℝ) * 2 ^ (n - 1)) + 2 * (n:ℝ) ^ 2) * cF ^ 2 * (1 + PAS) ^ n / (D : ℝ) := by ring
  have hLside : Cmain * (1 + X) ^ (n - 1) ≤ Cmain / κ * (1 + X) ^ n / L := by
    have h3 : (1 + X) ^ (n - 1) ≤ (1 + X) ^ n / (κ * L) := by
      rw [le_div_iff₀ (mul_pos hκpos hLpos)]
      calc (1 + X) ^ (n - 1) * (κ * L) ≤ (1 + X) ^ (n - 1) * (1 + X) := by
            apply mul_le_mul_of_nonneg_left hκL1X (by positivity)
        _ = (1 + X) ^ n := by rw [pow_split_g n hn (1 + X)]; ring
    have e2 : Cmain / κ * (1 + X) ^ n / L = Cmain * ((1 + X) ^ n / (κ * L)) := by
      have hκne : κ ≠ 0 := ne_of_gt hκpos
      field_simp
    rw [e2]; exact mul_le_mul_of_nonneg_left h3 hCmain0
  linarith [hDside, hLside]


end Salt.MaynardK
