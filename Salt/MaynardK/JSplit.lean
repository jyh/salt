/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.MvSplit
import Salt.MaynardK.ICRel
import Salt.MaynardK.JMainSplit

/-!
# C1 · B4.2b — `mv_J_split` at general `n` (`mv_J_split_gen`)

`mv_J_split_gen_of` derives the J-side split engine from the two `Prop`s `MvJMainSplitGen` and
`InnerContractRelGen` (ported, as a falsifier, by an Opus executor from a frozen brief, 2026-10-11);
`mv_J_split_gen` discharges both with `mv_J_main_split_gen` (`JMainSplit`) and
`inner_contract_rel_gen` (`ICRel`). `mv_J_split_of_gen` (in `Controls`) re-derives the landed k = 5
statement (its private `mv_J_main_split` entering as a hypothesis).
-/

open Finset

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Twelve Salt.Maynard Salt.MaynardK

/-! ### Relative one-coordinate g-moments (`M0`, `MQ`, `MQ2`) over `sqfCop R W'` -/

/-! ### The 4-dim aggregate g-moments `T0` (opaque), `T1`, `T2` (relative) -/

-- factor a single "marked" coordinate over the product box (n = 4)
/-! ## NEW: the general-`n` relative aggregate moments `T0`, `T1`, `T2` -/

/-- the opaque aggregate `T0` at general `n ≥ 1`: under the `hcg` bound (as in `mjs_M0_op`),
`W'` squarefree and positive, `3 ≤ D`, every prime `∤ W'` above `D`, `2 ≤ R`,
`Σ_{ρ ∈ kSieveIndex n R W'} 1/Π_i gMult (ρ i) ≤ (cg · log R)^n` (`0 ≤ cg` carried unused). -/
private lemma T0_op_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
        (cg : ℝ) (_hcg0 : 0 ≤ cg)
    (hcg : ∀ D s z : ℕ, 3 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) → 0 < s → 2 ≤ z →
      (∑ r ∈ (Finset.range z).filter (fun r => Squarefree r ∧ r.Coprime W' ∧ s ∣ r),
        (Real.log r) ^ 0 / (gMult r : ℝ)) ≤ (1 / (gMult s : ℝ)) * cg * (Real.log z) ^ (0 + 1))
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ)) ≤ (cg * Real.log R) ^ n := by
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ cg * Real.log R := mjs_M0_op W' hW' hpos cg hcg D R hD hDW hR2
  have h1 := enlarge_to_PB (n := n) W' D R hD hDW (fun _ => (1:ℝ)) (fun _ => zero_le_one)
  refine le_trans h1 ?_
  have hfac := factor_one F_R ⟨0, hn⟩ (fun _ => (1:ℝ))
  simp only [one_mul] at hfac ⊢
  rw [hfac]
  calc (∑ x ∈ F_R, (1 / (gMult x : ℝ))) * (∑ x ∈ F_R, (1 / (gMult x : ℝ))) ^ (n - 1)
      = M0 ^ n := by rw [pow_split_g n hn M0]
    _ ≤ (cg * Real.log R) ^ n := pow_le_pow_left₀ hM0nn hM0le n

/-- the relative aggregate `T1` at general `n ≥ 1`, under the five hypotheses of `mjs_M0_rel`:
`Σ_{ρ ∈ kSieveIndex n R W'} (Σ_{p ∣ Π ρ} 1/(p − 1)) / Π_i gMult (ρ i)`
`≤ 8n · 2^(n−1) · (phiAtomSum R W')^n / D`. -/
private lemma T1_rel_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ))
      ≤ (8 * (n:ℝ) * 2 ^ (n - 1)) * (Salt.Maynard.phiAtomSum R W') ^ n / (D:ℝ) := by
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
    (fun ρ => ∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) (fun ρ => mjs_PFsum_nn _)
  refine le_trans h1 ?_
  have hstep2 : ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ Fintype.piFinset (fun _ : Fin n => F_R),
          (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ i, (1 / (gMult (ρ i) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    exact mul_le_mul_of_nonneg_right (P_subadd ρ hρne)
      (Finset.prod_nonneg (fun i _ => by positivity))
  refine le_trans hstep2 ?_
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

/-- the relative aggregate `T2` at general `n ≥ 1`, under the five hypotheses of `mjs_M0_rel`:
`Σ_{ρ ∈ kSieveIndex n R W'} (Σ_{p ∣ Π ρ} 1/(p − 1))² / Π_i gMult (ρ i)`
`≤ 40n² · 2^(n−1) · (phiAtomSum R W')^n / D`. -/
private lemma T2_rel_g (n : ℕ) (hn : 1 ≤ n) (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (D R : ℕ) (hD : 3 ≤ D) (hDW : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) (hR2 : 2 ≤ R) :
    (∑ ρ ∈ kSieveIndex n R W',
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ))
      ≤ (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * (Salt.Maynard.phiAtomSum R W') ^ n / (D:ℝ) := by
  set PAS := Salt.Maynard.phiAtomSum R W' with hPAS
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hDR : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hDpos : (0:ℝ) < (D:ℝ) := by linarith
  set F_R := (Finset.range R).filter (fun x => Squarefree x ∧ x.Coprime W') with hF_R
  set PB := Fintype.piFinset (fun _ : Fin n => F_R) with hPBdef
  set M0 := ∑ x ∈ F_R, (1 / (gMult x : ℝ)) with hM0def
  set MQ2 := ∑ x ∈ F_R, (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / (gMult x : ℝ) with hMQ2def
  have hM0nn : 0 ≤ M0 := Finset.sum_nonneg (fun x _ => by positivity)
  have hM0le : M0 ≤ 2 * PAS := mjs_M0_rel W' hW' hpos D R hD hDW hR2
  have hMQ2le : MQ2 ≤ 40 * PAS / (D:ℝ) := mjs_MQ2_rel W' hW' hpos D R hD hDW hR2
  have hQsqmom : ∀ i : Fin n,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = MQ2 * M0 ^ (n - 1) := by
    intro i
    rw [hPBdef, factor_one F_R i (fun x => (∑ p ∈ x.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)]
    congr 1
    rw [hMQ2def]; apply Finset.sum_congr rfl; intro x _; rw [mul_one_div]
  have h1 := enlarge_to_PB (n := n) W' D R hD hDW
    (fun ρ => (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) (fun ρ => sq_nonneg _)
  refine le_trans h1 ?_
  rw [← hPBdef]
  have hstep2 : ∑ ρ ∈ PB,
        (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 * ∏ i, (1 / (gMult (ρ i) : ℝ))
      ≤ ∑ ρ ∈ PB, (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    apply Finset.sum_le_sum; intro ρ hr
    rw [hPBdef, Fintype.mem_piFinset] at hr
    have hρne : ∀ i, ρ i ≠ 0 := fun i => by
      have := hr i; rw [hF_R, Finset.mem_filter, Finset.mem_range] at this; exact this.2.1.ne_zero
    have hsub := P_subadd ρ hρne
    have hsq : (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
        ≤ (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2 :=
      pow_le_pow_left₀ (mjs_PFsum_nn _) hsub 2
    have hexp : (∑ i, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))) ^ 2
        = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
              * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) := by rw [pow_two, sum_mul_sum]
    rw [hexp] at hsq
    exact mul_le_mul_of_nonneg_right hsq (Finset.prod_nonneg (fun k _ => by positivity))
  refine le_trans hstep2 ?_
  have hdist : ∀ ρ : Fin n → ℕ,
      (∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
      = ∑ i, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) := by
    intro ρ; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun ρ _ => hdist ρ), Finset.sum_comm]
  have hswapj : ∀ i : Fin n,
      (∑ ρ ∈ PB, ∑ j, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      = ∑ j, ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => hswapj i)]
  have hij : ∀ i j : Fin n,
      (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ MQ2 * M0 ^ (n - 1) := by
    intro i j
    have hamgm : ∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ))
        ≤ ∑ ρ ∈ PB, (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
            * ∏ k, (1 / (gMult (ρ k) : ℝ))
            + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
              * ∏ k, (1 / (gMult (ρ k) : ℝ))) := by
      apply Finset.sum_le_sum; intro ρ _
      have hprodnn : 0 ≤ ∏ k, (1 / (gMult (ρ k) : ℝ)) :=
        Finset.prod_nonneg (fun k _ => by positivity)
      have hamg : (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
            * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1)))
          ≤ (1/2) * ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2
              + (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2) := by
        nlinarith [sq_nonneg ((∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          - (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))))]
      linarith only [mul_le_mul_of_nonneg_right hamg hprodnn]
    refine le_trans hamgm (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hQsqmom i, hQsqmom j]; ring
  calc ∑ i, ∑ j, (∑ ρ ∈ PB, (∑ p ∈ (ρ i).primeFactors, (1 / ((p:ℝ) - 1)))
          * (∑ p ∈ (ρ j).primeFactors, (1 / ((p:ℝ) - 1))) * ∏ k, (1 / (gMult (ρ k) : ℝ)))
      ≤ ∑ i : Fin n, ∑ j : Fin n, MQ2 * M0 ^ (n - 1) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hij i j))
    _ = (n:ℝ) ^ 2 * (MQ2 * M0 ^ (n - 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    _ ≤ (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * PAS ^ n / (D:ℝ) := by
        have hM0cube : M0 ^ (n - 1) ≤ (2 * PAS) ^ (n - 1) := pow_le_pow_left₀ hM0nn hM0le (n - 1)
        have hMM : MQ2 * M0 ^ (n - 1) ≤ (40 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1) :=
          mul_le_mul hMQ2le hM0cube (by positivity) (by positivity)
        calc (n:ℝ) ^ 2 * (MQ2 * M0 ^ (n - 1))
            ≤ (n:ℝ) ^ 2 * ((40 * PAS / (D:ℝ)) * (2 * PAS) ^ (n - 1)) :=
              mul_le_mul_of_nonneg_left hMM (by positivity)
          _ = (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * (PAS * PAS ^ (n - 1)) / (D:ℝ) := by
              rw [mul_pow]; ring
          _ = (40 * (n:ℝ) ^ 2 * 2 ^ (n - 1)) * PAS ^ n / (D:ℝ) := by
              rw [← pow_split_g n hn PAS]

/-- general-`n` `mjs_absorb`: the mixed-base absorptions of the opaque `1/L` pieces. -/
private lemma absorb_g (n : ℕ) (κ L : ℝ) (hκ : 0 < κ) (hL : 1 ≤ L) :
    κ * L * L ^ n ≤ 1 / κ ^ (n + 1) * (1 + κ * L) ^ (n + 2) * (1 / L)
    ∧ L ^ n ≤ 1 / κ ^ (n + 2) * (1 + κ * L) ^ (n + 2) * (1 / L) := by
  have hLpos : 0 < L := by linarith
  have hbase : (κ * L) ^ (n + 2) ≤ (1 + κ * L) ^ (n + 2) :=
    pow_le_pow_left₀ (by positivity) (by linarith) (n + 2)
  constructor
  · rw [show 1 / κ ^ (n + 1) * (1 + κ * L) ^ (n + 2) * (1 / L)
        = (1 + κ * L) ^ (n + 2) / (κ ^ (n + 1) * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc κ * L * L ^ n * (κ ^ (n + 1) * L) = (κ * L) ^ (n + 2) := by ring
      _ ≤ (1 + κ * L) ^ (n + 2) := hbase
  · rw [show 1 / κ ^ (n + 2) * (1 + κ * L) ^ (n + 2) * (1 / L)
        = (1 + κ * L) ^ (n + 2) / (κ ^ (n + 2) * L) by field_simp,
      le_div_iff₀ (by positivity)]
    calc L ^ n * (κ ^ (n + 2) * L) = κ ^ (n + 2) * L ^ (n + 1) := by ring
      _ ≤ κ ^ (n + 2) * L ^ (n + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc L ^ (n + 1) = L ^ (n + 1) * 1 := by ring
            _ ≤ L ^ (n + 1) * L := by apply mul_le_mul_of_nonneg_left hL (by positivity)
            _ = L ^ (n + 2) := by ring
      _ = (κ * L) ^ (n + 2) := by ring
      _ ≤ (1 + κ * L) ^ (n + 2) := hbase

set_option maxHeartbeats 2000000 in
-- the general-`n` square-expansion and absorption calc chains are long; the k = 5 template is too
omit [Salt.Maynard.TupleChoice] in
/-- the J-side split engine at general `n ≥ 1`, derived from the two `Prop`s
`MvJMainSplitGen n P m` and `InnerContractRelGen n P m`: some `A ≥ 0` such that for
admissible `W'`, `D` (`W'` squarefree and positive, `PhiUpperAtom`, `3 ≤ D`, every prime
`∤ W'` above `D`), some `c ≥ 0` with, for `1 ≤ log R`,
`|Σ_{r ∈ kSieveIndex (n+1) R W', r m = 1} (Σ_{u < R} yFg R W' P (update r m u)/φ(u))²`
`/ Π_{i ≠ m} gMult (r i) − (φ(W')/W' · log R)^(n+2) · ∫ (contractB m P)²|`
`≤ c · (1 + φ(W')/W' · log R)^(n+2) / log R`
`+ A · (1 + φ(W')/W' · log R + phiAtomSum R W')^(n+2) / D`. -/
theorem mv_J_split_gen_of (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1))
    (hMain : MvJMainSplitGen n P m) (hIC : InnerContractRelGen n P m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D := by
  classical
  obtain ⟨Amain, hAmain0, hAmain⟩ := hMain
  obtain ⟨Aic, hAic0, hAic⟩ := hIC
  set cF : ℝ := ((contractB m P).map (fun mo => |(mo.2.2 : ℝ)|)).sum with hcFdef
  have hcF0 : 0 ≤ cF := by
    rw [hcFdef]; apply List.sum_nonneg; intro x hx; rw [List.mem_map] at hx
    obtain ⟨mo, _, rfl⟩ := hx; exact abs_nonneg _
  set C1 : ℝ := 8 * (n:ℝ) * 2 ^ (n - 1) with hC1def
  set C2 : ℝ := 40 * (n:ℝ) ^ 2 * 2 ^ (n - 1) with hC2def
  have hC1 : 0 ≤ C1 := by rw [hC1def]; positivity
  have hC2 : 0 ≤ C2 := by rw [hC2def]; positivity
  refine ⟨Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2, by
    have h1 : 0 ≤ (2 * C1) * cF * Aic := by
      apply mul_nonneg (mul_nonneg (by linarith) hcF0) hAic0
    have h2 : 0 ≤ (2 * C2) * Aic ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  obtain ⟨cg, hcg0, hcg⟩ := marked_sqf_g W' hW' hpos 0
  obtain ⟨cmain, hcmain0, hcmain⟩ := hAmain W' D hW' hpos hUpper hD hDW
  obtain ⟨cic, hcic0, hcic⟩ := hAic W' D hW' hpos hUpper hD hDW
  set κ : ℝ := (W'.totient : ℝ) / W' with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hpos) (by exact_mod_cast hpos)
  have hκle1 : κ ≤ 1 := by
    rw [hκdef, div_le_one (by exact_mod_cast hpos)]; exact_mod_cast Nat.totient_le W'
  refine ⟨cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2),
          by positivity, ?_⟩
  intro R hlogR
  obtain ⟨hRpos, hR2⟩ := Salt.Twelve.nat_pos_two_le_of_one_le_log hlogR
  set L : ℝ := Real.log R with hLdef
  set X : ℝ := κ * L with hXdef
  set PAS : ℝ := Salt.Maynard.phiAtomSum R W' with hPASdef
  have hPAS0 : 0 ≤ PAS := pas_nonneg R W'
  have hL1 : 1 ≤ L := hlogR
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hDpos : (0:ℝ) < (D:ℝ) := by
    have : (3:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    linarith
  have hclogR : 0 ≤ cg * L := mul_nonneg hcg0 hLpos.le
  set Y : ℝ := 1 + X + PAS with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith
  have hXY : X ≤ Y := by rw [hYdef]; linarith
  have hPASY : PAS ≤ Y := by rw [hYdef]; linarith
  have h1PASY : 1 + PAS ≤ Y := by rw [hYdef]; linarith
  have hY0 : 0 ≤ Y := by linarith
  -- abbreviations
  set filt := (kSieveIndex (n + 1) R W').filter (fun r => r m = 1) with hfiltdef
  set Denom : (Fin (n + 1) → ℕ) → ℝ := fun r => ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ)
    with hDenomdef
  set Inn : (Fin (n + 1) → ℕ) → ℝ := fun r => ∑ u ∈ Finset.range R,
      yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ) with hInndef
  set Ev : (Fin (n + 1) → ℕ) → ℝ := fun r =>
      eval (contractB m P) (fun i => Real.log (r (m.succAbove i)) / L) with hEvdef
  set Pr : (Fin (n + 1) → ℕ) → ℝ := fun r =>
      ∑ p ∈ (∏ i, r i).primeFactors, (1 / ((p:ℝ) - 1)) with hPrdef
  have hX_eq : (W'.totient : ℝ) / W' * Real.log R = X := by rw [hXdef, hκdef, hLdef]
  -- Denom positive on filt
  have hDenompos : ∀ r ∈ filt, 0 < Denom r := by
    intro r hr; rw [hfiltdef, Finset.mem_filter, mem_kSieveIndex_iff] at hr
    obtain ⟨⟨hsqf, _, hcop, _⟩, _⟩ := hr
    rw [hDenomdef]; apply Finset.prod_pos; intro i _
    have := box_g_pos (hsqf i) (hcop i) hD hDW; exact_mod_cast this
  have hprodeq : ∀ r ∈ filt, (∏ i, r i) = ∏ i : Fin n, r (m.succAbove i) := by
    intro r hr; rw [hfiltdef, Finset.mem_filter] at hr
    rw [Fin.prod_univ_succAbove (fun j => r j) m, hr.2, one_mul]
  -- |Ev| ≤ cF on filt
  have hEvbd : ∀ r ∈ filt, |Ev r| ≤ cF := by
    intro r hr
    have hrmem := hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have hrk := hr.1
    rw [hEvdef, hcFdef]
    apply mjs_eval_bpoly_bound
    · intro i; apply div_nonneg (Real.log_nonneg _) hLpos.le
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (kSieveIndex_coord_pos hrk (m.succAbove i)).ne'
    · intro i; rw [div_le_one hLpos, hLdef]
      exact Real.log_le_log (by exact_mod_cast kSieveIndex_coord_pos hrk (m.succAbove i))
        (by exact_mod_cast (kSieveIndex_coord_lt hrk (m.succAbove i)).le)
    · have hpe := hprodeq r hrmem
      have hprodlt : (∏ i, r i) < R := ((mem_kSieveIndex_iff r).mp hrk).2.2.2
      have hlogsum : (∑ i : Fin n, Real.log (r (m.succAbove i))) = Real.log ((∏ i, r i : ℕ):ℝ) := by
        have h1 : ((∏ i, r i : ℕ):ℝ) = ∏ i : Fin n, ((r (m.succAbove i) : ℕ):ℝ) := by
          rw [hpe, Nat.cast_prod]
        rw [h1, Real.log_prod
          (fun i _ => by exact_mod_cast (kSieveIndex_coord_pos hrk (m.succAbove i)).ne')]
      rw [← Finset.sum_div, div_le_one hLpos, hlogsum, hLdef]
      exact Real.log_le_log
        (by exact_mod_cast Finset.prod_pos (fun i _ => kSieveIndex_coord_pos hrk i))
        (by exact_mod_cast hprodlt.le)
  -- inner_contract_rel per r
  have hInnbd : ∀ r ∈ filt, |Inn r - X * Ev r| ≤ cic + Aic * PAS * Pr r := by
    intro r hr
    rw [hfiltdef, Finset.mem_filter] at hr
    have := hcic R hlogR r hr.1 hr.2
    rw [hX_eq] at this
    exact this
  -- the reindex helper
  have hreindex_gen : ∀ (gn : ℕ → ℝ),
      (∑ r ∈ filt, gn (∏ i, r i) / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W', gn (∏ i, ρ i) / ∏ i, (gMult (ρ i) : ℝ) := by
    intro gn
    rw [← sum_filt_removeNth_g R W' m (fun ρ => gn (∏ i, ρ i) / ∏ i, (gMult (ρ i) : ℝ))]
    rw [hfiltdef]
    apply Finset.sum_congr rfl
    intro r hr
    have hrf : r ∈ filt := by rw [hfiltdef]; exact hr
    simp only [hDenomdef, Fin.removeNth_apply]
    rw [erase_prod_removeNth_g m (fun i => (gMult (r i):ℝ)), hprodeq r hrf]
  -- S0, S1, S2 bounds
  have hS0le : (∑ r ∈ filt, (1:ℝ) / Denom r) ≤ (cg * L) ^ n := by
    have key : (∑ r ∈ filt, (1:ℝ) / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W', (1:ℝ) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun _ => 1)
    rw [key]; exact T0_op_g n hn W' hW' hpos cg hcg0 hcg D R hD hDW hR2
  have hS1le : (∑ r ∈ filt, Pr r / Denom r) ≤ C1 * PAS ^ n / (D:ℝ) := by
    have key : (∑ r ∈ filt, Pr r / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => ∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1)))
    rw [key, hPASdef]; exact T1_rel_g n hn W' hW' hpos D R hD hDW hR2
  have hS2le : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) ≤ C2 * PAS ^ n / (D:ℝ) := by
    have key : (∑ r ∈ filt, (Pr r) ^ 2 / Denom r)
        = ∑ ρ ∈ kSieveIndex n R W',
            (∑ p ∈ (∏ i, ρ i).primeFactors, (1 / ((p:ℝ) - 1))) ^ 2 / ∏ i, (gMult (ρ i) : ℝ) :=
      hreindex_gen (fun N => (∑ p ∈ N.primeFactors, (1 / ((p:ℝ) - 1))) ^ 2)
    rw [key, hPASdef]; exact T2_rel_g n hn W' hW' hpos D R hD hDW hR2
  -- === main part via mv_J_main_split ===
  have hEvSum : |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ n * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ n / L + Amain * (1 + PAS) ^ n / (D:ℝ) := by
    have h := hcmain R hlogR
    rw [hX_eq, ← hLdef, ← hPASdef] at h
    exact h
  have hmainpart : |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
        - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
      ≤ cmain * (1 + X) ^ (n + 2) / L + Amain * Y ^ (n + 2) / (D:ℝ) := by
    have hfac : X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)
        = X ^ 2 * ((∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
          - X ^ n * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)) := by ring
    rw [hfac, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ X ^ 2)]
    -- X² · (1/L-bound + 1/D-bound)
    have hLpart : X ^ 2 * (cmain * (1 + X) ^ n / L) ≤ cmain * (1 + X) ^ (n + 2) / L := by
      have hXsq : X ^ 2 ≤ (1 + X) ^ 2 := pow_le_pow_left₀ hX0 (by linarith) 2
      have e : X ^ 2 * (cmain * (1 + X) ^ n / L) = cmain * (X ^ 2 * (1 + X) ^ n) / L := by ring
      have e2 : cmain * (1 + X) ^ (n + 2) / L = cmain * ((1 + X) ^ 2 * (1 + X) ^ n) / L := by ring
      rw [e, e2]
      refine div_le_div_of_nonneg_right ?_ hLpos.le
      refine mul_le_mul_of_nonneg_left ?_ hcmain0
      exact mul_le_mul_of_nonneg_right hXsq (by positivity)
    have hDpart : X ^ 2 * (Amain * (1 + PAS) ^ n / (D:ℝ)) ≤ Amain * Y ^ (n + 2) / (D:ℝ) := by
      have hkey : X ^ 2 * (1 + PAS) ^ n ≤ Y ^ (n + 2) := by
        calc X ^ 2 * (1 + PAS) ^ n ≤ Y ^ 2 * Y ^ n :=
              mul_le_mul (pow_le_pow_left₀ hX0 hXY 2) (pow_le_pow_left₀ (by linarith) h1PASY n)
                (by positivity) (by positivity)
          _ = Y ^ (n + 2) := by ring
      have e : X ^ 2 * (Amain * (1 + PAS) ^ n / (D:ℝ))
          = Amain * (X ^ 2 * (1 + PAS) ^ n) / (D:ℝ) := by
        ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ hDpos.le
      exact mul_le_mul_of_nonneg_left hkey hAmain0
    calc X ^ 2 * |(∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ n * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ X ^ 2 * (cmain * (1 + X) ^ n / L + Amain * (1 + PAS) ^ n / (D:ℝ)) :=
          mul_le_mul_of_nonneg_left hEvSum (by positivity)
      _ = X ^ 2 * (cmain * (1 + X) ^ n / L) + X ^ 2 * (Amain * (1 + PAS) ^ n / (D:ℝ)) := by ring
      _ ≤ cmain * (1 + X) ^ (n + 2) / L + Amain * Y ^ (n + 2) / (D:ℝ) := add_le_add hLpart hDpart
  -- === error part (Approach A: Inn² − X²Ev² = 2X·Ev·δ + δ²) ===
  have hPrnn : ∀ r, 0 ≤ Pr r := fun r => by rw [hPrdef]; exact mjs_PFsum_nn _
  have hterm : ∀ r ∈ filt,
      |(Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)|
      ≤ ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r := by
    intro r hr
    have hdpos := hDenompos r hr
    have hE := hEvbd r hr
    have hI := hInnbd r hr
    have hPr := hPrnn r
    set δ : ℝ := Inn r - X * Ev r with hδdef
    set Q : ℝ := Aic * PAS * Pr r with hQdef
    have hQnn : 0 ≤ Q := by rw [hQdef]; positivity
    have hδbd : |δ| ≤ cic + Q := by rw [hδdef, hQdef]; exact hI
    have hnum : (Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2 = 2 * X * (Ev r) * δ + δ ^ 2 := by
      rw [hδdef]; ring
    have habs : |(Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2|
        ≤ (2 * X * cF * cic + 2 * cic ^ 2) + 2 * X * cF * Aic * PAS * Pr r
          + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2 := by
      rw [hnum]
      have h1 : |2 * X * (Ev r) * δ| = 2 * X * |Ev r| * |δ| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * X)]
      have h2 : |2 * X * (Ev r) * δ| ≤ 2 * X * cF * (cic + Q) := by
        rw [h1]
        have hb : |Ev r| * |δ| ≤ cF * (cic + Q) :=
          mul_le_mul hE hδbd (abs_nonneg _) hcF0
        calc 2 * X * |Ev r| * |δ| = 2 * X * (|Ev r| * |δ|) := by ring
          _ ≤ 2 * X * (cF * (cic + Q)) := mul_le_mul_of_nonneg_left hb (by positivity)
          _ = 2 * X * cF * (cic + Q) := by ring
      have h3 : |δ ^ 2| ≤ 2 * cic ^ 2 + 2 * Q ^ 2 := by
        rw [abs_pow]
        have hsq : |δ| ^ 2 ≤ (cic + Q) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hδbd 2
        linarith only [hsq, sq_nonneg (cic - Q)]
      have hcomb : 2 * X * cF * (cic + Q) + (2 * cic ^ 2 + 2 * Q ^ 2)
          = (2 * X * cF * cic + 2 * cic ^ 2) + 2 * X * cF * Aic * PAS * Pr r
            + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2 := by rw [hQdef]; ring
      calc |2 * X * (Ev r) * δ + δ ^ 2|
          ≤ |2 * X * (Ev r) * δ| + |δ ^ 2| := abs_add_le _ _
        _ ≤ 2 * X * cF * (cic + Q) + (2 * cic ^ 2 + 2 * Q ^ 2) := add_le_add h2 h3
        _ = _ := hcomb
    have heq : (Inn r) ^ 2 / Denom r - X ^ 2 * ((Ev r) ^ 2 / Denom r)
        = ((Inn r) ^ 2 - X ^ 2 * (Ev r) ^ 2) / Denom r := by ring
    rw [heq, abs_div, abs_of_pos hdpos]
    exact div_le_div_of_nonneg_right habs hdpos.le
  have herr : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
      ≤ ∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hbound_eq : (∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r)
      = (2 * X * cF * cic + 2 * cic ^ 2) * (∑ r ∈ filt, 1 / Denom r)
        + (2 * X * cF * Aic * PAS) * (∑ r ∈ filt, Pr r / Denom r)
        + (2 * Aic ^ 2 * PAS ^ 2) * (∑ r ∈ filt, (Pr r) ^ 2 / Denom r) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have herr2 : (∑ r ∈ filt, ((2 * X * cF * cic + 2 * cic ^ 2)
          + 2 * X * cF * Aic * PAS * Pr r + 2 * Aic ^ 2 * PAS ^ 2 * (Pr r) ^ 2) / Denom r)
      ≤ (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
        + (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
        + (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ)) := by
    rw [hbound_eq]
    have c0 : 0 ≤ 2 * X * cF * cic + 2 * cic ^ 2 := by positivity
    have c1 : 0 ≤ 2 * X * cF * Aic * PAS := by positivity
    have c2 : 0 ≤ 2 * Aic ^ 2 * PAS ^ 2 := by positivity
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact mul_le_mul_of_nonneg_left hS0le c0
    · exact mul_le_mul_of_nonneg_left hS1le c1
    · exact mul_le_mul_of_nonneg_left hS2le c2
  -- === absorptions ===
  obtain ⟨habsXL0, habsL0⟩ := absorb_g n κ L hκpos hL1
  have habsXL : X * L ^ n ≤ (1 / κ ^ (n + 1)) * (1 + X) ^ (n + 2) * (1 / L) := by
    rw [hXdef]; exact habsXL0
  have habsL : L ^ n ≤ (1 / κ ^ (n + 2)) * (1 + X) ^ (n + 2) * (1 / L) := by
    rw [hXdef]; exact habsL0
  -- assemble error side
  have hLLnn : (0:ℝ) ≤ 1 / L := by positivity
  have hXPAS5 : X * PAS ^ (n + 1) ≤ Y ^ (n + 2) := by
    calc X * PAS ^ (n + 1) ≤ Y * Y ^ (n + 1) :=
          mul_le_mul hXY (pow_le_pow_left₀ hPAS0 hPASY (n + 1)) (by positivity) hY0
      _ = Y ^ (n + 2) := by ring
  have hPAS6 : PAS ^ (n + 2) ≤ Y ^ (n + 2) := pow_le_pow_left₀ hPAS0 hPASY (n + 2)
  -- the 1/L opaque pieces
  have hm1 : (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
      ≤ (2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1 + X) ^
              (n + 2) / L := by
    have e : (2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
        = (2 * cF * cic * cg ^ n) * (X * L ^ n) + (2 * cic ^ 2 * cg ^ n) * (L ^ n) := by ring
    rw [e]
    have hb1 : (2 * cF * cic * cg ^ n) * (X * L ^ n)
        ≤ (2 * cF * cic * cg ^ n) * ((1 / κ ^ (n + 1)) * (1 + X) ^ (n + 2) * (1 / L)) :=
      mul_le_mul_of_nonneg_left habsXL (by positivity)
    have hb2 : (2 * cic ^ 2 * cg ^ n) * (L ^ n)
        ≤ (2 * cic ^ 2 * cg ^ n) * ((1 / κ ^ (n + 2)) * (1 + X) ^ (n + 2) * (1 / L)) :=
      mul_le_mul_of_nonneg_left habsL (by positivity)
    calc (2 * cF * cic * cg ^ n) * (X * L ^ n) + (2 * cic ^ 2 * cg ^ n) * (L ^ n)
        ≤ (2 * cF * cic * cg ^ n) * ((1 / κ ^ (n + 1)) * (1 + X) ^ (n + 2) * (1 / L))
          + (2 * cic ^ 2 * cg ^ n) * ((1 / κ ^ (n + 2)) * (1 + X) ^ (n + 2) * (1 / L))
                  := add_le_add hb1 hb2
      _ = (2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1 + X) ^
              (n + 2) / L := by
        ring
  -- the 1/D relative pieces
  have hm2 : (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
      ≤ ((2 * C1) * cF * Aic) * Y ^ (n + 2) / (D:ℝ) := by
    have e : (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
        = ((2 * C1) * cF * Aic) * (X * PAS ^ (n + 1)) / (D:ℝ) := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    exact mul_le_mul_of_nonneg_left hXPAS5 (mul_nonneg (mul_nonneg (by linarith) hcF0) hAic0)
  have hm3 : (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ))
      ≤ ((2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ) := by
    have e : (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ))
        = ((2 * C2) * Aic ^ 2) * (PAS ^ (n + 2)) / (D:ℝ) := by ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    exact mul_le_mul_of_nonneg_left hPAS6 (mul_nonneg (by linarith) (sq_nonneg _))
  -- === final assembly ===
  have hgoal : |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
        - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
      ≤ (cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1
              + X) ^ (n + 2) / L
        + (Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ) := by
    calc |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r)
            - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ |(∑ r ∈ filt, (Inn r) ^ 2 / Denom r) - X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)|
          + |X ^ 2 * (∑ r ∈ filt, (Ev r) ^ 2 / Denom r)
            - X ^ (n + 2) * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ ≤ ((2 * X * cF * cic + 2 * cic ^ 2) * (cg * L) ^ n
            + (2 * X * cF * Aic * PAS) * (C1 * PAS ^ n / (D:ℝ))
            + (2 * Aic ^ 2 * PAS ^ 2) * (C2 * PAS ^ n / (D:ℝ)))
          + (cmain * (1 + X) ^ (n + 2) / L + Amain * Y ^ (n + 2) / (D:ℝ)) :=
          add_le_add (le_trans herr herr2) hmainpart
      _ ≤ (cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) *
              (1 + X) ^ (n + 2) / L
          + (Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ) := by
          have hexpand :
              (cmain + 2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2))
                  * (1 + X) ^ (n + 2) / L
              = (2 * cF * cic * cg ^ n / κ ^ (n + 1) + 2 * cic ^ 2 * cg ^ n / κ ^ (n + 2)) * (1
                      + X) ^ (n + 2) / L
                + cmain * (1 + X) ^ (n + 2) / L := by ring
          have hexpand2 :
              (Amain + (2 * C1) * cF * Aic + (2 * C2) * Aic ^ 2) * Y ^ (n + 2) / (D:ℝ)
              = ((2 * C1) * cF * Aic) * Y ^ (n + 2) / (D:ℝ) + ((2 * C2) * Aic ^ 2) * Y ^ (n + 2)
                      / (D:ℝ)
                + Amain * Y ^ (n + 2) / (D:ℝ) := by ring
          rw [hexpand, hexpand2]
          linarith [hm1, hm2, hm3]
  -- the frozen goal is definitionally the `Inn/Denom/X/Y` form
  exact hgoal

omit [Salt.Maynard.TupleChoice] in
/-- **B4.2b: the J-side split engine at general `n`, unconditional.** -/
theorem mv_J_split_gen (n : ℕ) (hn : 1 ≤ n) (P : BPoly (n + 1)) (m : Fin (n + 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex (n + 1) R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yFg R W' P (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ (n + 2)
              * ((simplexInt (sq (contractB m P)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ (n + 2) / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ (n + 2) / D :=
  mv_J_split_gen_of n hn P m (mv_J_main_split_gen n hn P m) (inner_contract_rel_gen n hn P m)

end Salt.MaynardK

