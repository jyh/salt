/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MaynardK.MvIGen
import Salt.MaynardK.MvJGen
import Salt.MaynardK.ISplit
import Salt.MaynardK.JSplit
import Salt.MaynardK.InnerS2Gen
import Salt.MaynardK.QBridge
import Salt.MaynardK.WinCore105

/-!
# Controls: the general-`k` engines recover the landed k = 5 statements

Each theorem below restates a landed k = 5 result of `Salt/Twelve/` (or a hypothesis-form of
one, where the original is `private`) verbatim, and proves it as the `k = 5` (`n = 4`)
instance of the corresponding general-`k` engine of `Salt/MaynardK/`. They are checks on the
generalisations, not inputs to `gaps_le_636`: none of them is in its dependency closure.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace Salt.MaynardK

open Salt.Maynard Salt.Twelve

/-- CONTROL: the landed k = 5 keystone, its statement copied VERBATIM, is a corollary. -/
theorem mv_I_of_gen (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ kSieveIndex 5 R W',
            eval (ofPoly F) (fun i => Real.log (r i) / Real.log R) ^ 2
              / ∏ i, (Nat.totient (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 5
            * ((simplexInt (sq (ofPoly F)) : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 5
          * (1 / Real.log R + 1 / D) := by
  simpa only [eval_sq] using mv_I_gen W' hW' hpos hUpper 5 (by norm_num) (sq (ofPoly F))

/-- CONTROL: the landed k = 5 keystone `Salt.Twelve.mv_J`, its statement copied VERBATIM,
is the `n = 4`, `P = ofPoly F` instance of `mv_J_gen`. -/
theorem mv_J_of_gen (W' : ℕ) (hW' : Squarefree W') (hpos : 0 < W')
    (hUpper : PhiUpperAtom W') (F : Poly) (m : Fin 5) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ D R : ℕ, 3 ≤ D →
      (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) → 1 ≤ Real.log R →
      |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
            (∑ u ∈ Finset.range R,
                yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
              / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
        - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
            * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
      ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6
          * (1 / Real.log R + 1 / D) := by
  have hyF : ∀ (R W' : ℕ) (s : Fin 5 → ℕ), yFg (n := 4) R W' (ofPoly F) s = yF R W' F s :=
    fun _ _ _ => rfl
  have hcontr : contractB m (ofPoly F) = contractAt m F := by
    simp only [contractB, ofPoly, contractAt, List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, Nat.factorial_zero, mul_one, add_zero, Prod.mk.injEq,
      true_and]
    rw [Nat.factorial_succ]
    have h1 : ((a.1 m).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  obtain ⟨c, hc0, hc⟩ := mv_J_gen W' hW' hpos hUpper 4 (by norm_num) (ofPoly F) m
  refine ⟨c, hc0, fun D R hD hDW hR => ?_⟩
  have h := hc D R hD hDW hR
  rw [hcontr] at h
  simp only [hyF] at h
  exact h

/-- CONTROL: the landed `MvSplit.mv_I_split` statement, VERBATIM, as the k = 5 corollary. -/
theorem mv_I_split_of_gen (F : Poly) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ kSieveIndex 5 R W',
              eval (ofPoly F) (fun i => Real.log (r i) / Real.log R) ^ 2
                / ∏ i, (Nat.totient (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 5
              * ((simplexInt (sq (ofPoly F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 5 / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ 5 / D := by
  simpa only [eval_sq] using mv_I_split_gen 5 (by norm_num) (sq (ofPoly F))

/-- CONTROL. The landed `mv_J_split` statement, VERBATIM, recovered as the `n = 4`,
`P = ofPoly F` instance of `mv_J_split_gen_of`. `hIC` is supplied by the LANDED public
`Salt.Twelve.inner_contract_rel`; `mv_J_main_split` is `private` in `MvSplit.lean`, so its
k = 5 statement is taken VERBATIM as the hypothesis `hMain5` (it cannot be supplied from
outside). -/
theorem mv_J_split_of_gen (F : Poly) (m : Fin 5)
    (hMain5 : ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
              eval (contractAt m F) (fun i => Real.log (r (m.succAbove i)) / Real.log R) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 4
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 4 / Real.log R
          + A * (1 + Salt.Maynard.phiAtomSum R W') ^ 4 / D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 3 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 1 ≤ Real.log R →
        |(∑ r ∈ (kSieveIndex 5 R W').filter (fun r => r m = 1),
              (∑ u ∈ Finset.range R,
                  yF R W' F (Function.update r m u) / (Nat.totient u : ℝ)) ^ 2
                / ∏ i ∈ Finset.univ.erase m, (gMult (r i) : ℝ))
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D := by
  have hcontr : contractB m (ofPoly F) = contractAt m F := by
    simp only [contractB, ofPoly, contractAt, List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, Nat.factorial_zero, mul_one, add_zero, Prod.mk.injEq,
      true_and]
    rw [Nat.factorial_succ]
    have h1 : ((a.1 m).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hMain : MvJMainSplitGen 4 (ofPoly F) m := by
    unfold MvJMainSplitGen; rw [hcontr]; exact hMain5
  have hIC : InnerContractRelGen 4 (ofPoly F) m := by
    unfold InnerContractRelGen; rw [hcontr]; exact inner_contract_rel F m
  have h := mv_J_split_gen_of 4 (by norm_num) (ofPoly F) m hMain hIC
  rw [hcontr] at h
  exact h

/-- **CONTROL** — the landed `Salt.Twelve.s2_inner_yF` statement VERBATIM, as a
corollary of `s2_inner_y_gen` at `k = 5`, `y = yF R W' F`. -/
theorem s2_inner_yF_of_gen (F : Poly) (m : Fin 5) (hQ : Qabs F ≤ 1)
    (hQd : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' →
      300 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        (Salt.Maynard.phiAtomSum R W' + lemma53Const * 5 * Real.log R / D) ^ 2
            * (2 * Salt.Maynard.phiAtomSum R W') ^ 4
          ≤ CF * Qdiag_gv 5 R W' m (yF R W' F)) :
    ∃ CF : ℝ, 0 ≤ CF ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' → PhiUpperAtom W' →
      300 ≤ D → (∀ p : ℕ, p.Prime → ¬ p ∣ W' → D < p) →
      ((W' : ℝ) / W'.totient ≤ 5 * Real.sqrt D) →
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → 1 ≤ Real.log R →
        S2InnerBoundQC 5 R W' m (yF R W' F) CF := by
  obtain ⟨CF, hCF, hcmp⟩ := hQd
  refine ⟨CF, hCF, ?_⟩
  intro W' D hW' hpos hUpper hD hDlt hκ
  obtain ⟨R₀, hR₀⟩ := hcmp W' D hW' hpos hUpper hD hDlt hκ
  refine ⟨max R₀ 2, ?_⟩
  intro R hR hlogR
  have hR2 : 2 ≤ R := le_trans (le_max_right R₀ 2) hR
  have hqd := hR₀ R (le_trans (le_max_left R₀ 2) hR) hlogR
  have hyB : ∀ s, |yF R W' F s| ≤ 1 := fun s =>
    le_trans (yF_abs_le_Qabs R W' F s) (by exact_mod_cast hQ)
  have hysupp : ∀ s, s ∉ kSieveIndex 5 R W' → yF R W' F s = 0 := by
    intro s hs; unfold yF; rw [if_neg hs]
  have hqd' : (Salt.Maynard.phiAtomSum R W' + lemma53Const * ((5 : ℕ) : ℝ) * Real.log R / D) ^ 2
        * (2 * Salt.Maynard.phiAtomSum R W') ^ (5 - 1)
      ≤ CF * Qdiag_gv 5 R W' m (yF R W' F) := by
    have h5 : ((5 : ℕ) : ℝ) = 5 := by norm_num
    rw [h5, show (5 - 1 : ℕ) = 4 from rfl]
    exact hqd
  intro s hs α hα
  exact s2_inner_y_gen 5 R W' D m (yF R W' F) hyB hysupp hR2 hW' hpos hDlt
    (le_trans (by norm_num) hD) CF hqd' hs α hα

/-- **CONTROL: the landed k = 5 `qdiag_bridge` statement, VERBATIM, as a corollary at `n = 4`,
`P = ofPoly F`.** -/
theorem qdiag_bridge_k5 (F : Poly) (m : Fin 5) (hQ : Qabs F ≤ 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W' D : ℕ, Squarefree W' → 0 < W' →
      PhiUpperAtom W' → 300 ≤ D → (∀ p : ℕ, p.Prime → ¬p ∣ W' → D < p) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℕ, 2 ≤ R → 1 ≤ Real.log R →
        |Qdiag_mW 5 R W' m (yF R W' F)
          - ((W'.totient : ℝ) / W' * Real.log R) ^ 6
              * ((simplexInt (sq (contractAt m F)) : ℚ) : ℝ)|
        ≤ c * (1 + (W'.totient : ℝ) / W' * Real.log R) ^ 6 / Real.log R
          + A * ((W' : ℝ) / W'.totient)
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D
          + A * ((W' : ℝ) / W'.totient) ^ 2
              * (1 + (W'.totient : ℝ) / W' * Real.log R
                   + Salt.Maynard.phiAtomSum R W') ^ 6 / D ^ 2 := by
  have hcontr : contractB m (ofPoly F) = contractAt m F := by
    simp only [contractB, ofPoly, contractAt, List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, Nat.factorial_zero, mul_one, add_zero, Prod.mk.injEq,
      true_and]
    rw [Nat.factorial_succ]
    have h1 : ((a.1 m).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hy1 : ∀ R W' : ℕ, ∀ s, |yFg R W' (ofPoly F) s| ≤ 1 := fun R W' s =>
    le_trans (yF_abs_le_Qabs R W' F s) (by exact_mod_cast hQ)
  obtain ⟨A, hA0, hA⟩ := qdiag_bridge_gen 4 (by norm_num) (ofPoly F) m hy1
  refine ⟨A, hA0, ?_⟩
  intro W' D hW' hpos hUpper hD hDW
  obtain ⟨c, hc0, hc⟩ := hA W' D hW' hpos hUpper (by norm_num; omega) hDW
  refine ⟨c, hc0, ?_⟩
  intro R hR2 hlogR
  have h := hc R hR2 hlogR
  rw [hcontr] at h
  exact h

/-- **CONTROL: the landed `Salt.Twelve.S1_lt_sum_S2mW` statement, VERBATIM, as the `k = 5`
instance.** -/
theorem S1_lt_sum_S2mW_k5 (K₀ N R ν₀ W' : ℕ) (y : (Fin 5 → ℕ) → ℝ)
    (δ : ℝ) (errEH cval : Fin 5 → ℝ)
    (hφ : 0 < (Nat.totient W' : ℝ)) (hcval : ∀ m : Fin 5, 0 ≤ cval m) (hδ0 : 0 ≤ δ)
    (hDpi : ∀ m : Fin 5, δ ≤ deltaPi 5 K₀ N m)
    (hcompat : ∀ m : Fin 5, cval m ≤ Qdiag_mW 5 R W' m y)
    (hEHres : ∀ m : Fin 5,
      deltaPi 5 K₀ N m / (Nat.totient W' : ℝ) * Qdiag_mW 5 R W' m y - errEH m
        ≤ S2mW 5 K₀ N R ν₀ W' m y)
    (hnum : S1 5 K₀ N R W' ν₀ y
      < (∑ m : Fin 5, δ / (Nat.totient W' : ℝ) * cval m) - ∑ m : Fin 5, errEH m) :
    S1 5 K₀ N R W' ν₀ y < ∑ m : Fin 5, S2mW 5 K₀ N R ν₀ W' m y :=
  S1_lt_sum_S2mW_k 5 K₀ N R ν₀ W' y δ errEH cval hφ hcval hδ0 hDpi hcompat hEHres hnum

end Salt.MaynardK
