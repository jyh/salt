/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Twelve.WinCore
import Salt.Maynard.LevelConsume

/-!
# C1 · B4.4a — the S₂ main-term lower bound at level 1/2

`Salt.Twelve.S2mW_ge_compatMain_theta_uniform` with the level `3999/4000 → 1/2`:
`lod_error_pow_theta → lod_error_pow` and `range_haircut_mono_theta → range_haircut_mono`
(`LevelConsume.lean:33/272`), the BV-strength inputs. k-generic as before.
-/

namespace Salt.MaynardK

set_option linter.unusedSectionVars false
variable [Salt.Maynard.TupleChoice]

open Salt.Maynard Salt.Twelve


/-- The S₂ main-term lower bound at level `1/2`, uniform in the weight: under `HasLevel (1/2)`, for
`k, K₀ ≥ 1`, squarefree `W'`, every prime `p ∤ W'` at least `D`, and all `hSeq k i < D`, there
are `C₀, B' ≥ 0` and `N₀` such that for `R ≥ 2`, `|y| ≤ 1`, `ν₀ + h` coprime to `W'` on the
tuple, `N ≥ N₀`, `R ≤ N` and `W' R² ≤ ⌊N^{1/2} / (log N)^{B'}⌋`, every coordinate `m` has `S2mW
k K₀ N R ν₀ W' m y ≥ deltaPi k K₀ N m / φ(W') · s2CompatFormM k R W' m y − C₀ (1 + log R)^{2k+2}
N / (log N)^{2k+4}`. `Salt.Twelve.S2mW_ge_compatMain_theta_uniform` with the level `3999/4000 →
1/2`.
-/
theorem S2mW_ge_compatMain_half_uniform (k K₀ W' D : ℕ) (hk : 1 ≤ k) (hK₀ : 1 ≤ K₀)
    (hW' : Squarefree W') (hD : ∀ p : ℕ, p.Prime → ¬ p ∣ W' → D ≤ p)
    (hlt : ∀ i : Fin k, hSeq k i < D) (hLoD : HasLevel (1 / 2)) :
    ∃ (C₀ B' : ℝ) (N₀ : ℕ), 0 ≤ C₀ ∧ 0 ≤ B' ∧
      ∀ (R ν₀ : ℕ) (y : (Fin k → ℕ) → ℝ), 2 ≤ R → (∀ r, |y r| ≤ 1) →
        (∀ h ∈ H k, Nat.Coprime (ν₀ + h) W') →
        ∀ N : ℕ, N₀ ≤ N → R ≤ N →
          (W' * R ^ 2 ≤ ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'⌋₊) →
        ∀ m : Fin k,
          S2mW k K₀ N R ν₀ W' m y
            ≥ deltaPi k K₀ N m / (Nat.totient W' : ℝ) * s2CompatFormM k R W' m y
              - C₀ * (1 + Real.log R) ^ (2 * k + 2) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
  classical
  obtain ⟨Clam, hClam0, hdisc⟩ :=
    abs_S2mW_sub_compatMainW_le_disc_R_uniform k K₀ W' D hK₀ hW' hD hlt
  obtain ⟨C, B', N₁, hB'0, hEHb⟩ := lod_error_pow k (2 * k + 4) (by omega) hLoD
  have hCnn : 0 ≤ C := by
    set x₀ := max N₁ 2 with hx₀
    have hmax2 : 2 ≤ x₀ := le_max_right N₁ 2
    have hb := hEHb x₀ (le_max_left N₁ 2)
    have hx0pos : 0 < x₀ := by omega
    have hlogx0 : 0 < Real.log x₀ :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x₀ by omega))
    have hLHS0 : (0 : ℝ) ≤ ∑ q ∈ (Finset.range (⌊(x₀ : ℝ) ^ (1 / 2 : ℝ)
          / (Real.log x₀) ^ B'⌋₊ + 1)).filter Squarefree,
        (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x₀ q :=
      Finset.sum_nonneg (fun q _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x₀ q))
    have hpos : 0 < (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) :=
      div_pos (by exact_mod_cast hx0pos) (pow_pos hlogx0 _)
    by_contra hCneg
    have hbad : C * (x₀ : ℝ) / (Real.log x₀) ^ (2 * k + 4) < 0 := by
      rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos (not_le.mp hCneg) hpos
    linarith [hLHS0, hb, hbad]
  refine ⟨2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1), B',
    max (max (max 2 N₁) (D₀ k)) ⌈Real.exp (2 * B')⌉₊, ?_, hB'0, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * Clam ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg h1 hCnn) (by positivity)
  intro R ν₀ y hR hy1 hν₀ N hN0 hRN hrange m
  have hlogR : (0 : ℝ) ≤ Real.log R :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1 : ℕ) ≤ R))
  have hN0a : max (max 2 N₁) (D₀ k) ≤ N := le_trans (le_max_left _ _) hN0
  have hle2N1 : max 2 N₁ ≤ N := le_trans (le_max_left _ _) hN0a
  have hD0N : D₀ k ≤ N := le_trans (le_max_right _ _) hN0a
  have hexp2N : ⌈Real.exp (2 * B')⌉₊ ≤ N := le_trans (le_max_right _ _) hN0
  have h2N : 2 ≤ N := le_trans (le_max_left 2 N₁) hle2N1
  have hN1N : N₁ ≤ N := le_trans (le_max_right 2 N₁) hle2N1
  have hNpos : 0 < N := by omega
  have hhm : hSeq k m ≤ N := le_trans (hSeq_le_D₀ k m) hD0N
  have hNleK0N : N ≤ K₀ * N := Nat.le_mul_of_pos_left N (by omega)
  have hlogN0 : 0 < Real.log N :=
    Real.log_pos (by exact_mod_cast (show (1 : ℕ) < N by omega))
  have hlogN2B' : 2 * B' ≤ Real.log N := by
    have h1 : Real.exp (2 * B') ≤ (N : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hexp2N)
    calc 2 * B' = Real.log (Real.exp (2 * B')) := (Real.log_exp _).symm
      _ ≤ Real.log N := Real.log_le_log (Real.exp_pos _) h1
  have endpoint : ∀ x : ℕ, N ≤ x → x ≤ (K₀ + 1) * N →
      ∑ q ∈ (Finset.range (W' * R ^ 2 + 1)).filter Squarefree,
          (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    intro x hNx hxub
    have hNxr : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hNx
    have hmono : ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (Real.log N) ^ B'⌋₊
        ≤ ⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ :=
      Nat.floor_mono (range_haircut_mono B' hB'0 N x h2N hNx hlogN2B')
    have hWRx : W' * R ^ 2 ≤ ⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ :=
      le_trans hrange hmono
    have hsub : (Finset.range (W' * R ^ 2 + 1)).filter Squarefree
        ⊆ (Finset.range (⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ + 1)).filter
            Squarefree :=
      Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (by omega))
    have hlogx0 : 0 < Real.log x :=
      Real.log_pos (by exact_mod_cast (show (1 : ℕ) < x by omega))
    have hlogxN : Real.log N ≤ Real.log x := Real.log_le_log (by exact_mod_cast hNpos) hNxr
    have hd1pos : 0 < (Real.log x) ^ (2 * k + 4) := pow_pos hlogx0 _
    have hd2pos : 0 < (Real.log N) ^ (2 * k + 4) := pow_pos hlogN0 _
    have hd21 : (Real.log N) ^ (2 * k + 4) ≤ (Real.log x) ^ (2 * k + 4) :=
      pow_le_pow_left₀ hlogN0.le hlogxN _
    calc ∑ q ∈ (Finset.range (W' * R ^ 2 + 1)).filter Squarefree,
            (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q
        ≤ ∑ q ∈ (Finset.range (⌊(x : ℝ) ^ (1 / 2 : ℝ) / (Real.log x) ^ B'⌋₊ + 1)).filter
            Squarefree, (3 * k : ℝ) ^ q.primeFactors.card * maxDiscrepancy x q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun q _ _ => mul_nonneg (by positivity) (maxDiscrepancy_nonneg x q))
      _ ≤ C * (x : ℝ) / (Real.log x) ^ (2 * k + 4) := hEHb x (le_trans hN1N hNx)
      _ ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
          rw [div_le_div_iff₀ hd1pos hd2pos]
          have hxubr : (x : ℝ) ≤ ((K₀ : ℝ) + 1) * (N : ℝ) := by exact_mod_cast hxub
          have step_num : C * (x : ℝ) ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) := by
            calc C * (x : ℝ) ≤ C * (((K₀ : ℝ) + 1) * (N : ℝ)) :=
                  mul_le_mul_of_nonneg_left hxubr hCnn
              _ = C * ((K₀ : ℝ) + 1) * (N : ℝ) := by ring
          have hcnum : 0 ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) :=
            mul_nonneg (mul_nonneg hCnn (by positivity)) (by positivity)
          exact mul_le_mul step_num hd21 (pow_nonneg hlogN0.le _) hcnum
  have hexp : (K₀ + 1) * N = K₀ * N + N := by ring
  have hx1lb : N ≤ K₀ * N + hSeq k m := le_trans hNleK0N (Nat.le_add_right _ _)
  have hx1ub : K₀ * N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hx2ub : N + hSeq k m ≤ (K₀ + 1) * N := by rw [hexp]; omega
  have hEP1 := endpoint (K₀ * N + hSeq k m) hx1lb hx1ub
  have hEP2 := endpoint (N + hSeq k m) (Nat.le_add_right _ _) hx2ub
  have hfib1 := compat_pair_fiber_leW k R W' hW' m
    (fun q => maxDiscrepancy (K₀ * N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (K₀ * N + hSeq k m) q)
  have hfib2 := compat_pair_fiber_leW k R W' hW' m
    (fun q => maxDiscrepancy (N + hSeq k m) q)
    (fun q => maxDiscrepancy_nonneg (N + hSeq k m) q)
  have hsplit : (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)))
      = (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
          ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
            (if IsCollisionPair d e then 0
             else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)))
        + (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
            ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
              (if IsCollisionPair d e then 0
               else maxDiscrepancy (N + hSeq k m) (qModW k W' d e))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases hcol : IsCollisionPair d e
    · simp only [if_pos hcol, add_zero]
    · simp only [if_neg hcol]
  have hDiscSum : (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
        ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
          (if IsCollisionPair d e then 0
           else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)))
      ≤ C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
        + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    rw [hsplit]
    exact add_le_add (le_trans hfib1 hEP1) (le_trans hfib2 hEP2)
  have hLnn : 0 ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _)
  have hfinal : |S2mW k K₀ N R ν₀ W' m y
        - deltaPi k K₀ N m / (Nat.totient W' : ℝ) * s2CompatFormM k R W' m y|
      ≤ 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
          * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by
    refine le_trans (hdisc R ν₀ y hR hy1 hν₀ m N hRN) ?_
    calc Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
          * (∑ d ∈ (kSieveIndex k R W').filter (fun d => d m = 1),
              ∑ e ∈ (kSieveIndex k R W').filter (fun e => e m = 1),
                (if IsCollisionPair d e then 0
                 else maxDiscrepancy (K₀ * N + hSeq k m) (qModW k W' d e)
                      + maxDiscrepancy (N + hSeq k m) (qModW k W' d e)))
        ≤ Clam ^ 2 * (1 + Real.log R) ^ (2 * k + 2)
            * (C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)
              + C * ((K₀ : ℝ) + 1) * (N : ℝ) / (Real.log N) ^ (2 * k + 4)) :=
          mul_le_mul_of_nonneg_left hDiscSum hLnn
      _ = 2 * Clam ^ 2 * C * ((K₀ : ℝ) + 1) * (1 + Real.log R) ^ (2 * k + 2)
            * (N : ℝ) / (Real.log N) ^ (2 * k + 4) := by ring
  have := (abs_le.mp hfinal).1
  linarith

end Salt.MaynardK
