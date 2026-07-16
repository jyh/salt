/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Goldbach.Ledger

/-!
# The Goldbach F2 ledger, part 2 — the certificate rows at the punctured operating point

The four value certs `normalized_package` consumes, each the twin row re-instantiated at
the punctured carriers through Ledger part 1's depth facts:

* **`gold_hcertA1_at_op`** — `9779/10000 ≤ fchain(maxDepth)(logRatio z D)`:
  `fchain_A1_final` (depth-uniform at `n ≥ 2`) ∘ `logRatio_A1_mem` ∘
  `two_le_maxDepth_goldA1`.
* **`gold_hcertA2_at_op`** — the `A2grid` bound at the PUNCTURED top-window filter and
  the gold depth function, via the generic `A2grid_topwindow_le`; the per-prime range
  rows (`a12_cdivStop`, `logRatio_cdiv_le_three`) transfer through filter weakening
  (`Prime ∧ ¬·∣N → Prime`).
* **`gold_hcertA3_at_op`** — `Fchain(maxDepth)(logRatio y Dlev) ≤ 243/100`:
  `Fchain_switch_le` ∘ the tower membership ∘ `one_le_maxDepth_goldSwitch`.
* **`gold_aggSlack_le`** — the A₂ aggregate slack over the punctured filter, by subset
  monotonicity from the twin `aggSlack_le` (nonneg summands).

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.Chen Salt.BrunLower

namespace Salt.Goldbach

/-- **`hcertA1` at the punctured op** (uniformly in the residue `a`). -/
theorem gold_hcertA1_at_op : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ a : ℕ,
    (9779 / 10000 : ℝ) ≤
      fchain (maxDepth (goldA1SieveW opQ a N (goldOpP N)
          (goldOpP_squarefree N) (goldOpP_odd N)))
        (logRatio (opZ N) (opD N)) := by
  obtain ⟨xm, hmem⟩ := logRatio_A1_mem
  obtain ⟨xd, hd⟩ := two_le_maxDepth_goldA1
  refine ⟨max xm xd, fun N hN a => ?_⟩
  have hxm : xm ≤ N := le_trans (le_max_left _ _) hN
  have hxd : xd ≤ N := le_trans (le_max_right _ _) hN
  have hmemx : logRatio (opZ N) (opD N) ∈ Set.Icc (39992 / 10000 : ℝ) 4 := by
    rw [opZ, opD]
    exact hmem N hxm
  exact fchain_A1_final _ (hd N hxd a) _ hmemx

/-- **`hcertA3` at the punctured op.** -/
theorem gold_hcertA3_at_op : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    Fchain (maxDepth (goldSwitchSieve N (opZ N) (opY N) (goldOpPs N)
        (goldOpPs_squarefree N) (goldOpPs_odd N)))
      (logRatio (opY N) (opDlev N)) ≤ 243 / 100 := by
  obtain ⟨xt, -, htower⟩ := opf_tower
  obtain ⟨xd, hd⟩ := one_le_maxDepth_goldSwitch
  refine ⟨max xt xd, fun N hN => ?_⟩
  have hxt : xt ≤ N := le_trans (le_max_left _ _) hN
  have hxd : xd ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem, _, _⟩ := htower N hxt
  exact Fchain_switch_le _ (hd N hxd) _ hmem

/-- **`hcertA2` at the punctured op** — the `M2G` grid symbol bounded by the generic
top-window cert at the punctured filter and the gold depth function. -/
theorem gold_hcertA2_at_op : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N → ∀ a : ℕ,
    A2grid ((Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N))
        (opZ N) (opD N)
        (fun p => maxDepth (goldA2SieveW opQ a N (goldOpP N) p
            (goldOpP_squarefree N) (goldOpP_odd N)))
      ≤ (1250 / 1249) * ((3 + 43 / 75) * (Real.log 6 / 4 + 1125 / 3997000
          + A2weight (opZ N) ((opZ N) ^ 4) ((opY N : ℝ) + 1)
              * (21 / Real.log (opZ N) + 2 / ((opZ N : ℝ) - 1)))) := by
  obtain ⟨xW, hW⟩ := logRatio_A2_window_mem
  obtain ⟨xT, hT⟩ := logRatio_A2_topwindow_mem
  obtain ⟨xS, hS⟩ := a12_cdivStop
  obtain ⟨xU, hU⟩ := logRatio_cdiv_le_three
  obtain ⟨xt, -, htower⟩ := opf_tower
  obtain ⟨xd, hd⟩ := two_le_maxDepth_goldA2
  refine ⟨max (max (max xW xT) (max xS xU)) (max xt xd), fun N hN a => ?_⟩
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨hxW, hxT⟩, hxS, hxU⟩, hxt, hxd⟩ := hN
  obtain ⟨_, _, _, hz3, _, _, hzy, _, _, _, _, _, _, _, _, _, _⟩ := htower N hxt
  have hz2 : 2 ≤ opZ N := by omega
  have hzyR : (opZ N : ℝ) ≤ (opY N : ℝ) + 1 := by
    have : (opZ N : ℝ) ≤ (opY N : ℝ) := by exact_mod_cast hzy
    linarith
  obtain ⟨hLD_lo, -⟩ := hW N hxW
  have hLDlo' : (4 - 8 / 10000) * Real.log (opZ N) ≤ Real.log (opD N) := by
    rw [opZ, opD]
    exact hLD_lo
  obtain ⟨hLy_lo, hLy_hi⟩ := hT N hxT
  apply A2grid_topwindow_le _ (opZ N) (opD N) ((opY N : ℝ) + 1) _ hz2 hzyR (by positivity)
    A2massSum_le_final hLDlo' hLy_lo hLy_hi
  · -- hP: the punctured members are window primes
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hzp, hpy⟩, hpp, -⟩ := hp
    refine ⟨hpp, by exact_mod_cast hzp, ?_⟩
    have : (p : ℝ) ≤ (opY N : ℝ) := by exact_mod_cast hpy
    linarith
  · -- hN: the gold A₂ depth is ≥ 1 (indeed ≥ 2)
    intro p _
    have := hd N hxd a p
    omega
  · -- hsrange: the operating range rows through filter weakening
    intro p hp
    have hp' : p ∈ (Finset.Icc (opZ N) (opY N)).filter Nat.Prime := by
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    exact ⟨hS N hxS p hp', hU N hxU p hp'⟩

/-- **The punctured A₂ aggregate slack** — subset monotonicity from the twin row
(`aggSlack_le`): every summand is nonneg and the punctured filter is a sub-filter. -/
theorem gold_aggSlack_le : ∃ x₁ : ℕ, ∀ N : ℕ, x₁ ≤ N →
    ∑ p ∈ (Finset.Icc (opZ N) (opY N)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
        (1 / ((p : ℝ) - 1)) * (opEps * CsharpB opEps * Real.exp 2
            * hBJS (logRatio (opZ N) (cdiv (opD N) p)))
      ≤ opEps * CsharpB opEps * (11 / 10) := by
  obtain ⟨xa, ha⟩ := aggSlack_le
  obtain ⟨xt, -, htower⟩ := opf_tower
  refine ⟨max xa xt, fun N hN => ?_⟩
  have hxa : xa ≤ N := le_trans (le_max_left _ _) hN
  have hxt : xt ≤ N := le_trans (le_max_right _ _) hN
  have hz3 : 3 ≤ opZ N := (htower N hxt).2.2.2.1
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (ha N hxa)
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp _
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast le_trans hz3 hp.1.1
    exact mul_nonneg (div_nonneg (by norm_num) (by linarith)) (slack_nn _)

end Salt.Goldbach
