/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Mathlib
import Salt.Chen.MassLedger
import Salt.Chen.ChainValues

/-!
# MR3 — the A₁ mass-reduction (MR1's sibling; the whole-window even-level scalar)

On the A₁ window `s ∈ [2,4]` the even Rosser-chain levels are **exact scalars**, just as the
odd levels are on `[1,3]` (MR1).  For an **even** level `k ≥ 4`, the even window (BJS (16)) gives

  `fseq k s = (1/s)·∫_s^{k+2} fseq (k−1) (t−1) dt = (1/s)·∫_{s−1}^{k+1} fseq (k−1) u du`

(change of variables `u = t−1`; the support edge of `fseq (k−1)` is `(k−1)+2 = k+1`).  Split the
integral at `u = 3` (legal since `s ∈ [2,4] ⟹ s−1 ∈ [1,3]`):

* the **flat piece** `∫_{s−1}^3 fseq (k−1) u du = massE (k−2)·(log 3 − log (s−1))`, because on
  `[1,3]` the odd level `k−1` is flat, `fseq (k−1) u = massE (k−2)/u` (MR1's `fseq_odd_eq_massE`),
  and `∫ u⁻¹ = log`;
* the **tail piece** `∫_3^{k+1} fseq (k−1) u du = massO (k−1)`.

## The `massO` upper limit is `n+2`, NOT `n+1` (deviation from the flags DESIGN text)

The flags "2026-07-13 DESIGN: the A₁ mass-reduction" entry writes `massO n := ∫_3^{n+1} fseq n`.
That upper limit is **off by one**: `fseq n` is supported up to `n+2` (`fseq_eq_zero_of_ge`), and
the tail piece produced by the change of variables is `∫_3^{k+1} fseq (k−1) = ∫_3^{(k−1)+2} fseq
(k−1)`,
i.e. the mass runs to the **support edge** `(k−1)+2`.  Using `n+1` would drop the nonzero mass on
`[n+1, n+2]`, breaking both the exact identity and the numeric cross-check (`Σ_{odd j} massO j =
4·evenSum(4) = 0.086584`, verified against the `∫_3^{n+2}` definition to full precision).  So we set
`massO n := ∫_3^{n+2} fseq n`, the exact sibling of `massE n := ∫_2^{n+2} fseq n` (only the lower
limit differs, `3` vs `2`).  The frozen constant `Σ massO ≤ 11/125` (true 0.086584) is unaffected —
it is a property of the sum, and 0.086584 < 0.088 with the correct `∫_3^{n+2}` masses.

## The A₁ ledger row (item 3)

`fchain N s = 1 − evenSum`, `evenSum = f₂(s) + (1/s)[(log 3 − log(s−1))·Σ massE + Σ massO]`.  On the
grid `s ∈ [39992/10000, 4]`: `log(3/(s−1)) ≤ (4−s)/(s−1)` (`log x ≤ x−1`) and
`f₂ ≤ (4−s)²/(s(s−1))` (`fseq_two_le_sq`).  With `Σ massE ≤ 43/75` (MR2) and `Σ massO ≤ 11/125`
(MR4) the worst point `s = 39992/10000` gives `evenSum ≤ 221/10000`, i.e. `fchain ≥ 9779/10000`
(margin ≈ 5.7·10⁻⁵ on the rational bound).
-/

namespace Salt.Chen

open MeasureTheory intervalIntegral Set

/-! ### The odd-level tail-mass scalar -/

/-- The tail mass of the odd level `n` above `3`: `∫_3^{n+2} fseq n`.  The upper limit `n+2` is the
support edge of `fseq n` (`fseq_eq_zero_of_ge`), so this is the entire mass of `fseq n` on `[3,∞)`.
Sibling of `massE n = ∫_2^{n+2} fseq n` (only the lower limit differs: `3` vs `2`). -/
noncomputable def massO (n : ℕ) : ℝ := ∫ u in (3 : ℝ)..((n : ℝ) + 2), fseq n u

/-- `massO n ≥ 0` (integral of the nonnegative `fseq n` over a correctly-oriented interval). -/
theorem massO_nonneg (n : ℕ) : 0 ≤ massO n := by
  unfold massO
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · apply intervalIntegral.integral_nonneg
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      linarith
    · intro u _; exact fseq_nonneg n u

/-! ### The even-level → (flat mass, tail mass) identity -/

/-- **The even-level mass identity.**  For an even level `k ≥ 4` and `s ∈ [2,4]`,
`fseq k s = (massE (k−2)·(log 3 − log (s−1)) + massO (k−1))/s`.  Flat piece via MR1's
`fseq_odd_eq_massE` + `∫ u⁻¹ = log`; tail piece is `massO (k−1)`.  (ℕ-subtraction is handled by the
internal reparametrisation `k = i + 2`.) -/
theorem fseq_even_eq_masses {k : ℕ} (hk : 4 ≤ k) (hke : Even k) {s : ℝ}
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    fseq k s = (massE (k - 2) * (Real.log 3 - Real.log (s - 1)) + massO (k - 1)) / s := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  have hi0 : i ≠ 0 := by omega
  have hie : Even i := by
    have h := Nat.even_iff.mp hke; exact Nat.even_iff.mpr (by omega)
  have hev : Even (i + 1 + 1) := by
    have h := Nat.even_iff.mp hie; exact Nat.even_iff.mpr (by omega)
  have hsub2 : i + 2 - 2 = i := by omega
  have hsub1 : i + 2 - 1 = i + 1 := by omega
  rw [hsub2, hsub1]
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1pos : (0 : ℝ) < s - 1 := by linarith
  have hs1le3 : s - 1 ≤ 3 := by linarith
  -- even window (BJS (16))
  have hwin : fseq (i + 2) s
      = (1 / s) * ∫ t in s..((i : ℝ) + 4), fseq (i + 1) (t - 1) := by
    have h := fseq_even_window (n := i + 1) hev hs2
    have hup : ((i + 1 : ℕ) : ℝ) + 3 = (i : ℝ) + 4 := by push_cast; ring
    rw [hup] at h
    exact h
  -- change of variables u = t − 1
  have hcv : (∫ t in s..((i : ℝ) + 4), fseq (i + 1) (t - 1))
      = ∫ u in (s - 1)..((i : ℝ) + 3), fseq (i + 1) u := by
    have e2 : (i : ℝ) + 4 - 1 = (i : ℝ) + 3 := by ring
    rw [integral_comp_sub_right (fun u => fseq (i + 1) u) 1, e2]
  -- split at u = 3
  have hsplit3 : (∫ u in (s - 1)..((i : ℝ) + 3), fseq (i + 1) u)
      = (∫ u in (s - 1)..(3 : ℝ), fseq (i + 1) u)
        + ∫ u in (3 : ℝ)..((i : ℝ) + 3), fseq (i + 1) u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (fseq_intervalIntegrable (i + 1) (s - 1) 3)
      (fseq_intervalIntegrable (i + 1) 3 ((i : ℝ) + 3))).symm
  -- tail piece is massO (i+1)
  have htail : (∫ u in (3 : ℝ)..((i : ℝ) + 3), fseq (i + 1) u) = massO (i + 1) := by
    have hb : ((i + 1 : ℕ) : ℝ) + 2 = (i : ℝ) + 3 := by push_cast; ring
    unfold massO; rw [hb]
  -- flat piece is massE i · (log 3 − log (s−1))
  have hflat : (∫ u in (s - 1)..(3 : ℝ), fseq (i + 1) u)
      = massE i * (Real.log 3 - Real.log (s - 1)) := by
    have hcongr : (∫ u in (s - 1)..(3 : ℝ), fseq (i + 1) u)
        = ∫ u in (s - 1)..(3 : ℝ), massE i * u⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hs1le3] at hu
      obtain ⟨hu1, hu2⟩ := hu
      have hu1' : (1 : ℝ) ≤ u := by linarith
      rw [fseq_odd_eq_massE hi0 hie hu1' hu2, div_eq_mul_inv]
    rw [hcongr, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hs1pos (by norm_num : (0 : ℝ) < 3),
      Real.log_div (by norm_num) (ne_of_gt hs1pos)]
  rw [hwin, hcv, hsplit3, hflat, htail]
  ring

/-! ### The even-sum mass ledger (the A₁ reduction) -/

/-- **The A₁ even-sum reduction.**  Given upper bounds `ME`, `MO` on the MR1/MR4 mass sums,
the truncated even sum obeys `evenSum ≤ (4−s)²/(s(s−1)) + ((4−s)/(s−1)·ME + MO)/s` on the operating
window `[2,4]`.  Reindexes `k ↦ (k−2, k−1)` onto the even/odd mass index sets and bounds the flat
factor `log 3 − log(s−1) ≤ (4−s)/(s−1)` and the leading term `f₂ ≤ (4−s)²/(s(s−1))`. -/
theorem evenSum_le_of_massSums (N : ℕ) (hN : 2 ≤ N) (ME MO : ℝ)
    (hME0 : 0 ≤ ME) (_hMO0 : 0 ≤ MO)
    (hME : (∑ i ∈ (Finset.range N).filter (fun i => Even i ∧ 2 ≤ i), massE i) ≤ ME)
    (hMO : (∑ j ∈ (Finset.range N).filter (fun j => Odd j ∧ 3 ≤ j), massO j) ≤ MO)
    {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s)
      ≤ (4 - s) ^ 2 / (s * (s - 1)) + ((4 - s) / (s - 1) * ME + MO) / s := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hs1ne : s - 1 ≠ 0 := ne_of_gt hs1
  have hs1le3 : s - 1 ≤ 3 := by linarith
  -- a/s ≤ b/s helper (positive denominator)
  have hdivs : ∀ a b : ℝ, a ≤ b → a / s ≤ b / s := by
    intro a b h
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hs0.le)
  set F := (Finset.range (N + 1)).filter (fun n => Even n) with hF
  set K := (Finset.range (N + 1)).filter (fun n => Even n ∧ 4 ≤ n) with hK
  -- peel: Σ_F = Σ_K + Σ_R, with R = {0,2}
  have hFK : F.filter (fun n => 4 ≤ n) = K := by rw [hK, hF, Finset.filter_filter]
  have hsplit : (∑ n ∈ F, fseq n s)
      = (∑ n ∈ K, fseq n s) + (∑ n ∈ F.filter (fun n => ¬ 4 ≤ n), fseq n s) := by
    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not F (fun n => 4 ≤ n) (fun n => fseq n s)]
    rw [hFK]
  have hR : F.filter (fun n => ¬ 4 ≤ n) = {0, 2} := by
    rw [hF, Finset.filter_filter]
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton,
      Nat.even_iff]
    omega
  have hRsum : (∑ n ∈ F.filter (fun n => ¬ 4 ≤ n), fseq n s) = fseq 2 s := by
    rw [hR, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 2), fseq_zero, zero_add]
  -- rewrite each K-term via the mass identity
  have hKterm : ∀ k ∈ K, fseq k s
      = (massE (k - 2) * (Real.log 3 - Real.log (s - 1)) + massO (k - 1)) / s := by
    intro k hk
    rw [hK, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, hke, hk4⟩ := hk
    exact fseq_even_eq_masses hk4 hke hs2 hs4
  have hKsum : (∑ k ∈ K, fseq k s)
      = ((∑ k ∈ K, massE (k - 2)) * (Real.log 3 - Real.log (s - 1))
          + ∑ k ∈ K, massO (k - 1)) / s := by
    rw [Finset.sum_congr rfl (fun k hk => hKterm k hk), ← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  -- the two reindexed mass sums are bounded by ME, MO
  have hSE0 : (0 : ℝ) ≤ ∑ k ∈ K, massE (k - 2) := Finset.sum_nonneg (fun k _ => massE_nonneg _)
  have hSE : (∑ k ∈ K, massE (k - 2)) ≤ ME := by
    have hinj : Set.InjOn (fun k => k - 2) (↑K : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, hK, Finset.mem_filter, Finset.mem_range] at hx hy
      simp only at hxy
      omega
    have himg : (∑ k ∈ K, massE (k - 2)) = ∑ i ∈ K.image (fun k => k - 2), massE i :=
      (Finset.sum_image hinj).symm
    rw [himg]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => massE_nonneg i)) hME
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨k, hkK, rfl⟩ := hi
    rw [hK, Finset.mem_filter, Finset.mem_range] at hkK
    obtain ⟨hkN, hke, hk4⟩ := hkK
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, by omega⟩
    rw [Nat.even_iff]; rw [Nat.even_iff] at hke; omega
  have hSO : (∑ k ∈ K, massO (k - 1)) ≤ MO := by
    have hinj : Set.InjOn (fun k => k - 1) (↑K : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, hK, Finset.mem_filter, Finset.mem_range] at hx hy
      simp only at hxy
      omega
    have himg : (∑ k ∈ K, massO (k - 1)) = ∑ j ∈ K.image (fun k => k - 1), massO j :=
      (Finset.sum_image hinj).symm
    rw [himg]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => massO_nonneg j)) hMO
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, hkK, rfl⟩ := hj
    rw [hK, Finset.mem_filter, Finset.mem_range] at hkK
    obtain ⟨hkN, hke, hk4⟩ := hkK
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, by omega⟩
    rw [Nat.odd_iff]; rw [Nat.even_iff] at hke; omega
  -- the flat log factor
  have hL0 : (0 : ℝ) ≤ Real.log 3 - Real.log (s - 1) := by
    have := (Real.log_le_log_iff hs1 (by norm_num : (0 : ℝ) < 3)).mpr hs1le3
    linarith
  have hLub : Real.log 3 - Real.log (s - 1) ≤ (4 - s) / (s - 1) := by
    have hlog : Real.log (3 / (s - 1)) ≤ 3 / (s - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by norm_num) hs1ne] at hlog
    have harith : 3 / (s - 1) - 1 = (4 - s) / (s - 1) := by field_simp; ring
    linarith [hlog, harith]
  have hAsq0 : (0 : ℝ) ≤ (4 - s) / (s - 1) := div_nonneg (by linarith) hs1.le
  -- numerator bound
  have hnum : (∑ k ∈ K, massE (k - 2)) * (Real.log 3 - Real.log (s - 1))
      + ∑ k ∈ K, massO (k - 1) ≤ (4 - s) / (s - 1) * ME + MO := by
    have h1 : (∑ k ∈ K, massE (k - 2)) * (Real.log 3 - Real.log (s - 1))
        ≤ (4 - s) / (s - 1) * ME := by
      calc (∑ k ∈ K, massE (k - 2)) * (Real.log 3 - Real.log (s - 1))
          ≤ ME * ((4 - s) / (s - 1)) := mul_le_mul hSE hLub hL0 hME0
        _ = (4 - s) / (s - 1) * ME := by ring
    linarith [h1, hSO]
  -- assemble
  rw [hsplit, hRsum, hKsum]
  have hKbound : ((∑ k ∈ K, massE (k - 2)) * (Real.log 3 - Real.log (s - 1))
      + ∑ k ∈ K, massO (k - 1)) / s ≤ ((4 - s) / (s - 1) * ME + MO) / s := hdivs _ _ hnum
  have hf2 : fseq 2 s ≤ (4 - s) ^ 2 / (s * (s - 1)) := fseq_two_le_sq hs2 hs4
  linarith [hKbound, hf2]

/-- **The A₁ ledger row.**  With `Σ massE ≤ 43/75` (MR2) and `Σ massO ≤ 11/125` (MR4), the
truncated `fchain` reaches the frozen A₁ lower value `9779/10000` uniformly on `[39992/10000, 4]`.
Worst point `s = 39992/10000`; the rational close has margin ≈ 5.7·10⁻⁵. -/
theorem fchain_ge_A1_of_massSums (N : ℕ) (hN : 2 ≤ N)
    (hME : (∑ i ∈ (Finset.range N).filter (fun i => Even i ∧ 2 ≤ i), massE i) ≤ 43 / 75)
    (hMO : (∑ j ∈ (Finset.range N).filter (fun j => Odd j ∧ 3 ≤ j), massO j) ≤ 11 / 125) :
    ∀ s ∈ Set.Icc (39992 / 10000 : ℝ) 4, (9779 / 10000 : ℝ) ≤ fchain N s := by
  intro s hs
  obtain ⟨hlo, hhi⟩ := hs
  have hs2 : (2 : ℝ) ≤ s := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hs1 : (0 : ℝ) < s - 1 := by linarith
  have hs0' : s ≠ 0 := ne_of_gt hs0
  have hs1' : s - 1 ≠ 0 := ne_of_gt hs1
  have hden : (0 : ℝ) < s * (s - 1) := mul_pos hs0 hs1
  have hev := evenSum_le_of_massSums N hN (43 / 75) (11 / 125) (by norm_num) (by norm_num)
    hME hMO hs2 hhi
  have expand : (4 - s) ^ 2 / (s * (s - 1)) + ((4 - s) / (s - 1) * (43 / 75) + 11 / 125) / s
      = ((4 - s) ^ 2 + (43 / 75) * (4 - s) + (11 / 125) * (s - 1)) / (s * (s - 1)) := by
    field_simp
    ring
  have hpoly : (4 - s) ^ 2 + (43 / 75) * (4 - s) + (11 / 125) * (s - 1)
      ≤ (221 / 10000) * (s * (s - 1)) := by
    have hgap : (0 : ℝ) ≤ s - 39992 / 10000 := by linarith
    have hgap4 : (0 : ℝ) ≤ 4 - s := by linarith
    nlinarith [mul_nonneg hgap hgap4, sq_nonneg (4 - s), hlo, hhi]
  have hRHS : (4 - s) ^ 2 / (s * (s - 1)) + ((4 - s) / (s - 1) * (43 / 75) + 11 / 125) / s
      ≤ 221 / 10000 := by
    rw [expand, div_le_iff₀ hden]
    linarith [hpoly]
  have hsum : (∑ n ∈ (Finset.range (N + 1)).filter (fun n => Even n), fseq n s) ≤ 221 / 10000 :=
    hev.trans hRHS
  unfold fchain
  linarith [hsum]

/-! ### The crude odd-tail-mass interface -/

/-- **Crude tail mass.**  `massO n ≤ (5/3)·(99/100)^{n−1}·e^{−6/5}` for `n ≥ 1`, from `fseq_le` and
the majorant integral `∫_3^c hbar ≤ (5/6)·hbar 3 = (5/6)·e^{−16/5}` (`intbound_hi` at `a = 3`).  The
constant collapses: `2·(5/6)·e²·e^{−16/5} = (5/3)·e^{−6/5}`.  Sibling of `massE_le_crude` (its lower
limit `2` gives the multiplier `e²·e^{−2} = 1`; here the lower limit `3` gives `e²·e^{−16/5} =
e^{−6/5}`). -/
theorem massO_le_crude (n : ℕ) (hn : 1 ≤ n) :
    massO n ≤ (5 / 3) * (99 / 100) ^ (n - 1) * Real.exp (-(6 / 5)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold massO
  set U : ℝ := ((k + 1 : ℕ) : ℝ) + 2 with hU
  have hab : (3 : ℝ) ≤ U := by
    rw [hU]; push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hconst_nonneg : (0 : ℝ) ≤ 2 * Real.exp 2 * (99 / 100) ^ k := by positivity
  have hmono : (∫ u in (3 : ℝ)..U, fseq (k + 1) u)
      ≤ ∫ u in (3 : ℝ)..U, 2 * Real.exp 2 * (99 / 100) ^ k * hbar u :=
    intervalIntegral.integral_mono_on hab (fseq_intervalIntegrable (k + 1) _ _)
      ((continuous_const.mul hbar_continuous).intervalIntegrable _ _)
      (fun u _ => fseq_le k u)
  rw [intervalIntegral.integral_const_mul] at hmono
  have hhbar3 : hbar 3 = Real.exp (-2 - 6 / 5) := by
    unfold hbar
    rw [max_eq_left (by norm_num : (2 : ℝ) ≤ 3)]
    congr 1; ring
  have hib : (∫ u in (3 : ℝ)..U, hbar u) ≤ (5 / 6) * Real.exp (-2 - 6 / 5) := by
    have := intbound_hi 3 U (by norm_num : (2 : ℝ) ≤ 3)
    rwa [hhbar3] at this
  have hprod : 2 * Real.exp 2 * (99 / 100 : ℝ) ^ k * ((5 / 6) * Real.exp (-2 - 6 / 5))
      = (5 / 3) * (99 / 100) ^ k * Real.exp (-(6 / 5)) := by
    have he : Real.exp 2 * Real.exp (-2 - 6 / 5) = Real.exp (-(6 / 5)) := by
      rw [← Real.exp_add]; congr 1; norm_num
    have hrw : 2 * Real.exp 2 * (99 / 100 : ℝ) ^ k * ((5 / 6) * Real.exp (-2 - 6 / 5))
        = (5 / 3) * (99 / 100) ^ k * (Real.exp 2 * Real.exp (-2 - 6 / 5)) := by ring
    rw [hrw, he]
  calc (∫ u in (3 : ℝ)..U, fseq (k + 1) u)
      ≤ 2 * Real.exp 2 * (99 / 100) ^ k * ∫ u in (3 : ℝ)..U, hbar u := hmono
    _ ≤ 2 * Real.exp 2 * (99 / 100) ^ k * ((5 / 6) * Real.exp (-2 - 6 / 5)) :=
        mul_le_mul_of_nonneg_left hib hconst_nonneg
    _ = (5 / 3) * (99 / 100) ^ k * Real.exp (-(6 / 5)) := hprod

end Salt.Chen
