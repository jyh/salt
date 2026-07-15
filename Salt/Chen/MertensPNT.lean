/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.TripleCount
import Salt.Chen.StepBound2

/-!
# The fiber-independent Mertens/PNT layer (M-recon nodes M1, M3, M4)

Design: `docs/blueprints/flags.md`, the `2026-07-13 M-RECON` and `THE SW4 GATE — CATCH #49`
entries.  The "absolute-numbers" layer the C5 symbolic design deferred; now on the critical
path for SW4 / the H-glue.  This module supplies the three fiber-*independent* pieces (M2, the
two-sided W-ratio, waits on the fiber-shape design block):

* **M1 — the LOWER windowed Mertens.**  `sum_inv_prime_window_ge`: the exact mirror of the
  landed upper `Salt.BrunLower.sum_inv_prime_window_le`, obtained by re-running the `window_core`
  Abel pass with the opposite sign.  Same window Finset (`primesInWindow`), same two-sided
  `abs_Sfun_sub_log_le` input; honest constant `C₃' = 19` (`= 18` from the Abel `R`-terms plus
  `1/log w` from the one boundary prime `⌊z⌋₊`).

* **M3 — the window Λ-mass, two-sided.**  `lambda_mass_lower` / `lambda_mass_upper`: from
  `psiTot_pnt` at the two endpoints `x−2`, `x/2−1` via the index-aligning
  `twinWindow_mass_eq` (`∑_{twinWindow} Λ = ψ(x−2) − ψ(x/2−1)`).  The endpoint error terms
  collapse to `2K·x/log x` through the monotonicity of `t ↦ t/log t` on `[e, ∞)`
  (`self_div_log_le`, from mathlib's `Real.log_div_self_antitoneOn`).

* **M4 — the rounding thresholds.**  `logRatio_A1_mem` / `logRatio_A3_mem`: the operating-point
  membership under nat-floors, landing in the frozen `fchain_A1_final` / `Fchain_A2_final`
  windows.  See the module's M4 section and the `flags.md` M4-edge note for the exact
  left-edge (3.9992) analysis.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset MeasureTheory Set intervalIntegral ArithmeticFunction
open Salt.Maynard Salt.BrunLower Salt.LS

namespace Salt.Chen

/-! ## Section M1 — the lower windowed Mertens

We re-run the corpus `window_core` Abel pass (`Salt/BrunLower/MertensWindow.lean`, ~line 472)
with every inequality flipped.  The Abel *identities* (`sum_mul_eq_sub_integral_mul₁`,
`integral_add_adjacent_intervals`) are reused verbatim; only the pointwise bound on
`deriv mF · Sfun`, the integral monotonicity direction, and the two boundary bounds change sign.
The two-sided `abs_Sfun_sub_log_le` supplies both halves. -/

/-- **The windowed Abel core, LOWER form.**  The exact mirror of `Salt.BrunLower.window_core`.
`∑_{p ≤ ⌊z⌋} (log p)/p·(1/log p) − (same at w) ≥ log(log z/log w) − 18/log w`, in the `mF·mC`
(Abel) form.  Same `18` as the upper: the Mertens constant cancels, only the two-sided `R`-term
(`|S(t) − log t| ≤ 6`) survives, weighted to `O(1/log w)`. -/
theorem window_core_lower {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    Real.log (Real.log z / Real.log w) - 18 / Real.log w
      ≤ (∑ k ∈ Finset.Icc 0 ⌊z⌋₊, mF k * mC k) - (∑ k ∈ Finset.Icc 0 ⌊w⌋₊, mF k * mC k) := by
  have hz : (2:ℝ) ≤ z := le_trans hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlwne : Real.log w ≠ 0 := ne_of_gt hlogw
  have hlzne : Real.log z ≠ 0 := ne_of_gt hlogz
  have hlogwz : Real.log w ≤ Real.log z := Real.log_le_log (by linarith) hwz
  have hinvzw : (Real.log z)⁻¹ ≤ (Real.log w)⁻¹ := by
    rw [← one_div, ← one_div]; exact one_div_le_one_div_of_le hlogw hlogwz
  have hinvz0 : (0:ℝ) ≤ (Real.log z)⁻¹ := by positivity
  have hinvw0 : (0:ℝ) ≤ (Real.log w)⁻¹ := by positivity
  have hGint_z : IntegrableOn (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      (Set.Icc 2 z) :=
    integrableOn_mul_sum_Icc mC (m := 0) (by norm_num) (integrableOn_deriv_mF_real hz)
  have hII_2w : IntervalIntegrable (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      volume 2 w := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hw]
    exact hGint_z.mono_set (Set.Icc_subset_Icc le_rfl hwz)
  have hII_wz : IntervalIntegrable (fun t => deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      volume w z := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hwz]
    exact hGint_z.mono_set (Set.Icc_subset_Icc hw le_rfl)
  have habelz := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one z
    (fun s hs => differentiableAt_mF (by simp only [Set.mem_Icc] at hs; exact hs.1))
    (integrableOn_deriv_mF_real hz)
  have habelw := sum_mul_eq_sub_integral_mul₁ mC mC_zero mC_one w
    (fun s hs => differentiableAt_mF (by simp only [Set.mem_Icc] at hs; exact hs.1))
    (integrableOn_deriv_mF_real hw)
  rw [← intervalIntegral.integral_of_le hz,
    show (∑ k ∈ Finset.Icc 0 ⌊z⌋₊, mC k) = Sfun z from rfl] at habelz
  rw [← intervalIntegral.integral_of_le hw,
    show (∑ k ∈ Finset.Icc 0 ⌊w⌋₊, mC k) = Sfun w from rfl] at habelw
  have hadd : (∫ t in (2:ℝ)..w, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      + (∫ t in w..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      = ∫ t in (2:ℝ)..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k :=
    intervalIntegral.integral_add_adjacent_intervals hII_2w hII_wz
  -- pointwise UPPER bound on `deriv mF t · Sfun t` (uses the LOWER half `Sfun t ≥ log t − 6`)
  have hpt_up : ∀ t ∈ Set.Icc w z,
      deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k
        ≤ -(t * Real.log t)⁻¹ + 6 * (t * Real.log t ^ 2)⁻¹ := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have ht2 : (2:ℝ) ≤ t := le_trans hw ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hinvnn : (0:ℝ) ≤ (t * Real.log t ^ 2)⁻¹ := by positivity
    have hSt : Real.log t - 6 ≤ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k := by
      have := abs_Sfun_sub_log_le ht2
      rw [abs_le] at this
      have hSeq : Sfun t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k := rfl
      linarith [this.1]
    rw [deriv_mF ht2]
    have hkey : (t * Real.log t ^ 2)⁻¹ * (Real.log t - 6)
        ≤ (t * Real.log t ^ 2)⁻¹ * (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k) :=
      mul_le_mul_of_nonneg_left hSt hinvnn
    have hsplit : (t * Real.log t ^ 2)⁻¹ * (Real.log t - 6)
        = (t * Real.log t)⁻¹ - 6 * (t * Real.log t ^ 2)⁻¹ := by
      have hne : Real.log t ≠ 0 := ne_of_gt hlogt
      field_simp
    nlinarith [hkey, hsplit]
  have hIntA : (∫ t in w..z, -(t * Real.log t)⁻¹)
      = -(Real.log (Real.log z) - Real.log (Real.log w)) := by
    rw [intervalIntegral.integral_neg, integral_inv_tlog_real hw hwz]
  have hIntB : (∫ t in w..z, 6 * (t * Real.log t ^ 2)⁻¹)
      = 6 * ((Real.log w)⁻¹ - (Real.log z)⁻¹) := by
    rw [intervalIntegral.integral_const_mul, integral_inv_tlogsq_real hw hwz]
  have hAintble : IntervalIntegrable (fun t => -(t * Real.log t)⁻¹) volume w z :=
    ((continuousOn_inv_tlog_real hw hwz).intervalIntegrable).neg
  have hBintble : IntervalIntegrable (fun t => 6 * (t * Real.log t ^ 2)⁻¹) volume w z :=
    ((continuousOn_inv_tlogsq_real hw hwz).intervalIntegrable).const_mul 6
  have hUint : (∫ t in w..z, (-(t * Real.log t)⁻¹ + 6 * (t * Real.log t ^ 2)⁻¹))
      = -(Real.log (Real.log z) - Real.log (Real.log w))
        + 6 * ((Real.log w)⁻¹ - (Real.log z)⁻¹) := by
    rw [intervalIntegral.integral_add hAintble hBintble, hIntA, hIntB]
  have hmono_up : (∫ t in w..z, deriv mF t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mC k)
      ≤ ∫ t in w..z, (-(t * Real.log t)⁻¹ + 6 * (t * Real.log t ^ 2)⁻¹) :=
    intervalIntegral.integral_mono_on hwz hII_wz (hAintble.add hBintble) hpt_up
  have hSz := abs_Sfun_sub_log_le hz
  have hSw := abs_Sfun_sub_log_le hw
  rw [abs_le] at hSz hSw
  have hAbound' : 1 - 6 * (Real.log w)⁻¹ ≤ mF z * Sfun z := by
    have hmFz : mF z = (Real.log z)⁻¹ := rfl
    have h1 : 1 - 6 * (Real.log z)⁻¹ = (Real.log z)⁻¹ * (Real.log z - 6) := by
      rw [mul_sub, inv_mul_cancel₀ hlzne]; ring
    calc 1 - 6 * (Real.log w)⁻¹ ≤ 1 - 6 * (Real.log z)⁻¹ := by linarith [hinvzw]
      _ = (Real.log z)⁻¹ * (Real.log z - 6) := h1
      _ ≤ (Real.log z)⁻¹ * Sfun z := mul_le_mul_of_nonneg_left (by linarith [hSz.1]) hinvz0
      _ = mF z * Sfun z := by rw [hmFz]
  have hBbound' : mF w * Sfun w ≤ 1 + 6 * (Real.log w)⁻¹ := by
    have hmFw : mF w = (Real.log w)⁻¹ := rfl
    have h1 : 1 + 6 * (Real.log w)⁻¹ = (Real.log w)⁻¹ * (Real.log w + 6) := by
      rw [mul_add, inv_mul_cancel₀ hlwne]; ring
    calc mF w * Sfun w = (Real.log w)⁻¹ * Sfun w := by rw [hmFw]
      _ ≤ (Real.log w)⁻¹ * (Real.log w + 6) :=
          mul_le_mul_of_nonneg_left (by linarith [hSw.2]) hinvw0
      _ = 1 + 6 * (Real.log w)⁻¹ := h1.symm
  rw [Real.log_div hlzne hlwne, div_eq_mul_inv]
  linarith [habelz, habelw, hadd, hmono_up, hUint, hAbound', hBbound', hinvz0]

/-- **The frozen M1 target.**  `log(log z/log w) − 19/log w ≤ ∑_{w ≤ p < z} 1/p` for
`2 ≤ w ≤ z`.  `w₀ = 2`, `C₃' = 19`.  Mirror of `Salt.BrunLower.sum_inv_prime_window_le`
over the identical `primesInWindow w z` set; the single extra `1/log w` (vs the Abel `18`)
absorbs the lone boundary prime `⌊z⌋₊` that the `[⌊w⌋,⌊z⌋]` Abel window may carry outside
`[w, z)`. -/
theorem sum_inv_prime_window_ge {w z : ℝ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    Real.log (Real.log z / Real.log w) - 19 / Real.log w
      ≤ ∑ p ∈ Salt.BrunLower.primesInWindow w z, (1 : ℝ) / p := by
  have hz : (2:ℝ) ≤ z := le_trans hw hwz
  have hlogw : 0 < Real.log w := Real.log_pos (by linarith)
  have hfloorwz : ⌊w⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor hwz
  have hw2 : 2 ≤ ⌊w⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hw_pos : 0 < ⌊w⌋₊ := by omega
  set Wz := (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime with hWz
  set Ww := (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime with hWw
  have hWwWz : Ww ⊆ Wz := by
    rw [hWw, hWz]; apply Finset.filter_subset_filter
    intro x hx; rw [Finset.mem_range] at hx ⊢; omega
  have hcore := window_core_lower hw hwz
  rw [Salt.BrunLower.sum_mF_mul_mC_eq z, Salt.BrunLower.sum_mF_mul_mC_eq w, ← hWz, ← hWw] at hcore
  have hsdiff : (∑ p ∈ Wz, (1:ℝ)/p) - (∑ p ∈ Ww, (1:ℝ)/p) = ∑ p ∈ Wz \ Ww, (1:ℝ)/p := by
    rw [eq_comm, eq_sub_iff_add_eq]; exact Finset.sum_sdiff hWwWz
  have hfloorlog : Real.log w ≤ (⌊w⌋₊ : ℝ) := by
    have h1 : Real.log w ≤ w - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h2 : w < (⌊w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w
    linarith
  -- `Wz \ Ww ⊆ {⌊z⌋} ∪ primesInWindow`: the only member outside `[w, z)` is `p = ⌊z⌋ = z`.
  have hCsub : Wz \ Ww ⊆ insert ⌊z⌋₊ (Salt.BrunLower.primesInWindow w z) := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    simp only [hWz, hWw, Finset.mem_filter, Finset.mem_range, not_and] at hp
    obtain ⟨⟨hpz, hpp⟩, hpnotw⟩ := hp
    have hpge : ⌊w⌋₊ < p := by
      rcases Nat.lt_or_ge ⌊w⌋₊ p with h | h
      · exact h
      · exact absurd hpp (hpnotw (by omega))
    have hple : p ≤ ⌊z⌋₊ := by omega
    rw [Finset.mem_insert]
    by_cases hpltz : (p:ℝ) < z
    · right
      rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_ceil.mpr hpltz, hpp, ?_⟩
      have h1 : (⌊w⌋₊ : ℝ) + 1 ≤ (p:ℝ) := by exact_mod_cast hpge
      have h2 : w < (⌊w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one w
      linarith
    · left
      rw [not_lt] at hpltz
      have hzf : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
      have hpzf : (p:ℝ) ≤ (⌊z⌋₊:ℝ) := by exact_mod_cast hple
      have hpe : (p:ℝ) = (⌊z⌋₊:ℝ) := by linarith
      exact_mod_cast hpe
  have hnn : ∀ p ∈ insert ⌊z⌋₊ (Salt.BrunLower.primesInWindow w z), p ∉ Wz \ Ww →
      0 ≤ (1:ℝ)/p := fun p _ _ => by positivity
  have hstep : ∑ p ∈ Wz \ Ww, (1:ℝ)/p
      ≤ ∑ p ∈ insert ⌊z⌋₊ (Salt.BrunLower.primesInWindow w z), (1:ℝ)/p :=
    Finset.sum_le_sum_of_subset_of_nonneg hCsub hnn
  have hins : ∑ p ∈ insert ⌊z⌋₊ (Salt.BrunLower.primesInWindow w z), (1:ℝ)/p
      ≤ 1/(⌊z⌋₊:ℝ) + ∑ p ∈ Salt.BrunLower.primesInWindow w z, (1:ℝ)/p := by
    by_cases hmem : ⌊z⌋₊ ∈ Salt.BrunLower.primesInWindow w z
    · rw [Finset.insert_eq_self.mpr hmem]
      have : (0:ℝ) ≤ 1/(⌊z⌋₊:ℝ) := by positivity
      linarith
    · rw [Finset.sum_insert hmem]
  have hinvz : 1/(⌊z⌋₊:ℝ) ≤ 1/(⌊w⌋₊:ℝ) := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast hw_pos
    · exact_mod_cast hfloorwz
  have hinvw : 1/(⌊w⌋₊:ℝ) ≤ 1/Real.log w := one_div_le_one_div_of_le hlogw hfloorlog
  have hsplit : (18:ℝ)/Real.log w + 1/Real.log w = 19/Real.log w := by rw [← add_div]; norm_num
  linarith [hcore, hsdiff, hstep, hins, hinvz, hinvw, hsplit]

/-! ## Section M3 — the window Λ-mass (two-sided)

`twinWindow x = Icc (x/2) (x−2)`, so `∑_{twinWindow} Λ = ψ(x−2) − ψ(x/2−1)`.  The PNT
(`psiTot_pnt`) pins each endpoint to its main term with a `K··/log ·` error; the two errors
collapse to `2K·x/log x` via the monotonicity of `t ↦ t/log t`. -/

/-- `t ↦ t/log t` is monotone increasing on `[e, ∞)` (reciprocal of mathlib's
`Real.log_div_self_antitoneOn`).  For `e ≤ a ≤ b`: `a/log a ≤ b/log b`. -/
private theorem self_div_log_le {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le ha0 hab
  have h1a : (1:ℝ) < a := lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) ha
  have hloga : 0 < Real.log a := Real.log_pos h1a
  have hlogb : 0 < Real.log b := Real.log_pos (lt_of_lt_of_le h1a hab)
  have hanti := Real.log_div_self_antitoneOn (Set.mem_Ici.mpr ha)
    (Set.mem_Ici.mpr (le_trans ha hab)) hab
  rw [div_le_div_iff₀ hb0 ha0] at hanti
  rw [div_le_div_iff₀ hloga hlogb]
  linear_combination hanti

/-- **Index alignment.**  `∑_{n ∈ twinWindow x} Λ n = ψ(x−2) − ψ(x/2−1)` for `4 ≤ x`.  The
window `Icc (x/2) (x−2)` is the top slab of `Icc 1 (x−2)` after removing `Icc 1 (x/2−1)`. -/
theorem twinWindow_mass_eq {x : ℕ} (hx : 4 ≤ x) :
    ∑ n ∈ twinWindow x, vonMangoldt n = psiTot (x - 2) - psiTot (x / 2 - 1) := by
  have hunion : Finset.Icc 1 (x - 2) = Finset.Icc 1 (x / 2 - 1) ∪ twinWindow x := by
    unfold twinWindow; ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (x / 2 - 1)) (twinWindow x) := by
    unfold twinWindow; simp only [Finset.disjoint_left, Finset.mem_Icc]; omega
  have hsum : psiTot (x - 2) = psiTot (x / 2 - 1) + ∑ n ∈ twinWindow x, vonMangoldt n := by
    unfold psiTot; rw [hunion, Finset.sum_union hdisj]
  linarith [hsum]

/-- **M3, LOWER.**  `x/2 − 1 − 2K·x/log x ≤ ∑_{n ∈ twinWindow x} Λ n` for `8 ≤ x`, with the
`psiTot_pnt` constant `K ≥ 0`.  From the endpoint subtraction `ψ(x−2) − ψ(x/2−1)`; the two
`K··/log ·` errors are each `≤ K·x/log x` by `self_div_log_le`. -/
theorem lambda_mass_lower :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 8 ≤ x →
      (x : ℝ) / 2 - 1 - 2 * K * x / Real.log x ≤ ∑ n ∈ twinWindow x, vonMangoldt n := by
  obtain ⟨K, hK0, hK⟩ := psiTot_pnt
  refine ⟨K, hK0, fun x hx => ?_⟩
  have hx8R : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hU3 : 3 ≤ x - 2 := by omega
  have hL3 : 3 ≤ x / 2 - 1 := by omega
  have hmass : ∑ n ∈ twinWindow x, vonMangoldt n = psiTot (x - 2) - psiTot (x / 2 - 1) :=
    twinWindow_mass_eq (by omega)
  have hpU := abs_le.mp (hK (x - 2) hU3)
  have hpL := abs_le.mp (hK (x / 2 - 1) hL3)
  -- casts of the two nat endpoints
  have hUx : ((x - 2 : ℕ) : ℝ) = (x : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ x)]; norm_num
  have hL3R : (3 : ℝ) ≤ ((x / 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hL3
  have hdiv : ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
    have h := Nat.div_mul_le_self x 2
    have hh : ((x / 2 : ℕ) : ℝ) * 2 ≤ (x:ℝ) := by exact_mod_cast h
    linarith
  have hLle : ((x / 2 - 1 : ℕ) : ℝ) ≤ (x : ℝ) / 2 - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ x / 2)]; push_cast; linarith
  -- the two `t/log t` comparisons against `x/log x`
  have hUe : Real.exp 1 ≤ ((x - 2 : ℕ) : ℝ) := by rw [hUx]; linarith [Real.exp_one_lt_three]
  have hUxle : ((x - 2 : ℕ) : ℝ) ≤ (x : ℝ) := by rw [hUx]; linarith
  have hLe : Real.exp 1 ≤ ((x / 2 - 1 : ℕ) : ℝ) := by linarith [Real.exp_one_lt_three, hL3R]
  have hLxle : ((x / 2 - 1 : ℕ) : ℝ) ≤ (x : ℝ) := by linarith [hLle]
  have hUdl : ((x - 2 : ℕ) : ℝ) / Real.log ((x - 2 : ℕ) : ℝ) ≤ (x : ℝ) / Real.log x :=
    self_div_log_le hUe hUxle
  have hLdl : ((x / 2 - 1 : ℕ) : ℝ) / Real.log ((x / 2 - 1 : ℕ) : ℝ) ≤ (x : ℝ) / Real.log x :=
    self_div_log_le hLe hLxle
  have herr : K * ((x - 2 : ℕ):ℝ) / Real.log ((x - 2:ℕ):ℝ)
        + K * ((x / 2 - 1 : ℕ):ℝ) / Real.log ((x / 2 - 1:ℕ):ℝ)
      ≤ 2 * K * (x:ℝ) / Real.log x := by
    have b1 := mul_le_mul_of_nonneg_left hUdl hK0
    have b2 := mul_le_mul_of_nonneg_left hLdl hK0
    have e1 : K * ((x - 2:ℕ):ℝ) / Real.log ((x-2:ℕ):ℝ)
        = K * (((x-2:ℕ):ℝ) / Real.log ((x-2:ℕ):ℝ)) := by ring
    have e2 : K * ((x / 2 - 1:ℕ):ℝ) / Real.log ((x/2-1:ℕ):ℝ)
        = K * (((x/2-1:ℕ):ℝ) / Real.log ((x/2-1:ℕ):ℝ)) := by ring
    have e3 : 2 * K * (x:ℝ) / Real.log x
        = K * ((x:ℝ)/Real.log x) + K * ((x:ℝ)/Real.log x) := by ring
    rw [e1, e2, e3]; linarith [b1, b2]
  have hmain : (x:ℝ)/2 - 1 ≤ ((x - 2:ℕ):ℝ) - ((x / 2 - 1:ℕ):ℝ) := by rw [hUx]; linarith [hLle]
  rw [hmass]
  linarith [hpU.1, hpL.2, herr, hmain]

/-- **M3, UPPER.**  `∑_{n ∈ twinWindow x} Λ n ≤ x/2 + 2K·x/log x` for `8 ≤ x`.  Same endpoint
subtraction; the H-glue may want both sides. -/
theorem lambda_mass_upper :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℕ, 8 ≤ x →
      ∑ n ∈ twinWindow x, vonMangoldt n ≤ (x : ℝ) / 2 + 2 * K * x / Real.log x := by
  obtain ⟨K, hK0, hK⟩ := psiTot_pnt
  refine ⟨K, hK0, fun x hx => ?_⟩
  have hx8R : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
  have hU3 : 3 ≤ x - 2 := by omega
  have hL3 : 3 ≤ x / 2 - 1 := by omega
  have hmass : ∑ n ∈ twinWindow x, vonMangoldt n = psiTot (x - 2) - psiTot (x / 2 - 1) :=
    twinWindow_mass_eq (by omega)
  have hpU := abs_le.mp (hK (x - 2) hU3)
  have hpL := abs_le.mp (hK (x / 2 - 1) hL3)
  have hUx : ((x - 2 : ℕ) : ℝ) = (x : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ x)]; norm_num
  have hL3R : (3 : ℝ) ≤ ((x / 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hL3
  have hLnn : (0 : ℝ) ≤ ((x / 2 - 1 : ℕ) : ℝ) := by positivity
  have hUe : Real.exp 1 ≤ ((x - 2 : ℕ) : ℝ) := by rw [hUx]; linarith [Real.exp_one_lt_three]
  have hUxle : ((x - 2 : ℕ) : ℝ) ≤ (x : ℝ) := by rw [hUx]; linarith
  have hLe : Real.exp 1 ≤ ((x / 2 - 1 : ℕ) : ℝ) := by linarith [Real.exp_one_lt_three, hL3R]
  have hLxle : ((x / 2 - 1 : ℕ) : ℝ) ≤ (x : ℝ) := by
    have hdiv : ((x / 2 : ℕ) : ℝ) ≤ (x : ℝ) / 2 := by
      have h := Nat.div_mul_le_self x 2
      have hh : ((x / 2 : ℕ) : ℝ) * 2 ≤ (x:ℝ) := by exact_mod_cast h
      linarith
    have : ((x / 2 - 1 : ℕ) : ℝ) ≤ (x:ℝ)/2 := by
      rw [Nat.cast_sub (by omega : 1 ≤ x / 2)]; push_cast; linarith
    linarith
  have hUdl : ((x - 2 : ℕ) : ℝ) / Real.log ((x - 2 : ℕ) : ℝ) ≤ (x : ℝ) / Real.log x :=
    self_div_log_le hUe hUxle
  have hLdl : ((x / 2 - 1 : ℕ) : ℝ) / Real.log ((x / 2 - 1 : ℕ) : ℝ) ≤ (x : ℝ) / Real.log x :=
    self_div_log_le hLe hLxle
  have herr : K * ((x - 2 : ℕ):ℝ) / Real.log ((x - 2:ℕ):ℝ)
        + K * ((x / 2 - 1 : ℕ):ℝ) / Real.log ((x / 2 - 1:ℕ):ℝ)
      ≤ 2 * K * (x:ℝ) / Real.log x := by
    have b1 := mul_le_mul_of_nonneg_left hUdl hK0
    have b2 := mul_le_mul_of_nonneg_left hLdl hK0
    have e1 : K * ((x - 2:ℕ):ℝ) / Real.log ((x-2:ℕ):ℝ)
        = K * (((x-2:ℕ):ℝ) / Real.log ((x-2:ℕ):ℝ)) := by ring
    have e2 : K * ((x / 2 - 1:ℕ):ℝ) / Real.log ((x/2-1:ℕ):ℝ)
        = K * (((x/2-1:ℕ):ℝ) / Real.log ((x/2-1:ℕ):ℝ)) := by ring
    have e3 : 2 * K * (x:ℝ) / Real.log x
        = K * ((x:ℝ)/Real.log x) + K * ((x:ℝ)/Real.log x) := by ring
    rw [e1, e2, e3]; linarith [b1, b2]
  -- upper on the main term: `(x−2) − (x/2−1) ≤ x/2` (since `⌊x/2⌋ ≥ (x−1)/2`)
  have hmain : ((x - 2:ℕ):ℝ) - ((x / 2 - 1:ℕ):ℝ) ≤ (x:ℝ)/2 := by
    have hcast : ((x / 2 - 1 : ℕ):ℝ) = ((x / 2 : ℕ):ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ x / 2)]; norm_num
    have hxlow : (x:ℝ) - 1 ≤ 2 * ((x / 2 : ℕ):ℝ) := by
      have hnat : x ≤ 2 * (x / 2) + 1 := by omega
      have : (x:ℝ) ≤ 2 * ((x / 2 : ℕ):ℝ) + 1 := by exact_mod_cast hnat
      linarith
    rw [hUx, hcast]; linarith
  rw [hmass]
  linarith [hpU.2, hpL.1, herr, hmain]

end Salt.Chen
