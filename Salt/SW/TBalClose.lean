/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.SW.DHExtractW
import Salt.SW.CrushH

/-!
# T-BAL THE CLOSE — the β₀-balance (the composable half of the master)

The support-native master (freeze:11, δ = 0; `docs/exploration/tbal-s0-freeze.md`) is
`3/4 ≤ 2·x^{β₀−σ}·[u·X₁·ln x + 1/x + E(β₀)] + 4·u·x^{1−σ}·L₂/c₀ + E(ρ)`, with `u = 1 − β₀`,
`σ = Re ρ`.  This module lands the **β₀-side** of that master — the part that IS pure composition
of the landed suppliers — and it makes precise (in `docs/blueprints/flags.md`, node T-BAL / THE
CLOSE) why the full R7/R8 do NOT compose: the **ρ-side** `‖D_ρ‖ ≤ 4·u·x^{1−σ}·L₂/c₀ + E(ρ)`
(the `L(1,χ)`-carrying complex-detector extraction, the sharp u-gain form) is a genuine MISSING
supplier — the only landed complex-ρ detector bounds (`norm_shifted_detector_{mollified,
unmollified}_le`) are the trivial Pólya–Vinogradov `N^{1−σ}` form, with NO `(1−β₀)` factor, so
they diverge on the contradiction ray.

`dh_balance_beta0_real` : at a real zero `β₀`, the `selWeight` β₀-detector's floor `1 − 1/Y` meets
its `L(1,χ)`-main extraction upper bound (`dh_extraction_upper_W`), and the `L(1,χ)` **cancels**:
the main term `L₁·selMainTerm·Y^{1−β₀}/((1−β₀)(2−β₀)) = L₁·Y^{1−β₀}/(H·(1−β₀)(2−β₀)) ≤ Y^{1−β₀}`
via `selberg_opt_eq` (`selMainTerm = 1/H`) + `H_lower` (`L₁/((1−β₀)(2−β₀)) ≤ H`).  Net:
`1 − 1/Y ≤ Y^{1−β₀} + E(β₀)`.

This L₁-cancellation is exactly why the β₀-side carries NO information about `L(1,χ)` — the whole
Deuring–Heilbronn repulsion lives on the (missing) ρ-side, whose detector main term `∝ L₁·x^{1−σ}`
is NOT divided by `H`.  Guard-gated like `H_lower`/`L1_lower_siegel` (the `hN`/`hscale`/`hguard`/
`hcov` guards are discharged at the ledger scale by the ρ-side inversion — the blocked step).
-/

open Finset

noncomputable section

namespace Salt.SW

/-- **The `selWeight` β₀-detector floor.** The mollified detector's `n = 1` term is `1 − 1/Y`
(`dhCoeffW(1) = θ₁² = 1`, `1^{−β₀} = 1`, `(1 − 1/Y)₊ = 1 − 1/Y`); every other term is `≥ 0`
(`dhCoeffW_nonneg`, needs `χ² = 1`).  The `selWeight` analog of `dhDetector_floor`. -/
theorem dhW_detector_floor_beta0 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    {β₀ : ℝ} {z Y : ℕ} (hz : 1 ≤ z) (hY : 1 ≤ Y) :
    1 - 1 / (Y : ℝ)
      ≤ ∑ n ∈ Finset.Icc 1 Y,
          dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / (Y : ℝ)) := by
  have hYR : (0 : ℝ) < (Y : ℝ) := by exact_mod_cast hY
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 Y := Finset.mem_Icc.mpr ⟨le_refl 1, hY⟩
  have hterm :
      dhCoeffW χ (selWeight χ z) 1 * ((1 : ℕ) : ℝ) ^ (-β₀) * dhKernR (((1 : ℕ) : ℝ) / (Y : ℝ))
        = 1 - 1 / (Y : ℝ) := by
    rw [dhCoeffW_one, selWeight_apply_one χ hsq hz, one_pow, Nat.cast_one, Real.one_rpow, one_mul,
      one_mul, dhKernR_eq (by rw [div_le_one hYR]; exact_mod_cast hY)]
  have hnn : ∀ n ∈ Finset.Icc 1 Y,
      0 ≤ dhCoeffW χ (selWeight χ z) n * (n : ℝ) ^ (-β₀) * dhKernR ((n : ℝ) / (Y : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact mul_nonneg (mul_nonneg (dhCoeffW_nonneg χ hsq _ (by omega))
      (Real.rpow_nonneg (by positivity) _)) (dhKernR_nonneg _)
  calc 1 - 1 / (Y : ℝ)
      = dhCoeffW χ (selWeight χ z) 1 * ((1 : ℕ) : ℝ) ^ (-β₀) * dhKernR (((1 : ℕ) : ℝ) / (Y : ℝ)) :=
        hterm.symm
    _ ≤ _ := Finset.single_le_sum hnn h1mem

/-- **The β₀-balance (the composable half of the T-BAL master).** For a real primitive `χ` at a
real zero `β₀`, under the `H_lower` deep-regime guards (`hN`/`hscale`/`hguard` at the Siegel scale
`N`, and the coverage guard `hcov` at `z`) and the `R6` detector length `2·z⁴ ≤ Y`:
`1 − 1/Y ≤ Y^{1−β₀} + C₂·z·(1 + log(z²))⁹·Y^{1/2−β₀}`, `C₂ = 136 + 48M + 48M·Z₀ + 144M/(1−β₀)`,
`M = √q(1 + log q)`.

The `L(1,χ)` of the extraction main term cancels against `H(z)` (`selberg_opt_eq` + `H_lower`), so
this β₀-side inequality is `L(1,χ)`-free — the analytic content (the repulsion) lives only on the
ρ-side.  This is the FULLY composed β₀-half of the master; the ρ-side that would complete R7/R8 is
the missing supplier flagged at node T-BAL / THE CLOSE. -/
theorem dh_balance_beta0_real {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hsq : χ ^ 2 = 1) (hq : 2 ≤ q) {β₀ : ℝ}
    (hzero : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0) (hlo : 1 / 2 ≤ β₀) (hhi : β₀ < 1)
    {Z₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → ‖zetaHol s‖ ≤ Z₀)
    {N : ℕ} (hN : 4 ≤ N) (hscale : (N : ℝ) ^ (1 - β₀) ≤ Real.exp 1)
    (hguard : 2 * (34 + 12 * (Real.sqrt q * (1 + Real.log q))
        + 12 * (Real.sqrt q * (1 + Real.log q)) * Z₀
        + 36 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀)) * (N : ℝ) ^ (1 / 2 - β₀) ≤ 1 / 64)
    {z Y : ℕ} (hz : 2 ≤ z) (hY : 2 * z ^ 4 ≤ Y)
    (hcov : crushErr q Z₀ β₀ z ≤ 27 / 100 * ((1 - β₀) * (z : ℝ) ^ (1 - β₀))) :
    1 - 1 / (Y : ℝ)
      ≤ (Y : ℝ) ^ (1 - β₀)
        + (136 + 48 * (Real.sqrt q * (1 + Real.log q))
            + 48 * (Real.sqrt q * (1 + Real.log q)) * Z₀
            + 144 * (Real.sqrt q * (1 + Real.log q)) / (1 - β₀))
          * (z : ℝ) * (1 + Real.log ((z : ℝ) ^ 2)) ^ 9 * (Y : ℝ) ^ (1 / 2 - β₀) := by
  have hu : 0 < 1 - β₀ := by linarith
  have hu2 : 0 < 2 - β₀ := by linarith
  have hz1 : 1 ≤ z := by omega
  have hY1 : 1 ≤ Y := by have := Nat.one_le_pow 4 z (by omega); omega
  have hne : selHSum χ z ≠ 0 := (selHSum_pos χ hsq hz1).ne'
  have hune : (1 - β₀) ≠ 0 := hu.ne'
  have hu2ne : (2 - β₀) ≠ 0 := hu2.ne'
  have hfloor := dhW_detector_floor_beta0 χ hsq (β₀ := β₀) hz1 hY1
  have hR6 := dh_extraction_upper_W χ hχ hsq hq hzero hlo hhi hZ hz1 hY
  have hHl := H_lower χ hχ hsq hq hzero hlo hhi hZ hN hscale hguard hz hcov
  have hopt := selberg_opt_eq χ hsq hz1
  have hHpos := selHSum_pos χ hsq hz1
  set L₁ := (DirichletCharacter.LFunction χ 1).re with hL1
  have hYrp : (0 : ℝ) ≤ (Y : ℝ) ^ (1 - β₀) := Real.rpow_nonneg (by positivity) _
  -- main-term cancellation: L₁·selMainTerm·Y^{1−β₀}/((1−β₀)(2−β₀)) ≤ Y^{1−β₀}
  have hcancel : L₁ * selMainTerm χ z * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
      ≤ (Y : ℝ) ^ (1 - β₀) := by
    rw [hopt]
    have hrw : L₁ * (1 / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) / ((1 - β₀) * (2 - β₀))
        = (L₁ / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀) := by
      field_simp
    rw [hrw]
    have hle1 : L₁ / ((1 - β₀) * (2 - β₀)) / selHSum χ z ≤ 1 := (div_le_one hHpos).mpr hHl
    calc (L₁ / ((1 - β₀) * (2 - β₀)) / selHSum χ z) * (Y : ℝ) ^ (1 - β₀)
        ≤ 1 * (Y : ℝ) ^ (1 - β₀) := mul_le_mul_of_nonneg_right hle1 hYrp
      _ = (Y : ℝ) ^ (1 - β₀) := one_mul _
  -- floor ≤ Σ ≤ main + E ≤ Y^{1−β₀} + E
  linarith [hfloor, (abs_le.mp hR6).2, hcancel]

end Salt.SW

end
