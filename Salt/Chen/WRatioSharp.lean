/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.SwitchSieve
import Salt.Chen.MertensPNT
import Salt.BrunLower.MertensDischarge
import Salt.BrunLower.MertensWindow

/-!
# M2 — the two-sided `W`-ratio over the nested sieve window `[z, y)`

Design: `docs/blueprints/flags.md`, the `2026-07-13 M-RECON`, `M134 … catch #51` and the
SW-FIBER design-block entries.  The M-recon's node **M2**: bound the ratio of the two Hardy–
Littlewood density products carried by the switched sieve (modulus `Ps`, the `[w₀, y)` window)
and the `A₁/A₂` sieve (modulus `P`, the `[w₀, z)` window), under the nesting `P ∣ Ps`.

Since both `switchSieve` and `twinA1Sieve` carry the SAME dimension-1 density `ν = nuChen`
(`ν(p) = 1/(p−1)`), the density product `Salt.BrunLower.W` depends only on the modulus, and the
nesting factorises it:

  `W(switchSieve …) = W(twinA1Sieve …) · ∏_{p ∈ Ps.primeFactors \ P.primeFactors}(1 − ν(p))`.

The caller (H-glue) supplies `Ps.primeFactors \ P.primeFactors = primesInWindow z y`, reducing
the ratio to the pure window product `∏_{z ≤ p < y}(1 − ν(p))`, which this file brackets
two-sidedly.  The exponentiated main term is `log z / log y` (`= 3/8` at the operating point
`z = x^{1/8}`, `y = x^{1/2−ε′}`, but everything is stated PARAMETRIC in the reals `z, y`).

## The route (per the M-brief)

Write `log ∏ = Σ_{z ≤ p < y} log(1 − ν(p))` and bracket `−log(1 − ν(p))` pointwise:

* **upper** `−log(1 − ν(p)) ≤ 1/(p−2) ≤ 1/p + 6/p²` (from `log x⁻¹ ≤ x⁻¹ − 1`; the *sharp*
  bound — the crude `2/p` of `BrunLower.neg_log_one_sub_nu_le` would double the main term and
  ruin the lower `W`-bound), and
* **lower** `−log(1 − ν(p)) ≥ ν(p) ≥ 1/p` (from `log(1 − ν) ≤ −ν`).

Sum with the two-sided window Mertens — `Salt.BrunLower.sum_inv_prime_window_le` (`C₃ = 19`) and
`Salt.Chen.sum_inv_prime_window_ge` (`C₃′ = 19`) — giving `Σ 1/p = log(log y/log z) ± 19/log z`,
plus the elementary square-tail `Σ 1/p² ≤ 1/(z−1) ≤ 1/log z`
(`Salt.BrunLower.sum_one_div_sq_le`).  Exponentiate:

* `window_prod_lower` : `(log z/log y)·(1 − 25/log z) ≤ ∏`, all `z ≥ 3` (no extra threshold).
* `window_prod_upper` : `∏ ≤ (log z/log y)·(1 + 38/log z)`, on `log z ≥ 38`
  (an ∃-threshold on the `1 + C/log z` correction, per the brief; harmless — the operating
  point has `log z = (log x)/8 ≫ 38`).

Composed with the factorisation `W_switch_factor` and the window hypothesis `hwin`, this yields
the `W`-ratio pair `W_ratio_upper` / `W_ratio_lower` (product form, SW4-consumable) and their
division-form corollaries `W_ratio_upper_div` / `W_ratio_lower_div`.

No `sorry`, no `native_decide`, no new axioms; `maxHeartbeats` default.
-/

namespace Salt.Chen

/-! ## Pointwise two-sided bracket for `−log(1 − nuChen p)` -/

/-- **Sharp pointwise upper bound.**  For an odd prime `p ≥ 3`,
`−log(1 − ν(p)) ≤ 1/p + 6/p²` where `ν = nuChen` (`ν(p) = 1/(p−1)`).  Via `log x⁻¹ ≤ x⁻¹ − 1`
at `x = 1 − ν(p)`, giving `−log(1 − ν) ≤ 1/(p−2)`, then `1/(p−2) ≤ 1/p + 6/p²` for `p ≥ 3`. -/
lemma neg_log_one_sub_nuChen_le {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    -Real.log (1 - nuChen p) ≤ 1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2) := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := ne_of_gt hp1
  have hp2' : (p : ℝ) - 2 ≠ 0 := ne_of_gt hp2
  have hp0' : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hnu : nuChen p = 1 / ((p : ℝ) - 1) := nuChen_prime hp
  have ha_pos : (0 : ℝ) < 1 - nuChen p := by
    rw [hnu]
    have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  -- `−log(1 − ν) ≤ (1 − ν)⁻¹ − 1 = 1/(p−2)`
  have hlog : Real.log (1 - nuChen p)⁻¹ ≤ (1 - nuChen p)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at hlog
  have hval : (1 - nuChen p)⁻¹ - 1 = 1 / ((p : ℝ) - 2) := by
    have h1sub : 1 - nuChen p = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
      rw [hnu, eq_div_iff hp1']; field_simp; ring
    rw [h1sub, inv_div, div_sub_one hp2', show ((p : ℝ) - 1) - ((p : ℝ) - 2) = 1 by ring]
  rw [hval] at hlog
  -- `1/(p−2) ≤ (p+6)/p² = 1/p + 6/p²`
  have h1 : 1 / ((p : ℝ) - 2) ≤ ((p : ℝ) + 6) / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hp2 (by positivity)]
    nlinarith [hpR]
  have h2 : ((p : ℝ) + 6) / (p : ℝ) ^ 2 = 1 / (p : ℝ) + 6 * (1 / (p : ℝ) ^ 2) := by
    field_simp
  linarith [hlog, h1, h2]

/-- **Pointwise lower bound.**  For an odd prime `p ≥ 3`, `1/p ≤ −log(1 − ν(p))` where
`ν = nuChen`.  Via `log(1 − ν) ≤ −ν` and `ν(p) = 1/(p−1) ≥ 1/p`. -/
lemma neg_log_one_sub_nuChen_ge {p : ℕ} (hp : Nat.Prime p) (hp3 : 3 ≤ p) :
    1 / (p : ℝ) ≤ -Real.log (1 - nuChen p) := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hnu : nuChen p = 1 / ((p : ℝ) - 1) := nuChen_prime hp
  have ha_pos : (0 : ℝ) < 1 - nuChen p := by
    rw [hnu]
    have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  have hlog : Real.log (1 - nuChen p) ≤ (1 - nuChen p) - 1 := Real.log_le_sub_one_of_pos ha_pos
  have hge : 1 / (p : ℝ) ≤ nuChen p := by
    rw [hnu]; exact one_div_le_one_div_of_le hp1 (by linarith)
  linarith [hlog, hge]

/-! ## Window membership facts and factor positivity -/

/-- Every member of `primesInWindow z y` (for `z ≥ 3`) is a prime `≥ 3`. -/
lemma window_mem_facts {z y : ℝ} (hz : 3 ≤ z) {p : ℕ}
    (hp : p ∈ Salt.BrunLower.primesInWindow z y) : Nat.Prime p ∧ 3 ≤ p := by
  rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨_, hpp, hzp⟩ := hp
  refine ⟨hpp, ?_⟩
  have : (3 : ℝ) ≤ (p : ℝ) := le_trans hz hzp
  exact_mod_cast this

/-- Each window factor `1 − ν(p)` is positive (`ν(p) = 1/(p−1) ≤ 1/2` on `p ≥ 3`). -/
lemma window_fac_pos {z y : ℝ} (hz : 3 ≤ z) {p : ℕ}
    (hp : p ∈ Salt.BrunLower.primesInWindow z y) : 0 < 1 - nuChen p := by
  obtain ⟨hpp, hp3⟩ := window_mem_facts hz hp
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [nuChen_prime hpp]
  have : 1 / ((p : ℝ) - 1) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-- The window product is positive. -/
lemma window_prod_pos {z y : ℝ} (hz : 3 ≤ z) :
    0 < ∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p) :=
  Finset.prod_pos (fun _ hp => window_fac_pos hz hp)

/-! ## The square-tail bound `Σ_{z ≤ p < y} 1/p² ≤ 1/log z` -/

/-- **Square tail.**  `Σ_{p ∈ primesInWindow z y} 1/p² ≤ 1/log z` for `z ≥ 3`.  Elementary:
subset into `Icc ⌈z⌉₊ ⌈y⌉₊`, apply the telescoping `Salt.BrunLower.sum_one_div_sq_le`
(`≤ 1/(⌈z⌉₊ − 1)`), then `⌈z⌉₊ − 1 ≥ z − 1 ≥ log z`. -/
lemma sum_inv_sq_window_le {z y : ℝ} (hz : 3 ≤ z) :
    ∑ p ∈ Salt.BrunLower.primesInWindow z y, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / Real.log z := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hz1 : (0 : ℝ) < z - 1 := by linarith
  have hMz : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
  have hM2 : 2 ≤ ⌈z⌉₊ := by
    have : (2 : ℝ) ≤ (⌈z⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have hsub : Salt.BrunLower.primesInWindow z y ⊆ Finset.Icc ⌈z⌉₊ ⌈y⌉₊ := by
    intro p hp
    rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hplt, _, hzp⟩ := hp
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr hzp, by omega⟩
  have hnn : ∀ p ∈ Finset.Icc ⌈z⌉₊ ⌈y⌉₊, p ∉ Salt.BrunLower.primesInWindow z y →
      0 ≤ (1 : ℝ) / (p : ℝ) ^ 2 := fun _ _ _ => by positivity
  calc ∑ p ∈ Salt.BrunLower.primesInWindow z y, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Finset.Icc ⌈z⌉₊ ⌈y⌉₊, (1 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    _ ≤ 1 / ((⌈z⌉₊ : ℝ) - 1) := Salt.BrunLower.sum_one_div_sq_le hM2
    _ ≤ 1 / (z - 1) := one_div_le_one_div_of_le hz1 (by linarith)
    _ ≤ 1 / Real.log z :=
        one_div_le_one_div_of_le hlogz
          (by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < z by linarith)])

/-! ## `log ∏` bracketed by the window `Σ 1/p` (and the square tail) -/

/-- `log ∏_{z ≤ p < y}(1 − ν) ≤ −Σ 1/p` (the sharp direction, from the pointwise lower bound). -/
lemma window_log_prod_le {z y : ℝ} (hz : 3 ≤ z) :
    Real.log (∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p))
      ≤ -∑ p ∈ Salt.BrunLower.primesInWindow z y, (1 : ℝ) / (p : ℝ) := by
  rw [Real.log_prod (fun p hp => (window_fac_pos hz hp).ne'), ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpp, hp3⟩ := window_mem_facts hz hp
  have h := neg_log_one_sub_nuChen_ge hpp hp3
  linarith

/-- `−(Σ 1/p + 6·Σ 1/p²) ≤ log ∏_{z ≤ p < y}(1 − ν)` (from the sharp pointwise upper bound). -/
lemma window_log_prod_ge {z y : ℝ} (hz : 3 ≤ z) :
    -((∑ p ∈ Salt.BrunLower.primesInWindow z y, (1 : ℝ) / (p : ℝ))
        + 6 * ∑ p ∈ Salt.BrunLower.primesInWindow z y, (1 : ℝ) / (p : ℝ) ^ 2)
      ≤ Real.log (∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p)) := by
  rw [Real.log_prod (fun p hp => (window_fac_pos hz hp).ne'), Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hpp, hp3⟩ := window_mem_facts hz hp
  have h := neg_log_one_sub_nuChen_le hpp hp3
  linarith

/-! ## The two-sided window product bounds -/

/-- **`window_prod_lower`.**  `(log z/log y)·(1 − 25/log z) ≤ ∏_{z ≤ p < y}(1 − ν(p))` for
`3 ≤ z ≤ y`.  Explicit constant `C′ = 25` (`= 19` window-Mertens `+ 6` square-tail); no extra
threshold beyond `z ≥ 3`. -/
theorem window_prod_lower {z y : ℝ} (hz : 3 ≤ z) (hzy : z ≤ y) :
    (Real.log z / Real.log y) * (1 - 25 / Real.log z)
      ≤ ∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p) := by
  have hz2 : (2 : ℝ) ≤ z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hApos : 0 < Real.log y / Real.log z := div_pos hlogy hlogz
  have hexp_eq : Real.exp (-Real.log (Real.log y / Real.log z)) = Real.log z / Real.log y := by
    rw [Real.exp_neg, Real.exp_log hApos, inv_div]
  set Prd := ∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p) with hPrd
  have hPrd_pos : 0 < Prd := window_prod_pos hz
  have hSle := Salt.BrunLower.sum_inv_prime_window_le hz2 hzy
  have hT := sum_inv_sq_window_le (y := y) hz
  have hge := window_log_prod_ge (y := y) hz
  rw [← hPrd] at hge
  have h25 : (25 : ℝ) / Real.log z = 19 / Real.log z + 6 * (1 / Real.log z) := by ring
  have hlogPrd : -Real.log (Real.log y / Real.log z) - 25 / Real.log z ≤ Real.log Prd := by
    linarith [hge, hSle, hT, h25]
  have hexp1 : Real.exp (-Real.log (Real.log y / Real.log z) - 25 / Real.log z) ≤ Prd := by
    have h := Real.exp_le_exp.mpr hlogPrd
    rwa [Real.exp_log hPrd_pos] at h
  have hexp2 : Real.exp (-Real.log (Real.log y / Real.log z) - 25 / Real.log z)
      = (Real.log z / Real.log y) * Real.exp (-(25 / Real.log z)) := by
    rw [sub_eq_add_neg, Real.exp_add, hexp_eq]
  have hexp3 : (Real.log z / Real.log y) * (1 - 25 / Real.log z)
      ≤ (Real.log z / Real.log y) * Real.exp (-(25 / Real.log z)) := by
    apply mul_le_mul_of_nonneg_left _ (div_nonneg hlogz.le hlogy.le)
    have := Real.add_one_le_exp (-(25 / Real.log z))
    linarith
  calc (Real.log z / Real.log y) * (1 - 25 / Real.log z)
      ≤ (Real.log z / Real.log y) * Real.exp (-(25 / Real.log z)) := hexp3
    _ = Real.exp (-Real.log (Real.log y / Real.log z) - 25 / Real.log z) := hexp2.symm
    _ ≤ Prd := hexp1

/-- **`window_prod_upper`.**  `∏_{z ≤ p < y}(1 − ν(p)) ≤ (log z/log y)·(1 + 38/log z)` for
`3 ≤ z ≤ y` and `log z ≥ 38`.  Explicit constant `C = 38`; the `log z ≥ 38` threshold makes
`19/log z ≤ 1/2` so `exp(19/log z) ≤ 1/(1 − 19/log z) ≤ 1 + 38/log z` (an ∃-threshold on the
`1 + C/log z` correction, per the M-brief — at the operating point `log z = (log x)/8 ≫ 38`). -/
theorem window_prod_upper {z y : ℝ} (hz : 3 ≤ z) (hzy : z ≤ y) (hz38 : 38 ≤ Real.log z) :
    ∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p)
      ≤ (Real.log z / Real.log y) * (1 + 38 / Real.log z) := by
  have hz2 : (2 : ℝ) ≤ z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hApos : 0 < Real.log y / Real.log z := div_pos hlogy hlogz
  have hexp_eq : Real.exp (-Real.log (Real.log y / Real.log z)) = Real.log z / Real.log y := by
    rw [Real.exp_neg, Real.exp_log hApos, inv_div]
  set Prd := ∏ p ∈ Salt.BrunLower.primesInWindow z y, (1 - nuChen p) with hPrd
  have hPrd_pos : 0 < Prd := window_prod_pos hz
  have hSge := Salt.Chen.sum_inv_prime_window_ge hz2 hzy
  have hle := window_log_prod_le (y := y) hz
  rw [← hPrd] at hle
  have hlogPrd : Real.log Prd ≤ -Real.log (Real.log y / Real.log z) + 19 / Real.log z := by
    linarith [hle, hSge]
  have hexp1 : Prd ≤ Real.exp (-Real.log (Real.log y / Real.log z) + 19 / Real.log z) := by
    have h := Real.exp_le_exp.mpr hlogPrd
    rwa [Real.exp_log hPrd_pos] at h
  have hexp2 : Real.exp (-Real.log (Real.log y / Real.log z) + 19 / Real.log z)
      = (Real.log z / Real.log y) * Real.exp (19 / Real.log z) := by
    rw [Real.exp_add, hexp_eq]
  have hb_le : 19 / Real.log z ≤ 1 / 2 := by
    rw [div_le_iff₀ hlogz]; linarith
  have hexp3 : Real.exp (19 / Real.log z) ≤ 1 + 38 / Real.log z := by
    have hb_nonneg : (0 : ℝ) ≤ 19 / Real.log z := by positivity
    have h1mb : (0 : ℝ) < 1 - 19 / Real.log z := by linarith
    have hen : 1 - 19 / Real.log z ≤ Real.exp (-(19 / Real.log z)) := by
      have := Real.add_one_le_exp (-(19 / Real.log z)); linarith
    have hexpb_pos : 0 < Real.exp (19 / Real.log z) := Real.exp_pos _
    have hle1 : (1 - 19 / Real.log z) * Real.exp (19 / Real.log z) ≤ 1 := by
      have h2 : 1 - 19 / Real.log z ≤ (Real.exp (19 / Real.log z))⁻¹ := by
        rwa [Real.exp_neg] at hen
      have h3 := mul_le_mul_of_nonneg_right h2 hexpb_pos.le
      rwa [inv_mul_cancel₀ hexpb_pos.ne'] at h3
    have hexpb : Real.exp (19 / Real.log z) ≤ 1 / (1 - 19 / Real.log z) := by
      rw [le_div_iff₀ h1mb, mul_comm]; exact hle1
    have h38 : (38 : ℝ) / Real.log z = 2 * (19 / Real.log z) := by ring
    have hfrac : 1 / (1 - 19 / Real.log z) ≤ 1 + 38 / Real.log z := by
      rw [h38, div_le_iff₀ h1mb]
      nlinarith [mul_nonneg hb_nonneg (show (0 : ℝ) ≤ 1 - 2 * (19 / Real.log z) by linarith)]
    linarith [hexpb, hfrac]
  calc Prd ≤ Real.exp (-Real.log (Real.log y / Real.log z) + 19 / Real.log z) := hexp1
    _ = (Real.log z / Real.log y) * Real.exp (19 / Real.log z) := hexp2
    _ ≤ (Real.log z / Real.log y) * (1 + 38 / Real.log z) :=
        mul_le_mul_of_nonneg_left hexp3 (div_nonneg hlogz.le hlogy.le)

/-! ## The factorisation of `W` across the `P ∣ Ps` nesting -/

/-- **`W_switch_factor`.**  Because `switchSieve` and `twinA1Sieve` share the density
`ν = nuChen`, the density product factorises across the modulus nesting `P ∣ Ps`:

  `W(switchSieve …) = W(twinA1Sieve …) · ∏_{p ∈ Ps.primeFactors \ P.primeFactors}(1 − ν(p))`.

`W` depends only on the modulus and density, so the switched-sieve `z, y` play no role. -/
theorem W_switch_factor (x z y P Ps : ℕ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPs : Squarefree Ps) (hPsodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hdvd : P ∣ Ps) :
    Salt.BrunLower.W (switchSieve x z y Ps hPs hPsodd)
      = Salt.BrunLower.W (twinA1Sieve x P hP hPodd)
        * ∏ p ∈ Ps.primeFactors \ P.primeFactors, (1 - nuChen p) := by
  have hsub : P.primeFactors ⊆ Ps.primeFactors := Nat.primeFactors_mono hdvd hPs.ne_zero
  have hWs : Salt.BrunLower.W (switchSieve x z y Ps hPs hPsodd)
      = ∏ p ∈ Ps.primeFactors, (1 - nuChen p) := by
    simp only [Salt.BrunLower.W, switchSieve_prodPrimes, switchSieve_nu]
  have hWt : Salt.BrunLower.W (twinA1Sieve x P hP hPodd)
      = ∏ p ∈ P.primeFactors, (1 - nuChen p) := by
    simp only [Salt.BrunLower.W, twinA1Sieve_prodPrimes, twinA1Sieve_nu]
  rw [hWs, hWt, ← Finset.prod_sdiff hsub]
  ring

/-! ## The composed two-sided `W`-ratio (product forms + division corollaries) -/

/-- **`W_ratio_upper`** (product form, SW4-consumable).  Under the nesting `P ∣ Ps` and the
window identification `hwin`, the switched density product is bounded by the `A₁`-product times
`(log z/log y)·(1 + 38/log z)` (`z, y` the real window endpoints; `log z ≥ 38`). -/
theorem W_ratio_upper (x z y P Ps : ℕ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPs : Squarefree Ps) (hPsodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hdvd : P ∣ Ps) {zr yr : ℝ} (hz : 3 ≤ zr) (hzy : zr ≤ yr) (hz38 : 38 ≤ Real.log zr)
    (hwin : Ps.primeFactors \ P.primeFactors = Salt.BrunLower.primesInWindow zr yr) :
    Salt.BrunLower.W (switchSieve x z y Ps hPs hPsodd)
      ≤ Salt.BrunLower.W (twinA1Sieve x P hP hPodd)
        * ((Real.log zr / Real.log yr) * (1 + 38 / Real.log zr)) := by
  rw [W_switch_factor x z y P Ps hP hPodd hPs hPsodd hdvd, hwin]
  exact mul_le_mul_of_nonneg_left (window_prod_upper hz hzy hz38)
    (Salt.BrunLower.W_pos _).le

/-- **`W_ratio_lower`** (product form, SW4-consumable).  The mirror lower `W`-bound with explicit
`C′ = 25`; no threshold beyond `zr ≥ 3`. -/
theorem W_ratio_lower (x z y P Ps : ℕ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPs : Squarefree Ps) (hPsodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hdvd : P ∣ Ps) {zr yr : ℝ} (hz : 3 ≤ zr) (hzy : zr ≤ yr)
    (hwin : Ps.primeFactors \ P.primeFactors = Salt.BrunLower.primesInWindow zr yr) :
    Salt.BrunLower.W (twinA1Sieve x P hP hPodd)
        * ((Real.log zr / Real.log yr) * (1 - 25 / Real.log zr))
      ≤ Salt.BrunLower.W (switchSieve x z y Ps hPs hPsodd) := by
  rw [W_switch_factor x z y P Ps hP hPodd hPs hPsodd hdvd, hwin]
  exact mul_le_mul_of_nonneg_left (window_prod_lower hz hzy) (Salt.BrunLower.W_pos _).le

/-- **`W_ratio_upper_div`** — ratio form: `W(switch)/W(twinA1) ≤ (log z/log y)·(1 + 38/log z)`. -/
theorem W_ratio_upper_div (x z y P Ps : ℕ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPs : Squarefree Ps) (hPsodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hdvd : P ∣ Ps) {zr yr : ℝ} (hz : 3 ≤ zr) (hzy : zr ≤ yr) (hz38 : 38 ≤ Real.log zr)
    (hwin : Ps.primeFactors \ P.primeFactors = Salt.BrunLower.primesInWindow zr yr) :
    Salt.BrunLower.W (switchSieve x z y Ps hPs hPsodd)
        / Salt.BrunLower.W (twinA1Sieve x P hP hPodd)
      ≤ (Real.log zr / Real.log yr) * (1 + 38 / Real.log zr) := by
  rw [div_le_iff₀ (Salt.BrunLower.W_pos _), mul_comm]
  exact W_ratio_upper x z y P Ps hP hPodd hPs hPsodd hdvd hz hzy hz38 hwin

/-- **`W_ratio_lower_div`** — ratio form: `(log z/log y)·(1 − 25/log z) ≤ W(switch)/W(twinA1)`. -/
theorem W_ratio_lower_div (x z y P Ps : ℕ)
    (hP : Squarefree P) (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p)
    (hPs : Squarefree Ps) (hPsodd : ∀ p ∈ Ps.primeFactors, 3 ≤ p)
    (hdvd : P ∣ Ps) {zr yr : ℝ} (hz : 3 ≤ zr) (hzy : zr ≤ yr)
    (hwin : Ps.primeFactors \ P.primeFactors = Salt.BrunLower.primesInWindow zr yr) :
    (Real.log zr / Real.log yr) * (1 - 25 / Real.log zr)
      ≤ Salt.BrunLower.W (switchSieve x z y Ps hPs hPsodd)
          / Salt.BrunLower.W (twinA1Sieve x P hP hPodd) := by
  rw [le_div_iff₀ (Salt.BrunLower.W_pos _), mul_comm]
  exact W_ratio_lower x z y P Ps hP hPodd hPs hPsodd hdvd hz hzy hwin

end Salt.Chen
