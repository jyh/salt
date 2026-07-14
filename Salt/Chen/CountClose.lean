/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.AbelPass2

/-!
# AB3 — the count-line close: the ℕ-window ↔ `primesInWindow` bridge and the (187) tail

Design: `docs/blueprints/flags.md`, the AB1/AB2 entries.  This is the composition node of the
Chen count line.  It reconciles the ℕ-indexed sieve windows (`S1set`/`S2set`, the fibered form
of `weightedPairSum`) with the real-bounded prime windows (`BrunLower.primesInWindow`) that the
two Abel passes (`applicationA`/`applicationB`) consume, and evaluates the (187) tail — the mass
of the inner `p₂`-integral beyond the `√(x/p₁)` cutoff of `Ifun`.

## Section map

* **Section 1 — the window bridges (piece 1).**  `S2set_subset_primesInWindow` (the inner
  `p₂`-window `S2set ⊆ primesInWindow y (√x+1)`, direct — nonneg summands make the
  subset-monotone step one-directional) and `S1set_subset_insert` (the outer `p₁`-window
  `S1set ⊆ insert z (insert y (primesInWindow z y))`, the two endpoint corrections).

* **Section 2 — the (187) tail (piece 2).**  `tail187_integral_le` — the honest explicit bound on
  `∫_{√(x/p₁)}^{√x+1} h_{p₁}(t)/(t log t) dt` via a direct integrand estimate (integrand
  `≤ 36/(t·log²x)` on the tail, then `∫ dt/t = log(b/a)`).

## ⚠ A DESIGN GAP surfaced by this node (see `flags.md`, the AB3 entry)

The landed `pairSet`/`S2set` cut the inner window at `p₂² ≤ x` (i.e. `p₂ ≤ √x`), whereas
BJS Lemma 52 — and the landed `cbar` — correspond to the SHARP admissible cutoff
`p₂ ≤ √(x/p₁)` (forced by `p₁p₂² ≤ p₁p₂p₃ ≤ x`).  The extra pairs `p₂ ∈ (√(x/p₁), √x]` have
EMPTY triple-fibre yet carry positive weight `1/(p₁p₂ log(x/p₁p₂))` in `weightedPairSum`.
Their mass is the (187) tail, and — crucially — it is `Θ(1/log x)`, NOT `o(1/log x)`:

  `∫_{√(x/p₁)}^{√x} h_{p₁}/(t log t) = (1/log x)·(1/(1−β))·log(1/(1−2β))`, `β = log p₁/log x`,

a positive `Θ(1)` numerator over `log x`.  Summed against the outer `p₁`-loop this gives

  `weightedPairSum·log x → c̄ + ∫_{1/8}^{1/3} (1/β)(1/(1−β))log(1/(1−2β)) dβ ≈ c̄ + 0.744 ≈ 1.107`,

so the landed chain yields `tripleSum ≤ (1.107/2 + o(1))·x/log x ≈ 0.554·x/log x`, NOT the
`c̄/2 ≈ 0.1815` the AB2 slack ledger and the SW4 re-gate assume.  Hence
`tripleSum_le_cbar_final` with the `c̄/2` leading constant is **not provable from the landed
`pairSet`**.  The fix is a design change (Fable-tier): tighten `pairSet`/`S2set` to
`p₁·p₂² ≤ x` (equivalently `q.1 * q.2 * q.2 ≤ x`) — the projection of `tripleSet` still lands in
it, and the tail vanishes — then re-derive `card_tripleSet_le_pairSum`, `per_pair_weighted_le`,
`tripleSum_le_weighted_pairSum`.  This file therefore lands the correct bridge + honest tail
(the pieces that survive the fix unchanged or near-unchanged) and flags the assembly.

No `sorry`, no `native_decide`, no new axioms.
-/

open MeasureTheory intervalIntegral Set
open scoped BigOperators

namespace Salt.Chen

/-! ## Section 1 — the ℕ-window ↔ `primesInWindow` bridges (piece 1) -/

/-- **Inner bridge.**  The closed ℕ `p₂`-window `S2set x yN` (`yN < p`, `p² ≤ x`) is contained
in the half-open real window `primesInWindow yR (√x + 1)` whenever `yR ≤ yN + 1` (e.g.
`yN = ⌊yR⌋`).  Direction: `S2set ⊆ primesInWindow`, so a sum over `S2set` of nonnegative
summands is `≤` the sum over `primesInWindow` — the one-directional monotone step the inner
Abel pass (`applicationA`, over `primesInWindow`) needs. -/
theorem S2set_subset_primesInWindow {x yN : ℕ} {yR : ℝ}
    (hyR : yR ≤ (yN : ℝ) + 1) :
    S2set x yN ⊆ Salt.BrunLower.primesInWindow yR (Real.sqrt x + 1) := by
  intro p hp
  rw [S2set, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨_, hyp, hpx, hpp⟩ := hp
  rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, hpp, ?_⟩
  · -- `p < ⌈√x + 1⌉₊  ↔  (p:ℝ) < √x + 1`, from `p² ≤ x ⟹ p ≤ √x`
    rw [Nat.lt_ceil]
    have hppx : (p : ℝ) * (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast hpx
    have hple : (p : ℝ) ≤ Real.sqrt x := by
      rw [← Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ (p : ℝ))]
      exact Real.sqrt_le_sqrt hppx
    linarith
  · -- `yR ≤ (p:ℝ)`, from `yN < p` (so `yN + 1 ≤ p` in ℕ) and `yR ≤ yN + 1`
    have hyp1 : yN + 1 ≤ p := hyp
    have : (yN : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hyp1
    linarith

/-- **Outer bridge.**  The closed ℕ `p₁`-window `S1set x zN yN` (`zN ≤ p ≤ yN`) is contained in
`primesInWindow zR yR` together with the two endpoint corrections `{zN, yN}`, whenever
`zR ≤ zN + 1` and `yN ≤ yR` (e.g. `zN = ⌊zR⌋`, `yN = ⌊yR⌋`).  The interior primes fall inside
the real window `[zR, yR)`; only `p = zN` (if `zN < zR`) and `p = yN` (if `yN = yR`) can escape
it, and they are absorbed as the two boundary-prime corrections. -/
theorem S1set_subset_insert {x zN yN : ℕ} {zR yR : ℝ}
    (hzR : zR ≤ (zN : ℝ) + 1) (hyR : (yN : ℝ) ≤ yR) :
    S1set x zN yN ⊆ insert zN (insert yN (Salt.BrunLower.primesInWindow zR yR)) := by
  intro p hp
  rw [S1set, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨_, hzp, hpy, hpp⟩ := hp
  rw [Finset.mem_insert, Finset.mem_insert]
  by_cases h1 : p = zN
  · exact Or.inl h1
  · refine Or.inr ?_
    by_cases h2 : p = yN
    · exact Or.inl h2
    · refine Or.inr ?_
      rw [Salt.BrunLower.primesInWindow, Finset.mem_filter, Finset.mem_range]
      have hzlt : zN < p := lt_of_le_of_ne hzp (Ne.symm h1)
      have hylt : p < yN := lt_of_le_of_ne hpy h2
      refine ⟨?_, hpp, ?_⟩
      · -- `(p:ℝ) < yR`, from `p < yN` and `yN ≤ yR`
        rw [Nat.lt_ceil]
        have hp1 : p + 1 ≤ yN := hylt
        have hpR : (p : ℝ) + 1 ≤ (yN : ℝ) := by exact_mod_cast hp1
        linarith
      · -- `zR ≤ (p:ℝ)`, from `zN < p` and `zR ≤ zN + 1`
        have hz1 : zN + 1 ≤ p := hzlt
        have hzRp : (zN : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hz1
        linarith

/-! ## Section 2 — the (187) tail (piece 2, honest `Θ(1/log x)` form)

The inner Abel pass (`applicationA`) integrates `h_{p₁}/(t log t)` up to `√x+1`, whereas `Ifun`
stops at `√(x/p₁)`.  The gap `∫_{√(x/p₁)}^{√x+1}` is the BJS (187) tail.  We bound it by a direct
integrand estimate: on the tail `log t ≥ log x/3` and `log(x/(p₁t)) ≥ log x/12`, so the integrand
is `≤ 36·t⁻¹/log²x`, and `∫ t⁻¹ dt = log(b/a) ≤ log 2 + log x/6`.  The resulting bound is
`Θ(1/log x)` — the honest size (see the header): this tail does NOT vanish against `c̄/log x`. -/

/-- **The (187) tail bound.**  For `9 ≤ log x`, `1 < p₁`, `log p₁ ≤ log x/3`,

  `∫_{√(x/p₁)}^{√x+1} h_{p₁}(t)/(t log t) dt ≤ 6/log x + 36·log 2/log²x`. -/
theorem tail187_integral_le {x : ℕ} {p₁ : ℝ}
    (hx : (9 : ℝ) ≤ Real.log x) (hp1 : 1 < p₁) (hp1hi : Real.log p₁ ≤ Real.log x / 3) :
    ∫ t in Real.sqrt ((x : ℝ) / p₁)..(Real.sqrt x + 1),
        hbjs (x : ℝ) p₁ t / (t * Real.log t)
      ≤ 6 / Real.log x + 36 * Real.log 2 / (Real.log x) ^ 2 := by
  have hp1pos : 0 < p₁ := by linarith
  -- `x > 0` from `log x ≥ 9` (else `log 0 = 0`)
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h; simp only [Nat.cast_zero, Real.log_zero] at hx; linarith
    · exact_mod_cast h
  set LN := Real.log (x : ℝ) with hLN
  have hLNpos : 0 < LN := by linarith
  have hxp1pos : (0 : ℝ) < (x : ℝ) / p₁ := div_pos hxpos hp1pos
  set a := Real.sqrt ((x : ℝ) / p₁) with ha_def
  set b := Real.sqrt (x : ℝ) + 1 with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr hxp1pos
  have hsqrtx : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hb : 0 < b := by rw [hb_def]; linarith
  -- `a ≤ √x ≤ b`
  have ha_le_sqrtx : a ≤ Real.sqrt (x : ℝ) := by
    rw [ha_def]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ hp1pos]; nlinarith [hxpos, hp1]
  have hab : a ≤ b := by rw [hb_def]; linarith
  -- `log a = (LN - log p₁)/2`
  have hloga : Real.log a = (LN - Real.log p₁) / 2 := by
    rw [ha_def, Real.log_sqrt (le_of_lt hxp1pos), Real.log_div hxpos.ne' hp1pos.ne', ← hLN]
  -- `log b ≤ log 2 + LN/2`  (from `√x + 1 ≤ 2√x`, valid since `√x ≥ 1`)
  have hsqrtx1 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by
      have : Real.exp 9 ≤ (x : ℝ) := by
        rw [← Real.exp_log hxpos]; exact Real.exp_le_exp.mpr hx
      nlinarith [Real.add_one_le_exp (9 : ℝ)])
  have hlogb : Real.log b ≤ Real.log 2 + LN / 2 := by
    have hble : b ≤ 2 * Real.sqrt (x : ℝ) := by rw [hb_def]; linarith
    calc Real.log b ≤ Real.log (2 * Real.sqrt (x : ℝ)) := Real.log_le_log hb hble
      _ = Real.log 2 + LN / 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt hxpos.le, ← hLN]
  -- the pointwise interval facts
  have hmem : ∀ t ∈ Set.Icc a b, 0 < t ∧ LN / 3 ≤ Real.log t
      ∧ LN / 12 ≤ Real.log ((x : ℝ) / (p₁ * t)) := by
    intro t ht
    rw [Set.mem_Icc] at ht
    obtain ⟨hta, htb⟩ := ht
    have htpos : 0 < t := lt_of_lt_of_le ha hta
    refine ⟨htpos, ?_, ?_⟩
    · have hloga_le : Real.log a ≤ Real.log t := Real.log_le_log ha hta
      rw [hloga] at hloga_le; linarith [hp1hi]
    · have hlogeq : Real.log ((x : ℝ) / (p₁ * t)) = LN - Real.log p₁ - Real.log t := by
        rw [Real.log_div hxpos.ne' (mul_pos hp1pos htpos).ne',
          Real.log_mul hp1pos.ne' htpos.ne', ← hLN]; ring
      rw [hlogeq]
      have hlogtb : Real.log t ≤ Real.log b := Real.log_le_log htpos htb
      have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      linarith [hp1hi, hlogtb, hlogb, hlog2, hx]
  -- pointwise bound: integrand `≤ 36/LN² · t⁻¹`
  have hpt : ∀ t ∈ Set.Icc a b,
      hbjs (x : ℝ) p₁ t / (t * Real.log t) ≤ 36 / LN ^ 2 * t⁻¹ := by
    intro t ht
    obtain ⟨htpos, hLt, hL1⟩ := hmem t ht
    have hLtpos : 0 < Real.log t := by linarith
    have hL1pos : 0 < Real.log ((x : ℝ) / (p₁ * t)) := by linarith
    have hbnd1 : (Real.log ((x : ℝ) / (p₁ * t)))⁻¹ ≤ 12 / LN := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < LN / 12 by positivity) hL1
      rwa [one_div, one_div_div] at h
    have hbnd2 : (Real.log t)⁻¹ ≤ 3 / LN := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < LN / 3 by positivity) hLt
      rwa [one_div, one_div_div] at h
    have hrw : hbjs (x : ℝ) p₁ t / (t * Real.log t)
        = (Real.log ((x : ℝ) / (p₁ * t)))⁻¹ * t⁻¹ * (Real.log t)⁻¹ := by
      rw [hbjs, div_eq_mul_inv, mul_inv]; ring
    have htinv : (0 : ℝ) ≤ t⁻¹ := le_of_lt (inv_pos.mpr htpos)
    rw [hrw]
    calc (Real.log ((x : ℝ) / (p₁ * t)))⁻¹ * t⁻¹ * (Real.log t)⁻¹
        ≤ (12 / LN) * t⁻¹ * (3 / LN) := by
          apply mul_le_mul _ hbnd2 (le_of_lt (inv_pos.mpr hLtpos)) (by positivity)
          exact mul_le_mul hbnd1 le_rfl htinv (by positivity)
      _ = 36 / LN ^ 2 * t⁻¹ := by ring
  -- integrability of both sides
  have hInt_f : IntervalIntegrable (fun t => hbjs (x : ℝ) p₁ t / (t * Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    have hlog_cont : ContinuousOn Real.log (Set.Icc a b) :=
      Real.continuousOn_log.mono (fun t ht => Set.mem_compl_singleton_iff.mpr (hmem t ht).1.ne')
    have hbjs_cont : ContinuousOn (fun t => hbjs (x : ℝ) p₁ t) (Set.Icc a b) := by
      simp only [hbjs]
      apply ContinuousOn.inv₀
      · apply ContinuousOn.log
        · exact continuousOn_const.div (by fun_prop)
            (fun t ht => (mul_pos hp1pos (hmem t ht).1).ne')
        · exact fun t ht => (div_pos hxpos (mul_pos hp1pos (hmem t ht).1)).ne'
      · exact fun t ht =>
          (lt_of_lt_of_le (show (0 : ℝ) < LN / 12 by positivity) (hmem t ht).2.2).ne'
    have hden_ne : ∀ t ∈ Set.Icc a b, t * Real.log t ≠ 0 :=
      fun t ht => (mul_pos (hmem t ht).1 (by linarith [(hmem t ht).2.1])).ne'
    exact hbjs_cont.div (continuousOn_id.mul hlog_cont) hden_ne
  have hInt_g : IntervalIntegrable (fun t => 36 / LN ^ 2 * t⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact continuousOn_const.mul
      (continuousOn_inv₀.mono (fun t ht => Set.mem_compl_singleton_iff.mpr (hmem t ht).1.ne'))
  -- monotone integral, then evaluate `∫ t⁻¹`
  calc ∫ t in a..b, hbjs (x : ℝ) p₁ t / (t * Real.log t)
      ≤ ∫ t in a..b, 36 / LN ^ 2 * t⁻¹ :=
        intervalIntegral.integral_mono_on hab hInt_f hInt_g hpt
    _ = 36 / LN ^ 2 * Real.log (b / a) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
    _ ≤ 6 / LN + 36 * Real.log 2 / LN ^ 2 := by
        have hlogba : Real.log (b / a) ≤ Real.log 2 + LN / 6 := by
          rw [Real.log_div hb.ne' ha.ne', hloga]; linarith [hlogb, hp1hi]
        have hcoef : (0 : ℝ) ≤ 36 / LN ^ 2 := by positivity
        calc 36 / LN ^ 2 * Real.log (b / a)
            ≤ 36 / LN ^ 2 * (Real.log 2 + LN / 6) :=
              mul_le_mul_of_nonneg_left hlogba hcoef
          _ = 6 / LN + 36 * Real.log 2 / LN ^ 2 := by field_simp; ring

end Salt.Chen
