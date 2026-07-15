/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.CountAtOp2

/-!
# HCOUNT-3 — the `(★)` composition (`hcount_star_at_op`)

Design: `docs/blueprints/flags.md`, the `2026-07-15 HCOUNT-2` entry (the three remaining pieces:
the CORR sum assembly, the `E_SW` fold wiring, the `(★)` composition) and the `2026-07-15 HCOUNT`
entry (the `(★)` premise shape and the honest `C` note); `Salt/Chen/CountAtOp.lean`'s module tail
(the `(★)` premise) and `Salt/Chen/CountAtOp2.lean`'s remaining-list.

`CountAtOp.hcount_at_op` closes the GlueNormalized `hcount` SLOT **modulo** the premise `(★)`

  `log x · tripleSumW opQ opA x (opZ x)(opY x) ≤ (cbar + ecountOp C x)·massLo x Kmass / φ(opQ)`,

with `massLo x Kmass = x/2 − 1 − 2·Kmass·x/log x`.  This module discharges `(★)` in three folds:

1. **CORR assembly** (`corr_le_at_op`): the keystone's Abel-error/boundary sum
   `CORR ≤ C_CORR/(log x)²` past a threshold, combining `Ifun_op_le` + `hbjs_sqrt_le`
   + the floor `hbjs` bound + `S1set_mertens`.
2. **`E_SW` fold**: `φ·log x·E_SW = O(x/(log x)^{11})` — the polylog-beats-power collapse
   (`φ ≤ opQ ≤ log x`, `log Lval ≥ log x/7`, `A = 13`), plus the `2·|pairSet|/L₀` boundary term.
3. **`hcount_star_at_op`**: the count keystone at op (rebuilt with the UNIFORM `psiTot_pnt`
   constant `K` — the landed keystone's `K` is per-instance existential, so we thread
   `psiTot_pnt` directly), folded via `slack_collapse` + folds 1+2 into
   `(cbar + ecountOp C x)·massLo`.

## The honest constant `C` (catch #76 — design note vs. landed)

The design note fixed `C = cbar·(11·K + 12·log 2)/4`, ASSUMING every slack piece is `cbar`-scaled.
The landed composition finds the CORR sum contributes a NON-`cbar`-scaled constant `C_CORR ≈ 945`
(the `Ifun`/`hbjs` reciprocal sums have no `cbar` factor in the keystone's `Rem`), so the honest
leading constant is

  `C = (cbar·(21·K + 14·log 2) + C_CORR + 2·cbar·Kmass + 4) / 2`,   `C_CORR = 255·log 2 + 768`,

with `K` the shared `psiTot_pnt` constant and `Kmass` the `lambda_mass_lower` mass constant.  This
is larger than the note's value, but `ecountOp C x = C/log(opZ x)` is still `≪ 0.01` at the tower
`x₀` (`log(opZ x) ≥ (opW'^opW')/8`, astronomically large), inside the razor's `M ≥ 1/100` margin,
so the downstream HEB requirement is unaffected by `C`'s size — only by its being a fixed real.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset ArithmeticFunction Salt.LS
open scoped BigOperators

namespace Salt.Chen

/-! ## Section A — the count bound with a UNIFORM `K`

`CountFinal.tripleSum_le_cbar_final` (and the `W` keystone) provide the `c̄/2` count bound with `K`
an INNER existential (chosen per instance).  Since the honest `(★)` needs a FIXED leading constant,
we rebuild the identical bound with `K` supplied as an explicit hypothesis (verbatim the landed
proof: `per_pair_weighted_le'` + `weightedPairSum'_le_cbar`).  At the operating point we then feed
it the uniform `psiTot_pnt` witness — the exact constant `tripleSum_le_weighted_pairSum'` uses. -/

/-- **`count_bound_uniformK` — the `c̄/2` count close with `K` explicit.**  Verbatim
`tripleSum_le_cbar_final`, but with `K` a hypothesis (`hpsi` the `psiTot_pnt`-shaped PNT row)
instead of the landed inner `∃ K`.  Lets the composition thread ONE uniform `K`. -/
theorem count_bound_uniformK {K : ℝ} (hK0 : 0 ≤ K)
    (hpsi : ∀ n : ℕ, 3 ≤ n → |psiTot n - (n : ℝ)| ≤ K * n / Real.log n)
    {x zN yN : ℕ} {zR yR : ℝ}
    (hx1 : 1 < (x : ℝ))
    (hzR2 : 2 ≤ zR) (hzRyR : zR ≤ yR)
    (hlogz : Real.log zR = Real.log x / 8) (hlogy : Real.log yR = Real.log x / 3)
    (hzN_le : (zN : ℝ) ≤ zR) (hzN_ge : zR ≤ (zN : ℝ) + 1)
    (hyN_le : (yN : ℝ) ≤ yR) (hyN_ge : yR ≤ (yN : ℝ) + 1)
    (hLval4 : 4 ≤ Real.log (Lval x yN)) :
    tripleSum x zN yN
      ≤ (1 + 3 * K / Real.log (Lval x yN))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
            * (cbar / 2) * ((x : ℝ) / Real.log x)
        + ( (1 + 3 * K / Real.log (Lval x yN))
              * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
              * ((x : ℝ) / 2)
              * ( ( Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
                    + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
                  + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
                      * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                            / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                          + (21 / Real.log yR)
                              * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) )
          + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) ) := by
  -- Step 1 (verbatim `tripleSum_le_weighted_pairSum'`, but with the explicit `K`):
  have hbound : tripleSum x zN yN ≤
      (1 + 3 * K / Real.log (Lval x yN))
          * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
          * ((x : ℝ) / 2) * weightedPairSum' x zN yN
      + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) := by
    have hstep : ∀ q ∈ pairSet' x zN yN,
        primeCountIoc (Lfun x q) (Ufun x q)
          ≤ (1 + 3 * K / Real.log (Lval x yN))
              * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ))) * ((x : ℝ) / 2)
              * (1 / ((q.1 : ℝ) * q.2 * logND x q)) + 1 / Real.log (Lval x yN) :=
      fun q hq => per_pair_weighted_le' hK0 hpsi hLval4 hq
    calc tripleSum x zN yN
        ≤ ∑ q ∈ pairSet' x zN yN, primeCountIoc (Lfun x q) (Ufun x q) :=
          triple_count_le_pairSum' x zN yN
      _ ≤ ∑ q ∈ pairSet' x zN yN, ((1 + 3 * K / Real.log (Lval x yN))
              * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ))) * ((x : ℝ) / 2)
              * (1 / ((q.1 : ℝ) * q.2 * logND x q)) + 1 / Real.log (Lval x yN)) :=
          Finset.sum_le_sum hstep
      _ = (1 + 3 * K / Real.log (Lval x yN))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ))) * ((x : ℝ) / 2)
            * weightedPairSum' x zN yN
          + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) := by
          rw [weightedPairSum', Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            nsmul_eq_mul, mul_one_div]
  -- Step 2 (verbatim `tripleSum_le_cbar_final`, the analytic heart folded in):
  have hwps := weightedPairSum'_le_cbar hx1 hzR2 hzRyR hlogz hlogy hzN_le hzN_ge hyN_le hyN_ge
  have hL₀pos : 0 < Real.log (Lval x yN) := by linarith [hLval4]
  have hLvalgt1 : (1 : ℝ) < (Lval x yN : ℝ) := by
    by_contra h
    have := Real.log_nonpos (by positivity) (not_lt.mp h)
    linarith [hLval4]
  have h2Lpos : 0 < Real.log (2 * (Lval x yN : ℝ)) := Real.log_pos (by linarith [hLvalgt1])
  have hA₁ : 0 ≤ 1 + 3 * K / Real.log (Lval x yN) := by
    have : 0 ≤ 3 * K / Real.log (Lval x yN) := div_nonneg (by linarith [hK0]) hL₀pos.le
    linarith
  have hA₂ : 0 ≤ 1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)) := by
    have h2 : 0 ≤ 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)) :=
      div_nonneg (by positivity) h2Lpos.le
    linarith
  have hcoef : 0 ≤ (1 + 3 * K / Real.log (Lval x yN))
      * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ))) * ((x : ℝ) / 2) := by
    apply mul_nonneg (mul_nonneg hA₁ hA₂); linarith [hx1]
  have hmul := mul_le_mul_of_nonneg_left hwps hcoef
  calc tripleSum x zN yN
      ≤ (1 + 3 * K / Real.log (Lval x yN))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
            * ((x : ℝ) / 2) * weightedPairSum' x zN yN
          + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) := hbound
    _ ≤ (1 + 3 * K / Real.log (Lval x yN))
            * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x yN : ℝ)))
            * ((x : ℝ) / 2)
            * ( cbar / Real.log x
                + ( ( Ifun (x : ℝ) yR (zN : ℝ) / (zN : ℝ) + Ifun (x : ℝ) yR (yN : ℝ) / (yN : ℝ)
                      + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
                    + ∑ p₁ ∈ S1set x zN yN, (1 / (p₁ : ℝ))
                        * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                              / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                            + (21 / Real.log yR)
                                * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) ) )
          + ((pairSet' x zN yN).card : ℝ) / Real.log (Lval x yN) := by linarith [hmul]
    _ = _ := by ring

/-! ## Section B — the operating-point numeric facts

The CORR assembly and the final fold need, past a threshold: `log x ≥ 96`, the floors
`opZ x, opY x ≥ log x` (via `x^{1/8} ≥ 2·log x` from `a12_logpow_le_rpow`, so
`opZ x ≥ x^{1/8} − 1 ≥ 2·log x − 1 ≥ log x`), and the window log bounds
`log(opZ x) ≤ log x/8`, `log(opY x) ≤ log x/3` (from `opf_window_floor_bounds`). -/

/-- **`op_at_facts` — the reusable at-op numeric bundle.**  Past a threshold: `96 ≤ log x`,
`log x ≤ opZ x`, `log x ≤ opY x`, `log(opZ x) ≤ log x/8`, `log(opY x) ≤ log x/3`, and
`1 ≤ opZ x`, `1 ≤ opY x`. -/
theorem op_at_facts : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    (96 : ℝ) ≤ Real.log x
      ∧ Real.log x ≤ (opZ x : ℝ)
      ∧ Real.log x ≤ (opY x : ℝ)
      ∧ Real.log (opZ x : ℝ) ≤ Real.log x / 8
      ∧ Real.log (opY x : ℝ) ≤ Real.log x / 3
      ∧ (1 : ℝ) ≤ (opZ x : ℝ)
      ∧ (1 : ℝ) ≤ (opY x : ℝ)
      ∧ Real.log x / 8 - 1 / 999999 ≤ Real.log (opZ x : ℝ)
      ∧ Real.log x / 3 - 1 / 999999 ≤ Real.log (opY x : ℝ) := by
  obtain ⟨xa, ha⟩ := a12_logpow_le_rpow 1 (1 / 16) (by norm_num) (by norm_num)
  refine ⟨max xa (10 ^ 48), fun x hx => ?_⟩
  have hxa : xa ≤ x := le_trans (le_max_left _ _) hx
  have hx48 : 10 ^ 48 ≤ x := le_trans (le_max_right _ _) hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48R
  have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hx48R
  obtain ⟨_, _, hZlog_le, hZlog_ge⟩ := opf_window_floor_bounds x hx48R (γ := 1 / 8) (le_refl _)
  obtain ⟨_, _, hYlog_le, hYlog_ge⟩ := opf_window_floor_bounds x hx48R (γ := 1 / 3) (by norm_num)
  -- `log x ≤ x^{1/16}` and `2 ≤ x^{1/16}`
  have ha16 : (Real.log x) ^ (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 16) := ha x hxa
  have hL_le16 : Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 16) := by rwa [Real.rpow_one] at ha16
  have h16nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_nonneg hxpos.le _
  have h16_ge2 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 16) := by
    have hmono : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 16) ≤ (x : ℝ) ^ ((1 : ℝ) / 16) :=
      Real.rpow_le_rpow (by positivity) hx48R (by norm_num)
    have heq : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 16) = (10 : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
        show ((48 : ℕ) : ℝ) * (1 / 16) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [heq] at hmono; linarith
  -- `x^{1/8} = x^{1/16}·x^{1/16} ≥ 2·log x`
  have h18eq : (x : ℝ) ^ ((1 : ℝ) / 8) = (x : ℝ) ^ ((1 : ℝ) / 16) * (x : ℝ) ^ ((1 : ℝ) / 16) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have h18_ge : (2 : ℝ) * Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [h18eq]
    have hlognn : (0 : ℝ) ≤ Real.log x := le_trans (by norm_num) hL96
    linarith [mul_le_mul_of_nonneg_right h16_ge2 hlognn,
      mul_le_mul_of_nonneg_left hL_le16 h16nn]
  -- `x^{1/3} ≥ x^{1/8} ≥ 2·log x`
  have h13_ge18 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
  -- floors `opZ x, opY x ≥ x^{·} − 1 ≥ 2 log x − 1 ≥ log x`
  have hZfl : (x : ℝ) ^ ((1 : ℝ) / 8) < (opZ x : ℝ) + 1 := by
    rw [opZ]; exact Nat.lt_floor_add_one _
  have hYfl : (x : ℝ) ^ ((1 : ℝ) / 3) < (opY x : ℝ) + 1 := by
    rw [opY]; exact Nat.lt_floor_add_one _
  have hZge : Real.log x ≤ (opZ x : ℝ) := by linarith [h18_ge, hZfl, hL96]
  have hYge : Real.log x ≤ (opY x : ℝ) := by linarith [h18_ge, h13_ge18, hYfl, hL96]
  refine ⟨hL96, hZge, hYge, ?_, ?_, by linarith [hZge, hL96], by linarith [hYge, hL96], ?_, ?_⟩
  · rw [opZ]; linarith [hZlog_le]
  · rw [opY]; linarith [hYlog_le]
  · rw [opZ]; linarith [hZlog_ge]
  · rw [opY]; linarith [hYlog_ge]

/-! ## Section C — the `hbjs` third bound and the windowed-Mertens reciprocal sums -/

/-- **`hbjs_le_third` — the uniform `hbjs ≤ 3/log N` bound.**  When `p·t ≤ N^{2/3}` (i.e.
`log(p·t) ≤ (2/3) log N`), `N/(p·t) ≥ N^{1/3}`, so `log(N/(p·t)) ≥ (log N)/3 > 0` and
`hbjs N p t = (log(N/(p·t)))⁻¹ ≤ 3/log N`. -/
theorem hbjs_le_third {N p t : ℝ} (hN : 1 < N) (hpt0 : 0 < p * t)
    (hlog : Real.log (p * t) ≤ 2 / 3 * Real.log N) : hbjs N p t ≤ 3 / Real.log N := by
  have hLN : 0 < Real.log N := Real.log_pos hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hden : Real.log N / 3 ≤ Real.log (N / (p * t)) := by
    rw [Real.log_div hNpos.ne' hpt0.ne']; linarith
  have hpos3 : (0 : ℝ) < Real.log N / 3 := by linarith
  rw [hbjs]
  calc (Real.log (N / (p * t)))⁻¹ ≤ (Real.log N / 3)⁻¹ := by
        apply inv_anti₀ hpos3 hden
    _ = 3 / Real.log N := by rw [inv_div]

/-- **`S1_recip_le` — the `S1set` reciprocal sum is `≤ 4` at op.**  `S1set_mertens` gives
`Σ_{S1} 1/p₁ ≤ log(log(opY x + 1)/log(opZ x)) + 19/log(opZ x)`; at op `log(opZ x) ≥ 11`
(so `19/log(opZ x) ≤ 2`) and the ratio `≤ 4` (so its log `≤ log 4 < 2`), giving `≤ 4`. -/
theorem S1_recip_le : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 : ℝ) / p₁ ≤ 4 := by
  obtain ⟨xt, _, htower⟩ := opf_tower
  obtain ⟨xf, hf⟩ := op_at_facts
  refine ⟨max xt xf, fun x hx => ?_⟩
  have hxt : xt ≤ x := le_trans (le_max_left _ _) hx
  have hxf : xf ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hL96, hZge, hYge, hZlog, hYlog, h1Z, h1Y, hZlog_ge, hYlog_ge⟩ := hf x hxf
  have hZY : opZ x ≤ opY x := by
    obtain ⟨_, _, _, _, _, _, h7, _⟩ := htower x hxt; exact h7
  have hz2 : (2 : ℝ) ≤ (opZ x : ℝ) := by linarith [hZge, hL96]
  have hzy1 : (opZ x : ℝ) ≤ (opY x : ℝ) + 1 := by
    have : (opZ x : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hZY
    linarith
  have hmert := S1set_mertens (x := x) hz2 hzy1
  have hlogZ_pos : 0 < Real.log (opZ x : ℝ) := Real.log_pos (by linarith [hZge, hL96])
  have hlogZ_ge11 : (11 : ℝ) ≤ Real.log (opZ x : ℝ) := by linarith [hZlog_ge, hL96]
  have hYpos : (1 : ℝ) < (opY x : ℝ) := by linarith [hYge, hL96]
  have hlogY1_pos : 0 < Real.log ((opY x : ℝ) + 1) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h19 : 19 / Real.log (opZ x : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hlogZ_pos]; linarith [hlogZ_ge11]
  have hlogY1_le : Real.log ((opY x : ℝ) + 1) ≤ Real.log 2 + Real.log x / 3 := by
    have hstep : Real.log ((opY x : ℝ) + 1) ≤ Real.log (2 * (opY x : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (lt_trans one_pos hYpos).ne'] at hstep
    linarith [hstep, hYlog]
  have hratio_le : Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hlogZ_pos]; linarith [hlogY1_le, hZlog_ge, hL96, hlog2]
  have hratio_pos : 0 < Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) :=
    div_pos hlogY1_pos hlogZ_pos
  have hlogratio : Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ)) ≤ 2 := by
    have h1 := Real.log_le_log hratio_pos hratio_le
    have h2 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    linarith [h1, h2, hlog2]
  linarith [hmert, hlogratio, h19]

/-- **`pairSum_le_at_op` — the pair reciprocal sum is `≤ 16` at op.**  `sum_inv_pairSet_le`
gives `Σ 1/(p₁p₂) ≤ M₁·M₂` with `M₁` (the `p₁`-window) and `M₂` (the `p₂`-window) each `≤ 4`
by the same windowed-Mertens estimates (`log(opZ x) ≥ 11`, `log(opY x + 1) ≥ 30`, ratios `≤ 4`). -/
theorem pairSum_le_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2) ≤ 16 := by
  obtain ⟨xt, _, htower⟩ := opf_tower
  obtain ⟨xf, hf⟩ := op_at_facts
  refine ⟨max xt (max xf (10 ^ 48)), fun x hx => ?_⟩
  have hxt : xt ≤ x := le_trans (le_max_left _ _) hx
  have hxf : xf ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx48 : 10 ^ 48 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  obtain ⟨hL96, hZge, hYge, hZlog, hYlog, h1Z, h1Y, hZlog_ge, hYlog_ge⟩ := hf x hxf
  have hZY : opZ x ≤ opY x := by
    obtain ⟨_, _, _, _, _, _, h7, _⟩ := htower x hxt; exact h7
  -- geometry rows for sum_inv_pairSet_le
  have hz2 : 2 ≤ opZ x := by
    have : (2 : ℝ) ≤ (opZ x : ℝ) := by linarith [hZge, hL96]
    exact_mod_cast this
  have hy1 : 1 ≤ opY x := by
    have : (1 : ℝ) ≤ (opY x : ℝ) := h1Y
    exact_mod_cast this
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48R
  have hysx : (opY x : ℝ) ≤ Real.sqrt x := by
    have hYle : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [opY]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
    refine le_trans hYle ?_
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
  have hmert := sum_inv_pairSet_le (x := x) hz2 hZY hy1 hysx
  -- M₁ ≤ 4 (same as `S1_recip_le`'s ratio) and M₂ ≤ 4
  have hlogZ_pos : 0 < Real.log (opZ x : ℝ) := Real.log_pos (by linarith [hZge, hL96])
  have hlogZ_ge11 : (11 : ℝ) ≤ Real.log (opZ x : ℝ) := by linarith [hZlog_ge, hL96]
  have hYpos : (1 : ℝ) < (opY x : ℝ) := by linarith [hYge, hL96]
  have hlogY1_pos : 0 < Real.log ((opY x : ℝ) + 1) := Real.log_pos (by linarith)
  have hlogY1_ge30 : (30 : ℝ) ≤ Real.log ((opY x : ℝ) + 1) := by
    have : Real.log (opY x : ℝ) ≤ Real.log ((opY x : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith [hYlog_ge, hL96, this]
  -- M₁ ≤ 4
  have hlogY1_le : Real.log ((opY x : ℝ) + 1) ≤ Real.log 2 + Real.log x / 3 := by
    have hstep : Real.log ((opY x : ℝ) + 1) ≤ Real.log (2 * (opY x : ℝ)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (lt_trans one_pos hYpos).ne'] at hstep
    linarith [hstep, hYlog]
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4le : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hM1 : Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ))
        + 19 / Real.log (opZ x : ℝ) ≤ 4 := by
    have hratio_le : Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) ≤ 4 := by
      rw [div_le_iff₀ hlogZ_pos]; linarith [hlogY1_le, hZlog_ge, hL96, hlog2]
    have hratio_pos : 0 < Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) :=
      div_pos hlogY1_pos hlogZ_pos
    have h1 : Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ)) ≤ 2 := by
      have := Real.log_le_log hratio_pos hratio_le; linarith [this, hlog4le, hlog2]
    have h19 : 19 / Real.log (opZ x : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hlogZ_pos]; linarith [hlogZ_ge11]
    linarith
  -- M₂ ≤ 4 (the `p₂`-window, running to `√x`)
  have hsx_pos : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  have hsx_ge1 : (1 : ℝ) ≤ Real.sqrt x := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (le_trans (by norm_num : (1 : ℝ) ≤ (10 : ℝ) ^ 48) hx48R)
  have hlogsx : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hxpos.le
  have hlogsx1_le : Real.log (Real.sqrt x + 1) ≤ Real.log 2 + Real.log x / 2 := by
    have hstep : Real.log (Real.sqrt x + 1) ≤ Real.log (2 * Real.sqrt x) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hsx_pos.ne'] at hstep
    linarith [hstep, hlogsx.le, hlogsx.ge]
  have hlogY1_geL3 : Real.log x / 3 - 1 / 999999 ≤ Real.log ((opY x : ℝ) + 1) := by
    have : Real.log (opY x : ℝ) ≤ Real.log ((opY x : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith [hYlog_ge, this]
  have hM2 : Real.log (Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1))
        + 19 / Real.log ((opY x : ℝ) + 1) ≤ 4 := by
    have hratio_le : Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1) ≤ 4 := by
      rw [div_le_iff₀ hlogY1_pos]; linarith [hlogsx1_le, hlogY1_geL3, hL96, hlog2]
    have hratio_pos : 0 < Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1) :=
      div_pos (Real.log_pos (by linarith)) hlogY1_pos
    have h1 : Real.log (Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1)) ≤ 2 := by
      have := Real.log_le_log hratio_pos hratio_le; linarith [this, hlog4le, hlog2]
    have h19 : 19 / Real.log ((opY x : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ hlogY1_pos]; linarith [hlogY1_ge30]
    linarith
  -- nonnegativity of the two windowed lengths (ratios `≥ 1`)
  have hM1nn : 0 ≤ Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ))
        + 19 / Real.log (opZ x : ℝ) := by
    have hr1 : (1 : ℝ) ≤ Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ) := by
      rw [le_div_iff₀ hlogZ_pos, one_mul]
      exact Real.log_le_log (by linarith [hZge, hL96]) (by
        have : (opZ x : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hZY
        linarith)
    have : 0 ≤ Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ)) :=
      Real.log_nonneg hr1
    have h19nn : 0 ≤ 19 / Real.log (opZ x : ℝ) := by positivity
    linarith
  have hM2nn : 0 ≤ Real.log (Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1))
        + 19 / Real.log ((opY x : ℝ) + 1) := by
    have hr1 : (1 : ℝ) ≤ Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1) := by
      rw [le_div_iff₀ hlogY1_pos, one_mul]
      exact Real.log_le_log (by linarith) (by linarith [hysx])
    have : 0 ≤ Real.log (Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1)) :=
      Real.log_nonneg hr1
    have h19nn : 0 ≤ 19 / Real.log ((opY x : ℝ) + 1) := by positivity
    linarith
  calc ∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2)
      ≤ (Real.log (Real.log ((opY x : ℝ) + 1) / Real.log (opZ x : ℝ)) + 19 / Real.log (opZ x : ℝ))
        * (Real.log (Real.log (Real.sqrt x + 1) / Real.log ((opY x : ℝ) + 1))
            + 19 / Real.log ((opY x : ℝ) + 1)) := hmert
    _ ≤ 4 * 4 := mul_le_mul hM1 hM2 hM2nn (by norm_num)
    _ = 16 := by norm_num

/-! ## Section D — fold 1: the CORR sum bound `CORR ≤ C_CORR/(log x)²`

The keystone's Abel-error/boundary sum has three scalar `Ifun` terms and a `p₁`-sum of
floor-`hbjs` + boundary-`hbjs` pieces.  Each `Ifun` term is `≤ (3/2)·log 2/(log x)²`
(`Ifun_op_le` gives `Ifun ≤ (3/2)·log2/log x`, then `/opZ` or `/opY ≤ 1/log x`); the dominant
`(21/log zR)·Ifun zR ≤ 252·log2/(log x)²`; the `p₁`-sum is `≤ 768/(log x)²`
(`hbjs_sqrt_le`/`hbjs_le_third` give `≤ 3/log x` per `hbjs`, `⌊√(x/p₁)⌋ ≥ opY x ≥ log x`,
`Σ 1/p₁ ≤ 4`).  Total `C_CORR = 255·log 2 + 768`. -/

/-- **`corr_le_at_op` — fold 1.**  Past a threshold, the keystone `CORR` sum at the op witnesses
(`zN = opZ x`, `yN = opY x`, carriers `zR, yR` with `log zR = log x/8`, `log yR = log x/3`) is
`≤ (255·log 2 + 768)/(log x)²`. -/
theorem corr_le_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ zR yR : ℝ, (2 : ℝ) ≤ zR → 0 < yR →
      Real.log zR = Real.log x / 8 → Real.log yR = Real.log x / 3 →
      ( Ifun (x : ℝ) yR (opZ x : ℝ) / (opZ x : ℝ) + Ifun (x : ℝ) yR (opY x : ℝ) / (opY x : ℝ)
          + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
        + ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ))
            * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                  / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) )
      ≤ (255 * Real.log 2 + 768) / (Real.log x) ^ 2 := by
  obtain ⟨xf, hf⟩ := op_at_facts
  obtain ⟨xs, hs⟩ := S1_recip_le
  refine ⟨max xf (max xs (10 ^ 48)), fun x hx zR yR hzR2 hyR0 hlogzR hlogyR => ?_⟩
  have hxf : xf ≤ x := le_trans (le_max_left _ _) hx
  have hxs : xs ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx48 : 10 ^ 48 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  have hx1 : (1 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx48R
  obtain ⟨hL96, hZge, hYge, hZlog, hYlog, h1Z, h1Y, hZlog_ge, hYlog_ge⟩ := hf x hxf
  have hLpos : 0 < Real.log x := by linarith [hL96]
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hS1 := hs x hxs
  -- the reusable `Ifun u / u ≤ (3/2)log2/(log x)²` at `u ∈ {opZ x, opY x}`
  have ifun_div_bound : ∀ u : ℝ, 1 ≤ u → Real.log u ≤ Real.log x / 3 → Real.log x ≤ u →
      Ifun (x : ℝ) yR u / u ≤ 3 / 2 * Real.log 2 / (Real.log x) ^ 2 := by
    intro u hu1 hulog hLu
    have hI_le := Ifun_op_le hx1 hyR0 hlogyR hu1 hulog
    have hI_le' : Ifun (x : ℝ) yR u * Real.log x ≤ 3 / 2 * Real.log 2 :=
      (le_div_iff₀ hLpos).mp hI_le
    have hupos : (0 : ℝ) < u := by linarith [hLpos, hLu]
    rw [div_le_div_iff₀ hupos (by positivity : (0 : ℝ) < (Real.log x) ^ 2)]
    nlinarith [mul_le_mul_of_nonneg_right hI_le' hLpos.le,
      mul_le_mul_of_nonneg_left hLu (by positivity : (0 : ℝ) ≤ 3 / 2 * Real.log 2), hLpos]
  have h_zN := ifun_div_bound (opZ x : ℝ) h1Z (by linarith [hZlog, hLpos]) hZge
  have h_yN := ifun_div_bound (opY x : ℝ) h1Y (by linarith [hYlog]) hYge
  -- the dominant `(21/log zR)·Ifun zR ≤ 252·log2/(log x)²`
  have h_zR : (21 / Real.log zR) * Ifun (x : ℝ) yR zR ≤ 252 * Real.log 2 / (Real.log x) ^ 2 := by
    have hI_le := Ifun_op_le (u := zR) hx1 hyR0 hlogyR (by linarith [hzR2])
      (by rw [hlogzR]; linarith [hLpos])
    have hcoef_nn : (0 : ℝ) ≤ 21 / Real.log zR := by rw [hlogzR]; positivity
    have hcoef_eq : (21 : ℝ) / Real.log zR = 168 / Real.log x := by
      rw [hlogzR, div_eq_div_iff (div_pos hLpos (by norm_num : (0 : ℝ) < 8)).ne' hLpos.ne']; ring
    calc (21 / Real.log zR) * Ifun (x : ℝ) yR zR
        ≤ (21 / Real.log zR) * (3 / 2 * Real.log 2 / Real.log x) :=
          mul_le_mul_of_nonneg_left hI_le hcoef_nn
      _ = 252 * Real.log 2 / (Real.log x) ^ 2 := by rw [hcoef_eq, pow_two]; ring
  -- the `p₁`-sum ≤ 768/(log x)²
  have h_sum : ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ))
        * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
              / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
            + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) )
      ≤ 768 / (Real.log x) ^ 2 := by
    have hpp : ∀ p₁ ∈ S1set x (opZ x) (opY x),
        (1 / (p₁ : ℝ)) * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
              / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
            + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) )
          ≤ (1 / (p₁ : ℝ)) * (192 / (Real.log x) ^ 2) := by
      intro p₁ hp₁
      rw [S1set, Finset.mem_filter, Finset.mem_Icc] at hp₁
      obtain ⟨⟨h1p, _⟩, hzp, hpy, hpp'⟩ := hp₁
      have hp1pos : (0 : ℝ) < (p₁ : ℝ) := by exact_mod_cast hpp'.pos
      have hp1nn : (0 : ℝ) ≤ (p₁ : ℝ) := hp1pos.le
      have hp1ge1 : (1 : ℝ) ≤ (p₁ : ℝ) := by exact_mod_cast hpp'.one_lt.le
      have hp1_le_opY : (p₁ : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hpy
      have hlogp1 : Real.log (p₁ : ℝ) ≤ Real.log x / 3 :=
        le_trans (Real.log_le_log hp1pos hp1_le_opY) hYlog
      -- the `√(x/p₁)` boundary `hbjs ≤ 3/log x`
      have hsqrt_le : hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ≤ 3 / Real.log x :=
        hbjs_sqrt_le hx1 hp1ge1 hlogp1
      -- the floor `⌊√(x/p₁)⌋ ≥ opY x ≥ log x`
      have hxp_pos : (0 : ℝ) < (x : ℝ) / (p₁ : ℝ) := div_pos hxpos hp1pos
      have hp1_le_x13 : (p₁ : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
        refine le_trans hp1_le_opY ?_
        rw [opY]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
      have hcube : (x : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.sqrt ((x : ℝ) / (p₁ : ℝ)) := by
        rw [show (x : ℝ) ^ ((1 : ℝ) / 3)
              = Real.sqrt (((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2)
            from (Real.sqrt_sq (Real.rpow_nonneg hxpos.le _)).symm]
        apply Real.sqrt_le_sqrt
        rw [le_div_iff₀ hp1pos,
          show ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (x : ℝ) ^ ((2 : ℝ) / 3) by
            rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hxpos.le]
            norm_num]
        calc (x : ℝ) ^ ((2 : ℝ) / 3) * (p₁ : ℝ)
            ≤ (x : ℝ) ^ ((2 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) :=
              mul_le_mul_of_nonneg_left hp1_le_x13 (Real.rpow_nonneg hxpos.le _)
          _ = (x : ℝ) := by
              rw [← Real.rpow_add hxpos, show (2 : ℝ) / 3 + (1 : ℝ) / 3 = 1 by norm_num,
                Real.rpow_one]
      have hfloor_ge_opY : (opY x : ℝ) ≤ (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ) := by
        have : opY x ≤ ⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ := by
          rw [opY]; exact Nat.floor_mono hcube
        exact_mod_cast this
      have hfloor_pos : (0 : ℝ) < (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ) := by
        linarith [hfloor_ge_opY, hYge, hLpos]
      have hpt_pos : (0 : ℝ) < (p₁ : ℝ) * (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ) :=
        mul_pos hp1pos hfloor_pos
      -- `log(p₁·floor) ≤ (2/3) log x` via `p₁·floor ≤ p₁·√(x/p₁) = √(p₁ x)`
      have hlog_pt : Real.log ((p₁ : ℝ) * (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ))
          ≤ 2 / 3 * Real.log x := by
        have hfl_le : (p₁ : ℝ) * (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ)
            ≤ (p₁ : ℝ) * Real.sqrt ((x : ℝ) / (p₁ : ℝ)) :=
          mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) hp1nn
        have heq : Real.log ((p₁ : ℝ) * Real.sqrt ((x : ℝ) / (p₁ : ℝ)))
            = 1 / 2 * Real.log (p₁ : ℝ) + 1 / 2 * Real.log x := by
          rw [Real.log_mul hp1pos.ne' (Real.sqrt_pos.mpr hxp_pos).ne',
            Real.log_sqrt hxp_pos.le, Real.log_div hxpos.ne' hp1pos.ne']
          ring
        have := Real.log_le_log hpt_pos hfl_le
        rw [heq] at this
        linarith [this, hlogp1]
      have hfloor_le : hbjs (x : ℝ) (p₁ : ℝ) (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ)
          ≤ 3 / Real.log x := hbjs_le_third hx1 hpt_pos hlog_pt
      have hLfloor : Real.log x ≤ (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ) :=
        le_trans hYge hfloor_ge_opY
      have hfloor_le' : hbjs (x : ℝ) (p₁ : ℝ) (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ)
          * Real.log x ≤ 3 := (le_div_iff₀ hLpos).mp hfloor_le
      -- bound the two hbjs pieces
      have hA : hbjs (x : ℝ) (p₁ : ℝ) (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ)
            / (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ) ≤ 3 / (Real.log x) ^ 2 := by
        rw [div_le_div_iff₀ hfloor_pos (by positivity : (0 : ℝ) < (Real.log x) ^ 2)]
        nlinarith [mul_le_mul_of_nonneg_right hfloor_le' hLpos.le, hLfloor, hLpos]
      have hB : (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ)))
            ≤ 189 / (Real.log x) ^ 2 := by
        have hcoef : (21 / Real.log yR) = 63 / Real.log x := by
          rw [hlogyR,
            div_eq_div_iff (div_pos hLpos (by norm_num : (0 : ℝ) < 3)).ne' hLpos.ne']
          ring
        rw [hcoef]
        calc (63 / Real.log x) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ)))
            ≤ (63 / Real.log x) * (3 / Real.log x) :=
              mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
          _ = 189 / (Real.log x) ^ 2 := by rw [pow_two]; ring
      have hbracket : hbjs (x : ℝ) (p₁ : ℝ) (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ)
              / (⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊ : ℝ)
            + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ)))
          ≤ 192 / (Real.log x) ^ 2 := by
        have heq3 : (3 : ℝ) / (Real.log x) ^ 2 + 189 / (Real.log x) ^ 2
            = 192 / (Real.log x) ^ 2 := by ring
        linarith [hA, hB, heq3]
      exact mul_le_mul_of_nonneg_left hbracket (by positivity)
    calc ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ))
            * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                  / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) )
        ≤ ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ)) * (192 / (Real.log x) ^ 2) :=
          Finset.sum_le_sum hpp
      _ = (∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ))) * (192 / (Real.log x) ^ 2) := by
          rw [← Finset.sum_mul]
      _ ≤ 4 * (192 / (Real.log x) ^ 2) := by
          apply mul_le_mul_of_nonneg_right hS1 (by positivity)
      _ = 768 / (Real.log x) ^ 2 := by ring
  -- assemble
  calc ( Ifun (x : ℝ) yR (opZ x : ℝ) / (opZ x : ℝ) + Ifun (x : ℝ) yR (opY x : ℝ) / (opY x : ℝ)
          + (21 / Real.log zR) * Ifun (x : ℝ) yR zR )
        + ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ))
            * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                  / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                + (21 / Real.log yR) * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) )
      ≤ (3 / 2 * Real.log 2 / (Real.log x) ^ 2 + 3 / 2 * Real.log 2 / (Real.log x) ^ 2
          + 252 * Real.log 2 / (Real.log x) ^ 2) + 768 / (Real.log x) ^ 2 := by
        linarith [h_zN, h_yN, h_zR, h_sum]
    _ = (255 * Real.log 2 + 768) / (Real.log x) ^ 2 := by ring

/-! ## Section E — fold 2: the `E_SW` main-term collapse (`A = 13`, base `7`)

`ESW_main_fold` (CountAtOp2) needs `log x/6 ≤ logLval`, but the honest op bound is
`logLval ≥ log x/7` (`logLval_op_ge` gives `log x/6 − 2 log 2 ≥ log x/7`), so we re-derive at
base `7`.  Converting the keystone's `logLval^(13:ℝ)` (real rpow) to `(13:ℕ)` (nat pow) makes it
polynomial: `logLval^13 ≥ (log x/7)^13 = (log x)^13/7^13`, so the `φ·log x·(Ksw·x/logLval^13·M)`
main collapses to `Ksw·M·7^13·x/(log x)^11` — the `O(x/(log x)^{11})` strip. -/

/-- **`esw_main_le13` — fold 2.**  The `E_SW` main term at `A = 13`, base `7`. -/
theorem esw_main_le13 {φ x logLval M Ksw : ℝ}
    (hφx : φ ≤ Real.log x) (hlogx : 0 < Real.log x)
    (hLval : Real.log x / 7 ≤ logLval) (hM : 0 ≤ M) (hKsw : 0 ≤ Ksw) (hx : 0 ≤ x) :
    φ * Real.log x * (Ksw * x / logLval ^ (13 : ℝ) * M)
      ≤ Ksw * M * (7 : ℝ) ^ (13 : ℕ) * x / (Real.log x) ^ (11 : ℕ) := by
  have hlogLval0 : 0 < logLval := by linarith
  rw [show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  set L := Real.log x with hLdef
  have hLne : L ≠ 0 := hlogx.ne'
  have hLpow : (0 : ℝ) < L ^ (13 : ℕ) := by positivity
  have hLvalpow : (0 : ℝ) < logLval ^ (13 : ℕ) := by positivity
  have h7pow : (0 : ℝ) < (7 : ℝ) ^ (13 : ℕ) := by positivity
  have hpow : L ^ (13 : ℕ) / (7 : ℝ) ^ (13 : ℕ) ≤ logLval ^ (13 : ℕ) := by
    rw [← div_pow]; exact pow_le_pow_left₀ (by positivity) hLval 13
  have hinv : (1 : ℝ) / logLval ^ (13 : ℕ) ≤ (7 : ℝ) ^ (13 : ℕ) / L ^ (13 : ℕ) := by
    rw [div_le_div_iff₀ hLvalpow hLpow, one_mul, mul_comm]
    have hm := mul_le_mul_of_nonneg_right hpow h7pow.le
    have hc : L ^ (13 : ℕ) / (7 : ℝ) ^ (13 : ℕ) * (7 : ℝ) ^ (13 : ℕ) = L ^ (13 : ℕ) := by
      field_simp
    linarith [hm, hc]
  have hchain : Ksw * x / logLval ^ (13 : ℕ) * M
      ≤ Ksw * x * M * ((7 : ℝ) ^ (13 : ℕ) / L ^ (13 : ℕ)) := by
    have h := mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ Ksw * x * M)
    calc Ksw * x / logLval ^ (13 : ℕ) * M = Ksw * x * M * (1 / logLval ^ (13 : ℕ)) := by ring
      _ ≤ Ksw * x * M * ((7 : ℝ) ^ (13 : ℕ) / L ^ (13 : ℕ)) := h
  have hLL : L * L / L ^ (13 : ℕ) = 1 / L ^ (11 : ℕ) := by
    rw [div_eq_div_iff hLpow.ne' (by positivity : (0 : ℝ) < L ^ (11 : ℕ)).ne']
    rw [show (13 : ℕ) = 2 + 11 by norm_num, pow_add]; ring
  calc φ * L * (Ksw * x / logLval ^ (13 : ℕ) * M)
      ≤ L * L * (Ksw * x * M * ((7 : ℝ) ^ (13 : ℕ) / L ^ (13 : ℕ))) := by
        apply mul_le_mul _ hchain (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hφx hlogx.le
    _ = Ksw * M * (7 : ℝ) ^ (13 : ℕ) * x * (L * L / L ^ (13 : ℕ)) := by ring
    _ = Ksw * M * (7 : ℝ) ^ (13 : ℕ) * x * (1 / L ^ (11 : ℕ)) := by rw [hLL]
    _ = Ksw * M * (7 : ℝ) ^ (13 : ℕ) * x / L ^ (11 : ℕ) := by ring

/-! ## Section F — the lower-order/power-suppressed terms

The boundary `|pairSet| ≤ opY x·√x ≤ x^{5/6}` terms and the `E_SW` strip `x/(log x)^{11}` are all
`≤ x/log x` past a threshold (`a12_logpow_le_rpow`/`a12_log_ge`: `7·log x ≤ x^{1/6}`,
`2·(log x)³ ≤ x^{1/6}`, `Ksw·16·7^13 ≤ (log x)^{10}`), as is the constant `cbar < 1 ≤ x/log x`. -/

/-- **`op_ls_facts` — the four lower-order bounds at op.**  Past a threshold, each of `cbar`, the
two `x^{5/6}·polylog` boundary terms, and the `x/(log x)^{11}` `E_SW` strip is `≤ x/log x`. -/
theorem op_ls_facts (Ksw : ℝ) : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    cbar ≤ (x : ℝ) / Real.log x
      ∧ 7 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) ≤ (x : ℝ) / Real.log x
      ∧ 2 * (Real.log x) ^ 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) ≤ (x : ℝ) / Real.log x
      ∧ Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / (Real.log x) ^ (11 : ℕ)
          ≤ (x : ℝ) / Real.log x := by
  obtain ⟨xa, ha⟩ := a12_logpow_le_rpow 1 (1 / 12) (by norm_num) (by norm_num)
  obtain ⟨xb, hb⟩ := a12_logpow_le_rpow 3 (1 / 12) (by norm_num) (by norm_num)
  obtain ⟨xc, hc⟩ := a12_log_ge (Ksw * 16 * (7 : ℝ) ^ (13 : ℕ))
  refine ⟨max xa (max xb (max xc (10 ^ 48))), fun x hx => ?_⟩
  have hxa : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc : xc ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hx48 : 10 ^ 48 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  have hL96 : (96 : ℝ) ≤ Real.log x := opf_log_ge_96 x hx48R
  have hLpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hL96
  -- `x^{1/12} ≥ log x`, `x^{1/12} ≥ (log x)^3`, `x^{1/12} ≥ 10^4`
  have h12a : Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
    have := ha x hxa; rwa [Real.rpow_one] at this
  have h12b : (Real.log x) ^ (3 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
    have := hb x hxb
    rwa [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have h12big : (10 : ℝ) ^ 4 ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := by
    have hmono : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 12) ≤ (x : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by positivity) hx48R (by norm_num)
    have heq : ((10 : ℝ) ^ 48) ^ ((1 : ℝ) / 12) = (10 : ℝ) ^ 4 := by
      rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
        show ((48 : ℕ) : ℝ) * (1 / 12) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [heq] at hmono; linarith
  have h12nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 12) := Real.rpow_nonneg hxpos.le _
  -- `x^{1/6} = x^{1/12}·x^{1/12}`, `x^{5/6}·x^{1/6} = x`
  have h16eq : (x : ℝ) ^ ((1 : ℝ) / 6) = (x : ℝ) ^ ((1 : ℝ) / 12) * (x : ℝ) ^ ((1 : ℝ) / 12) := by
    rw [← Real.rpow_add hxpos]; norm_num
  have h56eq : (x : ℝ) ^ ((5 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) = (x : ℝ) := by
    rw [← Real.rpow_add hxpos, show (5 : ℝ) / 6 + (1 : ℝ) / 6 = 1 by norm_num, Real.rpow_one]
  have h56nn : (0 : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 6) := Real.rpow_nonneg hxpos.le _
  -- `7·log x ≤ x^{1/6}` and `2·(log x)³ ≤ x^{1/6}`
  have h7L : 7 * Real.log x ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [h16eq]; nlinarith [h12a, h12big, h12nn, hLpos]
  have h2L3 : 2 * (Real.log x) ^ (3 : ℕ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := by
    rw [h16eq]; nlinarith [h12b, h12big, h12nn]
  -- `opY x · √x ≤ x^{5/6}`
  have hOY : (opY x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    rw [opY]; exact Nat.floor_le (Real.rpow_nonneg hxpos.le _)
  have hNS : (Nat.sqrt x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
    have h2 : (Nat.sqrt x : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast Nat.sqrt_le' x
    rw [← Real.sqrt_eq_rpow]
    calc (Nat.sqrt x : ℝ) = Real.sqrt ((Nat.sqrt x : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt h2
  have hpw : (opY x : ℝ) * (Nat.sqrt x : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 6) := by
    calc (opY x : ℝ) * (Nat.sqrt x : ℝ)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul hOY hNS (by positivity) (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ ((5 : ℝ) / 6) := by rw [← Real.rpow_add hxpos]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- cbar ≤ x/log x
    have hxL : Real.log x ≤ (x : ℝ) := by
      have := Real.log_le_sub_one_of_pos hxpos; linarith
    have h1t : (1 : ℝ) ≤ (x : ℝ) / Real.log x := (one_le_div hLpos).mpr hxL
    have hcbar1 : cbar < 1 := lt_trans cbar_lt (by norm_num)
    linarith [hcbar1, h1t]
  · -- 7·opY·√x ≤ x/log x
    rw [le_div_iff₀ hLpos]
    calc 7 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) * Real.log x
        ≤ 7 * (x : ℝ) ^ ((5 : ℝ) / 6) * Real.log x := by nlinarith [hpw, hLpos, h56nn]
      _ = (x : ℝ) ^ ((5 : ℝ) / 6) * (7 * Real.log x) := by ring
      _ ≤ (x : ℝ) ^ ((5 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
          mul_le_mul_of_nonneg_left h7L h56nn
      _ = (x : ℝ) := h56eq
  · -- 2·(log x)²·opY·√x ≤ x/log x
    rw [le_div_iff₀ hLpos]
    calc 2 * (Real.log x) ^ 2 * ((opY x : ℝ) * (Nat.sqrt x : ℝ)) * Real.log x
        ≤ 2 * (Real.log x) ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 6) * Real.log x := by
          have hcoef_nn : (0 : ℝ) ≤ 2 * (Real.log x) ^ 2 * Real.log x :=
            mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hLpos.le
          nlinarith [mul_le_mul_of_nonneg_left hpw hcoef_nn]
      _ = (x : ℝ) ^ ((5 : ℝ) / 6) * (2 * (Real.log x) ^ (3 : ℕ)) := by ring
      _ ≤ (x : ℝ) ^ ((5 : ℝ) / 6) * (x : ℝ) ^ ((1 : ℝ) / 6) :=
          mul_le_mul_of_nonneg_left h2L3 h56nn
      _ = (x : ℝ) := h56eq
  · -- Ksw·16·7^13·x/(log x)^11 ≤ x/log x
    have hL10 : Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) ≤ (Real.log x) ^ (10 : ℕ) := by
      have hc' := (hc x hxc).2
      have hL1 : (1 : ℝ) ≤ Real.log x := by linarith [hL96]
      calc Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) ≤ Real.log x := hc'
        _ ≤ (Real.log x) ^ (10 : ℕ) := le_self_pow₀ hL1 (by norm_num)
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (Real.log x) ^ (11 : ℕ)) hLpos]
    have hL11 : (Real.log x) ^ (11 : ℕ) = (Real.log x) ^ (10 : ℕ) * Real.log x := by
      rw [← pow_succ]
    rw [hL11]
    nlinarith [mul_le_mul_of_nonneg_right hL10 (mul_nonneg hxpos.le hLpos.le)]

/-! ## Section G — fold 3: the `(★)` composition `hcount_star_at_op`

Applies `count_bound_uniformK` (uniform `K₀ := psiTot_pnt`) + `tripleSumW_equidist` at the op
witnesses, multiplies by `log x·φ`, and folds the RHS via `slack_collapse` (the `W ≤ 2`
multiplicative slack, `≤ cbar·(21K + 14 log 2)·x/log x`), `corr_le_at_op` (the CORR sum), and
`esw_main_le13`/`op_ls_facts` (the `E_SW` strip and the `x^{5/6}` boundary terms) into
`(cbar + ecountOp C x)·massLo`.  The honest `C` is documented in the module header. -/

/-- **`hcount_star_at_op` — HCOUNT-3, the `(★)` premise at op.**  For every mass constant
`Kmass ≥ 0` (the `lambda_mass_lower` constant) there is an explicit `C ≥ 0` and a threshold past
which the count line closes against the PNT lower window mass:

  `log x · tripleSumW opQ opA x (opZ x)(opY x)
      ≤ (cbar + ecountOp C x)·(massLo x Kmass / φ(opQ))`,   `massLo = x/2 − 1 − 2·Kmass·x/log x`.

This is exactly `CountAtOp.hcount_at_op`'s `(★)` premise; the capstone `example` chains the two into
the fully closed GlueNormalized `hcount` SLOT. -/
theorem hcount_star_at_op (Kmass : ℝ) (hKmass : 0 ≤ Kmass) :
    ∃ (C : ℝ) (x₁ : ℕ), 0 ≤ C ∧ ∀ x : ℕ, x₁ ≤ x →
      Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
        ≤ (cbar + ecountOp C x)
            * (((x : ℝ) / 2 - 1 - 2 * Kmass * x / Real.log x) / (opQ.totient : ℝ)) := by
  obtain ⟨K₀, hK0, hpsi₀⟩ := psiTot_pnt
  obtain ⟨Ksw, Nsw, hKsw, hEq⟩ :=
    tripleSumW_equidist (A := 13) (C := 2) (by norm_num) (by norm_num)
  obtain ⟨xLv, hLvalrows⟩ := hcount_Lval_rows Nsw
  obtain ⟨xA, hAP3⟩ := hcount_op_AP3
  obtain ⟨xC, hCORR⟩ := corr_le_at_op
  obtain ⟨xF, hF⟩ := op_at_facts
  obtain ⟨xP, hP⟩ := pairSum_le_at_op
  obtain ⟨xLS, hLS⟩ := op_ls_facts Ksw
  obtain ⟨xW, hWth⟩ := a12_log_ge (7 * (6 * K₀ + 4 * Real.log 2))
  obtain ⟨xM, hMth⟩ := a12_log_ge (16 * Kmass)
  obtain ⟨xTow, _, htower⟩ := opf_tower
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbigC_nn : (0 : ℝ) ≤ (cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
      + 2 * cbar * Kmass + 4) / 2 := by
    have h1 := mul_nonneg cbar_pos.le hK0
    have h2 := mul_nonneg cbar_pos.le hlog2pos.le
    have h3 := mul_nonneg cbar_pos.le hKmass
    nlinarith [h1, h2, h3]
  refine ⟨(cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
        + 2 * cbar * Kmass + 4) / 2,
    max (max xLv xA) (max (max xC xF)
      (max (max xP xLS) (max (max (max xW xM) xTow) (10 ^ 48)))),
    hbigC_nn, fun x hx => ?_⟩
  -- thresholds (`omega` decomposes the nested `Nat.max`)
  have hxLv : xLv ≤ x := by omega
  have hxA : xA ≤ x := by omega
  have hxC : xC ≤ x := by omega
  have hxF : xF ≤ x := by omega
  have hxP : xP ≤ x := by omega
  have hxLS : xLS ≤ x := by omega
  have hxW : xW ≤ x := by omega
  have hxM : xM ≤ x := by omega
  have hxTow : xTow ≤ x := by omega
  have hx48 : 10 ^ 48 ≤ x := by omega
  have hx48R : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx48
  have hx256 : 256 ≤ x := le_trans (by norm_num) hx48
  have hx8R : (8 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx48R
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx48R
  -- op facts
  obtain ⟨hL96, hZge, hYge, hZlog, hYlog, h1Z, h1Y, hZlog_ge, hYlog_ge⟩ := hF x hxF
  set L := Real.log x with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL96
  have hφpos : (0 : ℝ) < (opQ.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  -- geometry rows (carriers zR = x^{1/8}, yR = x^{1/3})
  obtain ⟨hx1, h2zR, hzRyR, hlogzR, hlogyR, hzNle, hzNge, hyNle, hyNge⟩ :=
    hcount_op_geometry hx256 (zR := (x : ℝ) ^ ((1 : ℝ) / 8)) (yR := (x : ℝ) ^ ((1 : ℝ) / 3))
      rfl rfl
  have hyR0 : (0 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
  -- Lval rows and AP rows
  obtain ⟨hLval3, hNsw, hLval4, hQrange⟩ := hLvalrows x hxLv
  obtain ⟨hQpos, hQa2, hQz⟩ := hAP3 x hxA
  -- L₀ facts
  set L₀ := Real.log (Lval x (opY x)) with hL₀def
  have hL₀pos : 0 < L₀ := by linarith [hLval4]
  have hlogLval := logLval_op_ge hx48R
  have hlog2lt1 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hL₀7 : L / 7 ≤ L₀ := by linarith only [hlogLval, hL96, hlog2lt1]
  have hLW : 7 * (6 * K₀ + 4 * Real.log 2) ≤ L := (hWth x hxW).2
  have hL₀ge : 6 * K₀ + 4 * Real.log 2 ≤ L₀ := by linarith only [hL₀7, hLW]
  have hLM : 16 * Kmass ≤ L := (hMth x hxM).2
  -- count bound (uniform K₀) and equidistribution
  have hcount := count_bound_uniformK hK0 hpsi₀ hx1 h2zR hzRyR hlogzR hlogyR
    hzNle hzNge hyNle hyNge hLval4
  have hequiv := hEq opQ opA x (opZ x) (opY x) hQpos hQa2 hQz hLval3 hNsw hQrange
  have hCORRle := hCORR x hxC ((x : ℝ) ^ ((1 : ℝ) / 8)) ((x : ℝ) ^ ((1 : ℝ) / 3))
    h2zR hyR0 hlogzR hlogyR
  have hP16 := hP x hxP
  obtain ⟨hcbar_t, h7pw, h2L2pw, hesw⟩ := hLS x hxLS
  -- abbreviations
  set W := (1 + 3 * K₀ / L₀) * (1 + 4 * Real.log 2 / Real.log (2 * (Lval x (opY x) : ℝ))) with hWdef
  set φ := (opQ.totient : ℝ) with hφdef
  set t := (x : ℝ) / L with htdef
  set pw := (opY x : ℝ) * (Nat.sqrt x : ℝ) with hpwdef
  set E := ecountOp
      ((cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
        + 2 * cbar * Kmass + 4) / 2) x with hEdef
  set CE := ( Ifun (x : ℝ) ((x : ℝ) ^ ((1 : ℝ) / 3)) (opZ x : ℝ) / (opZ x : ℝ)
        + Ifun (x : ℝ) ((x : ℝ) ^ ((1 : ℝ) / 3)) (opY x : ℝ) / (opY x : ℝ)
        + (21 / Real.log ((x : ℝ) ^ ((1 : ℝ) / 8)))
            * Ifun (x : ℝ) ((x : ℝ) ^ ((1 : ℝ) / 3)) ((x : ℝ) ^ ((1 : ℝ) / 8)) )
      + ∑ p₁ ∈ S1set x (opZ x) (opY x), (1 / (p₁ : ℝ))
          * ( hbjs (x : ℝ) (p₁ : ℝ) (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
                / (↑(⌊Real.sqrt ((x : ℝ) / (p₁ : ℝ))⌋₊))
              + (21 / Real.log ((x : ℝ) ^ ((1 : ℝ) / 3)))
                  * hbjs (x : ℝ) (p₁ : ℝ) (Real.sqrt ((x : ℝ) / (p₁ : ℝ))) ) with hCEdef
  -- structural facts
  have hcbar_pos := cbar_pos
  have hLval3R : (3 : ℝ) ≤ (Lval x (opY x) : ℝ) := by exact_mod_cast hLval3
  have hLvalpos : (0 : ℝ) < (Lval x (opY x) : ℝ) := by linarith [hLval3R]
  have h2Lvalpos : 0 < Real.log (2 * (Lval x (opY x) : ℝ)) :=
    Real.log_pos (by linarith [hLval3R])
  have hM₀le : L₀ ≤ Real.log (2 * (Lval x (opY x) : ℝ)) := by
    rw [hL₀def]; exact Real.log_le_log hLvalpos (by linarith [hLval3R])
  have hW_nn : 0 ≤ W := by
    rw [hWdef]
    have h1 : (0 : ℝ) ≤ 1 + 3 * K₀ / L₀ := by
      have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hK0) hL₀pos.le
      linarith only [this]
    have h2 : (0 : ℝ) ≤ 1 + 4 * Real.log 2 / Real.log (2 * (Lval x (opY x) : ℝ)) := by
      have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hlog2pos.le) h2Lvalpos.le
      linarith only [this]
    exact mul_nonneg h1 h2
  have hW2 : W ≤ 2 := by
    have hsc := slack_collapse hK0 hLval4 hM₀le
    have hle1 : (6 * K₀ + 4 * Real.log 2) / L₀ ≤ 1 := by
      rw [div_le_one hL₀pos]; exact hL₀ge
    rw [← hWdef] at hsc; linarith only [hsc, hle1]
  have hLt : L * t = (x : ℝ) := by rw [htdef]; field_simp
  have hPpair_le_pw : ((pairSet x (opZ x) (opY x)).card : ℝ) ≤ pw := by
    rw [hpwdef]; exact_mod_cast pairSet_card_le x (opZ x) (opY x)
  have hPpr_le_pw : ((pairSet' x (opZ x) (opY x)).card : ℝ) ≤ pw := by
    rw [hpwdef]
    calc ((pairSet' x (opZ x) (opY x)).card : ℝ) ≤ ((pairSet x (opZ x) (opY x)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (pairSet'_subset_pairSet x (opZ x) (opY x))
      _ ≤ (opY x : ℝ) * (Nat.sqrt x : ℝ) := by exact_mod_cast pairSet_card_le x (opZ x) (opY x)
  have hSpair_nn : 0 ≤ ∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2) :=
    Finset.sum_nonneg (fun q _ => by positivity)
  -- equidistribution → tripleSumW ≤ tripleSum/φ + E_SW
  have hTW : tripleSumW opQ opA x (opZ x) (opY x) - tripleSum x (opZ x) (opY x) / φ
      ≤ Ksw * (x : ℝ) / L₀ ^ (13 : ℝ)
          * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))
        + 2 * ((pairSet x (opZ x) (opY x)).card : ℝ) :=
    le_trans (le_abs_self _) hequiv
  -- E_SW main and boundary bounds
  have hφL : φ ≤ L := by
    have hopQL : (opQ : ℝ) ≤ L := (htower x hxTow).1
    calc φ = (opQ.totient : ℝ) := hφdef
      _ ≤ (opQ : ℝ) := by exact_mod_cast Nat.totient_le opQ
      _ ≤ L := hopQL
  have hESWmain : L * φ * (Ksw * (x : ℝ) / L₀ ^ (13 : ℝ)
        * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2)))
      ≤ Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ) := by
    have hfold := esw_main_le13 (φ := φ) (x := x) (logLval := L₀)
      (M := ∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2)) (Ksw := Ksw)
      hφL hLpos hL₀7 hSpair_nn hKsw.le hxpos.le
    have hcoef_nn : 0 ≤ Ksw * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ) :=
      div_nonneg (mul_nonneg (mul_nonneg hKsw.le (by positivity)) hxpos.le) (pow_pos hLpos 11).le
    have hmono : Ksw * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))
          * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ)
        ≤ Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ) := by
      have e1 : Ksw * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))
            * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ)
          = (Ksw * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ))
              * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2)) := by ring
      have e2 : Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ)
          = (Ksw * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ)) * 16 := by ring
      rw [e1, e2]; exact mul_le_mul_of_nonneg_left hP16 hcoef_nn
    have hcomm : L * φ * (Ksw * (x : ℝ) / L₀ ^ (13 : ℝ)
          * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2)))
        = φ * L * (Ksw * (x : ℝ) / L₀ ^ (13 : ℝ)
            * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))) := by ring
    rw [hcomm]; exact le_trans hfold hmono
  have hESWbd : L * φ * (2 * ((pairSet x (opZ x) (opY x)).card : ℝ)) ≤ 2 * L ^ 2 * pw := by
    have h1 : φ * ((pairSet x (opZ x) (opY x)).card : ℝ) ≤ L * pw :=
      mul_le_mul hφL hPpair_le_pw (Nat.cast_nonneg _) hLpos.le
    calc L * φ * (2 * ((pairSet x (opZ x) (opY x)).card : ℝ))
        = 2 * L * (φ * ((pairSet x (opZ x) (opY x)).card : ℝ)) := by ring
      _ ≤ 2 * L * (L * pw) := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hLpos.le)
      _ = 2 * L ^ 2 * pw := by ring
  -- count bound (uniform K₀) times L
  have hCORR_nn : 0 ≤ (255 * Real.log 2 + 768) / L ^ 2 := by positivity
  have hxhalf_nn : (0 : ℝ) ≤ (x : ℝ) / 2 := by positivity
  have hCR1 : L * (W * ((x : ℝ) / 2) * CE) ≤ (255 * Real.log 2 + 768) * t := by
    have hb1 : W * ((x : ℝ) / 2) * CE
          ≤ W * ((x : ℝ) / 2) * ((255 * Real.log 2 + 768) / L ^ 2) :=
      mul_le_mul_of_nonneg_left hCORRle (mul_nonneg hW_nn hxhalf_nn)
    have hb2 : W * ((x : ℝ) / 2) * ((255 * Real.log 2 + 768) / L ^ 2)
          ≤ 2 * ((x : ℝ) / 2) * ((255 * Real.log 2 + 768) / L ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW2 hxhalf_nn) hCORR_nn
    have hb3 : L * (2 * ((x : ℝ) / 2) * ((255 * Real.log 2 + 768) / L ^ 2))
          = (255 * Real.log 2 + 768) * t := by
      rw [htdef]; field_simp
    calc L * (W * ((x : ℝ) / 2) * CE)
        ≤ L * (2 * ((x : ℝ) / 2) * ((255 * Real.log 2 + 768) / L ^ 2)) :=
          mul_le_mul_of_nonneg_left (le_trans hb1 hb2) hLpos.le
      _ = (255 * Real.log 2 + 768) * t := hb3
  have hLL₀ : L / L₀ ≤ 7 := by rw [div_le_iff₀ hL₀pos]; linarith [hL₀7]
  have hPpr_nn : 0 ≤ ((pairSet' x (opZ x) (opY x)).card : ℝ) := Nat.cast_nonneg _
  have hCR2 : L * (((pairSet' x (opZ x) (opY x)).card : ℝ) / L₀) ≤ 7 * pw := by
    have heq : L * (((pairSet' x (opZ x) (opY x)).card : ℝ) / L₀)
        = (L / L₀) * ((pairSet' x (opZ x) (opY x)).card : ℝ) := by ring
    rw [heq]
    calc (L / L₀) * ((pairSet' x (opZ x) (opY x)).card : ℝ)
        ≤ 7 * ((pairSet' x (opZ x) (opY x)).card : ℝ) :=
          mul_le_mul_of_nonneg_right hLL₀ hPpr_nn
      _ ≤ 7 * pw := by linarith only [hPpr_le_pw]
  -- combine equidistribution × Lφ
  have hLtSWφ : L * tripleSumW opQ opA x (opZ x) (opY x) * φ
      ≤ L * tripleSum x (opZ x) (opY x) + Ksw * 16 * (7 : ℝ) ^ (13 : ℕ) * (x : ℝ) / L ^ (11 : ℕ)
        + 2 * L ^ 2 * pw := by
    have hmul := mul_le_mul_of_nonneg_left hTW (mul_nonneg hLpos.le hφpos.le)
    have heq1 : L * φ * (tripleSumW opQ opA x (opZ x) (opY x)
          - tripleSum x (opZ x) (opY x) / φ)
        = L * tripleSumW opQ opA x (opZ x) (opY x) * φ - L * tripleSum x (opZ x) (opY x) := by
      field_simp
    have heq2 : L * φ * (Ksw * (x : ℝ) / L₀ ^ (13 : ℝ)
            * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2))
          + 2 * ((pairSet x (opZ x) (opY x)).card : ℝ))
        = L * φ * (Ksw * (x : ℝ) / L₀ ^ (13 : ℝ)
              * (∑ q ∈ pairSet x (opZ x) (opY x), 1 / ((q.1 : ℝ) * q.2)))
          + L * φ * (2 * ((pairSet x (opZ x) (opY x)).card : ℝ)) := by ring
    linarith only [hmul, heq1, heq2, hESWmain, hESWbd]
  -- combine count × L
  have hLtS : L * tripleSum x (opZ x) (opY x)
      ≤ W * (cbar / 2) * (x : ℝ) + (255 * Real.log 2 + 768) * t + 7 * pw := by
    have hmul := mul_le_mul_of_nonneg_left hcount hLpos.le
    have hexp : L * (W * (cbar / 2) * t
          + (W * ((x : ℝ) / 2) * CE + ((pairSet' x (opZ x) (opY x)).card : ℝ) / L₀))
        = L * (W * (cbar / 2) * t) + L * (W * ((x : ℝ) / 2) * CE)
          + L * (((pairSet' x (opZ x) (opY x)).card : ℝ) / L₀) := by ring
    have heq : L * (W * (cbar / 2) * t) = W * (cbar / 2) * (x : ℝ) := by rw [← hLt]; ring
    linarith only [hmul, hexp, heq, hCR1, hCR2]
  -- the multiplicative-slack collapse `W·(c̄/2)·x ≤ (c̄/2)·x + c̄·(21K+14log2)·t`
  have h6K0nn : (0 : ℝ) ≤ 6 * K₀ + 4 * Real.log 2 := by linarith only [hK0, hlog2pos]
  have hxc_nn : (0 : ℝ) ≤ cbar / 2 * (x : ℝ) := mul_nonneg (by linarith only [cbar_pos]) hxpos.le
  have hsc := slack_collapse hK0 hLval4 hM₀le
  rw [← hWdef] at hsc
  have hslack_le : W - 1 ≤ 7 * (6 * K₀ + 4 * Real.log 2) / L := by
    have h1 : (6 * K₀ + 4 * Real.log 2) / L₀ ≤ 7 * (6 * K₀ + 4 * Real.log 2) / L := by
      rw [div_le_div_iff₀ hL₀pos hLpos]
      nlinarith only [mul_nonneg h6K0nn (by linarith only [hL₀7] : (0 : ℝ) ≤ 7 * L₀ - L)]
    linarith only [hsc, h1]
  have hWslack : W * (cbar / 2) * (x : ℝ)
      ≤ cbar / 2 * (x : ℝ) + cbar * (21 * K₀ + 14 * Real.log 2) * t := by
    have hstep : (W - 1) * (cbar / 2 * (x : ℝ)) ≤ cbar * (21 * K₀ + 14 * Real.log 2) * t := by
      calc (W - 1) * (cbar / 2 * (x : ℝ))
          ≤ 7 * (6 * K₀ + 4 * Real.log 2) / L * (cbar / 2 * (x : ℝ)) :=
            mul_le_mul_of_nonneg_right hslack_le hxc_nn
        _ = cbar * (21 * K₀ + 14 * Real.log 2) * t := by rw [htdef]; field_simp; ring
    have hexp : W * (cbar / 2) * (x : ℝ)
        = cbar / 2 * (x : ℝ) + (W - 1) * (cbar / 2 * (x : ℝ)) := by ring
    rw [hexp]; linarith only [hstep]
  -- the mass bound and `ecount` lower bound
  have hml4 : (x : ℝ) / 4 ≤ (x : ℝ) / 2 - 1 - 2 * Kmass * x / L := by
    have h1 : 2 * Kmass * (x : ℝ) / L ≤ (x : ℝ) / 8 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]
      nlinarith only [mul_le_mul_of_nonneg_left hLM hxpos.le]
    linarith only [h1, hx8R]
  have hlogopZ_pos : 0 < Real.log (opZ x : ℝ) := Real.log_pos (by linarith only [hZge, hL96])
  have hEge : 8 * ((cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
        + 2 * cbar * Kmass + 4) / 2) / L ≤ E := by
    rw [hEdef]
    simp only [ecountOp]
    rw [div_le_div_iff₀ hLpos hlogopZ_pos]
    have := mul_le_mul_of_nonneg_left hZlog hbigC_nn
    linarith only [this]
  have hEml : (cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
        + 2 * cbar * Kmass + 4) * t
      ≤ E * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L) := by
    have hEnn : 0 ≤ E := le_trans (by positivity) hEge
    have hmm := mul_le_mul hEge hml4 (by positivity) hEnn
    calc (cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
            + 2 * cbar * Kmass + 4) * t
        = 8 * ((cbar * (21 * K₀ + 14 * Real.log 2) + (255 * Real.log 2 + 768)
              + 2 * cbar * Kmass + 4) / 2) / L * ((x : ℝ) / 4) := by rw [htdef]; ring
      _ ≤ E * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L) := hmm
  have hident : cbar * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L)
      = cbar / 2 * (x : ℝ) - cbar - 2 * cbar * Kmass * t := by rw [htdef]; ring
  -- final assembly
  rw [show (cbar + E) * (((x : ℝ) / 2 - 1 - 2 * Kmass * x / L) / φ)
        = ((cbar + E) * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L)) / φ from by ring,
    le_div_iff₀ hφpos,
    show (cbar + E) * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L)
        = cbar * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L)
          + E * ((x : ℝ) / 2 - 1 - 2 * Kmass * x / L) from by ring]
  linarith only [hLtSWφ, hLtS, hWslack, hcbar_t, h7pw, hesw, h2L2pw, hident, hEml]

/-! ## Section H — the capstone: HCOUNT fully closed + the GlueNormalized chain -/

/-- **`hcount_slot_closed` — HCOUNT COMPLETE.**  Chaining `hcount_star_at_op` (the `(★)` premise)
with `hcount_massBridge` (the `/φ` normalisation + PNT lower-mass core of `CountAtOp.hcount_at_op`)
discharges the GlueNormalized `hcount` SLOT UNCONDITIONALLY past a threshold:

  `log x · tripleSumW opQ opA x (opZ x)(opY x) ≤ (cbar + ecountOp C x)·((∑ Λ)/φ(opQ))`.

The `(★)` `hcount_star_at_op` produces is exactly `hcount_at_op`'s premise
(character-for-character); `hcount_massBridge` is the `C`-agnostic core `hcount_at_op` wraps, so
this is the honest `hcount_star_at_op → hcount_at_op → SLOT` chain. -/
theorem hcount_slot_closed :
    ∃ (C : ℝ) (x₁ : ℕ), 0 ≤ C ∧ ∀ x : ℕ, x₁ ≤ x →
      Real.log x * tripleSumW opQ opA x (opZ x) (opY x)
        ≤ (cbar + ecountOp C x)
            * ((∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ)) := by
  obtain ⟨Kmass, xB, hK0, hbridge⟩ := hcount_massBridge
  obtain ⟨C, xS, hC0, hstar⟩ := hcount_star_at_op Kmass hK0
  obtain ⟨xF, hF⟩ := op_at_facts
  refine ⟨C, max (max xB xS) xF, hC0, fun x hx => ?_⟩
  have hxB : xB ≤ x := by omega
  have hxS : xS ≤ x := by omega
  have hxF : xF ≤ x := by omega
  obtain ⟨hL96, hZge, _, _, _, _, _, _, _⟩ := hF x hxF
  have hlogopZ : 0 < Real.log (opZ x : ℝ) := Real.log_pos (by linarith only [hZge, hL96])
  have hce : 0 ≤ cbar + ecountOp C x := by
    have hecnn : 0 ≤ ecountOp C x := div_nonneg hC0 hlogopZ.le
    linarith only [cbar_pos, hecnn]
  exact hbridge x hxB (ecountOp C x) hce (hstar x hxS)

/-- **The compiled chain into GlueNormalized.**  The discharged `hcount` slot (`hcount_slot_closed`)
plugs verbatim into `GlueNormalized.hmA3_normalized` — the A₃ normalized package at the operating
point.  Mirror of `CountAtOp.lean`'s slot example, now with `hcountW` *proved* (past the
threshold) rather than assumed: the full `hcount_star_at_op → hcount_at_op → GlueNormalized`
chain, compiled. -/
theorem hcount_chain_at_op :
    ∃ (C : ℝ) (x₁ : ℕ), 0 ≤ C ∧ ∀ x : ℕ, x₁ ≤ x →
      ∀ {XW Wz Wy Fv slack3 R3 rho mainA3 : ℝ},
      0 < XW → XW = (∑ n ∈ twinWindow x, vonMangoldt n) / (opQ.totient : ℝ) * Wz →
      mainA3 ≤ Real.log x * (tripleSumW opQ opA x (opZ x) (opY x) * Wy * (Fv + slack3) + R3) →
      Fv ≤ 243 / 100 → 0 ≤ Fv + slack3 → Wy ≤ Wz * rho → 0 ≤ rho → 0 ≤ Wz →
      0 ≤ Real.log x * tripleSumW opQ opA x (opZ x) (opY x) →
      mainA3 ≤ XW * (cbar * (3 / 8) * (243 / 100)
          + (((cbar + ecountOp C x) * rho * (243 / 100 + slack3) - cbar * (3 / 8) * (243 / 100))
              + Real.log x * R3 / XW)) := by
  obtain ⟨C, x₁, hC0, hslot⟩ := hcount_slot_closed
  refine ⟨C, x₁, hC0, fun x hx XW Wz Wy Fv slack3 R3 rho mainA3
    hXW hXWdef hrawA3 hcertA3 hFslack_nn hWy hrho_nn hWz_nn hLTnn => ?_⟩
  exact hmA3_normalized hXW hXWdef hrawA3 hcertA3 hFslack_nn hWy hrho_nn hWz_nn hLTnn (hslot x hx)

end Salt.Chen
