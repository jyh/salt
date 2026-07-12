/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.Defs
import Salt.TwinBar.SliceCS
import Salt.TwinBar.Tonelli

/-!
# The twin-bar rung (`twinbar`) — assembly and the headliners (nodes T5 + T6)

Design: `docs/blueprints/twinbar.md`, proof-chain steps (iii)–(vi) and nodes
T5 (`combine`) / T6 (the H1/H2/H3 assembly + `two_log_two_lt_two`). This module
lands the three Fable-frozen headliners of the flagship NEGATIVE result.

## What this rung IS (the honesty contract — read before quoting any theorem)

**Claim.** For the twin tuple `{0, 2}` (`k = 2`), the Maynard–Selberg variational
gate `θ·(J₁ + J₂) > 2·I₂` is unsatisfiable by ANY continuous weight `F` at ANY
level of distribution `θ ≤ 1` — because
`J₁ F + J₂ F ≤ 2·log 2·I₂ F` (`twin_bar`) and `2·log 2 < 2`
(`two_log_two_lt_two`). This is Polymath8b (arXiv:1407.4897) Lemma 6.1 + Cor. 6.4
specialised to `k = 2`.

**What it does NOT claim.** It does NOT say "sieves cannot prove twin primes."
Parity-breaking inputs — bilinear / type-II information à la Friedlander–Iwaniec,
Chen's switching — MODIFY the underlying functional, and this bound does not apply
to a modified functional. The theorem certifies the exact boundary of the
UNMODIFIED Maynard class: no better `F`, and no better equidistribution level `θ`,
can cross it.

**The duality.** This is the negative dual of the landed `M5_cert`
(`2·Ical Fstar < Σ Jcal m Fstar`, `k = 5`) and `theta_ratio_cert`: same
variational framework, both directions machine-checked — what the method CAN do
(gaps ≤ 12, ≤ C modulo Siegel–Walfisz) and what it CANNOT (twins, ever). The
strict `<` guarded by `0 < I₂ F` in `no_twin_weight` is the exact `k = 2` analogue
of `M5_cert`'s shape.

**Scope remarks (from the blueprint's verify pass).**
* (a) The theorems are per-`F` bounds over CONTINUOUS `F`; Polymath8b's `M₂`
  (eq. 33) is an `L²`-sup. The standard density bridge upgrades a continuous-`F`
  bound to the sup; we state the artifact "over continuous weights" and leave the
  `L²`-sup as a possible later strengthening, NOT part of the floor.
* (b) `twin_gate_fails` (H2) covers `θ = 1`, a SUPERSET of Theorem 3.8's `ϑ < 1`
  range — strictly stronger, and NOT an assertion that `ϑ = 1` is an admissible
  EH level (EH[1] is false).
* (c) `Poly`-class membership holds in spirit (polynomials are continuous); the
  formal machine connection is node T7, excluded from this rung.

## The assembly (proof-chain steps iii–vi)

* (iii)/(iv) `sliceCS₁`/`sliceCS₂` (node T3) bound each slice; integrating in the
  outer variable gives `J₁ F ≤ log 2·∬ w₁·F²` and `J₂ F ≤ log 2·∬ w₂·F²`, the
  second in the `t₁`-outer order. Integrability of the RHS marginals comes from
  Fubini (`marginal₁_integrableOn`); the LHS square never needs an integrability
  side-condition because we integrate with `integral_mono_of_nonneg` (only the
  larger, integrable side is required).
* `simplex_swap` (node T4) turns the `J₂` bound's `t₁`-outer double integral into
  the `t₂`-outer order.
* (v) `w₁ + w₂ ≡ 2` collapses `∬ w₁·F² + ∬ w₂·F² = ∬ 2·F² = 2·I₂` (`combine`).
* (vi) `2·log 2 < 2` via `Real.log_lt_sub_one_of_pos` at `2`.
-/

namespace Salt.TwinBar

open MeasureTheory Set Function

/-! ## Geometry of the closed simplex (re-derived locally; Tonelli's are private) -/

/-- The closed simplex `R₂` is closed. -/
private theorem R₂_isClosed' : IsClosed R₂ := by
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
  exact isClosed_le (continuous_fst.add continuous_snd) continuous_const

/-- The closed simplex `R₂` is compact. -/
private theorem R₂_isCompact' : IsCompact R₂ := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := ((0:ℝ), (0:ℝ))) (b := ((1:ℝ), (1:ℝ))))
    R₂_isClosed'
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hp
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩ <;> simp <;> linarith

/-- The closed simplex `R₂` is measurable. -/
private theorem R₂_measurableSet' : MeasurableSet R₂ := R₂_isClosed'.measurableSet

/-! ## Parametric integrability of the slice marginals (Fubini route)

For a jointly continuous integrand on the compact simplex, the parameterised inner
integral is integrable in the outer variable over `Ioc 0 1`. We route through the
2-D indicator `R₂.indicator (uncurry G)` — integrable on the plane by compactness
(`ContinuousOn.integrableOn_compact'`) — whose Fubini marginal
(`Integrable.integral_prod_right` / `_left`) is integrable over all of `ℝ`, hence
over `Ioc 0 1`; on `[0,1]` that marginal equals the interval integral because the
plane slice's `R₂`-preimage is exactly `Icc 0 (1 − ·)`. -/

/-- **`t₂`-outer marginal integrability.** For `G` continuous on `R₂`, the map
`t₂ ↦ ∫ t₁ in 0..(1 − t₂), G t₁ t₂` is integrable on `Ioc 0 1`. -/
private theorem marginal₁_integrableOn {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (Function.uncurry G) R₂) :
    IntegrableOn (fun t₂ => ∫ t₁ in (0:ℝ)..(1 - t₂), G t₁ t₂) (Set.Ioc 0 1) volume := by
  set H : ℝ × ℝ → ℝ := R₂.indicator (Function.uncurry G) with hH
  have hInt : Integrable H (volume.prod volume) := by
    rw [hH, integrable_indicator_iff R₂_measurableSet']
    exact ContinuousOn.integrableOn_compact' R₂_isCompact' R₂_measurableSet' hG
  have hm : IntegrableOn (fun t₂ => ∫ t₁, H (t₁, t₂)) (Set.Ioc 0 1) volume :=
    hInt.integral_prod_right.integrableOn
  refine hm.congr_fun (fun t₂ ht₂ => ?_) measurableSet_Ioc
  obtain ⟨ht0, ht1⟩ := ht₂
  have hmeas : MeasurableSet ((fun t₁ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) :=
    R₂_measurableSet'.preimage (by fun_prop)
  have hrw : (fun t₁ => H (t₁, t₂))
      = ((fun t₁ => (t₁, t₂)) ⁻¹' R₂).indicator (fun t₁ => G t₁ t₂) := by
    funext t₁
    rw [hH, ← Set.indicator_comp_right (fun t₁ => ((t₁ : ℝ), t₂))]
    rfl
  have hpre : ((fun t₁ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) = Set.Icc 0 (1 - t₂) := by
    ext t₁
    simp only [Set.mem_preimage, R₂, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨ha, _, hc⟩; exact ⟨ha, by linarith⟩
    · rintro ⟨ha, hb⟩; exact ⟨ha, le_of_lt ht0, by linarith⟩
  change (∫ t₁, H (t₁, t₂)) = ∫ t₁ in (0:ℝ)..(1 - t₂), G t₁ t₂
  rw [hrw, integral_indicator hmeas, hpre, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₂)]

/-- **`t₁`-outer marginal integrability.** For `G` continuous on `R₂`, the map
`t₁ ↦ ∫ t₂ in 0..(1 − t₁), G t₁ t₂` is integrable on `Ioc 0 1`. -/
private theorem marginal₂_integrableOn {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (Function.uncurry G) R₂) :
    IntegrableOn (fun t₁ => ∫ t₂ in (0:ℝ)..(1 - t₁), G t₁ t₂) (Set.Ioc 0 1) volume := by
  set H : ℝ × ℝ → ℝ := R₂.indicator (Function.uncurry G) with hH
  have hInt : Integrable H (volume.prod volume) := by
    rw [hH, integrable_indicator_iff R₂_measurableSet']
    exact ContinuousOn.integrableOn_compact' R₂_isCompact' R₂_measurableSet' hG
  have hm : IntegrableOn (fun t₁ => ∫ t₂, H (t₁, t₂)) (Set.Ioc 0 1) volume :=
    hInt.integral_prod_left.integrableOn
  refine hm.congr_fun (fun t₁ ht₁ => ?_) measurableSet_Ioc
  obtain ⟨ht0, ht1⟩ := ht₁
  have hmeas : MeasurableSet ((fun t₂ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) :=
    R₂_measurableSet'.preimage (by fun_prop)
  have hrw : (fun t₂ => H (t₁, t₂))
      = ((fun t₂ => (t₁, t₂)) ⁻¹' R₂).indicator (fun t₂ => G t₁ t₂) := by
    funext t₂
    rw [hH, ← Set.indicator_comp_right (fun t₂ => ((t₁ : ℝ), t₂))]
    rfl
  have hpre : ((fun t₂ => ((t₁ : ℝ), t₂)) ⁻¹' R₂) = Set.Icc 0 (1 - t₁) := by
    ext t₂
    simp only [Set.mem_preimage, R₂, Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · rintro ⟨_, hb, hc⟩; exact ⟨hb, by linarith⟩
    · rintro ⟨ha, hb⟩; exact ⟨le_of_lt ht0, ha, by linarith⟩
  change (∫ t₂, H (t₁, t₂)) = ∫ t₂ in (0:ℝ)..(1 - t₁), G t₁ t₂
  rw [hrw, integral_indicator hmeas, hpre, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1 - t₁)]

/-! ## The numeric atom -/

/-- **`2·log 2 < 2`** (proof-chain step (vi)). Since `log 2 < 2 − 1 = 1`. -/
theorem two_log_two_lt_two : 2 * Real.log 2 < 2 := by
  have h : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    linarith
  linarith

/-! ## H1 — the mathematical keystone -/

/-- **H1, `twin_bar`.** For every continuous weight `F` on the simplex,
`J₁ F + J₂ F ≤ 2·log 2·I₂ F`. This is the Polymath8b `k = 2` bound: two per-slice
Cauchy–Schwarz estimates (`sliceCS₁`/`sliceCS₂`), one simplex Tonelli swap
(`simplex_swap`), and the magic identity `w₁ + w₂ ≡ 2`. -/
theorem twin_bar (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) R₂) :
    J₁ F + J₂ F ≤ 2 * Real.log 2 * I₂ F := by
  -- Joint continuity of the two weighted-square integrands on the simplex.
  have hcont₁ : ContinuousOn (Function.uncurry (fun t₁ t₂ => w₁ t₁ t₂ * (F t₁ t₂) ^ 2)) R₂ := by
    have h : Function.uncurry (fun t₁ t₂ => w₁ t₁ t₂ * (F t₁ t₂) ^ 2)
          = fun p : ℝ × ℝ => Function.uncurry w₁ p * (Function.uncurry F p) ^ 2 := rfl
    rw [h]; exact w₁_continuous.continuousOn.mul (hF.pow 2)
  have hcont₂ : ContinuousOn (Function.uncurry (fun t₁ t₂ => w₂ t₁ t₂ * (F t₁ t₂) ^ 2)) R₂ := by
    have h : Function.uncurry (fun t₁ t₂ => w₂ t₁ t₂ * (F t₁ t₂) ^ 2)
          = fun p : ℝ × ℝ => Function.uncurry w₂ p * (Function.uncurry F p) ^ 2 := rfl
    rw [h]; exact w₂_continuous.continuousOn.mul (hF.pow 2)
  -- Outer-integrability of the two `t₂`-outer marginals (for the combine step).
  have hB₁_ii : IntervalIntegrable
      (fun t₂ => ∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr
      (marginal₁_integrableOn hcont₁)
  have hB₂'_ii : IntervalIntegrable
      (fun t₂ => ∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mpr
      (marginal₁_integrableOn hcont₂)
  -- Step (iii): `J₁ F ≤ log 2 · ∬ w₁·F²`.
  have hJ1 : J₁ F
      ≤ Real.log 2 * ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₁
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₂ => sq_nonneg _)
    · exact (marginal₁_integrableOn hcont₁).const_mul (Real.log 2)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t₂ ht₂ => sliceCS₁ F hF (le_of_lt ht₂.1) ht₂.2)
  -- Step (iv), `t₁`-outer: `J₂ F ≤ log 2 · ∬ w₂·F²` (t₁ outer).
  have hJ2' : J₂ F
      ≤ Real.log 2 * ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), w₂ t₁ t₂ * (F t₁ t₂) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    unfold J₂
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun t₁ => sq_nonneg _)
    · exact (marginal₂_integrableOn hcont₂).const_mul (Real.log 2)
    · exact ae_restrict_of_forall_mem measurableSet_Ioc
        (fun t₁ ht₁ => sliceCS₂ F hF (le_of_lt ht₁.1) ht₁.2)
  -- The one Tonelli swap: land the `J₂` bound in the `t₂`-outer order.
  have hswap : (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2)
      = ∫ t₁ in (0:ℝ)..1, ∫ t₂ in (0:ℝ)..(1 - t₁), w₂ t₁ t₂ * (F t₁ t₂) ^ 2 :=
    simplex_swap (fun t₁ t₂ => w₂ t₁ t₂ * (F t₁ t₂) ^ 2) hcont₂
  have hJ2 : J₂ F
      ≤ Real.log 2 * ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2 := by
    rw [hswap]; exact hJ2'
  -- Step (v): `∬ w₁·F² + ∬ w₂·F² = 2·I₂` via `w₁ + w₂ ≡ 2`.
  have hcomb : (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2)
      + (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2)
      = 2 * I₂ F := by
    calc (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2)
          + (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2)
        = ∫ t₂ in (0:ℝ)..1, ((∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2)
            + (∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2)) :=
          (intervalIntegral.integral_add hB₁_ii hB₂'_ii).symm
      _ = ∫ t₂ in (0:ℝ)..1, 2 * ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2 := by
          refine intervalIntegral.integral_congr (fun t₂ ht₂ => ?_)
          rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht₂
          obtain ⟨h0, h1⟩ := ht₂
          have hw₂slice : Continuous (fun t₁ => w₂ t₁ t₂) := by unfold w₂; fun_prop
          rw [← intervalIntegral.integral_add
                (slice₁_weight_sq_intervalIntegrable hF h0 h1 (w₁_slice_continuous t₂))
                (slice₁_weight_sq_intervalIntegrable hF h0 h1 hw₂slice),
            ← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_congr (fun t₁ _ => by rw [← add_mul, w₁_add_w₂])
      _ = 2 * ∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), (F t₁ t₂) ^ 2 :=
          intervalIntegral.integral_const_mul 2 _
      _ = 2 * I₂ F := rfl
  -- Combine: `J₁ + J₂ ≤ log 2·(∬ w₁·F² + ∬ w₂·F²) = log 2·(2·I₂) = 2·log 2·I₂`.
  have hfinal : Real.log 2 * (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₁ t₁ t₂ * (F t₁ t₂) ^ 2)
      + Real.log 2 * (∫ t₂ in (0:ℝ)..1, ∫ t₁ in (0:ℝ)..(1 - t₂), w₂ t₁ t₂ * (F t₁ t₂) ^ 2)
      = 2 * Real.log 2 * I₂ F := by
    rw [← mul_add, hcomb]; ring
  linarith [hJ1, hJ2, hfinal]

/-! ## H2 — the `θ`-parameterised gate failure -/

set_option linter.unusedVariables false in
/-- **H2, `twin_gate_fails`.** At every level of distribution `θ ≤ 1` (including
`θ = 1`), `θ·(J₁ F + J₂ F) ≤ 2·I₂ F`: the Selberg functional never reaches the twin
gate. Uses `twin_bar` and `2·log 2 < 2`, with `0 ≤ J₁ + J₂` and `0 ≤ I₂`. The
frozen hypothesis `hθ0 : 0 < θ` is retained for interface fidelity with
`theta_ratio_cert` but is not consumed (the bound holds for every `θ ≤ 1`); the
`unusedVariables` linter is silenced locally to keep the statement byte-faithful. -/
theorem twin_gate_fails (F : ℝ → ℝ → ℝ) (hF : ContinuousOn (Function.uncurry F) R₂)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    θ * (J₁ F + J₂ F) ≤ 2 * I₂ F := by
  have hbar := twin_bar F hF
  nlinarith [hbar,
    mul_nonneg (sub_nonneg.mpr hθ1) (add_nonneg (J₁_nonneg F) (J₂_nonneg F)),
    mul_nonneg (by linarith [two_log_two_lt_two] : (0:ℝ) ≤ 2 - 2 * Real.log 2) (I₂_nonneg F)]

/-! ## H3 — the headline impossibility -/

/-- **H3, `no_twin_weight`.** There is NO continuous weight `F` with positive
`L²`-mass whose Selberg pair `J₁ + J₂` exceeds twice its mass: the strict twin gate
`2·I₂ F < J₁ F + J₂ F` (with `0 < I₂ F`) is unsatisfiable. This is the dual of
`M5_cert`'s existence result — for the twin tuple the gate can never be crossed. -/
theorem no_twin_weight :
    ¬ ∃ F : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry F) R₂ ∧
      0 < I₂ F ∧ 2 * I₂ F < J₁ F + J₂ F := by
  rintro ⟨F, hF, hI, hlt⟩
  have hbar := twin_bar F hF
  nlinarith [hbar, hlt,
    mul_pos (show (0:ℝ) < 2 - 2 * Real.log 2 by linarith [two_log_two_lt_two]) hI]

end Salt.TwinBar
