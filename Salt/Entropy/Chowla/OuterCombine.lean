/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The outer Fubini assembly (Tao 1509.05422 p. 22, (2.11) → (3.15)/(3.16)), spine node W3-a-3c

The final analytic node of the log-Chowla spine's wave 3.  It combines every
landed ingredient into Tao's p.22 chain: from the Chowla-failure DOOR input
`(2.11)` (an explicit hypothesis `h211`) to the decoupled two-point-correlation
lower bound `(3.15)/(3.16)`.

Route (the design's five steps, `docs/exploration/s3-a3-design.md`):

1. The deviation `|F(x₀, y) − decoupledMean(x₀)|` is bounded pointwise by
   `δ + 2·boxGrade·1_{badSet}` where `δ = ε²H/log H` is the calibration
   threshold and `boxGrade` is the deterministic `H/log H`-grade box.
2. Its outer expectation over `logMeasure` is `≤ δ + 2·boxGrade·(bad-event mass)`.
3. The bad-event mass disintegrates over the fibres of `X = liouvilleWindow`
   (`map_compProd_condDistrib` + `integral_compProd`) into the `μ.map X`-average
   of the CONDITIONAL bad-set mass, which the transport
   (`badSet_transport_at_calibration`) bounds on the good fibres and the Markov
   selection (`decrement_markov_fintype`) confines the bad fibres to small mass.
4. The deterministic box `|F| ≤ Σ_p (H/p + 1) ≤ boxGrade` (this file's
   `fBridgeF_abs_le_box`, via `primeWindow_card_le_of_regime` + `window_lb`); the
   decoupled mean obeys the same box.
5. Triangle-inequality against `h211` gives the conclusion.
-/
import Salt.Entropy.Chowla.Transport
import Salt.Entropy.Chowla.WindowCount
import Salt.Entropy.Chowla.MarkovExtract
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Salt.Entropy.Chowla

/-! ## The deterministic box (design step 4) -/

/-- The `H/log H`-grade deterministic box constant for the F-bridge and its
decoupled mean at a `‖·‖ ≤ 1` window pattern: `2·log 4·(2 + ε²)·(H/log H)`. -/
noncomputable def boxGrade (eps : ℚ) (H : ℕ) : ℝ :=
  2 * Real.log 4 * (2 + (eps : ℝ) ^ 2) * ((H : ℝ) / Real.log (H : ℝ))

/-- **The F-bridge box, raw sum form.**  For a `‖·‖ ≤ 1` pattern `v`, the F-bridge
is bounded by `Σ_{p ∈ 𝒫_H} (H/p + 1)`: triangle over the per-prime components plus
`fBridgeG_abs_le`. -/
lemma fBridgeF_abs_le_boxSum (eps : ℚ) (H : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (y : ZMod (PH eps H)) :
    |fBridgeF eps H v y| ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  unfold fBridgeF
  calc |∑ p : primeWindow eps H, fBridgeG eps H v p (residueProj eps H p y)|
      ≤ ∑ p : primeWindow eps H, |fBridgeG eps H v p (residueProj eps H p y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) :=
        Finset.sum_le_sum (fun p _ => fBridgeG_abs_le eps H hv p _)

/-- **The decoupled-mean box, raw sum form.**  The two-point correlation
`Σ_p (1/p) Σ_j v_j v_{j+p}` obeys the same `Σ_p (H/p + 1)` box (each inner sum has
`≤ H` unit-bounded terms). -/
lemma decoupledMean_abs_le_boxSum (eps : ℚ) (H : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)|
      ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
  have hinner : |∑ j ∈ Finset.range H,
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)| ≤ (H : ℝ) := by
    calc |∑ j ∈ Finset.range H, (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)|
        ≤ ∑ j ∈ Finset.range H, |(windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range H, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => windowVal_prod_abs_le hv j _)
      _ = (H : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
  have hstep : 1 / (p : ℝ) * |∑ j ∈ Finset.range H,
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)| ≤ 1 / (p : ℝ) * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hinner (by positivity)
  have hHp : 1 / (p : ℝ) * (H : ℝ) = (H : ℝ) / (p : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
  rw [hHp] at hstep; linarith

/-- **The box sum at the `H/log H` grade** (design step 4, the PNT input).  Under the
regime `√H ≤ ε²H/2` (feeding `primeWindow_card_le_of_regime`, `C₀ = 2·log 4`) and
`3 ≤ H`, the raw box `Σ_p (H/p + 1)` is `≤ boxGrade = 2·log 4·(2 + ε²)·(H/log H)`: each
window prime `p > ε²H/2` gives `H/p + 1 ≤ 2/ε² + 1`, and `|𝒫_H| ≤ 2·log 4·ε²H/log H`. -/
lemma boxSum_le_grade (eps : ℚ) (H : ℕ) (heps : 0 < eps)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H) :
    ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) ≤ boxGrade eps H := by
  have he : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have heps2 : (0 : ℝ) < (eps : ℝ) ^ 2 := by positivity
  have hene : (eps : ℝ) ≠ 0 := he.ne'
  have hB0 : (0 : ℝ) ≤ 2 / (eps : ℝ) ^ 2 + 1 := by positivity
  have hHR : (3 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlogpos : 0 < Real.log (H : ℝ) := Real.log_pos (by linarith)
  have hterm : ∀ p : primeWindow eps H, (H : ℝ) / (p : ℝ) + 1 ≤ 2 / (eps : ℝ) ^ 2 + 1 := by
    intro p
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
    have hle : (H : ℝ) / (p : ℝ) ≤ 2 / (eps : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hp0 heps2]; nlinarith [window_lb eps H p]
    linarith
  have hcard := primeWindow_card_le_of_regime eps H hreg hH
  calc ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1)
      ≤ ∑ _p : primeWindow eps H, (2 / (eps : ℝ) ^ 2 + 1) := Finset.sum_le_sum (fun p _ => hterm p)
    _ = ((primeWindow eps H).card : ℝ) * (2 / (eps : ℝ) ^ 2 + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (2 * Real.log 4) * ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)) * (2 / (eps : ℝ) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right hcard hB0
    _ = boxGrade eps H := by unfold boxGrade; field_simp

/-- **The F-bridge box** (design step 4).  `|F(v)(y)| ≤ boxGrade`. -/
lemma fBridgeF_abs_le_box (eps : ℚ) (H : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (y : ZMod (PH eps H)) :
    |fBridgeF eps H v y| ≤ boxGrade eps H :=
  (fBridgeF_abs_le_boxSum eps H hv y).trans (boxSum_le_grade eps H heps hreg hH)

/-- **The decoupled-mean box** (design step 4).  The two-point correlation `≤ boxGrade`. -/
lemma decoupledMean_abs_le_box (eps : ℚ) (H : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ)) : ℝ)|
      ≤ boxGrade eps H :=
  (decoupledMean_abs_le_boxSum eps H hv).trans (boxSum_le_grade eps H heps hreg hH)

/-! ### The same boxes at shift `h` (W-F3 wave A)

`boxGrade` and `boxSum_le_grade` never read the offset — they are statements about the
window primes alone — so the shift-`h` bridge `fBridgeF_h` and its decoupled mean inherit the
`H/log H`-grade box verbatim, with `fBridgeG_h_abs_le` in place of `fBridgeG_abs_le` and
`windowVal_prod_abs_le` (offset-blind) doing the inner work.  Nothing here is `h`-specific;
that is exactly why this part of the `h`-port is a transport and not a re-derivation. -/

/-- **The F-bridge box at shift `h`, raw sum form.**  `|F_h(v)(y)| ≤ Σ_{p ∈ 𝒫_H} (H/p + 1)`. -/
lemma fBridgeF_h_abs_le_boxSum (eps : ℚ) (H h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (y : ZMod (PH eps H)) :
    |fBridgeF_h eps H h v y| ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  unfold fBridgeF_h
  calc |∑ p : primeWindow eps H, fBridgeG_h eps H h v p (residueProj eps H p y)|
      ≤ ∑ p : primeWindow eps H, |fBridgeG_h eps H h v p (residueProj eps H p y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) :=
        Finset.sum_le_sum (fun p _ => fBridgeG_h_abs_le eps H h hv p _)

/-- **The decoupled-mean box at shift `h`, raw sum form.**  The shifted two-point correlation
`Σ_p (1/p) Σ_j v_j v_{j+p·h}` obeys the same `Σ_p (H/p + 1)` box: the inner sum still has `≤ H`
unit-bounded terms, and the unit bound `windowVal_prod_abs_le` does not see the offset. -/
lemma decoupledMean_h_abs_le_boxSum (eps : ℚ) (H h : ℕ) {v : Fin H → ℤ}
    (hv : ∀ i, |v i| ≤ 1) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)|
      ≤ ∑ p : primeWindow eps H, ((H : ℝ) / (p : ℝ) + 1) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ => ?_))
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (prime_of_mem_primeWindow p.2).pos
  have hinner : |∑ j ∈ Finset.range H,
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)| ≤ (H : ℝ) := by
    calc |∑ j ∈ Finset.range H,
          (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)|
        ≤ ∑ j ∈ Finset.range H,
            |(windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range H, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => windowVal_prod_abs_le hv j _)
      _ = (H : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (p : ℝ))]
  have hstep : 1 / (p : ℝ) * |∑ j ∈ Finset.range H,
      (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)| ≤ 1 / (p : ℝ) * (H : ℝ) :=
    mul_le_mul_of_nonneg_left hinner (by positivity)
  have hHp : 1 / (p : ℝ) * (H : ℝ) = (H : ℝ) / (p : ℝ) := by rw [div_mul_eq_mul_div, one_mul]
  rw [hHp] at hstep; linarith

/-- **The F-bridge box at shift `h`**: `|F_h(v)(y)| ≤ boxGrade`, the `h = 1` grade unchanged. -/
lemma fBridgeF_h_abs_le_box (eps : ℚ) (H h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (y : ZMod (PH eps H)) :
    |fBridgeF_h eps H h v y| ≤ boxGrade eps H :=
  (fBridgeF_h_abs_le_boxSum eps H h hv y).trans (boxSum_le_grade eps H heps hreg hH)

/-- **The decoupled-mean box at shift `h`**: the shifted two-point correlation `≤ boxGrade`. -/
lemma decoupledMean_h_abs_le_box (eps : ℚ) (H h : ℕ) {v : Fin H → ℤ} (hv : ∀ i, |v i| ≤ 1)
    (heps : 0 < eps) (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H) :
    |∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
        (windowVal H v j : ℝ) * (windowVal H v (j + (p : ℕ) * h) : ℝ)|
      ≤ boxGrade eps H :=
  (decoupledMean_h_abs_le_boxSum eps H h hv).trans (boxSum_le_grade eps H heps hreg hH)

/-! ## The bad-event disintegration (design step 3) -/

/-- **The outer bad-event mass disintegrates over the fibres of the window.**
The `logMeasure`-probability that the residue `y = residueWindow n` lands in the
`x₀ = liouvilleWindow n`-deviation set equals the `μ.map X`-average of the
CONDITIONAL bad-set mass.  `map_compProd_condDistrib` factorises the joint law and
`integral_compProd` integrates the badSet indicator fibrewise. -/
lemma outer_badMass_eq (eps : ℚ) (H : ℕ) (x ω : ℕ)
    [IsProbabilityMeasure (logMeasure x ω)] (δ : ℝ) :
    (logMeasure x ω).real
        {n | residueWindow eps H n ∈ badSet eps H (liouvilleWindow H n) δ}
      = ∫ x₀, ((condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
          ↑(badSet eps H x₀ δ)) ∂((logMeasure x ω).map (liouvilleWindow H)) := by
  classical
  set μ := logMeasure x ω
  set X := liouvilleWindow H
  set Y := residueWindow eps H
  set cd := condDistrib Y X μ
  set W := fun n => (X n, Y n) with hW
  set S : Set ((Fin H → ℤ) × ZMod (PH eps H)) := {p | p.2 ∈ badSet eps H p.1 δ} with hS
  have hXmeas : Measurable X := measurable_liouvilleWindow H
  have hYmeas : Measurable Y := measurable_residueWindow eps H
  have hWmeas : Measurable W := hXmeas.prodMk hYmeas
  have hSmeas : MeasurableSet S := (Set.to_countable _).measurableSet
  have hAeq : {n | Y n ∈ badSet eps H (X n) δ} = W ⁻¹' S := rfl
  have hρ : μ.map W = μ.map X ⊗ₘ cd := (map_compProd_condDistrib hYmeas hXmeas μ).symm
  haveI hpW : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hWmeas.aemeasurable
  haveI hpC : IsProbabilityMeasure (μ.map X ⊗ₘ cd) := hρ ▸ hpW
  have hint : Integrable (S.indicator 1) (μ.map X ⊗ₘ cd) :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  calc μ.real {n | Y n ∈ badSet eps H (X n) δ}
      = (μ.map W).real S := by
        rw [hAeq]; simp only [measureReal_def, Measure.map_apply hWmeas hSmeas]
    _ = (μ.map X ⊗ₘ cd).real S := by rw [hρ]
    _ = ∫ p, S.indicator 1 p ∂(μ.map X ⊗ₘ cd) := (integral_indicator_one hSmeas).symm
    _ = ∫ x₀, ∫ y, S.indicator 1 (x₀, y) ∂(cd x₀) ∂(μ.map X) :=
        MeasureTheory.Measure.integral_compProd hint
    _ = ∫ x₀, (cd x₀).real ↑(badSet eps H x₀ δ) ∂(μ.map X) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x₀ => ?_))
        change ∫ y, S.indicator 1 (x₀, y) ∂(cd x₀) = (cd x₀).real ↑(badSet eps H x₀ δ)
        rw [← integral_indicator_one (μ := cd x₀)
          (s := (↑(badSet eps H x₀ δ) : Set (ZMod (PH eps H))))
          ((Set.to_countable _).measurableSet)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp only [Set.indicator_apply, Set.mem_setOf_eq, hS, Finset.mem_coe, Pi.one_apply]

/-! ## The bad-event mass bound (design steps 2–3, W3-a-3a/3b folded in) -/

/-- **The disintegrated bad-event mass is small.**  The `μ.map X`-average of the
conditional bad-set mass (at the calibration threshold `δ = ε²H/log H`) is bounded
by `(t + 2 log 2)/g + (κ + (log P_H − H[Y]))/t`: on the good fibres
(`H[Y] − Hm[cd x₀] ≤ t`) the transport `badSet_transport_at_calibration` gives the
conditional bound `(t + 2 log 2)/g` (using `8 P_H² ω ≤ x`, `pH_headroom_at`, to cap
the (3.9) deficiency `log(1 + 8 P_H² ω/x) ≤ log 2`); the bad fibres are confined to
`μ.map X`-mass `≤ (κ + (log P_H − H[Y]))/t` by the Markov selection
`decrement_markov_fintype`. -/
lemma outer_badMass_le (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ}
    (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasure x ω] ≤ κ) :
    ∫ x₀, ((condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
        ↑(badSet eps H x₀ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))))
          ∂((logMeasure x ω).map (liouvilleWindow H))
      ≤ (t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasure x ω])) / t := by
  classical
  set μ := logMeasure x ω
  set X := liouvilleWindow H
  set Y := residueWindow eps H
  set cd := condDistrib Y X μ with hcd
  set δcal := (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) with hδcal
  set baddef : Set (Fin H → ℤ) := {x₀ | t < H[Y; μ] - Hm[cd x₀]} with hbaddef
  set β := (t + 2 * Real.log 2) / g with hβ
  have hXmeas : Measurable X := measurable_liouvilleWindow H
  have hYmeas : Measurable Y := measurable_residueWindow eps H
  haveI hpX : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  have hbaddef_meas : MeasurableSet baddef := (Set.to_countable _).measurableSet
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hC₀ : (0 : ℝ) < 2 * Real.log 4 := by positivity
  have hcard := primeWindow_card_le_of_regime eps H hreg hH
  -- (3.9) deficiency cap: log(1 + 8 P²ω/x) ≤ log 2
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hcorr : Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    have : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) ≤ 1 := (div_le_one hxpos).mpr hhead
    linarith
  -- a.e. the window pattern is ±1-valued
  have hae : ∀ᵐ x₀ ∂(μ.map X), ∀ i, |x₀ i| ≤ 1 := by
    rw [ae_iff, Measure.map_apply hXmeas ((Set.to_countable _).measurableSet)]
    have hpre : X ⁻¹' {x₀ : Fin H → ℤ | ¬ ∀ i, |x₀ i| ≤ 1} = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun i => abs_liouvilleWindow_le_one H n i
    rw [hpre, measure_empty]
  -- the pointwise a.e. bound
  have hbound : ∀ᵐ x₀ ∂(μ.map X),
      (cd x₀).real ↑(badSet eps H x₀ δcal) ≤ β + baddef.indicator 1 x₀ := by
    filter_upwards [hae] with x₀ hx₀le
    haveI : IsProbabilityMeasure (cd x₀) := by rw [hcd]; infer_instance
    by_cases hgood : H[Y; μ] - Hm[cd x₀] ≤ t
    · -- good fibre: transport + deficiency cap
      have hnotmem : x₀ ∉ baddef := by
        rw [hbaddef]; simp only [Set.mem_setOf_eq, not_lt]; exact hgood
      rw [Set.indicator_of_notMem hnotmem, add_zero]
      have htrans := badSet_transport_at_calibration eps H hx hω hωx hx₀le heps heps1 hne hC₀
        hcard hlog ht.le hgood hg hgle
      refine htrans.trans ?_
      rw [hβ]
      exact div_le_div_of_nonneg_right (by linarith [hcorr]) hg.le
    · -- bad fibre: probability ≤ 1 ≤ β + 1
      have hmem : x₀ ∈ baddef := by
        rw [hbaddef]; simp only [Set.mem_setOf_eq]; exact lt_of_not_ge hgood
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      calc (cd x₀).real ↑(badSet eps H x₀ δcal) ≤ 1 := measureReal_le_one
        _ ≤ β + 1 := by linarith
  -- integrate the a.e. bound
  have hbadmass : (μ.map X).real baddef
      ≤ (κ + (Real.log (PH eps H : ℝ) - H[Y; μ])) / t := by
    have hdm := decrement_markov_fintype (β := ZMod (PH eps H)) hXmeas hYmeas ht hI
    rwa [ZMod.card] at hdm
  calc ∫ x₀, (cd x₀).real ↑(badSet eps H x₀ δcal) ∂(μ.map X)
      ≤ ∫ x₀, (β + baddef.indicator 1 x₀) ∂(μ.map X) :=
        integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _) hbound
    _ = β + (μ.map X).real baddef := by
        rw [integral_add (integrable_const β) (integrable_of_finiteSupport _),
          integral_const, integral_indicator_one hbaddef_meas, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (t + 2 * Real.log 2) / g
        + (κ + (Real.log (PH eps H : ℝ) - H[Y; μ])) / t := by rw [← hβ]; linarith [hbadmass]

/-! ## The keystone (design step 5): the (2.11) → (3.15)/(3.16) combine -/

/-- **W3-a-3c, the outer Fubini assembly** (Tao 1509.05422 p.22, `(2.11) → (3.15)/(3.16)`).
From the Chowla-failure DOOR input `h211` (the (2.11)-model lower bound on the outer
mean of the F-bridge) the decoupled two-point correlation carries a lower bound of the
same `ε·H/log H` grade, up to an explicit error.

The error `ERROR = ε²H/log H + 2·boxGrade·((t + 2 log 2)/g + (κ + (log P_H − H[Y]))/t)`
is `≤ (c₁ − O(ε))·εH/log H` once the tower selects the budgets `t`, `κ`, `g` at Tao's
grade: `ε²H/log H = ε·(εH/log H)`, `boxGrade = Θ(H/log H)`, and the good/bad budgets
`(t + 2 log 2)/g`, `(κ + (log P_H − H[Y]))/t` are `o(ε)` in the regime (see the design
note; the budgets are downstream, hypothesis-parametric, discharged by W3-e).

Chain: (1) the deviation `|F(x₀, y) − decoupledMean(x₀)|` is `≤ ε²H/log H` off the bad
set and `≤ 2·boxGrade` on it (`fBridgeF_abs_le_box`, `decoupledMean_abs_le_box`);
(2) its outer integral is `≤ ε²H/log H + 2·boxGrade·(bad-event mass)`; (3) the bad-event
mass `≤ (t + 2 log 2)/g + (κ + (log P_H − H[Y]))/t` (`outer_badMass_eq` +
`outer_badMass_le`); (4) triangle against `h211`. -/
theorem outer_combine (eps : ℚ) (H : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasure x ω] ≤ κ)
    {c₁ : ℝ} (_hc₁ : 0 < c₁)
    (h211 : c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        - ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
              + (κ + (Real.log (PH eps H : ℝ)
                  - H[residueWindow eps H; logMeasure x ω])) / t))
      ≤ |∫ n, (∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ))
          ∂(logMeasure x ω)| := by
  classical
  set δc := (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) with hδc
  set f : ℕ → ℝ := fun n => fBridgeF eps H (liouvilleWindow H n) (residueWindow eps H n) with hf
  set gm : ℕ → ℝ := fun n => ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
      (windowVal H (liouvilleWindow H n) j : ℝ)
        * (windowVal H (liouvilleWindow H n) (j + (p : ℕ)) : ℝ) with hgm
  set A : Set ℕ := {n | residueWindow eps H n ∈ badSet eps H (liouvilleWindow H n) δc} with hA
  have hA_meas : MeasurableSet A := (Set.to_countable _).measurableSet
  have hbox0 : 0 ≤ boxGrade eps H := by
    have hlp : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
    rw [boxGrade]; positivity
  have hδ0 : 0 ≤ δc := by
    have hlp : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
    rw [hδc]; positivity
  have hf_int : Integrable f (logMeasure x ω) := integrable_of_finiteSupport _
  have hg_int : Integrable gm (logMeasure x ω) := integrable_of_finiteSupport _
  -- step 1: pointwise deviation bound
  have hdevbnd : ∀ n, |f n - gm n| ≤ δc + A.indicator (fun _ => 2 * boxGrade eps H) n := by
    intro n
    have hx₀ : ∀ i, |liouvilleWindow H n i| ≤ 1 := abs_liouvilleWindow_le_one H n
    have hmemiff : n ∈ A ↔ δc ≤ |f n - gm n| := by
      rw [hA]
      simp only [Set.mem_setOf_eq, badSet, Finset.mem_filter, Finset.mem_univ, true_and, hf, hgm]
    by_cases hmem : n ∈ A
    · rw [Set.indicator_of_mem hmem]
      have h1 := fBridgeF_abs_le_box eps H hx₀ heps hreg hH (residueWindow eps H n)
      have h2 := decoupledMean_abs_le_box eps H hx₀ heps hreg hH
      have htri : |f n - gm n| ≤ |f n| + |gm n| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      have h1' : |f n| ≤ boxGrade eps H := by rw [hf]; exact h1
      have h2' : |gm n| ≤ boxGrade eps H := by rw [hgm]; exact h2
      linarith
    · rw [Set.indicator_of_notMem hmem, add_zero]
      have := (not_iff_not.mpr hmemiff).mp hmem
      linarith [not_le.mp this]
  -- step 2: integrate to the explicit error
  have hdev_le : ∫ n, |f n - gm n| ∂(logMeasure x ω)
      ≤ δc + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasure x ω])) / t) := by
    have hmass : (logMeasure x ω).real A
        ≤ (t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasure x ω])) / t := by
      rw [hA, outer_badMass_eq eps H x ω δc]
      exact outer_badMass_le eps H hx hω hωx heps heps1 hne hreg hH hlog hhead ht hg hgle hI
    have hstep : ∫ n, |f n - gm n| ∂(logMeasure x ω)
        ≤ ∫ n, (δc + A.indicator (fun _ => 2 * boxGrade eps H) n) ∂(logMeasure x ω) :=
      integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hdevbnd)
    refine hstep.trans ?_
    rw [integral_add (integrable_const δc) (integrable_of_finiteSupport _),
      integral_const, integral_indicator_const _ hA_meas, probReal_univ, smul_eq_mul, one_mul,
      smul_eq_mul]
    nlinarith [hmass, hbox0]
  -- step 3: triangle against h211
  have htri : |(∫ n, f n ∂(logMeasure x ω)) - (∫ n, gm n ∂(logMeasure x ω))|
      ≤ ∫ n, |f n - gm n| ∂(logMeasure x ω) := by
    rw [← integral_sub hf_int hg_int]; exact abs_integral_le_integral_abs
  have hfg : |∫ n, f n ∂(logMeasure x ω)|
      ≤ |∫ n, gm n ∂(logMeasure x ω)| + ∫ n, |f n - gm n| ∂(logMeasure x ω) := by
    calc |∫ n, f n ∂(logMeasure x ω)|
        = |(∫ n, gm n ∂(logMeasure x ω))
            + ((∫ n, f n ∂(logMeasure x ω)) - (∫ n, gm n ∂(logMeasure x ω)))| := by
          congr 1; ring
      _ ≤ |∫ n, gm n ∂(logMeasure x ω)|
          + |(∫ n, f n ∂(logMeasure x ω)) - (∫ n, gm n ∂(logMeasure x ω))| := abs_add_le _ _
      _ ≤ |∫ n, gm n ∂(logMeasure x ω)| + ∫ n, |f n - gm n| ∂(logMeasure x ω) := by linarith [htri]
  -- assemble: c₁·εH/logH ≤ |∫ f| ≤ |∫ gm| + (δc + 2 boxGrade·(β + badmass))
  have hchain := le_trans h211 hfg
  linarith [hchain, hdev_le]

/-! ## The outer assembly at shift `h` (W-F3 wave B, node B-4)

The `h`-ports of the disintegration, the bad-mass bound and the keystone combine — the last
three objects of wave A's declared not-yet-ported list (`no outer_combine at h`,
`no (2.11) restated at shift h`).

⚠️ **SITE 3 OF THE THREE SYNCHRONISED SITES CLOSES HERE.**  `outer_combine`'s conclusion
spells the two-point offset INDEPENDENTLY of `badSet_h` (site 1, `Transport`) and of the
decoupled concentration lemmas (site 2, `FBridge`/`Decoupled`); at `h = 1` it reads
`windowVal H (liouvilleWindow H n) (j + (p : ℕ))`.  `outer_combine_h` writes wave A's fixed
target spelling `windowVal H v (j + (p : ℕ) * h)` (`OuterCombine.lean:150`), byte-identical to
sites 1 and 2, so all three now agree character-for-character.

WHAT MOVES AND WHAT DOES NOT.  `boxGrade` and `boxSum_le_grade` never read the offset and are
REUSED VERBATIM — no `_h` port exists or is needed, exactly as wave A recorded.  So are
`outer_badMass_eq`'s measure-theoretic substrate (`map_compProd_condDistrib`,
`integral_compProd`) and `decrement_markov_fintype`.  The error term is character-for-character
the `h = 1` error term: `ε²H/log H + 2·boxGrade·((t + 2 log 2)/g + (κ + (log P_H − H[Y]))/t)`.
The shift costs NOTHING in the outer assembly, as it cost nothing in the box (wave A) and
nothing in the concentration grade (B-2/B-3).

THE `(2.11)` AT SHIFT `h`.  There is no standalone `(2.11)` declaration in this file: `(2.11)`
enters `outer_combine` as the hypothesis `h211`.  `outer_combine_h` restates it at shift `h`
by replacing `fBridgeF` with wave A's `fBridgeF_h eps H h` — that, and nothing else, is the
roster item.  The `(2.11)` PRODUCER chain (`ChowlaFailure.lean`) is still at `h = 1` and is
NOT ported here; it is a door/wave-C surface.

THE `h = 1` RECOVERY, TWO SHAPES.  `outer_badMass_h_eq` / `outer_badMass_h_le` mention neither
the bridge nor the product index in the clear (both are sealed inside `badSet_h`), so their
recovery is the SINGLE rewrite `badSet_h_one` — a third shape, distinct from B-1's and
B-2/B-3's pairs.  `outer_combine_h` carries BOTH in the clear (the bridge in `h211`, the
product index in the conclusion) and needs `fBridgeF_h_one` + `Nat.mul_one`, B-2/B-3's second
pair.  Measured with negative controls, never asserted: dropping `Nat.mul_one` leaves
`j + ↑p * 1` against `j + ↑p`; dropping `fBridgeF_h_one` leaves `fBridgeF_h eps H 1` against
`fBridgeF`; dropping `badSet_h_one` leaves `badSet_h eps H 1 x₀ δ` against `badSet eps H x₀ δ`;
`rfl` alone fails in every case. -/

/-- **The outer bad-event mass disintegrates over the fibres of the window, at shift `h`** —
the `h`-port of `outer_badMass_eq`.  Identical argument: the disintegration is a statement
about a `Finset`-valued deviation set and the joint law of `(liouvilleWindow, residueWindow)`,
and reads nothing about the offset.  `outer_badMass_eq` is the `h = 1` member (recovered by
`badSet_h_one` alone). -/
lemma outer_badMass_h_eq (eps : ℚ) (H h : ℕ) (x ω : ℕ)
    [IsProbabilityMeasure (logMeasure x ω)] (δ : ℝ) :
    (logMeasure x ω).real
        {n | residueWindow eps H n ∈ badSet_h eps H h (liouvilleWindow H n) δ}
      = ∫ x₀, ((condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
          ↑(badSet_h eps H h x₀ δ)) ∂((logMeasure x ω).map (liouvilleWindow H)) := by
  classical
  set μ := logMeasure x ω
  set X := liouvilleWindow H
  set Y := residueWindow eps H
  set cd := condDistrib Y X μ
  set W := fun n => (X n, Y n) with hW
  set S : Set ((Fin H → ℤ) × ZMod (PH eps H)) := {q | q.2 ∈ badSet_h eps H h q.1 δ} with hS
  have hXmeas : Measurable X := measurable_liouvilleWindow H
  have hYmeas : Measurable Y := measurable_residueWindow eps H
  have hWmeas : Measurable W := hXmeas.prodMk hYmeas
  have hSmeas : MeasurableSet S := (Set.to_countable _).measurableSet
  have hAeq : {n | Y n ∈ badSet_h eps H h (X n) δ} = W ⁻¹' S := rfl
  have hρ : μ.map W = μ.map X ⊗ₘ cd := (map_compProd_condDistrib hYmeas hXmeas μ).symm
  haveI hpW : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hWmeas.aemeasurable
  haveI hpC : IsProbabilityMeasure (μ.map X ⊗ₘ cd) := hρ ▸ hpW
  have hint : Integrable (S.indicator 1) (μ.map X ⊗ₘ cd) :=
    (integrable_const (1 : ℝ)).indicator hSmeas
  calc μ.real {n | Y n ∈ badSet_h eps H h (X n) δ}
      = (μ.map W).real S := by
        rw [hAeq]; simp only [measureReal_def, Measure.map_apply hWmeas hSmeas]
    _ = (μ.map X ⊗ₘ cd).real S := by rw [hρ]
    _ = ∫ q, S.indicator 1 q ∂(μ.map X ⊗ₘ cd) := (integral_indicator_one hSmeas).symm
    _ = ∫ x₀, ∫ y, S.indicator 1 (x₀, y) ∂(cd x₀) ∂(μ.map X) :=
        MeasureTheory.Measure.integral_compProd hint
    _ = ∫ x₀, (cd x₀).real ↑(badSet_h eps H h x₀ δ) ∂(μ.map X) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x₀ => ?_))
        change ∫ y, S.indicator 1 (x₀, y) ∂(cd x₀) = (cd x₀).real ↑(badSet_h eps H h x₀ δ)
        rw [← integral_indicator_one (μ := cd x₀)
          (s := (↑(badSet_h eps H h x₀ δ) : Set (ZMod (PH eps H))))
          ((Set.to_countable _).measurableSet)]
        refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
        simp only [Set.indicator_apply, Set.mem_setOf_eq, hS, Finset.mem_coe, Pi.one_apply]

/-- **The disintegrated bad-event mass is small, at shift `h`** — the `h`-port of
`outer_badMass_le`.  Same bound `(t + 2 log 2)/g + (κ + (log P_H − H[Y]))/t`, with
`badSet_transport_at_calibration_h` on the good fibres and the offset-blind Markov selection
`decrement_markov_fintype` confining the bad ones.  The budgets are character-for-character
the `h = 1` budgets: the shift never reaches the estimate. -/
lemma outer_badMass_h_le (eps : ℚ) (H h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t)
    {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ}
    (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasure x ω] ≤ κ) :
    ∫ x₀, ((condDistrib (residueWindow eps H) (liouvilleWindow H) (logMeasure x ω) x₀).real
        ↑(badSet_h eps H h x₀ ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ))))
          ∂((logMeasure x ω).map (liouvilleWindow H))
      ≤ (t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasure x ω])) / t := by
  classical
  set μ := logMeasure x ω
  set X := liouvilleWindow H
  set Y := residueWindow eps H
  set cd := condDistrib Y X μ with hcd
  set δcal := (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) with hδcal
  set baddef : Set (Fin H → ℤ) := {x₀ | t < H[Y; μ] - Hm[cd x₀]} with hbaddef
  set β := (t + 2 * Real.log 2) / g with hβ
  have hXmeas : Measurable X := measurable_liouvilleWindow H
  have hYmeas : Measurable Y := measurable_residueWindow eps H
  haveI hpX : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  have hbaddef_meas : MeasurableSet baddef := (Set.to_countable _).measurableSet
  have hβ0 : 0 ≤ β := by rw [hβ]; positivity
  have hC₀ : (0 : ℝ) < 2 * Real.log 4 := by positivity
  have hcard := primeWindow_card_le_of_regime eps H hreg hH
  -- (3.9) deficiency cap: log(1 + 8 P²ω/x) ≤ log 2
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hcorr : Real.log (1 + 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ)) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    have : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) / (x : ℝ) ≤ 1 := (div_le_one hxpos).mpr hhead
    linarith
  -- a.e. the window pattern is ±1-valued
  have hae : ∀ᵐ x₀ ∂(μ.map X), ∀ i, |x₀ i| ≤ 1 := by
    rw [ae_iff, Measure.map_apply hXmeas ((Set.to_countable _).measurableSet)]
    have hpre : X ⁻¹' {x₀ : Fin H → ℤ | ¬ ∀ i, |x₀ i| ≤ 1} = ∅ := by
      ext n
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact fun i => abs_liouvilleWindow_le_one H n i
    rw [hpre, measure_empty]
  -- the pointwise a.e. bound
  have hbound : ∀ᵐ x₀ ∂(μ.map X),
      (cd x₀).real ↑(badSet_h eps H h x₀ δcal) ≤ β + baddef.indicator 1 x₀ := by
    filter_upwards [hae] with x₀ hx₀le
    haveI : IsProbabilityMeasure (cd x₀) := by rw [hcd]; infer_instance
    by_cases hgood : H[Y; μ] - Hm[cd x₀] ≤ t
    · -- good fibre: transport + deficiency cap
      have hnotmem : x₀ ∉ baddef := by
        rw [hbaddef]; simp only [Set.mem_setOf_eq, not_lt]; exact hgood
      rw [Set.indicator_of_notMem hnotmem, add_zero]
      have htrans := badSet_transport_at_calibration_h eps H h hx hω hωx hx₀le heps heps1 hne hC₀
        hcard hlog ht.le hgood hg hgle
      refine htrans.trans ?_
      rw [hβ]
      exact div_le_div_of_nonneg_right (by linarith [hcorr]) hg.le
    · -- bad fibre: probability ≤ 1 ≤ β + 1
      have hmem : x₀ ∈ baddef := by
        rw [hbaddef]; simp only [Set.mem_setOf_eq]; exact lt_of_not_ge hgood
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      calc (cd x₀).real ↑(badSet_h eps H h x₀ δcal) ≤ 1 := measureReal_le_one
        _ ≤ β + 1 := by linarith
  -- integrate the a.e. bound
  have hbadmass : (μ.map X).real baddef
      ≤ (κ + (Real.log (PH eps H : ℝ) - H[Y; μ])) / t := by
    have hdm := decrement_markov_fintype (β := ZMod (PH eps H)) hXmeas hYmeas ht hI
    rwa [ZMod.card] at hdm
  calc ∫ x₀, (cd x₀).real ↑(badSet_h eps H h x₀ δcal) ∂(μ.map X)
      ≤ ∫ x₀, (β + baddef.indicator 1 x₀) ∂(μ.map X) :=
        integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _) hbound
    _ = β + (μ.map X).real baddef := by
        rw [integral_add (integrable_const β) (integrable_of_finiteSupport _),
          integral_const, integral_indicator_one hbaddef_meas, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (t + 2 * Real.log 2) / g
        + (κ + (Real.log (PH eps H : ℝ) - H[Y; μ])) / t := by rw [← hβ]; linarith [hbadmass]

/-- **W3-a-3c at shift `h`, the outer Fubini assembly** — ⚠️ SITE 3 of the three synchronised
offset spellings, and the `h`-port of `outer_combine`.  From the shift-`h` `(2.11)` door input
`h211` (stated against wave A's `fBridgeF_h`) the SHIFTED decoupled two-point correlation
`∑_p (1/p) ∑_j v_j v_{j+p·h}` carries a lower bound of the same `ε·H/log H` grade, with the
error term character-for-character the `h = 1` error term.

Chain, unchanged: (1) the deviation `|F_h(x₀, y) − decoupledMean_h(x₀)|` is `≤ ε²H/log H` off
`badSet_h` and `≤ 2·boxGrade` on it (`fBridgeF_h_abs_le_box`, `decoupledMean_h_abs_le_box`,
both wave A, both at the UNCHANGED grade); (2) integrate; (3) the bad-event mass
(`outer_badMass_h_eq` + `outer_badMass_h_le`); (4) triangle against `h211`.  The offset
spelling `windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h)` matches `badSet_h` (site 1) and
`fBridge_h_concentration_decoupled_sharp` (site 2) verbatim. -/
theorem outer_combine_h (eps : ℚ) (H h : ℕ) {x ω : ℕ}
    (hx : 2 ≤ x) (hω : 2 ≤ ω) (hωx : ω ≤ x)
    [IsProbabilityMeasure (logMeasure x ω)]
    (heps : 0 < eps) (heps1 : (eps : ℝ) ≤ 1) (hne : (primeWindow eps H).Nonempty)
    (hreg : Real.sqrt (H : ℝ) ≤ (eps : ℝ) ^ 2 * (H : ℝ) / 2) (hH : 3 ≤ H)
    (hlog : 1 ≤ Real.log (H : ℝ))
    (hhead : 8 * (PH eps H : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ))
    {t : ℝ} (ht : 0 < t) {g : ℝ} (hg : 0 < g)
    (hgle : g ≤ (eps : ℝ) ^ 6 * (H : ℝ) /
        (18 * (2 * Real.log 4) * Real.log (H : ℝ)) - Real.log 2)
    {κ : ℝ} (hI : I[residueWindow eps H : liouvilleWindow H ; logMeasure x ω] ≤ κ)
    {c₁ : ℝ} (_hc₁ : 0 < c₁)
    (h211 : c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        ≤ |∫ n, fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
            ∂(logMeasure x ω)|) :
    c₁ * ((eps : ℝ) * (H : ℝ) / Real.log (H : ℝ))
        - ((eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ)
            + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
              + (κ + (Real.log (PH eps H : ℝ)
                  - H[residueWindow eps H; logMeasure x ω])) / t))
      ≤ |∫ n, (∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
          (windowVal H (liouvilleWindow H n) j : ℝ)
            * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ))
          ∂(logMeasure x ω)| := by
  classical
  set δc := (eps : ℝ) ^ 2 * (H : ℝ) / Real.log (H : ℝ) with hδc
  set f : ℕ → ℝ := fun n => fBridgeF_h eps H h (liouvilleWindow H n) (residueWindow eps H n)
    with hf
  set gm : ℕ → ℝ := fun n => ∑ p : primeWindow eps H, (1 / (p : ℝ)) * ∑ j ∈ Finset.range H,
      (windowVal H (liouvilleWindow H n) j : ℝ)
        * (windowVal H (liouvilleWindow H n) (j + (p : ℕ) * h) : ℝ) with hgm
  set A : Set ℕ := {n | residueWindow eps H n ∈ badSet_h eps H h (liouvilleWindow H n) δc} with hA
  have hA_meas : MeasurableSet A := (Set.to_countable _).measurableSet
  have hbox0 : 0 ≤ boxGrade eps H := by
    have hlp : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
    rw [boxGrade]; positivity
  have hδ0 : 0 ≤ δc := by
    have hlp : (0 : ℝ) < Real.log (H : ℝ) := zero_lt_one.trans_le hlog
    rw [hδc]; positivity
  have hf_int : Integrable f (logMeasure x ω) := integrable_of_finiteSupport _
  have hg_int : Integrable gm (logMeasure x ω) := integrable_of_finiteSupport _
  -- step 1: pointwise deviation bound
  have hdevbnd : ∀ n, |f n - gm n| ≤ δc + A.indicator (fun _ => 2 * boxGrade eps H) n := by
    intro n
    have hx₀ : ∀ i, |liouvilleWindow H n i| ≤ 1 := abs_liouvilleWindow_le_one H n
    have hmemiff : n ∈ A ↔ δc ≤ |f n - gm n| := by
      rw [hA]
      simp only [Set.mem_setOf_eq, badSet_h, Finset.mem_filter, Finset.mem_univ, true_and, hf, hgm]
    by_cases hmem : n ∈ A
    · rw [Set.indicator_of_mem hmem]
      have h1 := fBridgeF_h_abs_le_box eps H h hx₀ heps hreg hH (residueWindow eps H n)
      have h2 := decoupledMean_h_abs_le_box eps H h hx₀ heps hreg hH
      have htri : |f n - gm n| ≤ |f n| + |gm n| := by
        rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      have h1' : |f n| ≤ boxGrade eps H := by rw [hf]; exact h1
      have h2' : |gm n| ≤ boxGrade eps H := by rw [hgm]; exact h2
      linarith
    · rw [Set.indicator_of_notMem hmem, add_zero]
      have := (not_iff_not.mpr hmemiff).mp hmem
      linarith [not_le.mp this]
  -- step 2: integrate to the explicit error
  have hdev_le : ∫ n, |f n - gm n| ∂(logMeasure x ω)
      ≤ δc + 2 * boxGrade eps H * ((t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasure x ω])) / t) := by
    have hmass : (logMeasure x ω).real A
        ≤ (t + 2 * Real.log 2) / g
          + (κ + (Real.log (PH eps H : ℝ) - H[residueWindow eps H; logMeasure x ω])) / t := by
      rw [hA, outer_badMass_h_eq eps H h x ω δc]
      exact outer_badMass_h_le eps H h hx hω hωx heps heps1 hne hreg hH hlog hhead ht hg hgle hI
    have hstep : ∫ n, |f n - gm n| ∂(logMeasure x ω)
        ≤ ∫ n, (δc + A.indicator (fun _ => 2 * boxGrade eps H) n) ∂(logMeasure x ω) :=
      integral_mono_ae (integrable_of_finiteSupport _) (integrable_of_finiteSupport _)
        (Filter.Eventually.of_forall hdevbnd)
    refine hstep.trans ?_
    rw [integral_add (integrable_const δc) (integrable_of_finiteSupport _),
      integral_const, integral_indicator_const _ hA_meas, probReal_univ, smul_eq_mul, one_mul,
      smul_eq_mul]
    nlinarith [hmass, hbox0]
  -- step 3: triangle against h211
  have htri : |(∫ n, f n ∂(logMeasure x ω)) - (∫ n, gm n ∂(logMeasure x ω))|
      ≤ ∫ n, |f n - gm n| ∂(logMeasure x ω) := by
    rw [← integral_sub hf_int hg_int]; exact abs_integral_le_integral_abs
  have hfg : |∫ n, f n ∂(logMeasure x ω)|
      ≤ |∫ n, gm n ∂(logMeasure x ω)| + ∫ n, |f n - gm n| ∂(logMeasure x ω) := by
    calc |∫ n, f n ∂(logMeasure x ω)|
        = |(∫ n, gm n ∂(logMeasure x ω))
            + ((∫ n, f n ∂(logMeasure x ω)) - (∫ n, gm n ∂(logMeasure x ω)))| := by
          congr 1; ring
      _ ≤ |∫ n, gm n ∂(logMeasure x ω)|
          + |(∫ n, f n ∂(logMeasure x ω)) - (∫ n, gm n ∂(logMeasure x ω))| := abs_add_le _ _
      _ ≤ |∫ n, gm n ∂(logMeasure x ω)| + ∫ n, |f n - gm n| ∂(logMeasure x ω) := by linarith [htri]
  -- assemble: c₁·εH/logH ≤ |∫ f| ≤ |∫ gm| + (δc + 2 boxGrade·(β + badmass))
  have hchain := le_trans h211 hfg
  linarith [hchain, hdev_le]

end Salt.Entropy.Chowla
