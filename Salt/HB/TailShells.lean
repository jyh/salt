/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7EF
import Salt.SW.DensityStrip

/-!
# Arm B part B3-i — THE ROW-(iv) TAIL RE-GRADE: B2 spent shell by shell (STUB, design γ)

DRAFT FREEZE v0 STUB — statements only, every proof `sorry`; a kernel well-formedness pass,
not a landing. The crude count `137·(2T₀+5)·log(q(T₀+4))` is baked into `efEnvelope`'s
definition; this file cuts a sibling envelope whose two zero rows go through B2's log-free
density (`zeroCountM_density_logfree`) shell by shell at the ceiling, and prices the
exponential row's tail integral. Nothing here bears on twin primes.
-/

open Complex DirichletCharacter ArithmeticFunction Filter Set MeasureTheory
open Salt.SW
open scoped Topology

namespace Salt.HB

/-- B2's constant, chosen ONCE. -/
noncomputable def n9CB2 : ℝ := Classical.choose zeroCountM_density_logfree

/-- B2's exponent, chosen ONCE (`≤ 150`). -/
noncomputable def n9DB2 : ℝ := Classical.choose (Classical.choose_spec zeroCountM_density_logfree)

/-- Class A: `Classical.choose_spec` twice. -/
theorem n9B2_spec : 0 < n9CB2 ∧ 0 < n9DB2 ∧ n9DB2 ≤ 150 ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 2 ≤ q →
      ∀ (σ T : ℝ), 4 / 5 ≤ σ → σ ≤ 1 → 2 ≤ T →
        zeroCountM χ σ T ≤ n9CB2 * ((q : ℝ) * T) ^ (n9DB2 * (1 - σ)) := by
  exact Classical.choose_spec (Classical.choose_spec zeroCountM_density_logfree)

/-- The termwise form of `efZeroSumM_norm_le_harmonic`. Class A. -/
theorem efZeroSumM_norm_le_termwise {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {Z : Finset ℂ} {y : ℝ} (hy : 1 ≤ y) :
    ‖efZeroSumM χ Z y‖ ≤ ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * y ^ ρ.re / ‖ρ‖ := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
  rw [efZeroSumM]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun ρ _ => ?_)
  rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_natCast]
  exact le_of_eq (mul_div_assoc _ _ _).symm

/-- **THE SHELL SPEND** — B2 spent shell by shell at a ceiling `1 − w`. Class C. -/
theorem zeroSum_shells_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {σa T u w : ℝ} (hσa : 9 / 10 ≤ σa) (hT : 2 ≤ T)
    (hu : 1 ≤ u) {Z : Finset ℂ} (hZ : Z ⊆ boxZeros χ σa 1 T)
    (hw : 0 < w) (hw1 : w ≤ 1 / 10) (hbar : ∀ ρ ∈ Z, ρ.re ≤ 1 - w)
    (hy : 6 / 5 * n9DB2 * Real.log ((q : ℝ) * T) ≤ 3 / 4 * Real.log u)
    (hbig : 20 ≤ w * Real.log u) :
    ∑ ρ ∈ Z, (zeroMult χ ρ : ℝ) * u ^ ρ.re
      ≤ 2 * n9CB2 * u * Real.exp (-(w * Real.log u) / 4) := by
  sorry

/-- The shell row of the B3 envelope. -/
noncomputable def efShellRow (q : ℕ) (bceil u : ℝ) : ℝ :=
  (efH q u / u + 5 / 4) * (2 * n9CB2) * Real.exp (-((1 - bceil) * Real.log u) / 4)

/-- **THE B3 ENVELOPE** — `efEnvelope`'s first two summands verbatim, `β₀`'s own term kept
apart, the shell row in place of the two crude-count rows. -/
noncomputable def efEnvelopeB3 (q : ℕ) (β₀ bceil : ℝ) (m : ℕ) (σa σb u : ℝ) : ℝ :=
  ((efH q u + 1) * Real.log (u + efH q u)
    + (efShiftBound q (efT0 q u) σa σb u + efShiftBound q (efT0 q u) σa σb (u + efH q u))
        / efH q u
    + (m : ℝ) * (efH q u * u ^ (β₀ - 1))) / u
  + efShellRow q bceil u

/-- The raw form: `psiDefect_norm_le_of_ef` cut at `hkey`. No ceiling binder; the box's lower
edge `9/10 ≤ σ₀ − w` EXPORTED (R2's K3 repair — it is `hσ₀w` at `Lemma7EF.lean:404`, from
`DensityCrude.lean:870`; the shell lemma's `hσa` and `hbar` need it). Class B. -/
theorem psiDefect_norm_le_raw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {β₀ u h σa σb T₀ : ℝ}
    (hu : 3 ≤ u) (hh : 0 < h) (hσa : 9 / 10 ≤ σa) (hσab : σa < σb) (hσb : σb < 1)
    (hT₀ : 2 ≤ T₀) (hβ₀1 : β₀ ≤ 1) (hσbβ₀ : σb ≤ β₀)
    (hβ₀zero : LFunction χ (β₀ : ℂ) = 0) :
    ∃ σ₀ T w : ℝ,
      (σa ≤ σ₀ ∧ σ₀ ≤ σb) ∧ (T₀ ≤ T ∧ T ≤ T₀ + 1) ∧ 0 < w ∧
      (σb - σa) / (4 * (137 * (2 * T₀ + 7) * Real.log ((q : ℝ) * (T₀ + 5)) + 1)) ≤ w ∧
      9 / 10 ≤ σ₀ - w ∧
      ‖psiDefect χ β₀ (zeroMult χ (β₀ : ℂ)) u‖
        ≤ (h + 1) * Real.log (u + h)
          + (efShiftError q T σ₀ w u + efShiftError q T σ₀ w (u + h)) / h
          + (zeroMult χ (β₀ : ℂ) : ℝ) * (h * u ^ (β₀ - 1))
          + (h / u + 5 / 4) * ∑ ρ ∈ (boxZeros χ (σ₀ - w) 1 T).erase (β₀ : ℂ),
              (zeroMult χ ρ : ℝ) * u ^ ρ.re := by
  sorry

/-- **`hEF` FOR THE B3 ENVELOPE.** Class C (an assembly). -/
theorem psiDefect_norm_le_envelopeB3 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {β₀ bceil u σa σb : ℝ} {m : ℕ}
    (hu : 3 ≤ u) (hm : m = zeroMult χ (β₀ : ℂ)) (hσa : 9 / 10 ≤ σa) (hσab : σa < σb)
    (hσb : σb < 1) (hβ₀1 : β₀ ≤ 1) (hσbβ₀ : σb ≤ β₀) (hβ₀zero : LFunction χ (β₀ : ℂ) = 0)
    (hceil : ∀ ρ : ℂ, LFunction χ ρ = 0 → ρ ≠ (β₀ : ℂ) → 9 / 10 ≤ ρ.re → ρ.re ≤ 1 →
      |ρ.im| ≤ efT0 q u + 1 → ρ.re ≤ bceil)
    (hb16 : 16 / 17 ≤ bceil)
    (hy : 6 / 5 * n9DB2 * Real.log ((q : ℝ) * (efT0 q u + 1)) ≤ 3 / 4 * Real.log u)
    (hbig : 20 ≤ (1 - bceil) * Real.log u) :
    ‖psiDefect χ β₀ m u‖ ≤ u * efEnvelopeB3 q β₀ bceil m σa σb u := by
  sorry

/-- Class B: mirror `efEnvelope_nonneg`. -/
theorem efEnvelopeB3_nonneg {q : ℕ} {β₀ bceil σa σb u : ℝ} {m : ℕ} (hq : 2 ≤ q) (hu : 3 ≤ u)
    (hσa : 9 / 10 ≤ σa) (hσab : σa < σb) (hσb : σb < 1) :
    0 ≤ efEnvelopeB3 q β₀ bceil m σa σb u := by
  sorry

/-- Class B: mirror `continuousOn_efEnvelope_ceilFun`. -/
theorem continuousOn_efEnvelopeB3_ceilFun {q : ℕ} (hq : 2 ≤ q) {β₀ : ℝ} {B : ℝ → ℝ} (m : ℕ)
    (hB : ContinuousOn B (Set.Ici (3 : ℝ))) {σa σb : ℝ} (hσa : 9 / 10 ≤ σa) :
    ContinuousOn (fun u : ℝ => efEnvelopeB3 q β₀ (B u) m σa σb u) (Set.Ici (3 : ℝ)) := by
  sorry

/-- **THE B3 LEDGER** — rows (i)–(iii) of the sharp ledger verbatim, the shell row as is. Class B. -/
theorem efEnvelopeB3_le_ledger {q : ℕ} {β₀ bceil σa σb u M N : ℝ} {m : ℕ}
    (hq : 2 ≤ q) (hu : 3 ≤ u) (hM : M = Real.log ((q : ℝ) * u) + 2)
    (hN : N = Real.log q + 11 * Real.log M)
    (hσa : 9 / 10 ≤ σa) (hσab : σa < σb) (hσb : σb < 1) (hgap : 1 / 20 ≤ σb - σa)
    (hβ₀1 : β₀ ≤ 1) :
    efEnvelopeB3 q β₀ bceil m σa σb u
      ≤ ((m : ℝ) + 2 + 2 * 10 ^ 6 * N ^ 2 / M ^ 2) / M + M / u
        + 10 ^ 6 * M ^ 9 * N ^ 2 * u ^ (σb - 1)
        + (1 / M ^ 3 + 5 / 4) * (2 * n9CB2) * Real.exp (-((1 - bceil) * Real.log u) / 4) := by
  sorry

/-- **THE `E₁` BOUND** — the exponential row's tail integral. Class B. -/
theorem integral_rpow_div_log_tail_le {X ε : ℝ} (hX : 3 ≤ X) (hε : 0 < ε) :
    IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log v) (Set.Ioi X) ∧
    ∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log v ≤ X ^ (-ε) / (ε * Real.log X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have he : Real.exp 1 ≤ X :=
      le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hX
    exact (Real.le_log_iff_exp_le hX0).mpr he
  have hlt : -(1 : ℝ) - ε < -1 := by linarith
  have hg : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε)) (Set.Ioi X) :=
    integrableOn_Ioi_rpow_of_lt hlt hX0
  have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log v)
      (volume.restrict (Set.Ioi X)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    have hid : ContinuousOn (fun t : ℝ => t) (Set.Ioi X) := continuousOn_id
    exact ContinuousOn.div
      (hid.rpow_const (fun t ht => Or.inl (ne_of_gt (by linarith [Set.mem_Ioi.mp ht]))))
      (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [Set.mem_Ioi.mp ht])))
      (fun t ht => ne_of_gt (Real.log_pos (by linarith [Set.mem_Ioi.mp ht])))
  have hint : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log v) (Set.Ioi X) := by
    refine hg.mono' hmeas ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun v hv => ?_)))
    have hvX : X < v := hv
    have hv0 : (0 : ℝ) < v := by linarith
    have hlogv : (1 : ℝ) ≤ Real.log v :=
      le_trans hlogX (Real.log_le_log hX0 (le_of_lt hvX))
    have hrp : (0 : ℝ) < v ^ (-(1 : ℝ) - ε) := Real.rpow_pos_of_pos hv0 _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨hint, ?_⟩
  have hmaj : IntegrableOn (fun v : ℝ => v ^ (-(1 : ℝ) - ε) / Real.log X) (Set.Ioi X) :=
    hg.div_const _
  have hmono : (∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log v)
      ≤ ∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log X := by
    refine setIntegral_mono_on hint hmaj measurableSet_Ioi (fun v hv => ?_)
    have hvX : X < v := hv
    have hv0 : (0 : ℝ) < v := by linarith
    have hlogv : Real.log X ≤ Real.log v := Real.log_le_log hX0 (le_of_lt hvX)
    have hrp : (0 : ℝ) < v ^ (-(1 : ℝ) - ε) := Real.rpow_pos_of_pos hv0 _
    exact div_le_div_of_nonneg_left hrp.le (by linarith) hlogv
  have hdiv : (∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε) / Real.log X)
      = (∫ v in Set.Ioi X, v ^ (-(1 : ℝ) - ε)) / Real.log X := integral_div _ _
  rw [hdiv, integral_Ioi_rpow_of_lt hlt hX0] at hmono
  refine le_trans hmono (le_of_eq ?_)
  rw [show -(1 : ℝ) - ε + 1 = -ε by ring]
  field_simp

end Salt.HB
