/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.Lemma7EF
import Salt.HB.Lemma3Uncond
import Salt.Mertens.Third

/-!
# HB 1983, Lemma 7 — node N4b, wave **W3**: the `F` computation

Heath-Brown pp.209–210.  `F = ∏_{p ≥ z}(1 − χ(p)p^{−1})^{−1}` is the factor of `κS₁` in which
the exceptional zero re-enters, and the content of W3 is the evaluation

    log F  =  log log z − log(ηL) + γ₀ + δ,

with `η := ((1−β₀)L)^{−1}`, `L := log q`, `γ₀` the Euler–Mascheroni constant, and `δ` an
*explicitly bounded* error.  The route (design freeze v3 §4/W3):

1. `log F = ∑_{n ≥ z} χ(n)Λ(n)/(n log n) + O(z^{−1/2})` — the prime-power correction.
2. The `[z, X]` segment at a **split point `X`**, `∀`-quantified with `q^{250} ≤ X ≤ q^{500}`
   (R4's two-roles ruling: `X` is *never* bound to a consumer's `x`).  The `χ(p) = 1` half is
   killed by Lemma 3 (`pretenseSum_unconditional_absorbed`) at the Rankin point `σ = 1 + 1/Lp`,
   `Lp := 2L`; the coprime half is Mertens' second theorem.
3. The tail `∑_{n > X}` via W2's socket `logChiSum_tendsto_of_envelope`, whose main term is
   `−m·∫_X^∞ v^{β₀−2}/log v dv`.
4. **The integral** (§§1–3 below) — the block's calculus heart.

## `hm1` rides (design v3, **D11**)

The F-side cancellation holds **only at `m = 1`**: for `m ≥ 2` the tail contributes
`−m·∫ v^{β₀−2}/log v`, so `log F = log log z − m·log(ηL) + (m−1)·log log X + m·γ₀ + …` and `F`
carries `(ηL)^{−m}` as an *exponent*, breaking `κS₁·(L′/L)² ∝ (ηL)^{2−2m}`.  Therefore
`hm1 : zeroMult χ (β₀:ℂ) = 1` rides as a **named binder** on every W3 statement that touches the
tail.  The `m`-general form is *not* attempted here.

## §§1–3, the integral: what is proved and with which constants

* §1 `expIntegral_sub_log_gamma_abs_le`: for `0 < t₀ ≤ 1`,

      |∫_{t₀}^∞ e^{−t} dt/t − (−log t₀ − γ₀)|  ≤  t₀·(1 − 2 log t₀).

  Route: the `[e^{−t} log t]` integration by parts (an FTC on `[t₀, Y]` plus `Y → ∞`), then the
  landed `Salt.Mertens.integral_exp_neg_log : ∫_0^∞ e^{−v} log v dv = −γ₀`.  The two error
  pieces are `(1 − e^{−t₀})·log t₀` (cost `t₀|log t₀|`) and `∫_0^{t₀} e^{−t} log t dt`
  (cost `t₀ − t₀ log t₀`).
* §2 `integral_rpow_div_log_Ioi_eq_expIntegral`: HB's substitution `v = e^{t/(1−β₀)}`,

      ∫_X^∞ v^{β₀−2}(log v)^{−1} dv  =  ∫_{t₀}^∞ e^{−t} dt/t,   t₀ = (1−β₀)·log X.

* §3 `hb_F_tail_integral`: the two composed, **with the upper window edge consumed here and only
  here**.  `X ≤ q^{500}` enters as `hwin : log X ≤ 500·L`, giving `t₀ ≤ 500/η`, and the error is
  stated with its honest constant *visible*:

      |∫_X^∞ v^{β₀−2}/log v dv − (log(ηL) − log log X − γ₀)|  ≤  500·(1 + 2·log(ηL))/η.

  Per R4's finding the window exponent is **not** hidden inside an `O(·)`: the `500` is literal,
  and `hηlarge : 500 ≤ η` (which is what `t₀ ≤ 1` *means* at this window) is a named binder.

## §4, the segment; §5, the assembly

* §4 `logChiSum_re_eq` is HB's split of `(4.7)`, exact: for real `χ`,
  `∑_{z<n≤X} χΛ/(n log n) = 2·∑_{χ_ℝ=1} − ∑_{(n,q)=1}`, off the detector identity
  `χ_ℝ(n) = 2·1_{χ_ℝ(n)=1} − 1_{(n,q)=1}`.
* §4 `hb_chiOne_kill_at_window` **kills the `χ(p)=1` half**: the weight exchange
  (`≤ PretenseSum χ ⌊X⌋ / log z`, HB's `z₀`-factor) composed with Lemma 3
  (`pretenseSum_unconditional_absorbed`) at `σ = 1 + 1/Lp`, `σ′ = 1 + √ℓ/Lp`, `Lp := 2L`, with
  the Rankin factor `⌊X⌋^{1/(2L)} ≤ e^{250}` — the window's upper edge consumed a **second**
  time (`rankin_floor_le`), exactly as the freeze predicts.
* §5 `hb_logF_at_split_point` is the deliverable at the multiplicative mandate: ONE bound,

      |log F − (log log z − log(ηL) + γ₀)| ≤ Ecorr + Eseg + Etail + 500(1 + 2 log(ηL))/η,

  with `hm1` collapsing the socket's multiplicity.  Three inputs ride as **named binders with
  explicit bounds** (never as silent `O(·)`s): `hcorr` (HB's step 1 — blocked on the corpus
  having no infinite-Euler-product `F`; the prime-power half of it is `mertensB`'s business),
  `hseg` (the coprime half — Mertens' second theorem, mechanical Finset bookkeeping), and
  `htail` (W2's socket, carried verbatim by design).  See `docs/blueprints/flags.md`.
-/

namespace Salt.HB

open Complex DirichletCharacter ArithmeticFunction Filter MeasureTheory Set
open Salt.SW
open scoped Topology

/-! ## §1 — the exponential integral `E₁(t₀) = ∫_{t₀}^∞ e^{−t} dt/t` -/

/-- `t ↦ e^{−t}/t` is integrable on `(t₀, ∞)` for `t₀ > 0`: dominated by `t₀^{−1}e^{−t}`. -/
lemma integrableOn_expNeg_div_Ioi {t₀ : ℝ} (ht₀ : 0 < t₀) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi t₀) := by
  have hexp : IntegrableOn (fun t : ℝ => t₀⁻¹ * Real.exp (-t)) (Ioi t₀) := by
    have h := exp_neg_integrableOn_Ioi t₀ (b := 1) one_pos
    have h' : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi t₀) := by
      refine h.congr_fun (fun t _ => by norm_num) measurableSet_Ioi
    exact h'.const_mul _
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) / t)
      (volume.restrict (Ioi t₀)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      (fun t ht => ne_of_gt (lt_trans ht₀ (mem_Ioi.mp ht)))
  refine hexp.mono' hmeas ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun t ht => ?_)))
  have htt : t₀ < t := mem_Ioi.mp ht
  have ht0 : (0 : ℝ) < t := lt_trans ht₀ htt
  have hE : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ ht0]
  have h1 : Real.exp (-t) * t₀ ≤ Real.exp (-t) * t := by nlinarith
  have h2 : t₀⁻¹ * Real.exp (-t) * t = Real.exp (-t) * t / t₀ := by
    field_simp
  rw [h2, le_div_iff₀ ht₀]
  nlinarith

/-- `t ↦ e^{−t} log t` is integrable on `(0, ∞)`: `|log|` dominates on `(0,1]`, and the
`Γ`-integrand `e^{−t}t` dominates on `(1, ∞)`. -/
lemma integrableOn_expNeg_mul_log_Ioi_zero :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Ioi (0 : ℝ)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) :=
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · -- `(0,1]`: dominated by `|log t|`
    have hlog : IntegrableOn Real.log (Ioc (0 : ℝ) 1) volume := by
      have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := (1 : ℝ))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) * Real.log t)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact (Real.continuous_exp.comp continuous_neg).continuousOn.mul
        (Real.continuousOn_log.mono (fun t ht => ne_of_gt ht.1))
    refine hlog.norm.mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun t ht => ?_)))
    have hE1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    have hE0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hE0]
    nlinarith [abs_nonneg (Real.log t)]
  · -- `(1,∞)`: dominated by the `Γ(2)`-integrand `e^{−t}t`
    have hG : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 : ℝ) - 1)) (Ioi (1 : ℝ)) :=
      (Real.GammaIntegral_convergent (s := 2) (by norm_num)).mono_set
        (Ioi_subset_Ioi (by norm_num))
    have hG' : IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Ioi (1 : ℝ)) := by
      refine hG.congr_fun (fun x hx => ?_) measurableSet_Ioi
      norm_num
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t) * Real.log t)
        (volume.restrict (Ioi (1 : ℝ))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact (Real.continuous_exp.comp continuous_neg).continuousOn.mul
        (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [mem_Ioi.mp ht])))
    refine hG'.mono' hmeas
      ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun t ht => ?_)))
    have ht1 : (1 : ℝ) < t := mem_Ioi.mp ht
    have hE0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
    have hlog0 : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht1.le
    have hlt : Real.log t ≤ t := le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE0, abs_of_nonneg hlog0]
    nlinarith

lemma integrableOn_expNeg_mul_log_Ioi {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Ioi t₀) :=
  integrableOn_expNeg_mul_log_Ioi_zero.mono_set (Ioi_subset_Ioi ht₀)

/-- The derivative behind the integration by parts: `(e^{−t} log t)′ = e^{−t}/t − e^{−t} log t`. -/
lemma hasDerivAt_expNeg_mul_log {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.exp (-s) * Real.log s)
      (Real.exp (-t) / t - Real.exp (-t) * Real.log t) t := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
    have h := (hasDerivAt_neg t).exp
    rw [show Real.exp (-t) * (-1 : ℝ) = -Real.exp (-t) by ring] at h
    exact h
  have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht)
  have h := h1.mul h2
  rw [show -Real.exp (-t) * Real.log t + Real.exp (-t) * t⁻¹
      = Real.exp (-t) / t - Real.exp (-t) * Real.log t by rw [div_eq_mul_inv]; ring] at h
  exact h

/-- **The integration by parts, finite window.**  For `0 < t₀ ≤ Y`,

    ∫_{t₀}^Y e^{−t} dt/t = e^{−Y} log Y − e^{−t₀} log t₀ + ∫_{t₀}^Y e^{−t} log t dt. -/
lemma expIntegral_ibp {t₀ Y : ℝ} (ht₀ : 0 < t₀) (hY : t₀ ≤ Y) :
    (∫ t in t₀..Y, Real.exp (-t) / t)
      = Real.exp (-Y) * Real.log Y - Real.exp (-t₀) * Real.log t₀
        + ∫ t in t₀..Y, Real.exp (-t) * Real.log t := by
  have hmem : ∀ t ∈ uIcc t₀ Y, (0 : ℝ) < t := by
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact lt_of_lt_of_le ht₀ ht.1
  have hc1 : ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (uIcc t₀ Y) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id
      (fun t ht => ne_of_gt (hmem t ht))
  have hc2 : ContinuousOn (fun t : ℝ => Real.exp (-t) * Real.log t) (uIcc t₀ Y) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.mul
      (Real.continuousOn_log.mono (fun t ht => ne_of_gt (hmem t ht)))
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.exp (-t) / t) volume t₀ Y :=
    hc1.intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => Real.exp (-t) * Real.log t) volume t₀ Y :=
    hc2.intervalIntegrable
  have hftc : (∫ t in t₀..Y, (Real.exp (-t) / t - Real.exp (-t) * Real.log t))
      = Real.exp (-Y) * Real.log Y - Real.exp (-t₀) * Real.log t₀ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_expNeg_mul_log (hmem t ht)) (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at hftc
  linarith

/-- `e^{−Y} log Y → 0`. -/
lemma tendsto_expNeg_mul_log_atTop :
    Tendsto (fun Y : ℝ => Real.exp (-Y) * Real.log Y) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun Y : ℝ => Y * Real.exp (-Y)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg hY)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    have hlt : Real.log Y ≤ Y :=
      le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
    have hE : (0 : ℝ) < Real.exp (-Y) := Real.exp_pos _
    nlinarith

/-- **The integration by parts, improper.**  For `t₀ > 0`,

    ∫_{t₀}^∞ e^{−t} dt/t = −e^{−t₀} log t₀ + ∫_{t₀}^∞ e^{−t} log t dt. -/
lemma expIntegral_eq_sub {t₀ : ℝ} (ht₀ : 0 < t₀) :
    (∫ t in Ioi t₀, Real.exp (-t) / t)
      = -(Real.exp (-t₀) * Real.log t₀) + ∫ t in Ioi t₀, Real.exp (-t) * Real.log t := by
  have hL : Tendsto (fun Y : ℝ => ∫ t in t₀..Y, Real.exp (-t) / t) atTop
      (𝓝 (∫ t in Ioi t₀, Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi t₀ (integrableOn_expNeg_div_Ioi ht₀) tendsto_id
  have hR2 : Tendsto (fun Y : ℝ => ∫ t in t₀..Y, Real.exp (-t) * Real.log t) atTop
      (𝓝 (∫ t in Ioi t₀, Real.exp (-t) * Real.log t)) :=
    intervalIntegral_tendsto_integral_Ioi t₀ (integrableOn_expNeg_mul_log_Ioi ht₀.le) tendsto_id
  have hR : Tendsto (fun Y : ℝ => Real.exp (-Y) * Real.log Y
      - Real.exp (-t₀) * Real.log t₀ + ∫ t in t₀..Y, Real.exp (-t) * Real.log t) atTop
      (𝓝 (0 - Real.exp (-t₀) * Real.log t₀ + ∫ t in Ioi t₀, Real.exp (-t) * Real.log t)) :=
    (tendsto_expNeg_mul_log_atTop.sub tendsto_const_nhds).add hR2
  have heq : (∫ t in Ioi t₀, Real.exp (-t) / t)
      = 0 - Real.exp (-t₀) * Real.log t₀ + ∫ t in Ioi t₀, Real.exp (-t) * Real.log t := by
    refine tendsto_nhds_unique hL (hR.congr' ?_)
    filter_upwards [eventually_ge_atTop t₀] with Y hY
    exact (expIntegral_ibp ht₀ hY).symm
  rw [heq]; ring

/-- The `(0, t₀]` piece of the `γ`-integral, bounded by `∫_0^{t₀}|log|`. -/
lemma abs_integral_expNeg_mul_log_Ioc_le {t₀ : ℝ} (ht₀ : 0 < t₀) (ht1 : t₀ ≤ 1) :
    |∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t| ≤ t₀ - t₀ * Real.log t₀ := by
  have hlogI : IntegrableOn Real.log (Ioc (0 : ℝ) t₀) volume := by
    have h := intervalIntegral.intervalIntegrable_log' (a := (0 : ℝ)) (b := t₀)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le ht₀.le] at h
  have hfI : IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Ioc (0 : ℝ) t₀) volume :=
    integrableOn_expNeg_mul_log_Ioi_zero.mono_set Ioc_subset_Ioi_self
  have hval : (∫ t in Ioc (0 : ℝ) t₀, -Real.log t) = t₀ - t₀ * Real.log t₀ := by
    have h : (∫ t in (0 : ℝ)..t₀, Real.log t) = t₀ * Real.log t₀ - t₀ := by
      rw [integral_log]; simp
    rw [integral_neg]
    have h2 : (∫ t in Ioc (0 : ℝ) t₀, Real.log t) = t₀ * Real.log t₀ - t₀ := by
      rw [← h, intervalIntegral.integral_of_le ht₀.le]
    rw [h2]; ring
  calc |∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t|
      = ‖∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Ioc (0 : ℝ) t₀, ‖Real.exp (-t) * Real.log t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc (0 : ℝ) t₀, -Real.log t := by
        refine setIntegral_mono_on hfI.norm hlogI.neg measurableSet_Ioc (fun t ht => ?_)
        have ht0 : (0 : ℝ) < t := ht.1
        have htt : t ≤ 1 := le_trans ht.2 ht1
        have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le htt
        have hE1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hE0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos hE0, abs_of_nonpos hlog]
        nlinarith
    _ = t₀ - t₀ * Real.log t₀ := hval

/-- **§1's stone — the exponential integral against `−log t₀ − γ₀`.**  For `0 < t₀ ≤ 1`,

    |∫_{t₀}^∞ e^{−t} dt/t − (−log t₀ − γ₀)|  ≤  t₀·(1 − 2 log t₀),

`γ₀ = Real.eulerMascheroniConstant`.  (The two-sided elementary bound of the brief, at the
explicit constants `1` and `2`; note `log t₀ ≤ 0` on the range, so the right side is `≥ 0`.) -/
theorem expIntegral_sub_log_gamma_abs_le {t₀ : ℝ} (ht₀ : 0 < t₀) (ht1 : t₀ ≤ 1) :
    |(∫ t in Ioi t₀, Real.exp (-t) / t)
        - (-Real.log t₀ - Real.eulerMascheroniConstant)|
      ≤ t₀ * (1 - 2 * Real.log t₀) := by
  have hlog0 : Real.log t₀ ≤ 0 := Real.log_nonpos ht₀.le ht1
  -- the `γ`-integral split at `t₀`
  have hI0 : IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Ioc (0 : ℝ) t₀) volume :=
    integrableOn_expNeg_mul_log_Ioi_zero.mono_set Ioc_subset_Ioi_self
  have hI1 : IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.log t) (Ioi t₀) volume :=
    integrableOn_expNeg_mul_log_Ioi ht₀.le
  have hunion : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.log t)
      = (∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t)
        + ∫ t in Ioi t₀, Real.exp (-t) * Real.log t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi ht₀.le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI0 hI1
  have hγ : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.log t)
      = -Real.eulerMascheroniConstant := Salt.Mertens.integral_exp_neg_log
  have htail : (∫ t in Ioi t₀, Real.exp (-t) * Real.log t)
      = -Real.eulerMascheroniConstant - ∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t := by
    rw [hγ] at hunion; linarith
  -- assemble
  have hmain := expIntegral_eq_sub ht₀
  rw [htail] at hmain
  have hkey : (∫ t in Ioi t₀, Real.exp (-t) / t)
      - (-Real.log t₀ - Real.eulerMascheroniConstant)
      = (1 - Real.exp (-t₀)) * Real.log t₀
        - ∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t := by
    rw [hmain]; ring
  rw [hkey]
  -- the two error pieces
  have hexp : 1 - Real.exp (-t₀) ≤ t₀ := by
    have := Real.add_one_le_exp (-t₀); linarith
  have hexp0 : 0 ≤ 1 - Real.exp (-t₀) := by
    have : Real.exp (-t₀) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hb1 : |(1 - Real.exp (-t₀)) * Real.log t₀| ≤ t₀ * (-Real.log t₀) := by
    rw [abs_mul, abs_of_nonneg hexp0, abs_of_nonpos hlog0]
    exact mul_le_mul_of_nonneg_right hexp (by linarith)
  have hb2 := abs_integral_expNeg_mul_log_Ioc_le ht₀ ht1
  calc |(1 - Real.exp (-t₀)) * Real.log t₀
          - ∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t|
      ≤ |(1 - Real.exp (-t₀)) * Real.log t₀|
          + |∫ t in Ioc (0 : ℝ) t₀, Real.exp (-t) * Real.log t| := abs_sub _ _
    _ ≤ t₀ * (-Real.log t₀) + (t₀ - t₀ * Real.log t₀) := by linarith
    _ = t₀ * (1 - 2 * Real.log t₀) := by ring

/-! ## §2 — HB's substitution `v = e^{t/(1−β₀)}` -/

/-- **The substitution.**  For `β₀ < 1` and `X ≥ 3`, with `t₀ := (1−β₀)·log X`,

    ∫_X^∞ v^{β₀−2}(log v)^{−1} dv  =  ∫_{t₀}^∞ e^{−t} dt/t.

(`v = e^{t/(1−β₀)}` turns `v^{β₀−2}·dv/log v` into `e^{−t}dt/t` exactly: `(1−β₀)` cancels
against `log v = t/(1−β₀)` and `dv = v dt/(1−β₀)`.) -/
theorem integral_rpow_div_log_Ioi_eq_expIntegral {β₀ X : ℝ} (hβ₀1 : β₀ < 1) (hX : 3 ≤ X) :
    (∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v)
      = ∫ t in Ioi ((1 - β₀) * Real.log X), Real.exp (-t) / t := by
  set c : ℝ := 1 - β₀ with hc
  have hc0 : 0 < c := by simp only [hc]; linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have he : Real.exp 1 ≤ X := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hX
    exact (Real.le_log_iff_exp_le hX0).mpr he
  set t₀ : ℝ := c * Real.log X with ht₀def
  have ht₀ : 0 < t₀ := by simp only [ht₀def]; positivity
  set φ : ℝ → ℝ := fun t => Real.exp (t / c) with hφ
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hφt₀ : φ t₀ = X := by
    have hdiv : t₀ / c = Real.log X := by
      simp only [ht₀def]; field_simp
    simp only [hφ, hdiv, Real.exp_log hX0]
  have hφderiv : ∀ t : ℝ, HasDerivAt φ (Real.exp (t / c) / c) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => s / c) (1 / c) t := (hasDerivAt_id t).div_const c
    have h2 := h1.exp
    rw [show Real.exp (t / c) * (1 / c) = Real.exp (t / c) / c by ring] at h2
    exact h2
  have hφmono : ∀ {a b : ℝ}, a ≤ b → φ a ≤ φ b := by
    intro a b hab
    simp only [hφ]
    exact Real.exp_le_exp.mpr (by gcongr)
  have hφtop : Tendsto φ atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    simpa [div_eq_mul_inv] using tendsto_id.atTop_mul_const (inv_pos.mpr hc0)
  -- the integrand identity on the `t`-side
  have hpt : ∀ t : ℝ, 0 < t → (Real.exp (t / c) / c) • ((fun v : ℝ => v ^ (β₀ - 2) /
      Real.log v) ∘ φ) t = Real.exp (-t) / t := by
    intro t ht
    have hE : (0 : ℝ) < Real.exp (t / c) := Real.exp_pos _
    have hlogφ : Real.log (φ t) = t / c := by simp only [hφ, Real.log_exp]
    have hrp : (φ t) ^ (β₀ - 2) = Real.exp ((t / c) * (β₀ - 2)) := by
      simp only [hφ, ← Real.exp_mul]
    simp only [Function.comp_apply, smul_eq_mul, hlogφ, hrp]
    have hkey : Real.exp (t / c) / c * (Real.exp (t / c * (β₀ - 2)) / (t / c))
        = Real.exp (t / c + t / c * (β₀ - 2)) / t := by
      rw [Real.exp_add]
      field_simp
    rw [hkey]
    have hz : t / c + t / c * (β₀ - 2) = -t := by
      have hb : β₀ - 1 = -c := by simp only [hc]; ring
      have hsplit : t / c + t / c * (β₀ - 2) = (t / c) * (β₀ - 1) := by ring
      rw [hsplit, hb]
      field_simp
    rw [hz]
  -- the finite substitution
  have hfin : ∀ t₁ : ℝ, t₀ ≤ t₁ →
      (∫ v in X..φ t₁, v ^ (β₀ - 2) / Real.log v) = ∫ t in t₀..t₁, Real.exp (-t) / t := by
    intro t₁ ht₁
    have himg : φ '' (uIcc t₀ t₁) ⊆ Ici X := by
      rintro v ⟨t, ht, rfl⟩
      rw [Set.uIcc_of_le ht₁] at ht
      exact hφt₀ ▸ hφmono ht.1
    have hmem3 : ∀ t ∈ Ici X, (3 : ℝ) ≤ t := fun t ht => le_trans hX (mem_Ici.mp ht)
    have hid : ContinuousOn (fun t : ℝ => t) (Ici X) := continuousOn_id
    have hgc : ContinuousOn (fun v : ℝ => v ^ (β₀ - 2) / Real.log v) (Ici X) := by
      refine ContinuousOn.div (hid.rpow_const
        (fun t ht => Or.inl (ne_of_gt (by linarith [hmem3 t ht]))))
        (Real.continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [hmem3 t ht])))
        (fun t ht => ne_of_gt (Real.log_pos (by linarith [hmem3 t ht])))
    have hsub := intervalIntegral.integral_deriv_smul_comp'
      (f := φ) (f' := fun t => Real.exp (t / c) / c)
      (g := fun v : ℝ => v ^ (β₀ - 2) / Real.log v) (a := t₀) (b := t₁)
      (fun t _ => hφderiv t)
      (((Real.continuous_exp.comp (continuous_id.div_const c)).div_const c).continuousOn)
      (hgc.mono himg)
    rw [hφt₀] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le ht₁] at ht
    exact hpt t (lt_of_lt_of_le ht₀ ht.1)
  -- pass to the limit
  have hLtend : Tendsto (fun t₁ : ℝ => ∫ v in X..φ t₁, v ^ (β₀ - 2) / Real.log v) atTop
      (𝓝 (∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v)) :=
    intervalIntegral_tendsto_integral_Ioi X (integrableOn_rpow_div_log hβ₀1 hX) hφtop
  have hRtend : Tendsto (fun t₁ : ℝ => ∫ t in t₀..t₁, Real.exp (-t) / t) atTop
      (𝓝 (∫ t in Ioi t₀, Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi t₀ (integrableOn_expNeg_div_Ioi ht₀) tendsto_id
  refine tendsto_nhds_unique hLtend (hRtend.congr' ?_)
  filter_upwards [eventually_ge_atTop t₀] with t₁ ht₁
  exact (hfin t₁ ht₁).symm

/-! ## §3 — the integral at the design's currency, with the window edge explicit -/

/-- **THE INTEGRAL (N4b W3, HB p.210) — the upper window edge consumed here and only here.**
With `η := ((1−β₀)L)^{−1}` and `L := log q`, for a split point `X` with `3 ≤ X` and
`log X ≤ 500·L` (i.e. `X ≤ q^{500}`, the window's UPPER edge):

    | ∫_X^∞ v^{β₀−2}(log v)^{−1} dv − (log(ηL) − log log X − γ₀) |
        ≤  500·(1 + 2·log(ηL)) / η.

The window exponent is **not** hidden in an `O(·)` (R4's finding): the `500` is literal, and it
enters exactly twice — once as `t₀ = (1−β₀)log X ≤ 500/η` (the size of the error) and once as the
side condition `t₀ ≤ 1`, which at this window *is* `hηlarge : 500 ≤ η`.  HB's `O(η^{−1} log η)`
is this bound with `log(ηL)` in place of `log η` (the honest currency: `log(ηL) = −log(1−β₀)`). -/
theorem hb_F_tail_integral {β₀ L η X : ℝ}
    (hβ₀1 : β₀ < 1) (hL : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hX : 3 ≤ X) (hwin : Real.log X ≤ 500 * L) (hηlarge : 500 ≤ η) :
    |(∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v)
        - (Real.log (η * L) - Real.log (Real.log X) - Real.eulerMascheroniConstant)|
      ≤ 500 * (1 + 2 * Real.log (η * L)) / η := by
  have hc0 : (0 : ℝ) < 1 - β₀ := by linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have he : Real.exp 1 ≤ X := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hX
    exact (Real.le_log_iff_exp_le hX0).mpr he
  have hη0 : 0 < η := by rw [hη]; positivity
  set t₀ : ℝ := (1 - β₀) * Real.log X with ht₀def
  have ht₀ : 0 < t₀ := by simp only [ht₀def]; positivity
  -- `ηL = (1−β₀)^{−1}`
  have hηL : η * L = 1 / (1 - β₀) := by rw [hη]; field_simp
  have hηLpos : (0 : ℝ) < η * L := by rw [hηL]; positivity
  -- the window: `t₀ ≤ 500/η ≤ 1`
  have ht₀win : t₀ ≤ 500 / η := by
    have h1 : t₀ ≤ (1 - β₀) * (500 * L) := by
      simp only [ht₀def]
      exact mul_le_mul_of_nonneg_left hwin hc0.le
    have h2 : (1 - β₀) * (500 * L) = 500 / η := by
      rw [hη]; field_simp
    linarith
  have ht₀1 : t₀ ≤ 1 := by
    have : (500 : ℝ) / η ≤ 1 := by
      rw [div_le_one hη0]; linarith
    linarith
  -- `−log t₀ = log(ηL) − log log X`
  have hlogt₀ : Real.log t₀ = -Real.log (η * L) + Real.log (Real.log X) := by
    simp only [ht₀def]
    rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt (by linarith : (0:ℝ) < Real.log X)), hηL,
      Real.log_div one_ne_zero (ne_of_gt hc0), Real.log_one]
    ring
  -- the substitution and §1
  rw [integral_rpow_div_log_Ioi_eq_expIntegral hβ₀1 hX, ← ht₀def]
  have hstone := expIntegral_sub_log_gamma_abs_le ht₀ ht₀1
  have hrewrite : (-Real.log t₀ - Real.eulerMascheroniConstant)
      = Real.log (η * L) - Real.log (Real.log X) - Real.eulerMascheroniConstant := by
    rw [hlogt₀]; ring
  rw [hrewrite] at hstone
  refine le_trans hstone ?_
  -- the two factors, each bounded separately (their product is what the window prices)
  have hfac : 1 - 2 * Real.log t₀ ≤ 1 + 2 * Real.log (η * L) := by
    rw [hlogt₀]
    have : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
    linarith
  have hfac0 : (0 : ℝ) ≤ 1 - 2 * Real.log t₀ := by
    have : Real.log t₀ ≤ 0 := Real.log_nonpos ht₀.le ht₀1
    linarith
  have hfin : t₀ * (1 - 2 * Real.log t₀) ≤ (500 / η) * (1 + 2 * Real.log (η * L)) := by
    have h1 : t₀ * (1 - 2 * Real.log t₀) ≤ (500 / η) * (1 - 2 * Real.log t₀) :=
      mul_le_mul_of_nonneg_right ht₀win hfac0
    have h2 : (500 / η) * (1 - 2 * Real.log t₀) ≤ (500 / η) * (1 + 2 * Real.log (η * L)) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    linarith
  have : (500 / η) * (1 + 2 * Real.log (η * L)) = 500 * (1 + 2 * Real.log (η * L)) / η := by
    field_simp
  linarith

/-! ## §4 — the `[z, X]` segment: `χ = 2·1_{χ=1} − 1_{(·,q)=1}`, and the `χ(p)=1` kill -/

/-- For a **real** character the value `χ(n)` is the real number `χ_ℝ(n) = (χ n).re`. -/
lemma chi_eq_ofReal_chiRe {q : ℕ} (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1) (n : ℕ) :
    χ (n : ZMod q) = ((Salt.TwinBar.chiRe χ n : ℝ) : ℂ) := by
  have hQ : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  rcases hQ (n : ZMod q) with h | h | h <;> simp [Salt.TwinBar.chiRe, h]

/-- **The detector identity** behind HB's split of `(4.7)`: for a real character,

    χ_ℝ(n) = 2·1_{χ_ℝ(n)=1} − 1_{(n,q)=1}

(zero off the coprimes; `2·1 − 1 = 1` and `2·0 − 1 = −1` on them). -/
lemma chiRe_eq_two_mul_ind_sub {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hsq : χ ^ 2 = 1) (n : ℕ) :
    Salt.TwinBar.chiRe χ n
      = 2 * (if Salt.TwinBar.chiRe χ n = 1 then (1 : ℝ) else 0)
        - (if Nat.Coprime n q then (1 : ℝ) else 0) := by
  by_cases hcop : Nat.Coprime n q
  · rw [if_pos hcop]
    rcases chiRe_eq_one_or_neg_one χ hsq hcop with h1 | h1
    · rw [h1, if_pos rfl]; ring
    · rw [h1, if_neg (by norm_num : ¬((-1 : ℝ) = 1))]; ring
  · rw [if_neg hcop]
    have hnu : ¬ IsUnit ((n : ZMod q)) := fun h => hcop ((ZMod.isUnit_iff_coprime n q).mp h)
    have hz : Salt.TwinBar.chiRe χ n = 0 := by
      simp [Salt.TwinBar.chiRe, MulChar.map_nonunit χ hnu]
    rw [hz, if_neg (by norm_num : ¬((0 : ℝ) = 1))]; ring

/-- **The segment decomposition (HB (4.7)).**  For a real `χ` the log-weighted window sum is real
and splits into HB's two halves — twice the `χ(p)=1` part (killed by Lemma 3) minus the part over
integers coprime to `q` (Mertens' second theorem):

    ∑_{z<n≤X} χ(n)Λ(n)/(n log n)
       = 2·∑_{z<n≤X, χ_ℝ(n)=1} Λ(n)/(n log n) − ∑_{z<n≤X, (n,q)=1} Λ(n)/(n log n). -/
theorem logChiSum_re_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hsq : χ ^ 2 = 1)
    (z X : ℝ) :
    (logChiSum χ z X).re
      = 2 * (∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Salt.TwinBar.chiRe χ n = 1),
              wLog n * vonMangoldt n)
        - ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
              wLog n * vonMangoldt n := by
  classical
  have hterm : ∀ n : ℕ,
      (((wLog n : ℝ) : ℂ) * (((vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q))).re
        = 2 * (if Salt.TwinBar.chiRe χ n = 1 then wLog n * vonMangoldt n else 0)
          - (if Nat.Coprime n q then wLog n * vonMangoldt n else 0) := by
    intro n
    rw [chi_eq_ofReal_chiRe χ hsq n, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    by_cases hcop : Nat.Coprime n q
    · rw [if_pos hcop]
      rcases chiRe_eq_one_or_neg_one χ hsq hcop with h1 | h1
      · rw [h1, if_pos rfl]; ring
      · rw [h1, if_neg (by norm_num : ¬((-1 : ℝ) = 1))]; ring
    · rw [if_neg hcop]
      have hnu : ¬ IsUnit ((n : ZMod q)) := fun h => hcop ((ZMod.isUnit_iff_coprime n q).mp h)
      have hz : Salt.TwinBar.chiRe χ n = 0 := by
        simp [Salt.TwinBar.chiRe, MulChar.map_nonunit χ hnu]
      rw [hz, if_neg (by norm_num : ¬((0 : ℝ) = 1))]; ring
  rw [logChiSum, Complex.re_sum]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter, ← Finset.sum_filter]

/-! ### The `χ(p)=1` half -/

/-- **The crude weight exchange.**  On `n > z` the log-weighted `Λ`-sum over `χ_ℝ = 1` *primes*
is at most `(log z)^{−1}` times HB's `PretenseSum` — the "`z₀ = L/log z`" factor of his p.209
estimate `≪ L(log z)^{−1}(log η)^{−1/2}`. -/
lemma chiOne_prime_logWeighted_le {q : ℕ} (χ : DirichletCharacter ℂ q) {z X : ℝ}
    (hz : 3 ≤ z) :
    ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1),
        wLog n * vonMangoldt n
      ≤ PretenseSum χ ⌊X⌋₊ / Real.log z := by
  classical
  have hz0 : (0 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  set S := (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1) with hS
  have hstep : ∀ n ∈ S, wLog n * vonMangoldt n ≤ (Real.log n / n) / Real.log z := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hlo, _⟩, hp, _⟩ := hn
    have h2 : z < (⌊z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one z
    have h3 : (⌊z⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlo
    have hnz : (z : ℝ) < n := by linarith
    have hn0 : (0 : ℝ) < n := by linarith
    have hlogn : Real.log z ≤ Real.log n := Real.log_le_log hz0 hnz.le
    have hlogn0 : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlogz hlogn
    have hΛ : (vonMangoldt n : ℝ) = Real.log n :=
      ArithmeticFunction.vonMangoldt_apply_prime hp
    rw [wLog, hΛ]
    have hL : ((n : ℝ) * Real.log (n : ℝ))⁻¹ * Real.log (n : ℝ) = 1 / (n : ℝ) := by
      field_simp
    rw [hL, div_div, one_div, le_div_iff₀ (by positivity)]
    have hcalc : ((n : ℝ))⁻¹ * ((n : ℝ) * Real.log z) = Real.log z := by field_simp
    rw [hcalc]
    exact hlogn
  have hsub : S ⊆ (Finset.range (⌊X⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ Salt.TwinBar.chiRe χ p = 1) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Ioc] at hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn.2⟩
  have hnn : ∀ i ∈ (Finset.range (⌊X⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ Salt.TwinBar.chiRe χ p = 1),
      i ∉ S → 0 ≤ Real.log (i : ℝ) / i := by
    intro i hi _
    rw [Finset.mem_filter] at hi
    have hp : Nat.Prime i := hi.2.1
    have : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hp.two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  calc ∑ n ∈ S, wLog n * vonMangoldt n
      ≤ ∑ n ∈ S, (Real.log n / n) / Real.log z := Finset.sum_le_sum hstep
    _ = (∑ n ∈ S, Real.log n / n) / Real.log z := by rw [Finset.sum_div]
    _ ≤ PretenseSum χ ⌊X⌋₊ / Real.log z := by
        have hsum : (∑ n ∈ S, Real.log (n : ℝ) / (n : ℝ)) ≤ PretenseSum χ ⌊X⌋₊ := by
          rw [PretenseSum]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
        exact (div_le_div_iff_of_pos_right hlogz).mpr hsum

/-- **The Rankin factor at the window's upper edge.**  `⌊X⌋^{1/(2L)} ≤ e^{250}` under
`log X ≤ 500·L` at the campaign's `Lp := 2L` — the **second** (and last) consumption of the
window's upper edge inside W3, exactly as the freeze predicts. -/
lemma rankin_floor_le {L X : ℝ} (hL : 0 < L) (hX : 0 ≤ X) (hwin : Real.log X ≤ 500 * L) :
    ((⌊X⌋₊ : ℝ)) ^ (1 / (2 * L)) ≤ Real.exp 250 := by
  rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) ⌊X⌋₊) with h0 | h0
  · rw [← h0, Real.zero_rpow (by positivity)]
    exact (Real.exp_pos 250).le
  · rw [Real.rpow_def_of_pos h0, Real.exp_le_exp]
    have hle : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX
    have hlog : Real.log (⌊X⌋₊ : ℝ) ≤ Real.log X := Real.log_le_log h0 hle
    have hinv : (0 : ℝ) < 1 / (2 * L) := by positivity
    have h1 : Real.log (⌊X⌋₊ : ℝ) * (1 / (2 * L)) ≤ (500 * L) * (1 / (2 * L)) :=
      mul_le_mul_of_nonneg_right (le_trans hlog hwin) hinv.le
    have h2 : (500 * L) * (1 / (2 * L)) = 250 := by field_simp; ring
    linarith

/-- **HB's Lemma 3 at the split point, with the Rankin factor discharged.**  Firing
`pretenseSum_unconditional_absorbed` at `σ = 1 + 1/Lp`, `σ′ = 1 + √ℓ/Lp` with `Lp := 2L` and
`N := ⌊X⌋`, and paying the window's upper edge once:

    2·PretenseSum χ ⌊X⌋ ≤ e^{250}·( (1−β₀)(2L)² + 2 + (802 + 4Cs)·2L/√ℓ ).

Every constant is literal; nothing is hidden in an `O(·)`. -/
theorem two_mul_pretenseSum_le_at_window {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f)
    {β₀ r0 Sinv Cs L ell X : ℝ}
    (hell : 1 ≤ ell) (hellL : ell ≤ 2 * L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * ((2 * L) ^ 2 / ell))
    (hCR : 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ 800 * (2 * L))
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hr0 : 0 < r0) (hσr : 1 / (2 * L) ≤ r0 / 2) (hσ'r : Real.sqrt ell / (2 * L) ≤ r0 / 2)
    (hL : 0 < L) (hX : 0 ≤ X) (hwin : Real.log X ≤ 500 * L) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (zeroMult χ ρ : ℝ)) ∧
      ((∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖) →
        (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        2 * PretenseSum χ ⌊X⌋₊
          ≤ Real.exp 250 * ((1 - β₀) * (2 * L) ^ 2
              + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell)))) := by
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hell
  have hLp : (0 : ℝ) < 2 * L := by linarith
  have hL1 : (1 : ℝ) ≤ 2 * L := le_trans hell hellL
  have hs : (0 : ℝ) < Real.sqrt ell := Real.sqrt_pos.mpr hell0
  have hs1 : (1 : ℝ) ≤ Real.sqrt ell := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt ell * Real.sqrt ell = ell := Real.mul_self_sqrt hell0.le
  have hsle : Real.sqrt ell ≤ 2 * L := le_trans (by nlinarith [hmul]) hellL
  have hinv0 : (0 : ℝ) < 1 / (2 * L) := by positivity
  have hinv1 : 1 / (2 * L) ≤ 1 := (div_le_one hLp).mpr hL1
  have hσ1 : (1 : ℝ) < 1 + 1 / (2 * L) := by linarith
  have hσ2 : 1 + 1 / (2 * L) ≤ 2 := by linarith
  have hlt : 1 + 1 / (2 * L) ≤ 1 + Real.sqrt ell / (2 * L) := by
    have := (div_le_div_iff_of_pos_right hLp).mpr hs1
    linarith
  have hσ'2 : 1 + Real.sqrt ell / (2 * L) ≤ 2 := by
    have := (div_le_one hLp).mpr hsle
    linarith
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    pretenseSum_unconditional_absorbed χ hχ hf ⌊X⌋₊
      (σ := 1 + 1 / (2 * L)) (σ' := 1 + Real.sqrt ell / (2 * L))
      (β₀ := β₀) (r0 := r0) (Sinv := Sinv)
      hσ1 hσ2 hlt hσ'2 hβlo hβ1 hβ0 hr0 (by linarith) (by linarith)
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, ?_⟩
  intro hfloor hSinv
  have hmain := hbody hfloor hSinv
  have hrate := hbCoreRate_at_hb_optimum_absorbed (Lp := 2 * L) (ell := ell)
    (Sinv := Sinv) (Cs := Cs)
    (CR := 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f))) hell hellL hCs hSinvC hCR
  have hexp : (1 + 1 / (2 * L)) - 1 = 1 / (2 * L) := by ring
  have hpole : (1 - β₀) / (1 / (2 * L) : ℝ) ^ 2 = (1 - β₀) * (2 * L) ^ 2 := by field_simp
  have hNn : (0 : ℝ) ≤ (⌊X⌋₊ : ℝ) ^ (1 / (2 * L) : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbrk : (0 : ℝ) ≤ (1 - β₀) * (2 * L) ^ 2
      + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell)) := by positivity
  have hstep : (⌊X⌋₊ : ℝ) ^ ((1 + 1 / (2 * L)) - 1)
        * ((1 - β₀) / ((1 + 1 / (2 * L)) - 1) ^ 2
          + hbCoreRate (1 + 1 / (2 * L)) (1 + Real.sqrt ell / (2 * L)) Sinv
              (1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f))
                * ((1 + Real.sqrt ell / (2 * L)) - (1 + 1 / (2 * L)))))
      ≤ (⌊X⌋₊ : ℝ) ^ (1 / (2 * L) : ℝ)
          * ((1 - β₀) * (2 * L) ^ 2 + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell))) := by
    rw [hexp, hpole]
    nlinarith [mul_le_mul_of_nonneg_left hrate hNn]
  have hrank : (⌊X⌋₊ : ℝ) ^ (1 / (2 * L) : ℝ)
        * ((1 - β₀) * (2 * L) ^ 2 + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell)))
      ≤ Real.exp 250
          * ((1 - β₀) * (2 * L) ^ 2 + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell))) :=
    mul_le_mul_of_nonneg_right (rankin_floor_le hL hX hwin) hbrk
  linarith

/-- **THE `χ(p)=1` HALF, KILLED (N4b W3, HB p.209).**  Composing the weight exchange with
Lemma 3 at the split point: for `3 ≤ z` and `log X ≤ 500·L`,

    2·∑_{z<p≤X, χ_ℝ(p)=1} Λ(p)/(p log p)
        ≤ e^{250}·( (1−β₀)(2L)² + 2 + (802+4Cs)·2L/√ℓ ) / log z.

At the design's operating point (`ℓ = log η`, `(1−β₀)L = η^{−1}`) the bracket is
`4L/η + 2 + (802+4Cs)·2L/√(log η)`, so the whole thing is HB's
`≪ L(log z)^{−1}(log η)^{−1/2} = z₀(log η)^{−1/2}` — with every constant literal. -/
theorem hb_chiOne_kill_at_window {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f)
    {β₀ r0 Sinv Cs L ell z X : ℝ}
    (hell : 1 ≤ ell) (hellL : ell ≤ 2 * L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * ((2 * L) ^ 2 / ell))
    (hCR : 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ 800 * (2 * L))
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hr0 : 0 < r0) (hσr : 1 / (2 * L) ≤ r0 / 2) (hσ'r : Real.sqrt ell / (2 * L) ≤ r0 / 2)
    (hL : 0 < L) (hz : 3 ≤ z) (hX : 0 ≤ X) (hwin : Real.log X ≤ 500 * L) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (zeroMult χ ρ : ℝ)) ∧
      ((∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖) →
        (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        2 * ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1),
              wLog n * vonMangoldt n
          ≤ Real.exp 250 * ((1 - β₀) * (2 * L) ^ 2
              + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell))) / Real.log z) := by
  classical
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    two_mul_pretenseSum_le_at_window χ hχ hf hell hellL hCs hSinvC hCR hβlo hβ1 hβ0 hr0
      hσr hσ'r hL hX hwin
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, ?_⟩
  intro hfloor hSinv
  have hP := hbody hfloor hSinv
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hkill := chiOne_prime_logWeighted_le χ (z := z) (X := X) hz
  calc 2 * ∑ n ∈ (Finset.Ioc ⌊z⌋₊ ⌊X⌋₊).filter (fun n => Nat.Prime n ∧ Salt.TwinBar.chiRe χ n = 1),
          wLog n * vonMangoldt n
      ≤ 2 * (PretenseSum χ ⌊X⌋₊ / Real.log z) := by linarith
    _ = (2 * PretenseSum χ ⌊X⌋₊) / Real.log z := by ring
    _ ≤ Real.exp 250 * ((1 - β₀) * (2 * L) ^ 2
          + (2 + (802 + 4 * Cs) * ((2 * L) / Real.sqrt ell))) / Real.log z := by
        gcongr

/-! ## §5 — the assembly: `log F` at the multiplicative mandate -/

/-- **W3's DELIVERABLE — `log F = log log z − log(ηL) + γ₀ + δ`, `δ` bounded by ONE explicit
sum (N4b W3, HB (4.7) + p.210).**

The three carried rows are exactly HB's own three inputs, each a *named binder* with an
*explicit* bound (no free additive remainder reaches W4):

* `hcorr` — HB's step 1, `log F = ∑_{n ≥ z} χ(n)Λ(n)/(n log n) + O(z^{−1/2})`: the Euler-product
  ↔ `Λ`-series conversion together with the `k ≥ 2` prime-power tail.  It carries **no zero
  information**; `logF` and the tail sum `Stail` ride as reals/complexes with this one bound.
* `hseg` — the `[z,X]` segment `= log log z − log log X + O(…)`: `logChiSum_re_eq` splits it, the
  `χ(p)=1` half is discharged by `hb_chiOne_kill_at_window` above, and the coprime half is
  Mertens' second theorem.
* `htail` — W2's socket `logChiSum_tendsto_of_envelope`, quoted **verbatim** in its `m`-weighted
  form; `hm1` (design v3 **D11**) collapses `m = 1`, which is the *only* multiplicity at which
  the F-side cancellation is valid.

Everything else — HB's `−∫_X^∞ v^{β₀−2}/log v dv = −log(ηL) + log log X + γ₀` — is proved here,
in §§1–3, and enters with the window's honest constant `500·(1 + 2 log(ηL))/η`. -/
theorem hb_logF_at_split_point {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {β₀ L η z X logF Ecorr Eseg Etail : ℝ} {Stail : ℂ}
    (hβ₀1 : β₀ < 1) (hL : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hX : 3 ≤ X) (hwin : Real.log X ≤ 500 * L) (hηlarge : 500 ≤ η)
    (hm1 : zeroMult χ (β₀ : ℂ) = 1)
    (htail : ‖Stail + ((zeroMult χ (β₀ : ℂ) : ℕ) : ℂ)
        * ((∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v : ℝ) : ℂ)‖ ≤ Etail)
    (hseg : |(logChiSum χ z X).re
        - (Real.log (Real.log z) - Real.log (Real.log X))| ≤ Eseg)
    (hcorr : |logF - ((logChiSum χ z X).re + Stail.re)| ≤ Ecorr) :
    |logF - (Real.log (Real.log z) - Real.log (η * L) + Real.eulerMascheroniConstant)|
      ≤ Ecorr + Eseg + Etail + 500 * (1 + 2 * Real.log (η * L)) / η := by
  set I : ℝ := ∫ v in Ioi X, v ^ (β₀ - 2) / Real.log v with hIdef
  -- §3: the integral
  have hInt := hb_F_tail_integral (β₀ := β₀) (L := L) (η := η) (X := X)
    hβ₀1 hL hη hX hwin hηlarge
  rw [← hIdef] at hInt
  -- `hm1` collapses the socket's `m`
  have hone : ((zeroMult χ (β₀ : ℂ) : ℕ) : ℂ) = 1 := by rw [hm1]; norm_num
  rw [hone, one_mul] at htail
  have hre : |Stail.re + I| ≤ Etail := by
    have hnorm := Complex.abs_re_le_norm (Stail + ((I : ℝ) : ℂ))
    have hre' : (Stail + ((I : ℝ) : ℂ)).re = Stail.re + I := by
      simp [Complex.add_re]
    rw [hre'] at hnorm
    linarith
  -- the four-term triangle inequality
  set C : ℝ := (logChiSum χ z X).re with hCdef
  set S : ℝ := Stail.re with hSdef
  set g : ℝ := Real.eulerMascheroniConstant with hgdef
  have hsplit : logF - (Real.log (Real.log z) - Real.log (η * L) + g)
      = (logF - (C + S)) + (C - (Real.log (Real.log z) - Real.log (Real.log X)))
        + (S + I) - (I - (Real.log (η * L) - Real.log (Real.log X) - g)) := by ring
  rw [hsplit]
  have h1 : |(logF - (C + S)) + (C - (Real.log (Real.log z) - Real.log (Real.log X)))
        + (S + I) - (I - (Real.log (η * L) - Real.log (Real.log X) - g))|
      ≤ |(logF - (C + S)) + (C - (Real.log (Real.log z) - Real.log (Real.log X))) + (S + I)|
        + |I - (Real.log (η * L) - Real.log (Real.log X) - g)| := abs_sub _ _
  have h2 : |(logF - (C + S)) + (C - (Real.log (Real.log z) - Real.log (Real.log X)))
        + (S + I)|
      ≤ |(logF - (C + S)) + (C - (Real.log (Real.log z) - Real.log (Real.log X)))|
        + |S + I| :=
    abs_add_le _ _
  have h3 : |(logF - (C + S)) + (C - (Real.log (Real.log z) - Real.log (Real.log X)))|
      ≤ |logF - (C + S)| + |C - (Real.log (Real.log z) - Real.log (Real.log X))| :=
    abs_add_le _ _
  linarith


end Salt.HB
