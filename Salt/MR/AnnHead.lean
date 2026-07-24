/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.GrandComp

/-!
# ANN-HEAD — the annular head pin (`AnnHead`)

The closing pin of the ball-moment campaign (`docs/exploration/ball-moment-design.md`,
⟦RATIFIED — THE B-PIN⟧, JYH 2026-07-23).  The zone analysis dissolved to the single
annular object: the T1 head is annular **by construction** (the resonant core is the
moment row's mass; the gap floor is landed; only zone C survives), so the head is not a
ball but the `M_range` annulus itself.

`annHead g t₀ X T σ` is the `L²` mass of the seam polynomial on the shifted line
`Re = 1 + σ`, integrated over the `M_range` frequency window
`(logX)^{1/15} ≤ |t| ≤ T + (logX)^{1/16}` (capped at `|t| ≤ X`).  Two byte-level pins:

* **The annulus** matches `M_range`'s window VERBATIM (`DistHalasz.M_range`,
  `(1/15)`/`(1/16)`/`X`-cap), so a window frequency `t` is *definitionally* a
  `window_sup_decay` membership witness — no conversion.
* **The integrand** at the `1 + σ` line matches `window_sup_decay_sq`'s object EXACTLY
  (`GrandComp.window_sup_decay_sq`), so the pointwise sup decay applies verbatim.

**The B-pin (the seam crossed on the counting side).**  The pin sits at `Re = 1 + σ`
rather than the classical `Re = 1` line.  This consumes `window_sup_decay` directly: the
last analytic stone (the `1 + σ → 1` decay-preserving line shift) never has to exist,
because the moment rows restate at `1 + σ` where the masses only shrink.  The seam is
crossed on the mechanical/counting side, not the analytic side.  (T-0 provenance: the
`M_range` window and its `(logX)^{1/16}` widening are the T-0 card's ball geometry;
`AMENDMENT J0`/`B4` re-froze the downstream socket to the `e^{−cM}` shape, `c = 1/e`.)

The stones:
* `annHead_le_measure_sup` — the measure×sup bound (setIntegral over the annulus ≤ its
  measure `≤ 2(T + (logX)^{1/16})` times the `t`-free `window_sup_decay_sq` sup).
* `annHead_grade` — the pin specialized at `σ = 1/logX` (where `σ·logX = 1` collapses the
  `2log(σL)` correction), giving the clean grade
  `annHead ≤ C·(T + (logX)^{1/16})·(logX)²·exp(−(2/e)·M_range)`.
* `annHead_le_socket` — the over-satisfaction of the existing `hhead` socket
  (`HalaszHead.hhead_supplier_trivial`): since `e^{−2cM} ≤ e^{−cM}` and the annular
  polylog `≪ X`, the annular object over-satisfies the bare-`X` socket
  `annHead ≤ C₁·X·exp(−(1/e)·M_range)` (on the honest polylog window `T ≤ logX`),
  the cheapest lawful wire (the socket re-grade question is deferred).
-/

noncomputable section

namespace Salt.MR

open MeasureTheory Filter Asymptotics
open scoped BigOperators

/-- **The annular head (`annHead`).**  The `L²` mass of the seam polynomial (the double
`ellLin` of the trivial-window seam coefficient) on the shifted line `Re = 1 + σ`,
integrated over the `M_range` frequency annulus `(logX)^{1/15} ≤ |t| ≤ T + (logX)^{1/16}`,
capped at `|t| ≤ X`.  The annulus matches `M_range`'s window verbatim; the integrand
matches `window_sup_decay_sq`'s object verbatim (the B-pin at `Re = 1 + σ`). -/
def annHead (g : ℕ → ℂ) (t₀ X T σ : ℝ) : ℝ :=
  ∫ t in {t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X},
    ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
        (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2

/-- **P2 — the measure×sup bound (`annHead_le_measure_sup`).**  The annular head is at
most the annulus measure (`≤ 2(T + (logX)^{1/16})`, via the honest inclusion into the
outer interval) times the `t`-free `window_sup_decay_sq` sup.  Every window frequency `t`
is definitionally a `window_sup_decay_sq` membership witness (the P1 byte-match), so the
pointwise square bound is uniform across the annulus. -/
theorem annHead_le_measure_sup {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (hT : 0 ≤ T) :
    annHead g t₀ X T σ
      ≤ 2 * (T + (Real.log X) ^ (1 / 16 : ℝ))
        * (Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
          * Real.exp (-(2 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48))) := by
  unfold annHead
  set S := {t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X} with hSdef
  set B := Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
      * Real.exp (-(2 / Real.exp 1)
          * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
              - 2 * Real.log (σ * Real.log X) - 48)) with hB
  -- `X > 1`, so `logX > 0` and the `(logX)^{1/16}` widening is nonnegative.
  have hσinv_pos : (0 : ℝ) < 1 / σ := by positivity
  have hexp1 : (1 : ℝ) < Real.exp (1 / σ) := by
    have := Real.add_one_le_exp (1 / σ); linarith
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hexp1 hYX
  have hlogXpos : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hr : (0 : ℝ) ≤ (Real.log X) ^ (1 / 16 : ℝ) := Real.rpow_nonneg hlogXpos.le _
  have hR0 : (0 : ℝ) ≤ 2 * (T + (Real.log X) ^ (1 / 16 : ℝ)) := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- measurability of the annulus (finite intersection of closed abs-conditions)
  have hmeas : MeasurableSet S :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      ((measurableSet_le continuous_abs.measurable measurable_const).inter
        (measurableSet_le continuous_abs.measurable measurable_const))
  -- the annulus sits inside the outer interval, so its measure is `≤ 2(T + (logX)^{1/16})`
  have hsub : S ⊆ Set.Icc (-(T + (Real.log X) ^ (1 / 16 : ℝ)))
      (T + (Real.log X) ^ (1 / 16 : ℝ)) := by
    intro t ht
    exact Set.mem_Icc.mpr (abs_le.mp ht.2.1)
  have hvol : volume S ≤ ENNReal.ofReal (2 * (T + (Real.log X) ^ (1 / 16 : ℝ))) := by
    refine le_trans (measure_mono hsub) ?_
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  have hfin : volume S < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have htoReal : (volume S).toReal ≤ 2 * (T + (Real.log X) ^ (1 / 16 : ℝ)) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal hR0] at h
  -- pointwise: every window frequency IS a `window_sup_decay_sq` witness (byte-match)
  have hdom : ∀ t ∈ S,
      ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤ B := by
    intro t ht
    rw [hB]
    exact window_sup_decay_sq (t₀ := t₀) hg hσ0 hσ1 hYX ht
  by_cases hInt : IntegrableOn (fun t : ℝ =>
      ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) S
  · calc (∫ t in S, ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
              (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2)
        ≤ ∫ _t in S, B :=
          setIntegral_mono_on hInt (integrableOn_const hfin.ne) hmeas hdom
      _ = (volume S).toReal • B := setIntegral_const B
      _ = (volume S).toReal * B := smul_eq_mul _ _
      _ ≤ 2 * (T + (Real.log X) ^ (1 / 16 : ℝ)) * B :=
          mul_le_mul_of_nonneg_right htoReal hB0
  · rw [integral_undef hInt]
    exact mul_nonneg hR0 hB0

/-- **P3 — the annular grade (`annHead_grade`).**  The pin specialized at `σ = 1/logX`.
There `σ·logX = 1`, so `2·log(σ·logX) = 0` (the seam-crossing correction vanishes) and
`1/σ² = (logX)²`; the constants collapse honestly (`exp(96/e)` from the `−48` term).  The
clean form:
  `annHead ≤ C·(T + (logX)^{1/16})·(logX)²·exp(−(2/e)·M_range(...))`,
`C = 2·C_F²·exp(96/e)` an honest absolute constant. -/
theorem annHead_grade (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X T : ℝ, Real.exp 1 ≤ X → 0 ≤ T →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C * (T + (Real.log X) ^ (1 / 16 : ℝ)) * (Real.log X) ^ 2
            * Real.exp (-(2 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
  refine ⟨2 * Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * Real.exp (96 / Real.exp 1),
    by positivity, fun X T hX hT => ?_⟩
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le one_pos hL1
  have hσ0 : (0 : ℝ) < 1 / Real.log X := by positivity
  have hσ1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hLpos]; exact hL1
  have hYX : Real.exp (1 / (1 / Real.log X)) ≤ X :=
    le_of_eq (by rw [one_div_one_div, Real.exp_log hXpos])
  have hP2 := annHead_le_measure_sup (t₀ := t₀) hg hσ0 hσ1 hYX hT
  refine hP2.trans (le_of_eq ?_)
  have hσL : (1 / Real.log X) * Real.log X = 1 := by field_simp
  have hL2 : (1 : ℝ) / (1 / Real.log X) ^ 2 = (Real.log X) ^ 2 := by
    rw [div_pow, one_pow, one_div_one_div]
  have hexp : Real.exp (-(2 / Real.exp 1)
        * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T - 2 * 0 - 48))
      = Real.exp (-(2 / Real.exp 1)
          * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
        * Real.exp (96 / Real.exp 1) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hσL, Real.log_one, hL2, hexp]
  ring

/-- **The `c·(logX)³ = o(X)` threshold (∃-packaged).**  For `c > 0` there is an `X₀` beyond
which `c·(logX)³ ≤ X` — the polylog `≪ X` absorption behind the socket over-satisfaction,
from `isLittleO_log_rpow_rpow_atTop` at exponents `3` and `1`. -/
private lemma logpow3_le_self_eventually (c : ℝ) (hc : 0 < c) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c * (Real.log X) ^ 3 ≤ X := by
  have hlo : (fun x : ℝ => Real.log x ^ (3 : ℝ)) =o[atTop] fun x : ℝ => x ^ (1 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop 3 (by norm_num : (0 : ℝ) < 1)
  have hbound := hlo.bound (show (0 : ℝ) < 1 / c by positivity)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max a 1, fun X hX => ?_⟩
  have hXa : a ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hkey := ha X hXa
  have h1nn : (0 : ℝ) ≤ Real.log X ^ (3 : ℝ) := Real.rpow_nonneg hlogXnn 3
  have h2nn : (0 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h1nn, Real.norm_of_nonneg h2nn, Real.rpow_one,
    show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hkey
  calc c * (Real.log X) ^ 3 ≤ c * (1 / c * X) := mul_le_mul_of_nonneg_left hkey hc.le
    _ = X := by rw [← mul_assoc, mul_one_div, div_self hc.ne', one_mul]

/-- **P3 corollary — the socket over-satisfaction (`annHead_le_socket`).**  The annular
object over-satisfies the existing `hhead` socket
(`HalaszHead.hhead_supplier_trivial`, `Uhead ≤ C₁·X·exp(−(1/e)·M_range(...))`): since
`M_range ≥ 0` gives `e^{−(2/e)M} ≤ e^{−(1/e)M}`, and on the honest polylog window
`T ≤ logX` the measure×`(logX)²` factor is `≪ X`, the grade collapses to the bare-`X`
socket shape.  This is the cheapest lawful wire — the annular head feeds the existing
socket unchanged; the socket re-grade to the `(T/X + 1)` shape is deferred. -/
theorem annHead_le_socket (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ X T : ℝ, X₀ ≤ X → 0 ≤ T → T ≤ Real.log X →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C₁ * X * Real.exp (-(1 / Real.exp 1)
            * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
  obtain ⟨C, hC0, hgrade⟩ := annHead_grade g hg t₀
  obtain ⟨X₁, hX₁⟩ := logpow3_le_self_eventually (2 * C + 1) (by linarith)
  refine ⟨1, max X₁ (Real.exp 1), zero_le_one, fun X T hX hT hTL => ?_⟩
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1' : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe
  have hLnn : (0 : ℝ) ≤ Real.log X := by linarith
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ n
  have hg1 := hgrade X T hXe hT
  have hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T :=
    Mrange_nonneg _ hSeamOne X T
  set M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T with hMdef
  -- the `(logX)^{1/16}` widening is `≤ logX`, so the measure factor is `≤ 2·logX`
  have hr_le : (Real.log X) ^ (1 / 16 : ℝ) ≤ Real.log X := by
    calc (Real.log X) ^ (1 / 16 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
  have hTr : T + (Real.log X) ^ (1 / 16 : ℝ) ≤ 2 * Real.log X := by linarith
  -- fold the polylog measure factor into `2C·(logX)³`
  have hstep1 : C * (T + (Real.log X) ^ (1 / 16 : ℝ)) * (Real.log X) ^ 2
        * Real.exp (-(2 / Real.exp 1) * M)
      ≤ 2 * C * (Real.log X) ^ 3 * Real.exp (-(2 / Real.exp 1) * M) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc C * (T + (Real.log X) ^ (1 / 16 : ℝ)) * (Real.log X) ^ 2
        = C * (Real.log X) ^ 2 * (T + (Real.log X) ^ (1 / 16 : ℝ)) := by ring
      _ ≤ C * (Real.log X) ^ 2 * (2 * Real.log X) :=
          mul_le_mul_of_nonneg_left hTr (mul_nonneg hC0 (by positivity))
      _ = 2 * C * (Real.log X) ^ 3 := by ring
  -- `e^{−(2/e)M} ≤ e^{−(1/e)M}` since `M ≥ 0`
  have hstep2 : 2 * C * (Real.log X) ^ 3 * Real.exp (-(2 / Real.exp 1) * M)
      ≤ 2 * C * (Real.log X) ^ 3 * Real.exp (-(1 / Real.exp 1) * M) := by
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (mul_nonneg (by norm_num) hC0) (pow_nonneg hLnn 3))
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_mul]
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ hM0
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  calc annHead g t₀ X T (1 / Real.log X)
      ≤ C * (T + (Real.log X) ^ (1 / 16 : ℝ)) * (Real.log X) ^ 2
          * Real.exp (-(2 / Real.exp 1) * M) := hg1
    _ ≤ 2 * C * (Real.log X) ^ 3 * Real.exp (-(2 / Real.exp 1) * M) := hstep1
    _ ≤ 2 * C * (Real.log X) ^ 3 * Real.exp (-(1 / Real.exp 1) * M) := hstep2
    _ ≤ X * Real.exp (-(1 / Real.exp 1) * M) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        have hlp := hX₁ X hX1'
        have hmono : 2 * C * (Real.log X) ^ 3 ≤ (2 * C + 1) * (Real.log X) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLnn 3)
        linarith
    _ = 1 * X * Real.exp (-(1 / Real.exp 1) * M) := by ring

end Salt.MR

/-! ## PROP-WIRE — the annular head wired into the T-chain

`annHead_le_socket` over-satisfies the `hhead` socket of the v5 trivial-seam decay chain
(`HalaszHead.T1_decay_trivial`, whose `hhead` binder is
`Uhead ≤ C₁·X·exp(−(1/e)·M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)` — the socket
the annular RHS matches BYTE-for-byte).  The two stones below discharge that binder with
the *concrete* annular object, so the v5 T-chain runs end to end with `Uhead` a real
integral rather than a named hypothesis (`T1_decay_annular`), and feed that into the
`Iunit ≤ Gunit` socket of the terminal `Prop1Assembly.prop_A3'_assembly` (`prop_A3_T1_row_annular`).

Provenance: the B-pin (`annHead_le_socket`, `Re = 1 + σ`) → the socket
(`T1_decay_trivial.hhead`) → this wire.  The single remaining conditionality is the R3.1
floor `hfloor : (1/32)·loglog X ≤ M_range (…)` (the MULT-SHIU / HUPPER-supplied analytic
input) and the tail ledger `htail` — both carried as hypotheses exactly as the consumer does.

**Smooth-bridge mootness (the confirming look).**  The annular consumption path
—`annHead` → `GrandComp.window_sup_decay_sq` → `GrandComp.window_sup_decay` →
`SupF.head_sigma_bound` (+ `SupF.scale_floor_Mrange_seam`)— carries the seam head in the
`LSeries (ellLin …)` form throughout, priced by `SupF.euler_log_bound` (`SupF.lean:186`, the
absolutely-convergent Euler-product log estimate at `Re = 1 + σ > 1`).  It NEVER invokes
`smoothSeries`/`smoothEuler`: those (`SupF.lean:250–421`) are the finite-Euler-product
analytic continuation used only by the SEPARATE short-interval/"corpus" path, where the
`smoothSeries` `tsum` is non-summable and one continues via the finite product.  On the
`Re = 1 + σ` annular route the L-series is consumed directly (the B-pin crosses the seam on
the counting side), so the `smoothSeries ↔ smoothEuler` bridge is MOOT — no remaining
dependence.  (This note lives in the appended region, not the landed module docstring, to
keep the landed bytes frozen.) -/

namespace Salt.MR

/-- **W1 — the annular T1 decay (`T1_decay_annular`).**  The v5 T-chain decay theorem with
the head object CONCRETE: `T1_decay_trivial` (the cleanest consumer — it applies the R3.1
floor to deliver the final `(log X)^{−1/(32e)}` grade) instantiated at the trivial seam
datum `f = ellLin g`, with `Uhead := annHead g t₀ X T (1/log X)` and its `hhead` binder
DISCHARGED by `annHead_le_socket`.  `U := annHead + Utail`, `hsplit := rfl`; the tail ledger
`htail` and the R3.1 floor `hfloor` are carried as hypotheses (the honest remaining
conditionality, per the consumer).  The threshold `X₀ = max (socket X₀) (e)` folds the
socket's polylog-`≪ X` cutoff with the `e ≤ X` gate so `X₀ ≤ X` supplies both the socket's
`X₀ ≤ X` and `T1_decay_trivial`'s `Real.exp 1 ≤ X`.  This is the FIRST point where the head
`Uhead` is a real object end to end (the annular integral, not a named binder). -/
theorem T1_decay_annular (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ Real.log X → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X) + Utail
        ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hsock⟩ := annHead_le_socket g hg t₀
  refine ⟨C₁, max X₀ (Real.exp 1), hC₁, ?_⟩
  intro X ε Utail C₂ T hX hT hTL hε hC₂ htail hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hf : ∀ n, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  exact T1_decay_trivial hf t₀ t hXe hε hC₁ hC₂ rfl
    (hsock X T hX0 hT hTL) htail hfloor

/-- **W2 — the annular `int_U` row (`prop_A3_T1_row_annular`).**  W1 fed into the
`Iunit ≤ Gunit` socket of the terminal `Prop1Assembly.prop_A3'_assembly`: with the §8 eq-(24)
split `Itot = (annHead + Utail) + Imom` (hypothesis `hsplit`, the `int_U` row instantiated at
the annular head) and the moment grade `hmom : Imom ≤ Gmom`, the mean square is bounded by
the annular Halász grade plus the moment grade.  The assembly glue (`rw [hsplit]; linarith`)
is reproduced inline rather than importing `prop_A3'_assembly`, because the annular file sits
UPSTREAM of the assembly (import DAG: `AnnHead → GrandComp → HalaszHead`; `Prop1Assembly` is a
downstream terminal), and `Itot`/`Imom`/`Gmom`/the mean square `spoly` are held abstract so the
row is stated without that import — the socket `prop_A3'_assembly` consumes is exactly this
`Iunit ≤ Gunit` shape.

**Datum note (honest, no forced conversion).**  `prop_A3'_assembly`'s designated `hunit`
discharger `T1_decay_corrected_fgJ` uses the `fgJ` datum and the *corrected* R3.1 floor,
carrying the `o(1)` inflation `exp(c·(5·logloglog(2X+16)+Cfl))` IN the grade.  This wire
instead uses the `ellLin g` trivial-seam datum and the *clean* floor (the v5 route), so its
`Gunit` is the clean `(C₁+C₂)·X·((log X)^{−c/32} + (log X)^{−1/2+ε})`.  Both fit the abstract
socket; no datum conversion is forced.  The `fgJ`/corrected-floor twin is the one-line variant
obtained by swapping `annHead_le_socket`'s clean grade for the corrected-floor supplier. -/
theorem prop_A3_T1_row_annular (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T Itot Imom Gmom : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ Real.log X → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      Itot = (annHead g t₀ X T (1 / Real.log X) + Utail) + Imom →
      Imom ≤ Gmom →
      Itot ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) + Gmom := by
  obtain ⟨C₁, X₀, hC₁, hrow⟩ := T1_decay_annular g hg t₀ t
  refine ⟨C₁, X₀, hC₁, ?_⟩
  intro X ε Utail C₂ T Itot Imom Gmom hX hT hTL hε hC₂ htail hfloor hsplit hmom
  have hunit := hrow X ε Utail C₂ T hX hT hTL hε hC₂ htail hfloor
  rw [hsplit]; linarith [hunit, hmom]

end Salt.MR

/-! ## PROP-WIRE-T — the annular tail socket discharged

`T1_decay_annular`'s `Utail` binder is the last abstract object on the head/tail side of the
v5 T-chain.  The stone below discharges it at the CONCRETE landed S2′ tail object — the tail
ledger `HalaszHead.head_prep_utail` (⟸ `HalaszSeam.s2_tail_ledger`, the landed
`Tsplit = (log X)^4` tail closure) bounds VERBATIM the object the `htail` binder demands, so
the tail slot needs no named hypothesis and no adapter.

**No mismatch with the annular split's complement.**  `T1_decay_annular` carries `Utail`
purely as *any* real satisfying `Utail ≤ C₂·X·(log X)^{−1/2}` (its `hsplit := rfl` fixes only
`U = annHead + Utail`, imposing no shape on the tail).  The S2′ ledger object is a concrete
real satisfying exactly that bound, so instantiation is DIRECT — the tail integral's landed
ledger closure feeds the annular tail slot with byte-consistent `C₂` and `(log X)^{−1/2}`
grade.  (This note lives in the appended region, keeping the landed bytes frozen.) -/

namespace Salt.MR

/-- **W1-T — the annular T1 decay, tail wired (`T1_decay_annular_tailed`).**  `T1_decay_annular`
with its abstract `Utail` binder DISCHARGED at the concrete landed S2′ tail object.  The tail
slot is instantiated with the honest S2′ tail ledger shape

  `(Csup·L³)·(√L·X·(L⁴)⁻¹)`   (`L = log X`),

i.e. the sup-integrand bound `Csup·L³` times the hat-kernel tail mass `√L·X·(L⁴)⁻¹`, whose
`htail` bound `≤ Csup·X·L^{−1/2}` is supplied VERBATIM by `head_prep_utail`
(⟸ `s2_tail_ledger`).  So `C₂ := Csup`, and the T-chain now runs with BOTH the head (`annHead`,
the annular integral) and the tail (the S2′ ledger object) as CONCRETE objects — neither side
is a named binder any longer.  No adapter: `T1_decay_annular` treats `Utail` as any real ≤ the
bound, and the S2′ object satisfies it directly (see the section note on the split's complement).

The threshold `X₀ = max (annular X₀) (e²)` folds the annular socket's cutoff with the `e² ≤ X`
gate: `X₀ ≤ X` supplies both `T1_decay_annular`'s inputs and `head_prep_utail`'s strict
`1 < log X` (from `log X ≥ 2`, the `e²` gate strengthening the annular chain's own `e ≤ X`).

**Socket census after this stone.**  Head: CONCRETE (`annHead g t₀ X T (1/log X)`).  Tail:
CONCRETE (the S2′ ledger object `(Csup·L³)·(√L·X·(L⁴)⁻¹)`).  Remaining ABSTRACT: `hfloor` — the
R3.1 `(1/32)·loglog X` branch floor (the standing MULT-SHIU / branch analytic supply), carried
as a hypothesis exactly as the chain does; and the moment row (`Imom ≤ Gmom` in
`prop_A3_T1_row_annular`, abstract only by import-DAG position — `Prop1Assembly` is the
downstream terminal).  The head/tail side of the annular T-chain is now fully concrete. -/
theorem T1_decay_annular_tailed (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Csup T : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ Real.log X → 0 ≤ ε → 0 ≤ Csup →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X)
          + (Csup * (Real.log X) ^ 3)
              * (Real.sqrt (Real.log X) * X * ((Real.log X) ^ 4)⁻¹)
        ≤ (C₁ + Csup) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hchain⟩ := T1_decay_annular g hg t₀ t
  refine ⟨C₁, max X₀ (Real.exp 2), hC₁, ?_⟩
  intro X ε Csup T hX hT hTL hε hCsup hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe2 : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXe2
  -- `X ≥ e²` gives `log X ≥ 2 > 1`, the strict gate `head_prep_utail`/`s2_tail_ledger` need
  have hLog2 : (2 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe2
  have hL1 : (1 : ℝ) < Real.log X := by linarith
  -- the concrete tail bound, VERBATIM `T1_decay_annular`'s `htail` binder at `C₂ := Csup`
  have htail := head_prep_utail hL1 hXpos.le hCsup
  exact hchain X ε _ Csup T hX0 hT hTL hε hCsup htail hfloor

end Salt.MR
