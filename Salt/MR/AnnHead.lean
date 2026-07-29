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
`(logX)^{1/45} ≤ |t| ≤ T + (logX)^{1/46}` (capped at `|t| ≤ X`).  Two byte-level pins:

* **The annulus** matches `M_range`'s window VERBATIM (`DistHalasz.M_range`,
  `(1/45)`/`(1/46)`/`X`-cap), so a window frequency `t` is *definitionally* a
  `window_sup_decay` membership witness — no conversion.
* **The integrand** at the `1 + σ` line matches `window_sup_decay_sq`'s object EXACTLY
  (`GrandComp.window_sup_decay_sq`), so the pointwise sup decay applies verbatim.

**The B-pin (the seam crossed on the counting side).**  The pin sits at `Re = 1 + σ`
rather than the classical `Re = 1` line.  This consumes `window_sup_decay` directly: the
last analytic stone (the `1 + σ → 1` decay-preserving line shift) never has to exist,
because the moment rows restate at `1 + σ` where the masses only shrink.  The seam is
crossed on the mechanical/counting side, not the analytic side.  (T-0 provenance: the
`M_range` window and its `(logX)^{1/46}` widening are the T-0 card's ball geometry;
`AMENDMENT J0`/`B4` re-froze the downstream socket to the `e^{−cM}` shape, `c = 1/e`.)

The stones:
* `annHead_le_measure_sup` — the measure×sup bound (setIntegral over the annulus ≤ its
  measure `≤ 2(T + (logX)^{1/46})` times the `t`-free `window_sup_decay_sq` sup).
* `annHead_grade` — the pin specialized at `σ = 1/logX` (where `σ·logX = 1` collapses the
  `2log(σL)` correction), giving the clean grade
  `annHead ≤ C·(T + (logX)^{1/46})·(logX)²·exp(−(2/e)·M_range)`.
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
integrated over the `M_range` frequency annulus `(logX)^{1/45} ≤ |t| ≤ T + (logX)^{1/46}`,
capped at `|t| ≤ X`.  The annulus matches `M_range`'s window verbatim; the integrand
matches `window_sup_decay_sq`'s object verbatim (the B-pin at `Re = 1 + σ`). -/
def annHead (g : ℕ → ℂ) (t₀ X T σ : ℝ) : ℝ :=
  ∫ t in {t : ℝ | (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X},
    ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
        (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2

/-- **P2 — the measure×sup bound (`annHead_le_measure_sup`).**  The annular head is at
most the annulus measure (`≤ 2(T + (logX)^{1/46})`, via the honest inclusion into the
outer interval) times the `t`-free `window_sup_decay_sq` sup.  Every window frequency `t`
is definitionally a `window_sup_decay_sq` membership witness (the P1 byte-match), so the
pointwise square bound is uniform across the annulus. -/
theorem annHead_le_measure_sup {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (hT : 0 ≤ T) :
    annHead g t₀ X T σ
      ≤ 2 * (T + (Real.log X) ^ (1 / 46 : ℝ))
        * (Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
          * Real.exp (-(2 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48))) := by
  unfold annHead
  set S := {t : ℝ | (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X} with hSdef
  set B := Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
      * Real.exp (-(2 / Real.exp 1)
          * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
              - 2 * Real.log (σ * Real.log X) - 48)) with hB
  -- `X > 1`, so `logX > 0` and the `(logX)^{1/46}` widening is nonnegative.
  have hσinv_pos : (0 : ℝ) < 1 / σ := by positivity
  have hexp1 : (1 : ℝ) < Real.exp (1 / σ) := by
    have := Real.add_one_le_exp (1 / σ); linarith
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hexp1 hYX
  have hlogXpos : (0 : ℝ) < Real.log X := Real.log_pos hX1
  have hr : (0 : ℝ) ≤ (Real.log X) ^ (1 / 46 : ℝ) := Real.rpow_nonneg hlogXpos.le _
  have hR0 : (0 : ℝ) ≤ 2 * (T + (Real.log X) ^ (1 / 46 : ℝ)) := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- measurability of the annulus (finite intersection of closed abs-conditions)
  have hmeas : MeasurableSet S :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      ((measurableSet_le continuous_abs.measurable measurable_const).inter
        (measurableSet_le continuous_abs.measurable measurable_const))
  -- the annulus sits inside the outer interval, so its measure is `≤ 2(T + (logX)^{1/46})`
  have hsub : S ⊆ Set.Icc (-(T + (Real.log X) ^ (1 / 46 : ℝ)))
      (T + (Real.log X) ^ (1 / 46 : ℝ)) := by
    intro t ht
    exact Set.mem_Icc.mpr (abs_le.mp ht.2.1)
  have hvol : volume S ≤ ENNReal.ofReal (2 * (T + (Real.log X) ^ (1 / 46 : ℝ))) := by
    refine le_trans (measure_mono hsub) ?_
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  have hfin : volume S < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have htoReal : (volume S).toReal ≤ 2 * (T + (Real.log X) ^ (1 / 46 : ℝ)) := by
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
      _ ≤ 2 * (T + (Real.log X) ^ (1 / 46 : ℝ)) * B :=
          mul_le_mul_of_nonneg_right htoReal hB0
  · rw [integral_undef hInt]
    exact mul_nonneg hR0 hB0

/-- **P3 — the annular grade (`annHead_grade`).**  The pin specialized at `σ = 1/logX`.
There `σ·logX = 1`, so `2·log(σ·logX) = 0` (the seam-crossing correction vanishes) and
`1/σ² = (logX)²`; the constants collapse honestly (`exp(96/e)` from the `−48` term).  The
clean form:
  `annHead ≤ C·(T + (logX)^{1/46})·(logX)²·exp(−(2/e)·M_range(...))`,
`C = 2·C_F²·exp(96/e)` an honest absolute constant. -/
theorem annHead_grade (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X T : ℝ, Real.exp 1 ≤ X → 0 ≤ T →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
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
  -- the `(logX)^{1/46}` widening is `≤ logX`, so the measure factor is `≤ 2·logX`
  have hr_le : (Real.log X) ^ (1 / 46 : ℝ) ≤ Real.log X := by
    calc (Real.log X) ^ (1 / 46 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
  have hTr : T + (Real.log X) ^ (1 / 46 : ℝ) ≤ 2 * Real.log X := by linarith
  -- fold the polylog measure factor into `2C·(logX)³`
  have hstep1 : C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
        * Real.exp (-(2 / Real.exp 1) * M)
      ≤ 2 * C * (Real.log X) ^ 3 * Real.exp (-(2 / Real.exp 1) * M) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
        = C * (Real.log X) ^ 2 * (T + (Real.log X) ^ (1 / 46 : ℝ)) := by ring
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
      ≤ C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
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

/-! ## T-RESHAPE — the general-`T` socket (the `(T/X + 1)` re-grade)

Every landed annular row above gates at `T ≤ Real.log X`.  The gate is an artifact of the
socket's SHAPE, not of the analysis: `annHead_le_socket` prices the annulus measure by the
OUTER interval `2(T + (logX)^{1/46})` and then absorbs the whole `measure × (logX)²` factor
into the bare `X` of the `hhead` socket — which only fits while `T ≲ logX`.  The Lemma-14 /
Prop-1 consumers need `T` up to `X/h₁` (`Lemma14.lemma14_contour`'s `hMsup` datum sits at
`T = X/h₁`, and `h₁ ≥ 1` there), so the gate is BINDING.  The rows below retire it.

Two honest facts do the work.

* **The `X`-cap is already inside the annulus.**  `annHead`'s window carries `|t| ≤ X`
  VERBATIM (the `M_range` cap), so the annulus measure is `≤ 2X` for EVERY `T` — the outer
  interval is not the only cage.  `annHead_le_measure_sup_capX` re-runs the landed
  measure×sup page against that cap (no `T`-hypothesis at all);
  `annHead_grade_capX` is its `σ = 1/logX` specialization.

* **The honest general-`T` socket carries a `(logX)²`.**  The `σ = 1/logX` sup is
  `≍ (logX)²·e^{−(2/e)M}` (the `1/σ²` of `window_sup_decay_sq`), so the measure×sup grade is
  `X·(logX)²·e^{−(2/e)M}`.  Under `T ≤ logX` the landed row hid that polylog inside `X`
  (via `(logX)³ ≤ X`); at `T ≍ X` the measure has eaten all the room and there is nothing
  left to hide it in.  So the UNCONDITIONAL general-`T` socket is the `(T/X + 1)`-weighted
  grade WITH the polylog: `annHead ≤ C₁·(T/X + 1)·X·(logX)²·e^{−(1/e)M}`
  (`annHead_le_socket_T`, no upper `T`-gate).

**The exchange rate — and the CEILING that blocks it (read before wiring).**
`(logX)²·e^{−(1/e)M} ≤ 1` holds exactly when `M ≥ 2e·loglog X`, so the target socket
`C₁·(T/X + 1)·X·e^{−(1/e)M}` DOES hold for every `T ≥ 0` under the strengthened branch floor
`2e·loglog X ≤ M_range (…)` (`annHead_le_socket_T_of_floor` and the `…_T_of_floor` rows).
But that hypothesis EXCEEDS `M_range`'s structural ceiling: `M_range` is an infimum of
`pretDistSq f (costwist t) X = ∑_{p≤X} (1 − Re f(p)·conj g(p))/p` over 1-bounded data, so
every term is `≤ 2/p` and Mertens gives `M_range ≤ 2·loglog X + O(1)` — the extreme value
evaluated in `Dist.pretDistSq_principal_eval`.  Since `2e ≈ 5.44 > 2`, the strong floor is
ASYMPTOTICALLY UNSATISFIABLE: those rows are true theorems and exact exchange-rate
certificates, but they are NOT a usable socket.  Do not wire them.

**The residual, priced.**  With the best admissible floor `M ≥ 2·loglog X` the spare decay
is only `e^{−(1/e)M} ≤ (logX)^{−2/e}`, so the crude measure×sup route falls short of the
bare-`X` socket at `T ≍ X` by exactly `(logX)^{2 − 2/e} = (logX)^{1.264…}`.  That deficit is
intrinsic to measure×sup over a range of length `≍ X`: pricing a window of length `X` by its
pointwise sup discards everything.  The right engine at `T ≍ X` is the MEAN-VALUE moment row
(`Prop1Assembly.moment_core_bound` / `Ej_row`, the `(2T + 20N)` masses) — which is already
`T`-general and carries no gate.  This is the honest break, not a missing tactic.

**What IS unconditionally available.**  The bare-`X` socket survives verbatim for `T` up to
ANY fixed power of `logX`: `annHead_le_socket_polyT` (gate `T ≤ (logX)^A`, `A : ℕ`, `A ≥ 1`;
`A = 1` recovers the landed `annHead_le_socket`), because `(logX)^{A+2} ≪ X`.  For Lemma 14
that covers the large-`h₁` end of its range (`T = X/h₁ ≤ (logX)^A` ⟺ `h₁ ≥ X·(logX)^{−A}`),
and `h₁ ≤ h₂ ≤ X·(logX)^{−1/5}` there, so the range is non-empty.  Below that, the
unconditional statement is the polylog-graded `annHead_le_socket_T`.

At the Lemma-14 instantiation `T = X/h₁` with `h₁ ≥ 1` the weight `(T/X + 1) = 1/h₁ + 1 ≤ 2`
in every flavour, so the weight itself is never the obstruction — only the `(logX)²` is.

The constants are honest and explicit: `C = 2·C_F²·exp(96/e)` throughout (the same constant
as `annHead_grade`, the `2` being the interval-vs-radius factor and `exp(96/e)` the `−48`
seam-correction), and `C₁ = C` (`C₁ = 1` in the `polyT` row, as in the landed socket). -/

namespace Salt.MR

open MeasureTheory Filter Asymptotics

/-- **R1a — the `X`-capped measure×sup bound (`annHead_le_measure_sup_capX`).**  The landed
`annHead_le_measure_sup` page re-run against the annulus's OWN `|t| ≤ X` cap instead of the
outer interval `|t| ≤ T + (logX)^{1/46}`: the window sits inside `[-X, X]`, so its measure is
`≤ 2X` for every `T` — no `T`-hypothesis is needed, in either direction.  The pointwise
`window_sup_decay_sq` step is byte-identical to the landed one (every window frequency is a
membership witness by construction). -/
theorem annHead_le_measure_sup_capX {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ X T σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X) :
    annHead g t₀ X T σ
      ≤ 2 * X
        * (Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
          * Real.exp (-(2 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                  - 2 * Real.log (σ * Real.log X) - 48))) := by
  unfold annHead
  set S := {t : ℝ | (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X} with hSdef
  set B := Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * (1 / σ ^ 2)
      * Real.exp (-(2 / Real.exp 1)
          * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
              - 2 * Real.log (σ * Real.log X) - 48)) with hB
  have hσinv_pos : (0 : ℝ) < 1 / σ := by positivity
  have hexp1 : (1 : ℝ) < Real.exp (1 / σ) := by
    have := Real.add_one_le_exp (1 / σ); linarith
  have hX1 : (1 : ℝ) < X := lt_of_lt_of_le hexp1 hYX
  have hR0 : (0 : ℝ) ≤ 2 * X := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hmeas : MeasurableSet S :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      ((measurableSet_le continuous_abs.measurable measurable_const).inter
        (measurableSet_le continuous_abs.measurable measurable_const))
  -- the annulus sits inside `[-X, X]` by its OWN cap, so its measure is `≤ 2X`
  have hsub : S ⊆ Set.Icc (-X) X := fun t ht => Set.mem_Icc.mpr (abs_le.mp ht.2.2)
  have hvol : volume S ≤ ENNReal.ofReal (2 * X) := by
    refine le_trans (measure_mono hsub) ?_
    rw [Real.volume_Icc]
    apply le_of_eq
    congr 1
    ring
  have hfin : volume S < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have htoReal : (volume S).toReal ≤ 2 * X := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal hR0] at h
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
      _ ≤ 2 * X * B := mul_le_mul_of_nonneg_right htoReal hB0
  · rw [integral_undef hInt]
    exact mul_nonneg hR0 hB0

/-- **R1b — the `X`-capped annular grade (`annHead_grade_capX`).**  `annHead_le_measure_sup_capX`
specialized at `σ = 1/logX` exactly as `annHead_grade` specializes the landed page
(`σ·logX = 1` kills the `2log(σL)` correction, `1/σ² = (logX)²`, `exp(96/e)` from `−48`):
  `annHead ≤ C·X·(logX)²·exp(−(2/e)·M_range(...))`  for EVERY `T`,
`C = 2·C_F²·exp(96/e)` the same honest absolute constant as `annHead_grade`. -/
theorem annHead_grade_capX (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X T : ℝ, Real.exp 1 ≤ X →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C * X * (Real.log X) ^ 2
            * Real.exp (-(2 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
  refine ⟨2 * Real.exp (cpeel + (Real.log 4 + cpeel)) ^ 2 * Real.exp (96 / Real.exp 1),
    by positivity, fun X T hX => ?_⟩
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le one_pos hL1
  have hσ0 : (0 : ℝ) < 1 / Real.log X := by positivity
  have hσ1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hLpos]; exact hL1
  have hYX : Real.exp (1 / (1 / Real.log X)) ≤ X :=
    le_of_eq (by rw [one_div_one_div, Real.exp_log hXpos])
  have hP2 := annHead_le_measure_sup_capX (t₀ := t₀) (T := T) hg hσ0 hσ1 hYX
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

/-- **R1 — the general-`T` socket, unconditional (`annHead_le_socket_T`).**  The honest
`(T/X + 1)`-weighted re-grade of `annHead_le_socket`, with NO upper gate on `T`:
  `annHead ≤ C₁·(T/X + 1)·X·(logX)²·exp(−(1/e)·M_range(...))`.
Two cheap steps off `annHead_grade_capX`: `M_range ≥ 0` gives `e^{−(2/e)M} ≤ e^{−(1/e)M}`,
and `T/X + 1 ≥ 1` inflates the weight into the socket shape.  The `(logX)²` is the honest
residue — it is what `annHead_le_socket` hid inside the bare `X` using `T ≤ logX`, and at
`T ≍ X` there is no room left to hide it (see `annHead_le_socket_T_of_floor` for the exact
price of removing it). -/
theorem annHead_le_socket_T (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ X T : ℝ, X₀ ≤ X → 0 ≤ T →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C₁ * (T / X + 1) * X * (Real.log X) ^ 2
            * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
  obtain ⟨C, hC0, hgrade⟩ := annHead_grade_capX g hg t₀
  refine ⟨C, Real.exp 1, hC0, fun X T hX hT => ?_⟩
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ n
  have hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T :=
    Mrange_nonneg _ hSeamOne X T
  have hg1 := hgrade X T hX
  set M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T with hMdef
  have hw : (1 : ℝ) ≤ T / X + 1 := by
    have hTX : (0 : ℝ) ≤ T / X := div_nonneg hT hXpos.le
    linarith
  have hexp : Real.exp (-(2 / Real.exp 1) * M) ≤ Real.exp (-(1 / Real.exp 1) * M) := by
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_mul]
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ hM0
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hbase : (0 : ℝ) ≤ C * X * (Real.log X) ^ 2 :=
    mul_nonneg (mul_nonneg hC0 hXpos.le) (by positivity)
  have hrest : (0 : ℝ) ≤ X * (Real.log X) ^ 2 * Real.exp (-(1 / Real.exp 1) * M) :=
    mul_nonneg (mul_nonneg hXpos.le (by positivity)) (Real.exp_nonneg _)
  calc annHead g t₀ X T (1 / Real.log X)
      ≤ C * X * (Real.log X) ^ 2 * Real.exp (-(2 / Real.exp 1) * M) := hg1
    _ ≤ C * X * (Real.log X) ^ 2 * Real.exp (-(1 / Real.exp 1) * M) :=
        mul_le_mul_of_nonneg_left hexp hbase
    _ = (C * 1) * (X * (Real.log X) ^ 2 * Real.exp (-(1 / Real.exp 1) * M)) := by ring
    _ ≤ (C * (T / X + 1)) * (X * (Real.log X) ^ 2 * Real.exp (-(1 / Real.exp 1) * M)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hC0) hrest
    _ = C * (T / X + 1) * X * (Real.log X) ^ 2
          * Real.exp (-(1 / Real.exp 1) * M) := by ring

/-- **R1′ — the general-`T` socket at the BARE-`X` shape (`annHead_le_socket_T_of_floor`).**
The `(T/X + 1)·X·e^{−(1/e)M}` socket the consumers want, for EVERY `T ≥ 0`, at the honest
price: the strengthened branch floor `2e·loglog X ≤ M_range (…)`.  The exchange is exact —
`(logX)² · e^{−(1/e)M} = exp(2·loglogX − M/e) ≤ 1` iff `M ≥ 2e·loglogX` — so this hypothesis
is precisely what it costs to spend the `annHead_le_socket_T` polylog on the decay factor.
Compare the standing R3.1 floor `(1/32)·loglog X` (which this hypothesis implies, `2e > 1/32`
and `loglog X ≥ 0` for `X ≥ e`): the general-`T` bare-`X` socket wants the floor constant
raised from `1/32` to `2e`, a factor `64e ≈ 174`.

⚠ **NOT A USABLE SOCKET — the hypothesis exceeds `M_range`'s ceiling.**  `M_range` infimizes
`pretDistSq` over 1-bounded data, whose every term is `≤ 2/p`, so `M_range ≤ 2·loglog X +
O(1)` by Mertens (the extreme value is `Dist.pretDistSq_principal_eval`).  `2e ≈ 5.44 > 2`,
so no `X` large satisfies this floor.  The theorem is true and is recorded as the exact
exchange-rate certificate for the `(logX)²`; it must NOT be wired into a chain.  The usable
general-`T` statements are `annHead_le_socket_T` (polylog grade, no gate) and
`annHead_le_socket_polyT` (bare `X`, gate `T ≤ (logX)^A`). -/
theorem annHead_le_socket_T_of_floor (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ X T : ℝ, X₀ ≤ X → 0 ≤ T →
      2 * Real.exp 1 * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C₁ * (T / X + 1) * X
            * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
  obtain ⟨C, hC0, hgrade⟩ := annHead_grade_capX g hg t₀
  refine ⟨C, Real.exp 1, hC0, fun X T hX hT hfloor => ?_⟩
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  have hLpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le one_pos hL1
  have hg1 := hgrade X T hX
  set M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T with hMdef
  -- `(logX)² = exp(2·loglogX)`, and the strong floor says `2·loglogX ≤ M/e`
  have hLsq : (Real.log X) ^ 2 = Real.exp (2 * Real.log (Real.log X)) := by
    rw [two_mul, Real.exp_add, Real.exp_log hLpos]; ring
  have hkey : (Real.log X) ^ 2 * Real.exp (-(1 / Real.exp 1) * M) ≤ 1 := by
    rw [hLsq, ← Real.exp_add, Real.exp_le_one_iff]
    have hinv : (0 : ℝ) < 1 / Real.exp 1 := by positivity
    have h := mul_le_mul_of_nonneg_left hfloor hinv.le
    have hcancel : 1 / Real.exp 1 * (2 * Real.exp 1 * Real.log (Real.log X))
        = 2 * Real.log (Real.log X) := by field_simp
    linarith
  have hsplitexp : Real.exp (-(2 / Real.exp 1) * M)
      = Real.exp (-(1 / Real.exp 1) * M) * Real.exp (-(1 / Real.exp 1) * M) := by
    rw [← Real.exp_add]; congr 1; ring
  have hA : (0 : ℝ) ≤ C * X * Real.exp (-(1 / Real.exp 1) * M) :=
    mul_nonneg (mul_nonneg hC0 hXpos.le) (Real.exp_nonneg _)
  have hw : (1 : ℝ) ≤ T / X + 1 := by
    have hTX : (0 : ℝ) ≤ T / X := div_nonneg hT hXpos.le
    linarith
  have hrest : (0 : ℝ) ≤ X * Real.exp (-(1 / Real.exp 1) * M) :=
    mul_nonneg hXpos.le (Real.exp_nonneg _)
  calc annHead g t₀ X T (1 / Real.log X)
      ≤ C * X * (Real.log X) ^ 2 * Real.exp (-(2 / Real.exp 1) * M) := hg1
    _ = (C * X * Real.exp (-(1 / Real.exp 1) * M))
          * ((Real.log X) ^ 2 * Real.exp (-(1 / Real.exp 1) * M)) := by
        rw [hsplitexp]; ring
    _ ≤ (C * X * Real.exp (-(1 / Real.exp 1) * M)) * 1 :=
        mul_le_mul_of_nonneg_left hkey hA
    _ = (C * 1) * (X * Real.exp (-(1 / Real.exp 1) * M)) := by ring
    _ ≤ (C * (T / X + 1)) * (X * Real.exp (-(1 / Real.exp 1) * M)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hC0) hrest
    _ = C * (T / X + 1) * X * Real.exp (-(1 / Real.exp 1) * M) := by ring

end Salt.MR

/-! ## T-RESHAPE-WIRE — the general-`T` rows

The three landed head/tail rows (`T1_decay_annular`, `T1_decay_annular_tailed`,
`prop_A3_T1_row_annular`) re-run against the `T`-gate-free sockets above.  Nothing in the
chain below the socket ever used `T ≤ logX`: `T1_decay_trivial` binds `C₁` universally, so
the `(T/X + 1)` weight (and, in the polylog row, the `(logX)²`) is simply instantiated INTO
that binder — `C₁ := C₁·(T/X + 1)` — and the chain's own grade is unchanged.  The tail leg
is `T`-free outright (`head_prep_utail`/`s2_tail_ledger` carry no `T`).

Each row comes in the two honest flavours of the socket:

* `…_T` — the strong-floor flavour (`2e·loglog X ≤ M_range`), grade
  `(C₁·(T/X + 1) + C₂)·X·((logX)^{−c/32} + (logX)^{−1/2+ε})`: the CLEAN shape, which at
  `T = X/h₁`, `h₁ ≥ 1` is `≤ (2C₁ + C₂)·X·(…)` — the `O(X·e^{−cM})` head/tail leg the
  Lemma-14 / Prop-1 consumers want.
* `…_T_polylog` — the standing-floor flavour (`(1/32)·loglog X ≤ M_range`, the same
  hypothesis the landed rows carry), grade
  `(C₁·(T/X + 1)·(logX)² + C₂)·X·(…)`: unconditional, but the head arm is inflated by the
  `(logX)²` the crude measure×sup cannot shed at `T ≍ X`.

Both are strictly stronger than the landed rows in `T`-range (no upper gate at all, so `T`
may be `X/h₁`, `X`, or larger) and neither weakens any other hypothesis. -/

namespace Salt.MR

/-- **R2 — the general-`T` annular T1 decay (`T1_decay_annular_T_of_floor`).**  `T1_decay_annular`
with the `T ≤ logX` gate REMOVED, at the `(T/X + 1)`-weighted grade, under the strengthened
floor.  `T1_decay_trivial` is applied with its universally-bound `C₁` instantiated at
`C₁·(T/X + 1)` (nonneg since `T ≥ 0 < X`), its `hhead` discharged by
`annHead_le_socket_T_of_floor`, and its own `(1/32)·loglog X` floor derived from the strong
floor (`2e ≥ 4 > 1/32` and `loglog X ≥ 0` for `X ≥ e`). -/
theorem T1_decay_annular_T_of_floor (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T : ℝ),
      X₀ ≤ X → 0 ≤ T → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      2 * Real.exp 1 * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X) + Utail
        ≤ (C₁ * (T / X + 1) + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hsock⟩ := annHead_le_socket_T_of_floor g hg t₀
  refine ⟨C₁, max X₀ (Real.exp 1), hC₁, ?_⟩
  intro X ε Utail C₂ T hX hT hε hC₂ htail hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe
  have hllX : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hL1
  have hTX : (0 : ℝ) ≤ T / X := div_nonneg hT hXpos.le
  have hC₁w : (0 : ℝ) ≤ C₁ * (T / X + 1) := mul_nonneg hC₁ (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfloor' : (1 / 32) * Real.log (Real.log X)
      ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T := by
    have hmul : 2 * Real.log (Real.log X) ≤ Real.exp 1 * Real.log (Real.log X) :=
      mul_le_mul_of_nonneg_right he2 hllX
    linarith
  have hf : ∀ n, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  exact T1_decay_trivial hf t₀ t hXe hε hC₁w hC₂ rfl
    (hsock X T hX0 hT hfloor) htail hfloor'

/-- **R2′ — the general-`T` annular T1 decay, standing floor (`T1_decay_annular_T_polylog`).**
`T1_decay_annular` with the `T ≤ logX` gate REMOVED and EVERY other hypothesis kept exactly
as landed (in particular the standing `(1/32)·loglog X` floor).  The price of the removal is
visible in the grade: the head constant is `C₁·(T/X + 1)·(logX)²`, the honest residue of the
crude measure×sup at `T ≍ X`.  Discharged by `annHead_le_socket_T` (one `ring` reassociation
to move the `(logX)²` into `T1_decay_trivial`'s `C₁` slot). -/
theorem T1_decay_annular_T_polylog (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T : ℝ),
      X₀ ≤ X → 0 ≤ T → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X) + Utail
        ≤ (C₁ * (T / X + 1) * (Real.log X) ^ 2 + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hsock⟩ := annHead_le_socket_T g hg t₀
  refine ⟨C₁, max X₀ (Real.exp 1), hC₁, ?_⟩
  intro X ε Utail C₂ T hX hT hε hC₂ htail hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  have hTX : (0 : ℝ) ≤ T / X := div_nonneg hT hXpos.le
  have hC₁w : (0 : ℝ) ≤ C₁ * (T / X + 1) * (Real.log X) ^ 2 :=
    mul_nonneg (mul_nonneg hC₁ (by linarith)) (by positivity)
  have hhead : annHead g t₀ X T (1 / Real.log X)
      ≤ C₁ * (T / X + 1) * (Real.log X) ^ 2 * X
        * Real.exp (-(1 / Real.exp 1)
            * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
    have h := hsock X T hX0 hT
    calc annHead g t₀ X T (1 / Real.log X)
        ≤ C₁ * (T / X + 1) * X * (Real.log X) ^ 2
            * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := h
      _ = C₁ * (T / X + 1) * (Real.log X) ^ 2 * X
            * Real.exp (-(1 / Real.exp 1)
                * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by ring
  have hf : ∀ n, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  exact T1_decay_trivial hf t₀ t hXe hε hC₁w hC₂ rfl hhead htail hfloor

/-- **R3 — the general-`T` annular T1 decay, tail wired (`T1_decay_annular_tailed_T_of_floor`).**
`T1_decay_annular_tailed` with the `T ≤ logX` gate REMOVED.  The tail leg needs no change at
all: `head_prep_utail` (⟸ `s2_tail_ledger`) is `T`-FREE — its hypotheses are `1 < logX`,
`0 ≤ X`, `0 ≤ Csup` and nothing else — so the composite gate is exactly the head's, and the
threshold `X₀ = max (R2's X₀) (e²)` is the landed one (the `e²` arm supplying the ledger's
strict `1 < logX`).  Head and tail are both CONCRETE, now for every `T ≥ 0`. -/
theorem T1_decay_annular_tailed_T_of_floor (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Csup T : ℝ),
      X₀ ≤ X → 0 ≤ T → 0 ≤ ε → 0 ≤ Csup →
      2 * Real.exp 1 * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X)
          + (Csup * (Real.log X) ^ 3)
              * (Real.sqrt (Real.log X) * X * ((Real.log X) ^ 4)⁻¹)
        ≤ (C₁ * (T / X + 1) + Csup) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hchain⟩ := T1_decay_annular_T_of_floor g hg t₀ t
  refine ⟨C₁, max X₀ (Real.exp 2), hC₁, ?_⟩
  intro X ε Csup T hX hT hε hCsup hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe2 : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXe2
  have hLog2 : (2 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe2
  have hL1 : (1 : ℝ) < Real.log X := by linarith
  have htail := head_prep_utail hL1 hXpos.le hCsup
  exact hchain X ε _ Csup T hX0 hT hε hCsup htail hfloor

/-- **R4 — the general-`T` `int_U` row (`prop_A3_T1_row_annular_T_of_floor`).**
`prop_A3_T1_row_annular` with the `T ≤ logX` gate REMOVED: R2 fed into the `Iunit ≤ Gunit` of the
terminal `Prop1Assembly.prop_A3'_assembly`, with the §8 eq-(24) split and the moment grade
carried as hypotheses exactly as the landed row carries them.  The moment side is already
`T`-general (its `(2T + 20N)` masses hold for every `T ≥ 0`), so this is the last place the
gate lived on the head/tail side. -/
theorem prop_A3_T1_row_annular_T_of_floor (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T Itot Imom Gmom : ℝ),
      X₀ ≤ X → 0 ≤ T → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      2 * Real.exp 1 * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      Itot = (annHead g t₀ X T (1 / Real.log X) + Utail) + Imom →
      Imom ≤ Gmom →
      Itot ≤ (C₁ * (T / X + 1) + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) + Gmom := by
  obtain ⟨C₁, X₀, hC₁, hrow⟩ := T1_decay_annular_T_of_floor g hg t₀ t
  refine ⟨C₁, X₀, hC₁, ?_⟩
  intro X ε Utail C₂ T Itot Imom Gmom hX hT hε hC₂ htail hfloor hsplit hmom
  have hunit := hrow X ε Utail C₂ T hX hT hε hC₂ htail hfloor
  rw [hsplit]; linarith [hunit, hmom]

end Salt.MR

/-! ## T-RESHAPE-POLY — the gate widened to any fixed power of `logX` (unconditional)

The maximal honest widening of the LANDED socket shape: `annHead_le_socket`'s absorption
`C·(T + (logX)^{1/46})·(logX)² ≤ X` never needed `T ≤ logX` — it needed only
`(logX)^{A+2} ≪ X`, which holds for every fixed `A`.  So the whole landed column re-runs
verbatim with the gate `T ≤ Real.log X` replaced by `T ≤ (Real.log X)^A`, `A : ℕ`, `A ≥ 1`,
at the SAME bare-`X` socket, the SAME standing `(1/32)·loglog X` floor and the SAME grade;
`A = 1` recovers the landed rows exactly.  Only the threshold `X₀` moves (it now depends on
`A`, through `(2C+1)·(logX)^{A+2} ≤ X`).

This is the flavour to wire.  It covers the large-`h₁` end of Lemma 14's range
(`T = X/h₁ ≤ (logX)^A ⟺ h₁ ≥ X·(logX)^{−A}`, non-empty since `h₁` there may run up to
`X·(logX)^{−1/5}`).  It does NOT reach `h₁ = O(1)`; for that regime see the ceiling note
above — the measure×sup page cannot get there, and the mean-value moment row is the engine. -/

namespace Salt.MR

open Filter

/-- **The `c·(logX)^k = o(X)` threshold, general exponent (∃-packaged).**  The landed
`logpow3_le_self_eventually` with the exponent `3` promoted to an arbitrary `k : ℕ` — same
proof, same source (`isLittleO_log_rpow_rpow_atTop` at exponents `k` and `1`). -/
private lemma logpowN_le_self_eventually (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c * (Real.log X) ^ k ≤ X := by
  have hlo : (fun x : ℝ => Real.log x ^ (k : ℝ)) =o[atTop] fun x : ℝ => x ^ (1 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop k (by norm_num : (0 : ℝ) < 1)
  have hbound := hlo.bound (show (0 : ℝ) < 1 / c by positivity)
  rw [eventually_atTop] at hbound
  obtain ⟨a, ha⟩ := hbound
  refine ⟨max a 1, fun X hX => ?_⟩
  have hXa : a ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_right _ _) hX
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hX1
  have hkey := ha X hXa
  have h1nn : (0 : ℝ) ≤ Real.log X ^ (k : ℝ) := Real.rpow_nonneg hlogXnn _
  have h2nn : (0 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg h1nn, Real.norm_of_nonneg h2nn, Real.rpow_one,
    Real.rpow_natCast] at hkey
  calc c * (Real.log X) ^ k ≤ c * (1 / c * X) := mul_le_mul_of_nonneg_left hkey hc.le
    _ = X := by rw [← mul_assoc, mul_one_div, div_self hc.ne', one_mul]

/-- **R5 — the polylog-`T` socket (`annHead_le_socket_polyT`).**  `annHead_le_socket` with its
gate widened from `T ≤ logX` to `T ≤ (logX)^A` for an arbitrary fixed `A : ℕ`, `A ≥ 1`, at the
IDENTICAL bare-`X` conclusion `annHead ≤ C₁·X·exp(−(1/e)·M_range(...))` and with no new
hypothesis: the measure factor is now `≤ 2(logX)^A`, so the polylog to absorb is
`(logX)^{A+2}`, still `≪ X`.  `A = 1` is the landed socket.  Unconditional — this is the
usable general-`T` statement (see the ceiling note for why `T ≍ X` is out of reach). -/
theorem annHead_le_socket_polyT (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ X T : ℝ, X₀ ≤ X → 0 ≤ T → T ≤ (Real.log X) ^ A →
      annHead g t₀ X T (1 / Real.log X)
        ≤ C₁ * X * Real.exp (-(1 / Real.exp 1)
            * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) := by
  obtain ⟨C, hC0, hgrade⟩ := annHead_grade g hg t₀
  obtain ⟨X₁, hX₁⟩ := logpowN_le_self_eventually (2 * C + 1) (by linarith) (A + 2)
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
  -- `(logX)^{1/46} ≤ logX = (logX)^1 ≤ (logX)^A`, so the measure factor is `≤ 2(logX)^A`
  have hr_le : (Real.log X) ^ (1 / 46 : ℝ) ≤ (Real.log X) ^ A := by
    calc (Real.log X) ^ (1 / 46 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = (Real.log X) ^ (1 : ℕ) := by rw [Real.rpow_one, pow_one]
      _ ≤ (Real.log X) ^ A := pow_le_pow_right₀ hL1 hA
  have hTr : T + (Real.log X) ^ (1 / 46 : ℝ) ≤ 2 * (Real.log X) ^ A := by linarith
  have hstep1 : C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
        * Real.exp (-(2 / Real.exp 1) * M)
      ≤ 2 * C * (Real.log X) ^ (A + 2) * Real.exp (-(2 / Real.exp 1) * M) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    calc C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
        = C * (Real.log X) ^ 2 * (T + (Real.log X) ^ (1 / 46 : ℝ)) := by ring
      _ ≤ C * (Real.log X) ^ 2 * (2 * (Real.log X) ^ A) :=
          mul_le_mul_of_nonneg_left hTr (mul_nonneg hC0 (by positivity))
      _ = 2 * C * (Real.log X) ^ (A + 2) := by rw [pow_add]; ring
  have hstep2 : 2 * C * (Real.log X) ^ (A + 2) * Real.exp (-(2 / Real.exp 1) * M)
      ≤ 2 * C * (Real.log X) ^ (A + 2) * Real.exp (-(1 / Real.exp 1) * M) := by
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (mul_nonneg (by norm_num) hC0) (pow_nonneg hLnn _))
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_mul]
    apply neg_le_neg
    apply mul_le_mul_of_nonneg_right _ hM0
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  calc annHead g t₀ X T (1 / Real.log X)
      ≤ C * (T + (Real.log X) ^ (1 / 46 : ℝ)) * (Real.log X) ^ 2
          * Real.exp (-(2 / Real.exp 1) * M) := hg1
    _ ≤ 2 * C * (Real.log X) ^ (A + 2) * Real.exp (-(2 / Real.exp 1) * M) := hstep1
    _ ≤ 2 * C * (Real.log X) ^ (A + 2) * Real.exp (-(1 / Real.exp 1) * M) := hstep2
    _ ≤ X * Real.exp (-(1 / Real.exp 1) * M) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        have hlp := hX₁ X hX1'
        have hmono : 2 * C * (Real.log X) ^ (A + 2)
            ≤ (2 * C + 1) * (Real.log X) ^ (A + 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLnn _)
        linarith
    _ = 1 * X * Real.exp (-(1 / Real.exp 1) * M) := by ring

/-- **R6 — the polylog-`T` annular T1 decay (`T1_decay_annular_polyT`).**  `T1_decay_annular`
with the gate `T ≤ logX` widened to `T ≤ (logX)^A`; every other hypothesis, the grade and the
proof are the landed ones (`annHead_le_socket_polyT` discharges the `hhead` binder). -/
theorem T1_decay_annular_polyT (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ (Real.log X) ^ A → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X) + Utail
        ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hsock⟩ := annHead_le_socket_polyT g hg t₀ A hA
  refine ⟨C₁, max X₀ (Real.exp 1), hC₁, ?_⟩
  intro X ε Utail C₂ T hX hT hTL hε hC₂ htail hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
  have hf : ∀ n, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  exact T1_decay_trivial hf t₀ t hXe hε hC₁ hC₂ rfl
    (hsock X T hX0 hT hTL) htail hfloor

/-- **R7 — the polylog-`T` annular T1 decay, tail wired (`T1_decay_annular_tailed_polyT`).**
`T1_decay_annular_tailed` at the widened gate.  The tail leg is `T`-free
(`head_prep_utail` ⟸ `s2_tail_ledger`), so only the head's gate moves; the threshold
`X₀ = max (R6's X₀) (e²)` is the landed one. -/
theorem T1_decay_annular_tailed_polyT (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Csup T : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ (Real.log X) ^ A → 0 ≤ ε → 0 ≤ Csup →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      annHead g t₀ X T (1 / Real.log X)
          + (Csup * (Real.log X) ^ 3)
              * (Real.sqrt (Real.log X) * X * ((Real.log X) ^ 4)⁻¹)
        ≤ (C₁ + Csup) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C₁, X₀, hC₁, hchain⟩ := T1_decay_annular_polyT g hg t₀ t A hA
  refine ⟨C₁, max X₀ (Real.exp 2), hC₁, ?_⟩
  intro X ε Csup T hX hT hTL hε hCsup hfloor
  have hX0 : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXe2 : Real.exp 2 ≤ X := le_trans (le_max_right _ _) hX
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 2) hXe2
  have hLog2 : (2 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hXe2
  have hL1 : (1 : ℝ) < Real.log X := by linarith
  have htail := head_prep_utail hL1 hXpos.le hCsup
  exact hchain X ε _ Csup T hX0 hT hTL hε hCsup htail hfloor

/-- **R8 — the polylog-`T` `int_U` row (`prop_A3_T1_row_annular_polyT`).**
`prop_A3_T1_row_annular` at the widened gate: R6 fed into the abstract `Iunit ≤ Gunit` socket,
with the §8 eq-(24) split and the moment grade carried as hypotheses exactly as landed. -/
theorem prop_A3_T1_row_annular_polyT (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ)
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T Itot Imom Gmom : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ (Real.log X) ^ A → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      Itot = (annHead g t₀ X T (1 / Real.log X) + Utail) + Imom →
      Imom ≤ Gmom →
      Itot ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) + Gmom := by
  obtain ⟨C₁, X₀, hC₁, hrow⟩ := T1_decay_annular_polyT g hg t₀ t A hA
  refine ⟨C₁, X₀, hC₁, ?_⟩
  intro X ε Utail C₂ T Itot Imom Gmom hX hT hTL hε hC₂ htail hfloor hsplit hmom
  have hunit := hrow X ε Utail C₂ T hX hT hTL hε hC₂ htail hfloor
  rw [hsplit]; linarith [hunit, hmom]

end Salt.MR

/-! ## SEAM-WAVE — the `≤`-weakened `hsplit` row (the eq-(24) seam as an inequality)

The landed rows (`prop_A3_T1_row_annular`, `Prop1Assembly.prop_A3_T1_row_moment`) carry the
§8 eq-(24) seam as an EQUALITY binder `Itot = (annHead + Utail) + Imom`.  The 2026-07-24
audit entry in `docs/blueprints/flags.md` ("the hsplit/annHead object mismatch") records why
that equality is unsatisfiable at the intended instantiation: `annHead` is the FULL seam
L-series at `Re = 1 + σ` (true `L²`-mass `≍ T`, `ellLin`'s support being all squarefree `n`),
while the intended `Itot` is the dyadic-polynomial mean square (`≍ T/X + 1`).  A genuine
eq-(24) partition of the mean square yields an INEQUALITY `Itot ≤ (head + tail) + moment` —
every honest split drops mass at the seam.

The row below is the landed one with `hsplit` weakened from `=` to `≤` and NOTHING else
changed; the `=` rows stay as heritage.  Nothing here SUPPLIES the split — the supplying
stone is the seam row `SeamSplit.prop_A3_T1_row_split`, which proves a partition inequality
of exactly this shape for the dyadic object.  (Appended region; the landed bytes are frozen.)
-/

namespace Salt.MR

/-- **Z0 — the `≤`-weakened annular `int_U` row (`prop_A3_T1_row_annular_le`).**
`prop_A3_T1_row_annular` with the §8 eq-(24) binder weakened from
`Itot = (annHead + Utail) + Imom` to `Itot ≤ (annHead + Utail) + Imom`, and nothing else
changed.  This is the shape a genuine seam split can discharge (see the section note and
the flags entry "the hsplit/annHead object mismatch", 2026-07-24): a partition of the mean
square into head/tail/moment legs is an inequality, never an identity.  The proof is the
landed one with `rw [hsplit]` replaced by the transitive `linarith`. -/
theorem prop_A3_T1_row_annular_le (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t : ℝ) :
    ∃ C₁ X₀ : ℝ, 0 ≤ C₁ ∧ ∀ (X ε Utail C₂ T Itot Imom Gmom : ℝ),
      X₀ ≤ X → 0 ≤ T → T ≤ Real.log X → 0 ≤ ε → 0 ≤ C₂ →
      Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T →
      Itot ≤ (annHead g t₀ X T (1 / Real.log X) + Utail) + Imom →
      Imom ≤ Gmom →
      Itot ≤ (C₁ + C₂) * X
            * ((Real.log X) ^ (-(1 / Real.exp 1) / 32)
              + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) + Gmom := by
  obtain ⟨C₁, X₀, hC₁, hrow⟩ := T1_decay_annular g hg t₀ t
  refine ⟨C₁, X₀, hC₁, ?_⟩
  intro X ε Utail C₂ T Itot Imom Gmom hX hT hTL hε hC₂ htail hfloor hsplit hmom
  have hunit := hrow X ε Utail C₂ T hX hT hTL hε hC₂ htail hfloor
  linarith [hunit, hmom, hsplit]

end Salt.MR
