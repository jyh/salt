/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.GradeConst

/-!
# The `c`-GENERIC grade supplier (`RHSGradeC`)

`RHSGrade`/`GradeConst` land the joint-head grade at the BALL arm's pinned exponent
`c = 1/(2e)` — the numeral is baked into `rhsFbound` (`RHSGrade`:227), into `rhsSigmaG`
(`RHSGrade`:508), and into the two theorems that spend it (`joint_supF_pin`,
`beta_integral_pin_const`).  The U-7 CASE-A route needs the SAME chain at `c = 1/e`, so this
file re-runs exactly the `c`-carrying stones with the exponent freed, under the gates the
suppliers themselves state:

* `supF_pret_pointwise` (`PretSupply`:354) is ALREADY `c`-generic — its gates are
  `0 < c` and `c ≤ 1/e`; `joint_supF_pin` merely instantiates it at `1/(2e)`.  `joint_supF_pinC`
  re-passes a free `c` under those two gates and nothing else changes.
* `joint_sigma_integral` (`PretSupply`:481) is ALREADY `c`-generic — its gates are `0 < c` and
  `2c < 1`, inherited from `sigma_cutoff_pretentious_gen` (`SeamBallWeighted`:325), the honest
  convergence boundary of the σ-cutoff.  At the eventual `c = 1/e` the gate reads `2/e < 1` ✓.
  `beta_integral_pin_constC` re-passes a free `c` under those two gates.

**WHAT IS NOT CLONED.**  The whole amplitude side is `c`-FREE and is reused VERBATIM by
import: `crossKer_width_pin_const`, `widthKamp`/`widthKampBr`, `width_pin_bracket_le`,
`pin_width_gates`, `bridge_adapter`.  Nothing in `RHSGrade`, `GradeConst`, `PretSupply` or
`SeamBallWeighted` is touched.

**THE PIN IS RECOVERED, NOT REPLACED.**  `rhsFbound_eq_rhsFboundC` and
`rhsSigmaG_eq_rhsSigmaGC` are `rfl`: the landed `c = 1/(2e)` objects are literally the
`c`-generic ones at that numeral, so every existing consumer keeps its byte-for-byte shape and
the two families never diverge.

**LIVE GUARD (inherited).**  `c = 1/(2e)` is the BALL arm's halved constant; the free-`c` forms
here carry no route commitment — the caller's `hc0`/`hce`/`hc1` are the whole contract.

`GradeConst` keeps `four_log_le_selfC`, `pin_basic64`, `continuous_rpow_negC`,
`widthKamp_nonneg` and its two integrability pages `private`; they are re-derived here
verbatim under a `GC` suffix (the house's re-derivation convention, cf. `SupClose`'s
`pin_basic64S` and `FarStar`'s `pin_basic64T`).
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set

/-! ## §1 (W4-1) — the `c`-generic `Fbound` and σ-return, and the pin identities -/

/-- **The `c`-GENERIC `Fbound`** — `RHSGrade.rhsFbound` with the exponent freed:

  `rhsFboundC c M L σ = C_S·C_F·(1/σ)·exp(−c·(M − 2·log(σ·L) − 48))`.

This is `supF_pret_majorant_sigma`'s right-hand side at a general `c`, so `hFb`/`hpret` stay
`le_rfl` at every consumer. -/
def rhsFboundC (c M L σ : ℝ) : ℝ :=
  rhsCSF * (1 / σ) * Real.exp (-c * (M - 2 * Real.log (σ * L) - 48))

lemma rhsFboundC_nonneg (c M L : ℝ) {σ : ℝ} (hσ : 0 < σ) : 0 ≤ rhsFboundC c M L σ :=
  mul_nonneg (mul_nonneg rhsCSF_pos.le (by positivity)) (Real.exp_nonneg _)

/-- **The `c`-GENERIC σ-cutoff return** — `RHSGrade.rhsSigmaG` with the exponent freed:

  `rhsSigmaGC c M L = C_S·C_F·(e^{48c}/(1−2c))·e^{−cM}·L`.

This is `joint_sigma_integral`'s right-hand side at a general `c` (`CSF := rhsCSF`). -/
def rhsSigmaGC (c M L : ℝ) : ℝ :=
  rhsCSF * ((Real.exp (c * 48) / (1 - 2 * c)) * Real.exp (-(c * M)) * L)

/-- **THE PIN IDENTITY (`Fbound`).**  The landed ball-arm `rhsFbound` IS the `c`-generic
object at `c = 1/(2e)` — definitionally, so no consumer shape moves. -/
lemma rhsFbound_eq_rhsFboundC (M L σ : ℝ) :
    rhsFbound M L σ = rhsFboundC (1 / (2 * Real.exp 1)) M L σ := rfl

/-- **THE PIN IDENTITY (σ-return).**  The landed ball-arm `rhsSigmaG` IS the `c`-generic
object at `c = 1/(2e)`. -/
lemma rhsSigmaG_eq_rhsSigmaGC (M L : ℝ) :
    rhsSigmaG M L = rhsSigmaGC (1 / (2 * Real.exp 1)) M L := rfl

/-- **The `M`-slot of `rhsFboundC` is a constant factor** — the `c`-generic twin of
`SupStation.rhsFbound_eq_exp_mul` (:84).  `M` enters the exponential additively and σ-freely,
so every `M`-indexed integrability socket is the `M = 0` one scaled by `e^{−cM}`. -/
lemma rhsFboundC_eq_exp_mul (c M L σ : ℝ) :
    rhsFboundC c M L σ = Real.exp (-c * M) * rhsFboundC c 0 L σ := by
  unfold rhsFboundC
  rw [show -c * (M - 2 * Real.log (σ * L) - 48)
        = -c * M + -c * (0 - 2 * Real.log (σ * L) - 48) from by ring,
    Real.exp_add]
  ring

/-! ## §2 (W4-2) — the `t`-uniform `supF` at a FREE exponent -/

/-- **W4-2 — the `t`-uniform `supF` at a FREE `c`** (`joint_supF_pinC`).
`RHSGrade.joint_supF_pin` with the exponent freed: `joint_cs_factoring`'s `hsupF` binder,
discharged at the corpus pin (`c₀ = 1+1/L`, `y = L⁴`, `η = 1/log y`, `L = log k`) from
`supF_pret_pointwise` at the CALLER's `c`:

  `∀ t, ‖𝒮(s−α−β)·𝓛(s+β)‖ ≤ rhsFboundC c M L (β + 1/L)`,  `s = c₀ + (t−t₀')i`.

**The `c`-gates, in-statement (law #253):** `0 < c` and `c ≤ 1/e` — `supF_pret_pointwise`'s own
two, no more.  At `c = 1/(2e)` this is `joint_supF_pin` byte-for-byte (`rhsFbound_eq_rhsFboundC`
is `rfl`); at `c = 1/e` it is the CASE-A supply.

The `t`-dependence is killed by `hMt` alone: the floor is uniform in `t`, so the right-hand side
is genuinely `t`-free.  Gates discharged from `3 ≤ L`: `e ≤ y` (`y = L⁴ ≥ 81`), `σ := β+1/L ≤ 1`,
and the scale condition `e^{1/σ} ≤ k` (`1/σ ≤ L = log k`). -/
theorem joint_supF_pinC {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀' M k L c₀ y η : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀eq : c₀ = 1 + 1 / L)
    (hMt : ∀ t : ℝ, M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k)
    {α β : ℝ} (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β) (hαη : α ≤ η) (hβη : β ≤ η) (t : ℝ) :
    ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
          (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFboundC c M L (β + 1 / L) := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 3) hk
  have hL3 : (3 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hLinv3 : 1 / L ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hL0 (by norm_num : (0 : ℝ) < 3)]; linarith
  have hσ0 : (0 : ℝ) < β + 1 / L := by linarith
  -- the `y`-gates
  have hy0 : (0 : ℝ) < y := by rw [hy]; positivity
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hylo : Real.exp 1 ≤ y := by
    rw [hy]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL3 4]
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have hlogL1 : (1 : ℝ) ≤ Real.log L := by
    have h3 : Real.log 3 ≤ Real.log L := Real.log_le_log (by norm_num) hL3
    have h1 : (1 : ℝ) ≤ Real.log 3 := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) (by linarith)
    linarith
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  have hη4 : η ≤ 1 / 4 := by
    rw [hη, hlogy]
    rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 4)]
    linarith
  -- the twisted datum is 1-bounded at primes
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  -- the scale condition `e^{1/σ} ≤ k` on `σ ≥ 1/L`
  have hσL : 1 / (β + 1 / L) ≤ L := by
    rw [div_le_iff₀ hσ0]
    have h1 : L * (1 / L) = 1 := by field_simp
    nlinarith
  have hYX : Real.exp (1 / (c₀ - 1 + β)) ≤ k := by
    rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring]
    calc Real.exp (1 / (β + 1 / L)) ≤ Real.exp L := Real.exp_le_exp.mpr hσL
      _ = k := by rw [hL, Real.exp_log hk0]
  have hP := supF_pret_pointwise (g := fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) (y := y)
    hgtw (c := c) (t₀ := t₀') (t := t) (X := k) (c₀ := c₀)
    (α := α) (β := β) hc0 hce
    hylo (by rw [hc₀eq]; linarith) hα0 hβ0
    (by rw [← hη]; exact hαη) (by rw [← hη]; exact hβη)
    (by rw [hc₀eq]; linarith) hYX
  rw [show c₀ - 1 + β = β + 1 / L from by rw [hc₀eq]; ring, ← hL] at hP
  refine hP.trans ?_
  unfold rhsFboundC rhsCSF
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ?_
  · nlinarith [mul_le_mul_of_nonneg_left (hMt t) hc0.le]
  · have : (0 : ℝ) ≤ 1 / (β + 1 / L) := by positivity
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) this

/-! ## §3 (W4-3) — the per-`α` β-integral at a FREE exponent

`GradeConst.beta_integral_pin_const` re-run with the `c`-slot freed.  The only `c`-spend in
that page is `joint_sigma_integral`, whose own gates are `0 < c` and `2c < 1` (from
`sigma_cutoff_pretentious_gen`); everything upstream (the width amplitude, `bridge_adapter`,
the two integrability pages) is `c`-free plumbing over `rhsFboundC`.

The four `private` helpers `GradeConst` needs here are re-derived verbatim below. -/

/-- `4·log L ≤ L` for `L ≥ 64`.  Re-derivation of `GradeConst`'s private
`four_log_le_selfC`. -/
private lemma four_log_le_selfGC {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : (8 : ℝ) ≤ Real.sqrt L := by
    have h64 : Real.sqrt 64 = 8 := by
      rw [show (64 : ℝ) = 8 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h64]
    exact Real.sqrt_le_sqrt h
  have hlog : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  nlinarith

/-- The pin's elementary arithmetic at the `e^{64}` gate.  Re-derivation of `GradeConst`'s
private `pin_basic64`. -/
private lemma pin_basic64GC {k L y η : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 64 ≤ L ∧ (131072 : ℝ) ≤ y ∧ 0 < Real.log y ∧ 0 < η ∧ η ≤ 1 / 8
      ∧ 1 / L ≤ η ∧ L ^ 4 ≤ k := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hy131072 : (131072 : ℝ) ≤ y := by
    rw [hy]
    have h4 : (64 : ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL64 4
    norm_num at h4
    linarith
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  refine ⟨hk0, hL64, hy131072, hlogy0, by rw [hη]; positivity, ?_, ?_, ?_⟩
  · rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  · rw [hη, hlogy, div_le_div_iff₀ hL0 (by linarith)]
    linarith [four_log_le_selfGC hL64]
  · have h1 : Real.log (L ^ 4) ≤ Real.log k := by
      rw [Real.log_pow, ← hL]; push_cast; linarith [four_log_le_selfGC hL64]
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2

/-- Interval-integrability of the `c`-generic σ-integrand `rhsFboundC c M L σ/σ`.
Re-derivation of `GradeConst`'s private `rhs_sigma_div_integrableC` at the freed exponent. -/
private lemma rhs_sigma_div_integrableGC {c M L b : ℝ} (hL0 : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable (fun σ : ℝ => rhsFboundC c M L σ / σ) volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFboundC]
  refine ContinuousOn.div (ContinuousOn.mul ?_ ?_) continuousOn_id
    (fun σ hσ => (hpos σ hσ).ne')
  · exact continuousOn_const.mul
      (continuousOn_const.div continuousOn_id (fun σ hσ => (hpos σ hσ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL0).ne'))

/-- Interval-integrability of `bridge_adapter`'s translated `c`-generic integrand.
Re-derivation of `GradeConst`'s private `rhs_shift_integrableC` at the freed exponent. -/
private lemma rhs_shift_integrableGC {c M L η Kα : ℝ} (hL0 : 0 < L) (hη0 : 0 ≤ η) :
    IntervalIntegrable
      (fun β : ℝ => Kα * (rhsFboundC c M L (β + 1 / L) / (β + 1 / L))) volume 0 η := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ β ∈ Set.uIcc (0 : ℝ) η, (0 : ℝ) < β + 1 / L := by
    intro β hβ
    rw [Set.uIcc_of_le hη0, Set.mem_Icc] at hβ
    linarith [hβ.1]
  apply ContinuousOn.intervalIntegrable
  simp only [rhsFboundC]
  refine continuousOn_const.mul (ContinuousOn.div (ContinuousOn.mul ?_ ?_) ?_
    (fun β hβ => (hpos β hβ).ne'))
  · exact continuousOn_const.mul
      (continuousOn_const.div (by fun_prop) (fun β hβ => (hpos β hβ).ne'))
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log (by fun_prop)
      (fun β hβ => (mul_pos (hpos β hβ) hL0).ne'))
  · fun_prop

/-- Continuity of `α ↦ a^{−α}` at a positive base.  Re-derivation of `GradeConst`'s private
`continuous_rpow_negC` (staged for the `α`-integral of W4-4; `c`-free). -/
private lemma continuous_rpow_negGC {a : ℝ} (ha : 0 < a) :
    Continuous (fun α : ℝ => a ^ (-α)) := by
  have hrw : (fun α : ℝ => a ^ (-α)) = fun α : ℝ => Real.exp (Real.log a * (-α)) := by
    funext α; rw [Real.rpow_def_of_pos ha]
  rw [hrw]
  exact Real.continuous_exp.comp (by fun_prop)

/-- The width amplitude is nonnegative on the pin's data.  Re-derivation of `GradeConst`'s
private `widthKamp_nonneg` (`c`-free — the amplitude side never sees the exponent). -/
private lemma widthKamp_nonnegGC {Cb X h y c₀ : ℝ} (hCb0 : 0 ≤ Cb) (hX0 : 0 < X) (hh : 0 < h)
    (hy0 : 0 < y) : 0 ≤ widthKamp Cb X h y c₀ := by
  have hXh0 : (0 : ℝ) < X + h := by linarith
  have hy2 : (0 : ℝ) < y / 2 := by linarith
  have hA0 : (0 : ℝ) < (y / 2) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hy2 _
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold widthKamp widthKampBr
  have hrp : (0 : ℝ) ≤ (X + h) ^ c₀ := Real.rpow_nonneg hXh0.le _
  positivity

/-- **W4-3 — the per-`α` β-integral at the WIDTH face, at a FREE `c`**
(`beta_integral_pin_constC`).  `GradeConst.beta_integral_pin_const` with the exponent freed:
for `α ∈ [0,η]` and the pin `(k ≥ e^{64}, L = log k, y = L⁴, η = 1/log y, c₀ = 1+1/L,
h = k/√L)`,

  `∫₀^η rhsFboundC c M L (β+1/L)·crossKer ≤ (widthKamp·(k+h)^{−α})·rhsSigmaGC c M L`.

**The `c`-gates, in-statement (law #253):** `0 < c` and `2c < 1` — `joint_sigma_integral`'s own
two, inherited from `sigma_cutoff_pretentious_gen`, and the honest convergence boundary of the
σ-cutoff (at `2c = 1` the σ-integral diverges logarithmically).  At the CASE-A exponent
`c = 1/e` the gate reads `2/e < 1` ✓; at `c = 1/(2e)` this is `beta_integral_pin_const`
byte-for-byte.

The amplitude side is `c`-free and is CITED, not cloned: `crossKer_width_pin_const`,
`widthKamp`, `pin_width_gates`, `bridge_adapter`. -/
theorem beta_integral_pin_constC (g : ℕ → ℂ) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c Cb t₀' M k L c₀ y η h α : ℝ} (hc0 : 0 < c) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L) (hyk : y ≤ k) (hM0 : 0 ≤ M)
    (hα0 : 0 ≤ α) (hαη : α ≤ η)
    (hIβ : IntervalIntegrable (fun β => rhsFboundC c M L (β + 1 / L)
        * crossKer g k h y c₀ t₀' α β) volume 0 η) :
    (∫ β in (0 : ℝ)..η, rhsFboundC c M L (β + 1 / L) * crossKer g k h y c₀ t₀' α β)
      ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * rhsSigmaGC c M L := by
  obtain ⟨hk0, hL64, hy131072, _hlogy0, hη0, hη8, hLη, -⟩ := pin_basic64GC hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  obtain ⟨hh0, -, -, hyT⟩ := pin_width_gates hL64 hk0 hh hy
  have hkh0 : (0 : ℝ) < k + h := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hK0 : (0 : ℝ) ≤ widthKamp Cb k h y c₀ * (k + h) ^ (-α) :=
    mul_nonneg (widthKamp_nonnegGC hCb0 hk0 hh0 hy0) (Real.rpow_nonneg hkh0.le _)
  have hcross : ∀ β ∈ Icc (0 : ℝ) η,
      crossKer g k h y c₀ t₀' α β
        ≤ (widthKamp Cb k h y c₀ * (k + h) ^ (-α)) * (1 / (β + 1 / L)) := by
    intro β hβ
    exact crossKer_width_pin_const g hg hCb0 hCbound hL (by linarith) hy131072 hyk hc₀ hh0
      rfl hα0 hβ.1 (by linarith [hβ.2]) hyT
  have hsup0 : ∀ β ∈ Icc (0 : ℝ) η, 0 ≤ rhsFboundC c M L (β + 1 / L) := by
    intro β hβ
    exact rhsFboundC_nonneg c M L (by linarith [hβ.1])
  have hFnn : ∀ σ ∈ Icc (1 / L) (2 * η), 0 ≤ rhsFboundC c M L σ := by
    intro σ hσ
    exact rhsFboundC_nonneg c M L (lt_of_lt_of_le hLinv0 hσ.1)
  have hIσ := rhs_sigma_div_integrableGC (c := c) (M := M) (L := L) (b := 2 * η) hL0
    (by linarith)
  have hBA := bridge_adapter (g := g) (X := k) (h := h) (y := y) (c₀ := c₀) (t₀ := t₀')
    (L := L) (η := η) (Kα := widthKamp Cb k h y c₀ * (k + h) ^ (-α)) (α := α)
    (supF := fun _ β => rhsFboundC c M L (β + 1 / L)) (Fbound := rhsFboundC c M L)
    hL0 hLη hK0 hsup0 hcross (fun β _ => le_rfl) hFnn hIβ
    (rhs_shift_integrableGC hL0 hη0.le) hIσ
  refine le_trans hBA ?_
  refine mul_le_mul_of_nonneg_left ?_ hK0
  have hlogk3 : (3 : ℝ) ≤ Real.log k := by rw [← hL]; linarith
  rw [hL]
  exact joint_sigma_integral (Fbound := rhsFboundC c M (Real.log k))
    (c := c) (X := k) (b := 2 * η) (M := M) (CSF := rhsCSF)
    hc0 hc1 hlogk3 hM0 rhsCSF_pos.le (by rw [← hL]; linarith) (by rw [← hL]; exact hIσ)
    (fun σ _ => le_rfl)

end Salt.MR
