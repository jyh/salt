/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SupClose

/-!
# GRADE-CLOSE rung Z1 — the far term of the truncated grade (`FarClose`)

`SupClose.rhs_grade_at_scale_trunc` exits with

  `‖prop21RHS‖ ≤ gradeAbsConst Cb · k · e^{−M/(2e)} + (1/π)·η²·(Ffar·Kfar)`,

`M` the seam datum's own distance at the centre `t₁`, and the far remainder carried by two
FREE binders (`hFar`, `hKfar`).  This file discharges those two binders at the corpus pin
and prices the remainder against the crown's own currency.

## What lands here

* **F-1 `far_supF_bound`** — the `hFar` binder, discharged at the FREE `M = 0` floor:
  `Ffar := farFbound L = C_S·C_F·e^{24/e}·L`, uniform in `(α, β) ∈ [0,η]²` and in `t`.  The
  sup over the pin's `σ = β + 1/L ∈ [1/L, η+1/L]` of `(1/σ)·(σL)^{1/e}` is `L`, attained at
  `σ = 1/L`; the numeral is therefore SHARP in its `L`-power.
* **F-2 `far_kernel_bound`** — the `hKfar` binder at `T* := L⁴` from
  `TruncFactor.crossKerFar_pin_le`, with the two window masses taken at the lines the two
  legs actually live on: `c₀ − η` (low, `β`-uniformly valid) and `c₀` (high).
  `far_kernel_bound_T` is the same stone at a FREE truncation height `T`, which is what the
  Z1 residual below needs.
* **F-2b `far_window_mass_le`** — the mass numerals (`WindowBridge.window_mass_product` at
  `δ := η − 1/L`, `σ := 1/L`).  This is where the arithmetic verdict is read off.
* **F-3 `far_price_floor` / `far_term_priced`** — the `hMcap` page: under the crown's own
  cap `M ≤ (1/16)·log log X`, `e^{−M/(2e)} ≥ (log X)^{−1/(32e)}`, so the far socket may be
  stated M-FREE (pure arithmetic in `k, L, η, Kfar`), with no distance and no vacuity.
* **F-4 `rhs_grade_at_scale_closed`** — the ONE-term exit
  `‖prop21RHS‖ ≤ (gradeAbsConst Cb + Cfar)·k·e^{−M/(2e)}`, and `hRHS_socket_of_far`, whose
  STATEMENT is `CenterSupply.ball_sup_supplied`'s `hRHS` binder verbatim (the compile is the
  byte-exactness certificate) at `C₁ := gradeAbsConst Cb + Cfar`.

## THE Z1 ARITHMETIC VERDICT (the honest exponent page — read before consuming)

The far socket left open by F-4 is

  `(1/π)·η²·(farFbound L · Kfar) ≤ Cfar·k·(log X)^{−1/(32e)}`,  `Cfar` ABSOLUTE.

At the pin `h = k/√L`, `y = L⁴`, `η = 1/log y = 1/(4 log L)`, `T* = L⁴` it is **FALSE**.
The composed page, with every factor named:

  `Ffar ≍ C·L`  (F-1),
  `Kfar ≤ S(c₀−η)·S(c₀)·(k+h)^{c₀}·4(√L+1)/T`  (F-2/`far_kernel_bound_T`; `(k+h)^{c₀} ≤ 9k`),
  `S(c₀−η)·S(c₀) ≤ (log 4+4)²·(k/y)^{η−1/L}·y^{−1/L}·min(L', 1+2/(η−1/L))·min(L', 2+L)`  (F-2b),

so, `k` cancelling against the target's `k`,

  `far / (k·(log X)^{−1/(32e)}) ≍ C·η²·L·(k/y)^{η−1/L}·(log L)·L·√L/T · L^{1/(32e)}`
                              `≍ C·(k/y)^{η−1/L}·L^{5/2}/(T·log L)`.

The factor `(k/y)^{η−1/L} = exp((η − 1/L)(L − 4 log L)) = e^{L/(4 log L) − 2 + o(1)}` is the
low leg's ℓ¹ window-mass excess.  It is SUPERPOLYNOMIAL in `L`, so at `T = L⁴` the ratio
`e^{L/(4 log L)}·L^{−3/2}/log L` is UNBOUNDED: no absolute `Cfar` exists.  (The crossing is
invisible at the `e^{64}` gate and unmistakable soon after — the `L`-shape of the ratio, with
the absolute constants dropped, is `4·10^{−3}` at `L = 64`, `0.13` at `L = 200`, `1.1·10³` at
`L = 500`, `3·10⁹` at `L = 1000`.)  Nothing here is an artifact of a sloppy majorant:
the low leg genuinely carries `∑_{y<n<k/y} Λ(n)/n^{c₀−η} ≍ (k/y)^{η−1/L}/(η − 1/L)`, and
that ℓ¹ mass is exactly what the landed MAIN term does NOT pay (the width/Plancherel route
of `WidthGrade`/`GradeConst` never forms it — see ⟦V3a⟧).

**The two repairs, priced.**  (i) Raise the truncation height to `T* := y·k^{1/log y}
= L⁴·e^{L/(4 log L)}`: the ratio drops to `≤ L^{−3/2}/log L`, i.e. `8·10^{−5}` at `L = 64`
and decreasing — margin at every `L ≥ 64`.
Cost: the recentring gate `|t₁| + T ≤ R` of `SupClose.center_dist_floor_recentred` now needs
`R ≳ k^{1/log y} = e^{log k/(4 log log k)}`, i.e. Z2's overhang at a much larger compact
radius.  (ii) Keep `T* = L⁴` and replace the CRUDE far bound (`crossKerFar_le_tail`'s
`ℓ¹ × ℓ¹ × Poisson-tail`) by the width/Plancherel treatment of the far region — every
ingredient is landed (`band_weight_le_lorentz`, `widthA_plancherel`, `hatKernel_branch2`);
this pays no ℓ¹ mass at all and leaves Z2 untouched.  Repair (ii) looks strictly better and
is local to this arm.  BOTH are design-level; neither is taken here.  The socket is carried
as one named, M-free, purely arithmetic hypothesis, so a consumer at either repair discharges
it without re-opening anything above.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set
open scoped BigOperators

/-! ## §0 — the pin's arithmetic, re-derived

`SupClose`'s `four_log_le_selfS` / `pin_basic64S` are `private`; re-derived verbatim, plus
the STRICT form `4 log L < L` that the low leg's shift `δ = η − 1/L > 0` needs. -/

/-- `4·log L ≤ L` for `L ≥ 64`.  Re-derivation of `SupClose`'s private `four_log_le_selfS`. -/
private lemma four_log_le_selfF {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L ≤ L := by
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

/-- `4·log L < L` for `L ≥ 64` — the STRICT form (`s² − 8s + 8 > 0` at `s = √L ≥ 8`). -/
private lemma four_log_lt_selfF {L : ℝ} (h : 64 ≤ L) : 4 * Real.log L < L := by
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

/-- The pin's elementary arithmetic at the `e^{64}` gate.  Re-derivation of `SupClose`'s
private `pin_basic64S`, with `log y = 4 log L` and the STRICT gap `1/L < η` added. -/
private lemma pin_basic64F {k L y η : ℝ} (hk : Real.exp 64 ≤ k) (hL : L = Real.log k)
    (hy : y = L ^ 4) (hη : η = 1 / Real.log y) :
    0 < k ∧ 64 ≤ L ∧ (131072 : ℝ) ≤ y ∧ Real.log y = 4 * Real.log L ∧ 0 < η ∧ η ≤ 1 / 8
      ∧ 1 / L < η ∧ L ^ 4 ≤ k := by
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
  refine ⟨hk0, hL64, hy131072, hlogy, by rw [hη, hlogy]; positivity, ?_, ?_, ?_⟩
  · rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  · rw [hη, hlogy, div_lt_div_iff₀ hL0 (by linarith)]
    linarith [four_log_lt_selfF hL64]
  · have h1 : Real.log (L ^ 4) ≤ Real.log k := by
      rw [Real.log_pow, ← hL]; push_cast; linarith [four_log_le_selfF hL64]
    have h2 := Real.exp_le_exp.mpr h1
    rwa [Real.exp_log (by positivity), Real.exp_log hk0] at h2

/-! ## §1 — F-1: the far `𝒮·𝓛` majorant at the FREE `M = 0` floor -/

/-- **The far arm's `β`-uniform `𝒮·𝓛` majorant.**  `RHSGrade.rhsFbound` at `M = 0`,
maximized over the pin's `σ = β + 1/L ∈ [1/L, η + 1/L]`:

  `Ffar = C_S·C_F·e^{24/e}·L`.

The `σ`-sup of `(1/σ)·(σL)^{1/e}` is `L`, attained at `σ = 1/L`; the `L`-power is sharp. -/
def farFbound (L : ℝ) : ℝ := rhsCSF * Real.exp (24 / Real.exp 1) * L

lemma farFbound_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ farFbound L := by
  have h := rhsCSF_pos
  unfold farFbound
  positivity

/-- `rhsFbound 0 L σ ≤ farFbound L` on `σL ≥ 1`: the `M = 0` majorant's `σ`-sup. -/
private lemma rhsFbound_zero_le {L σ : ℝ} (hσ0 : 0 < σ) (hσL : 1 ≤ σ * L) :
    rhsFbound 0 L σ ≤ farFbound L := by
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hσL0 : (0 : ℝ) < σ * L := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log (σ * L) := Real.log_nonneg hσL
  have hσne : σ ≠ 0 := ne_of_gt hσ0
  have hkey : -(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48)
      = 1 / Real.exp 1 * Real.log (σ * L) + 24 / Real.exp 1 := by
    field_simp
    ring
  have h2c : 1 / Real.exp 1 ≤ 1 := by rw [div_le_one he0]; linarith
  have hexp_le : -(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48)
      ≤ Real.log (σ * L) + 24 / Real.exp 1 := by
    rw [hkey]
    nlinarith
  have hstep : Real.exp (-(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48))
      ≤ σ * L * Real.exp (24 / Real.exp 1) := by
    have hrw : σ * L * Real.exp (24 / Real.exp 1)
        = Real.exp (Real.log (σ * L) + 24 / Real.exp 1) := by
      rw [Real.exp_add, Real.exp_log hσL0]
    rw [hrw]
    exact Real.exp_le_exp.mpr hexp_le
  have hpos : (0 : ℝ) ≤ rhsCSF * (1 / σ) := by
    have := rhsCSF_pos; positivity
  unfold rhsFbound farFbound
  calc rhsCSF * (1 / σ) * Real.exp (-(1 / (2 * Real.exp 1)) * (0 - 2 * Real.log (σ * L) - 48))
      ≤ rhsCSF * (1 / σ) * (σ * L * Real.exp (24 / Real.exp 1)) :=
        mul_le_mul_of_nonneg_left hstep hpos
    _ = rhsCSF * Real.exp (24 / Real.exp 1) * L := by field_simp

/-- **F-1 — the far `supF` binder (`far_supF_bound`).**  `joint_cs_factoring_trunc`'s `hFar`
binder byte-for-byte, discharged at the FREE `M = 0` floor: `SupClose.joint_supF_pin_at` needs
only `M ≤ 𝔻²(…)`, and `M = 0` is supplied by `pretDistSq_nonneg` — no distance information,
no frequency hypothesis, no truncation.  The numeral is `β`- and `t`-uniform. -/
theorem far_supF_bound {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀' k L c₀ y η : ℝ}
    (hk : Real.exp 3 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I))
            (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
        ≤ farFbound L := by
  intro α hα β hβ t
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 3) hk
  have hL3 : (3 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 3]; exact Real.log_le_log (Real.exp_pos 3) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hgtw : ∀ p, p.Prime → ‖(fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist t₀' hp.one_lt.le, mul_one]
    exact hg p hp
  have hM0 : (0 : ℝ) ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
      (costwist (t - t₀')) k :=
    pretDistSq_nonneg _ _ _
      (fun n => ellLin_norm_le_one (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) hgtw n)
      (fun n => le_of_eq (costwist_norm (t - t₀') n))
  refine (joint_supF_pin_at hg hk hL hy hη hc₀ hα.1 hβ.1 hα.2 hβ.2 t hM0).trans ?_
  have hσ0 : (0 : ℝ) < β + 1 / L := by
    have : (0 : ℝ) < 1 / L := by positivity
    linarith [hβ.1]
  have hσL : 1 ≤ (β + 1 / L) * L := by
    have hid : (β + 1 / L) * L = β * L + 1 := by field_simp
    have : (0 : ℝ) ≤ β * L := mul_nonneg hβ.1 hL0.le
    rw [hid]; linarith
  exact rhsFbound_zero_le hσ0 hσL

/-! ## §2 — F-2: the far kernel binder at the pin -/

/-- **F-2 — the far kernel binder at `T* = L⁴` (`far_kernel_bound`).**
`joint_cs_factoring_trunc`'s `hKfar` binder, discharged from `TruncFactor.crossKerFar_pin_le`
with the two window masses read at the lines the legs actually live on:

* the LOW leg `windowSum(·−β)` at `c₀ − η ≤ c₀ − β` (uniform in `β ∈ [0,η]`);
* the HIGH leg `windowSum(·+β)` at `c₀ ≤ c₀ + β` (uniform in `β ≥ 0`).

`(k+h)^{c₀−α−β} ≤ (k+h)^{c₀}` makes the exponent `(α,β)`-free.  The mass numerals are
`far_window_mass_le`. -/
theorem far_kernel_bound {d : ℕ → ℂ} {t₀' k L c₀ y η : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar d k (k / Real.sqrt L) y c₀ t₀' α β (L ^ 4)
        ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
              ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η))
            * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
              ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀)
            * ((k + k / Real.sqrt L) ^ c₀ / (L ^ 2 * Real.sqrt L)) := by
  intro α hα β hβ
  obtain ⟨hk0, hL64, -, -, hη0, hη8, -, -⟩ := pin_basic64F hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hX1 : (1 : ℝ) ≤ k := by linarith
  have hL8 : (8 : ℝ) ≤ L := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hc : 0 < c₀ - α - β := by
    rw [hc₀]; linarith [hα.2, hβ.2, hα.1, hβ.1]
  have hMm0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
      ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η) := window_mass_nonneg d k y _
  have hMp0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
      ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀ := window_mass_nonneg d k y _
  have hbm : ∀ τ : ℝ, ‖windowSum d k y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
          ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η) := by
    intro τ
    refine norm_windowSum_le_mass d k y (c₀ - η) ?_
    rw [show (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp]
    linarith [hβ.2]
  have hbp : ∀ τ : ℝ, ‖windowSum d k y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
          ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀ := by
    intro τ
    refine norm_windowSum_le_mass d k y c₀ ?_
    rw [show (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp]
    linarith [hβ.1]
  refine (crossKerFar_pin_le hX1 hL8 hc hMm0 hMp0 hbm hbp).trans ?_
  have hbase : (1 : ℝ) ≤ k + k / Real.sqrt L := by
    have : (0 : ℝ) < k / Real.sqrt L := by positivity
    linarith
  have hrpow : (k + k / Real.sqrt L) ^ (c₀ - α - β) ≤ (k + k / Real.sqrt L) ^ c₀ :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hα.1, hβ.1])
  have hden : (0 : ℝ) < L ^ 2 * Real.sqrt L := by positivity
  gcongr

/-- The pin's amplitude ratio `4(k+h)/(h·T) = 4(√L+1)/T` at `h = k/√L`.  Re-derivation of
`TruncFactor`'s private `far_ratio_calc`. -/
private lemma far_ratio_calcF {X s Q : ℝ} (hX : 0 < X) (hs : 0 < s) (hQ : 0 < Q) :
    4 * (X + X / s) / (X / s * Q) = 4 * (s + 1) / Q := by
  have hX' : X ≠ 0 := ne_of_gt hX
  have hs' : s ≠ 0 := ne_of_gt hs
  have hQ' : Q ≠ 0 := ne_of_gt hQ
  field_simp

/-- **F-2 at a FREE truncation height (`far_kernel_bound_T`).**  `far_kernel_bound` with `T`
a parameter instead of the `L⁴` pin — the exact shape the Z1 residual needs (the module
docstring's repair (i)):

  `crossKerFar ≤ S(c₀−η)·S(c₀)·(k+h)^{c₀}·(4(√L+1)/T)`.

At `T = L⁴` this is `far_kernel_bound` (`4(√L+1)/L⁴ ≤ 1/(L²√L)`, `far_tail_absorb`). -/
theorem far_kernel_bound_T {d : ℕ → ℂ} {t₀' k L c₀ y η T : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hT : 0 < T) :
    ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar d k (k / Real.sqrt L) y c₀ t₀' α β T
        ≤ (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
              ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η))
            * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
              ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀)
            * ((k + k / Real.sqrt L) ^ c₀ * (4 * (Real.sqrt L + 1) / T)) := by
  intro α hα β hβ
  obtain ⟨hk0, hL64, -, -, hη0, hη8, -, -⟩ := pin_basic64F hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hk65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  have hX1 : (1 : ℝ) ≤ k := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hh0 : (0 : ℝ) < k / Real.sqrt L := by positivity
  have hLinv : (0 : ℝ) < 1 / L := by positivity
  have hc : 0 < c₀ - α - β := by
    rw [hc₀]; linarith [hα.2, hβ.2, hα.1, hβ.1]
  have hMm0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
      ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η) := window_mass_nonneg d k y _
  have hMp0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
      ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀ := window_mass_nonneg d k y _
  have hbm : ∀ τ : ℝ, ‖windowSum d k y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
          ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η) := by
    intro τ
    refine norm_windowSum_le_mass d k y (c₀ - η) ?_
    rw [show (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) - (β : ℂ)).re = c₀ - β from by simp]
    linarith [hβ.2]
  have hbp : ∀ τ : ℝ, ‖windowSum d k y (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ ∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
          ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀ := by
    intro τ
    refine norm_windowSum_le_mass d k y c₀ ?_
    rw [show (((c₀ : ℂ) + ((τ : ℝ) : ℂ) * I) + (β : ℂ)).re = c₀ + β from by simp]
    linarith [hβ.1]
  refine (crossKerFar_le_tail hX1 hh0 hc hT hMm0 hMp0 hbm hbp).trans ?_
  have hbase : (1 : ℝ) ≤ k + k / Real.sqrt L := by linarith
  have hbase0 : (0 : ℝ) < k + k / Real.sqrt L := by linarith
  have hsplit : 4 * (k + k / Real.sqrt L) ^ (c₀ - α - β + 1) / (k / Real.sqrt L * T)
      = (k + k / Real.sqrt L) ^ (c₀ - α - β)
        * (4 * (k + k / Real.sqrt L) / (k / Real.sqrt L * T)) := by
    rw [Real.rpow_add hbase0, Real.rpow_one]; ring
  rw [hsplit, far_ratio_calcF hk0 hs0 hT]
  have hrpow : (k + k / Real.sqrt L) ^ (c₀ - α - β) ≤ (k + k / Real.sqrt L) ^ c₀ :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith [hα.1, hβ.1])
  have hamp : (0 : ℝ) ≤ 4 * (Real.sqrt L + 1) / T := by positivity
  gcongr

/-- **F-2b — the mass numerals (`far_window_mass_le`).**  `WindowBridge.window_mass_product`
at the two lines of `far_kernel_bound`, with the shifts `δ := η − 1/L` (low) and
`σ := 1/L` (high).  The LOW leg's excess `(k/y)^{η−1/L}` is the whole Z1 arithmetic story:
at the pin it is `e^{L/(4 log L) − 2 + o(1)}`, superpolynomial in `L` — see the module
docstring's verdict. -/
theorem far_window_mass_le {d : ℕ → ℂ} (hd : ∀ p, p.Prime → ‖d p‖ ≤ 1) {k L c₀ y η : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) :
    (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
        ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ (c₀ - η))
      * (∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈k / y⌉₊,
        ‖lambdaLin (restrictAbove y d) n‖ / (n : ℝ) ^ c₀)
      ≤ (Real.log 4 + 4) ^ 2 * ((k / y) ^ (η - 1 / L) * y ^ (-(1 / L)))
          * (min (Real.log (⌈k / y⌉₊ : ℝ) + (Real.log 4 + 4)) (1 + 2 / (η - 1 / L))
              * min (Real.log (⌈k / y⌉₊ : ℝ) + (Real.log 4 + 4)) (2 + 1 / (1 / L))) := by
  obtain ⟨hk0, hL64, hy131072, -, hη0, hη8, hLη, hyk⟩ := pin_basic64F hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hyk' : y ≤ k := by rw [hy]; exact hyk
  have hXy : (1 : ℝ) ≤ k / y := (one_le_div hy0).mpr hyk'
  have hδ0 : (0 : ℝ) < η - 1 / L := by linarith
  have hδ1 : η - 1 / L ≤ 1 := by
    have : (0 : ℝ) < 1 / L := by positivity
    linarith
  have hσ0 : (0 : ℝ) < 1 / L := by positivity
  have hlow : 1 - (η - 1 / L) ≤ c₀ - η := by rw [hc₀]; ring_nf; linarith
  have hhigh : 1 + 1 / L ≤ c₀ := by rw [hc₀]
  exact window_mass_product d hd hy1 hXy hδ0 hδ1 hσ0 hlow hhigh

/-! ## §3 — F-3: the `hMcap` price of `e^{−M/(2e)}` -/

/-- **F-3a — the price floor (`far_price_floor`).**  Under the crown's OWN ball cap
(`CenterSupply.ball_sup_supplied`'s `hMcap` at `x := X`),

  `M ≤ (1/16)·log log X  ⟹  (log X)^{−1/(32e)} ≤ e^{−M/(2e)}`.

This is the exponent the far term must beat: `1/(32e) ≈ 0.0115`. -/
theorem far_price_floor {M X : ℝ} (hX : Real.exp 1 ≤ X)
    (hMcap : M ≤ 1 / 16 * Real.log (Real.log X)) :
    Real.log X ^ (-(1 / (32 * Real.exp 1))) ≤ Real.exp (-(1 / (2 * Real.exp 1)) * M) := by
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le he0 hX
  have hlog1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log he0 hX
  have hlog0 : (0 : ℝ) < Real.log X := by linarith
  have hrw : Real.log X ^ (-(1 / (32 * Real.exp 1)))
      = Real.exp (-(1 / (32 * Real.exp 1)) * Real.log (Real.log X)) := by
    rw [Real.rpow_def_of_pos hlog0, mul_comm]
  rw [hrw]
  refine Real.exp_le_exp.mpr ?_
  have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
  have h1 : 1 / (2 * Real.exp 1) * M
      ≤ 1 / (2 * Real.exp 1) * (1 / 16 * Real.log (Real.log X)) :=
    mul_le_mul_of_nonneg_left hMcap hc0.le
  have h2 : 1 / (2 * Real.exp 1) * (1 / 16 * Real.log (Real.log X))
      = 1 / (32 * Real.exp 1) * Real.log (Real.log X) := by ring
  linarith

/-- **F-3 — the far term priced (`far_term_priced`).**  The `M`-elimination: with the crown's
cap on `M`, the far remainder's socket may be stated in the `M`-FREE currency
`(log X)^{−1/(32e)}`.  What remains is pure arithmetic in `(k, L, η, Kfar)` — no distance, no
minimality, no vacuity.  (Whether that arithmetic HOLDS at `T = L⁴` is the module docstring's
verdict: it does not; it holds at `T ≈ y·k^{1/log y}`.) -/
theorem far_term_priced {M X k L η Cfar Kfar : ℝ} (hX : Real.exp 1 ≤ X) (hk0 : 0 ≤ k)
    (hCfar0 : 0 ≤ Cfar) (hMcap : M ≤ 1 / 16 * Real.log (Real.log X))
    (hfar : (1 / Real.pi) * (η ^ 2 * (farFbound L * Kfar))
      ≤ Cfar * k * Real.log X ^ (-(1 / (32 * Real.exp 1)))) :
    (1 / Real.pi) * (η ^ 2 * (farFbound L * Kfar))
      ≤ Cfar * k * Real.exp (-(1 / (2 * Real.exp 1)) * M) := by
  refine hfar.trans ?_
  exact mul_le_mul_of_nonneg_left (far_price_floor hX hMcap) (mul_nonneg hCfar0 hk0)

/-! ## §4 — F-4: the ONE-term exit, and the crown's `hRHS` shape -/

set_option maxHeartbeats 800000 in
-- The exit composes `rhs_grade_at_scale_trunc` (itself a long chain) with the far pricing,
-- and the `M`-term is a large opaque `pretDistSq` expression repeated five times; elaboration
-- of the `ring` step over it exceeds the default budget.
/-- **F-4 — THE CLOSED GRADE AT SCALE (`rhs_grade_at_scale_closed`).**
`SupClose.rhs_grade_at_scale_trunc` with its far remainder ABSORBED: the `hFar` binder is
discharged by F-1, and the remainder is priced by F-3 against the crown's own cap, giving the
ONE-term exit

  `‖prop21RHS‖ ≤ (gradeAbsConst Cb + Cfar)·k·e^{−(1/(2e))·M}`,
  `M = 𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t₁; X)`,

which is `CenterSupply.ball_sup_supplied`'s `hRHS` shape with `C₁ := gradeAbsConst Cb + Cfar`
(the byte-check is `hRHS_socket_of_far`).  `hmin` is the COMPACT minimality (`|v| ≤ R`) — the
sixth vacuity catch is behind us.

**The carried hypotheses, enumerated.**  (1) the pin equations `hL/hy/hη/hc₀/hh` and the
scale gate `e^{64} ≤ k`; (2) `hXk : ⌊X⌋₊ ≤ ⌊k⌋₊`; (3) the recentring gate
`hgate : |t₁| + T ≤ R` (⟦V3c⟧'s overhang — Z2); (4) `hmin` on the compact `|v| ≤ R`;
(5) `hMcap`, the crown's A-10 ball cap at `x := X`; (6) `hKfar`, the far kernel binder at the
truncation height `T` (F-2 discharges it at `T = L⁴`); (7) `hfar`, the M-FREE far arithmetic
socket (see the module verdict); (8) the four `JointIntegrableAt` sockets, upstream's own. -/
theorem rhs_grade_at_scale_closed {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb Cfar t₀ t₁ X k L c₀ y η h R T Kfar : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hCfar0 : 0 ≤ Cfar)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L)
    (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hXe : Real.exp 1 ≤ X) (hgate : |t₁| + T ≤ R)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hMcap : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ 1 / 16 * Real.log (Real.log X))
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
        α β T ≤ Kfar)
    (hfar : (1 / Real.pi) * (η ^ 2 * (farFbound L * Kfar))
      ≤ Cfar * k * Real.log X ^ (-(1 / (32 * Real.exp 1))))
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ (gradeAbsConst Cb + Cfar) * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  obtain ⟨hk0, hL64, -, -, -, -, -, -⟩ := pin_basic64F hk hL hy hη
  have hL0 : (0 : ℝ) < L := by linarith
  have hk3 : Real.exp 3 ≤ k :=
    le_trans (Real.exp_le_exp.mpr (by norm_num : (3 : ℝ) ≤ 64)) hk
  have hmain := rhs_grade_at_scale_trunc hg hCb0 hCbound hk hL hy hη hc₀ hh hXk hgate hmin
    (farFbound_nonneg hL0.le) (far_supF_bound hg hk3 hL hy hη hc₀) hKfar hInt
  have hprice := far_term_priced (M := pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀)
      (costwist t₁) X) (X := X) hXe hk0.le hCfar0 hMcap hfar
  have hring : (gradeAbsConst Cb + Cfar) * k
        * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      = gradeAbsConst Cb * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + Cfar * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
    ring
  linarith

set_option maxHeartbeats 800000 in
-- The statement is the crown's binder verbatim (five nested pin expressions per socket);
-- unifying them against `rhs_grade_at_scale_closed`'s five `rfl` pin equations exceeds the
-- default budget.
/-- **THE CROWN'S `hRHS` BINDER (`hRHS_socket_of_far`).**  The STATEMENT below is
`CenterSupply.ball_sup_supplied`'s `hRHS` hypothesis byte-for-byte, at
`C₁ := gradeAbsConst Cb + Cfar`; that this compiles from `rhs_grade_at_scale_closed` is the
binder-compatibility certificate (the house pattern of `SupClose.joint_cs_trunc_pin`).

The per-scale sockets are quantified over the SAME `k`-range as the crown's binder:
`hk64` (the scale gate, from `X₀` at the consumer), `hgate` (the recentring/overhang gate at
the truncation height `T k`), `hKf` (the far kernel binder), `hfar` (the M-free far
arithmetic), `hInt` (the four integrability sockets).  `hmin` and `hMcap` are `X`-level and
`k`-free. -/
theorem hRHS_socket_of_far {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb Cfar t₀ t₁ X R : ℝ} {N : ℕ} {T Kfar : ℕ → ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb) (hCfar0 : 0 ≤ Cfar)
    (hXe : Real.exp 1 ≤ X)
    (hmin : ∀ v : ℝ, |v| ≤ R →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hMcap : pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
      ≤ 1 / 16 * Real.log (Real.log X))
    (hk64 : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ))
    (hgate : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → |t₁| + T k ≤ R)
    (hKf : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ∀ α ∈ Icc (0 : ℝ) (1 / Real.log (Real.log (k : ℝ) ^ 4)),
        ∀ β ∈ Icc (0 : ℝ) (1 / Real.log (Real.log (k : ℝ) ^ 4)),
        crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (k : ℝ)
            ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (Real.log (k : ℝ) ^ 4)
            (1 + 1 / Real.log (k : ℝ)) (t₀ + t₁) α β (T k)
          ≤ Kfar k)
    (hfar : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      (1 / Real.pi) * ((1 / Real.log (Real.log (k : ℝ) ^ 4)) ^ 2
          * (farFbound (Real.log (k : ℝ)) * Kfar k))
        ≤ Cfar * (k : ℝ) * Real.log X ^ (-(1 / (32 * Real.exp 1))))
    (hInt : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
        (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
        (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
        (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) :
    ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
        ≤ (gradeAbsConst Cb + Cfar) * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by
  intro k hk1 hk2
  have hXk : ⌊X⌋₊ ≤ ⌊(k : ℝ)⌋₊ := by rw [Nat.floor_natCast]; exact hk1
  exact rhs_grade_at_scale_closed hg hCb0 hCbound hCfar0 (hk64 k hk1 hk2) rfl rfl rfl rfl rfl
    hXk hXe (hgate k hk1 hk2) hmin hMcap (hKf k hk1 hk2) (hfar k hk1 hk2) (hInt k hk1 hk2)

set_option maxHeartbeats 800000 in
-- The crown's binder block is instantiated wholesale (eight sockets, each carrying five pin
-- expressions); the unification exceeds the default budget.
/-- **THE CROWN AT THE NON-VACUOUS `hmin` (`ball_sup_closed`).**
`CenterSupply.ball_sup_supplied` with its `hRHS` socket supplied by `hRHS_socket_of_far`:
the pointwise weighted ball bound at `S₀ = C₁·e^{−(1/(2e))·𝔻²} + 4(log X)^{−1/2+1/1000}` with
`C₁ = gradeAbsConst Cb + Cfar` ABSOLUTE, and with the frequency structure entering ONLY
through the COMPACT minimality `hmin` (`|v| ≤ R`) — the sixth vacuity catch is not in this
chain.

**What is still carried, and where it bites.**  `hgate` (⟦V3c⟧'s overhang, Z2) and `hfar`
(the M-free far arithmetic).  At the truncation height `T k = (log k)⁴` the `hfar` socket is
FALSE — see the module docstring's verdict and the two priced repairs.  This theorem is the
frame those repairs plug into, not a closed result. -/
theorem ball_sup_closed {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (Tb Cb Cfar R : ℝ) (T Kfar : ℕ → ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → Real.exp 1 ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X →
        0 ≤ Cb → ShortIntervalDatum Cb → 0 ≤ Cfar →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ v : ℝ, |v| ≤ R →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
          pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
            ≤ (1 / 16) * Real.log (Real.log X)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → |t₁| + T k ≤ R) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          ∀ α ∈ Icc (0 : ℝ) (1 / Real.log (Real.log (k : ℝ) ^ 4)),
            ∀ β ∈ Icc (0 : ℝ) (1 / Real.log (Real.log (k : ℝ) ^ 4)),
            crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (k : ℝ)
                ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (Real.log (k : ℝ) ^ 4)
                (1 + 1 / Real.log (k : ℝ)) (t₀ + t₁) α β (T k) ≤ Kfar k) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          (1 / Real.pi) * ((1 / Real.log (Real.log (k : ℝ) ^ 4)) ^ 2
              * (farFbound (Real.log (k : ℝ)) * Kfar k))
            ≤ Cfar * (k : ℝ) * Real.log X ^ (-(1 / (32 * Real.exp 1)))) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
          JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
            (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) (k : ℝ)
            (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
            (1 / Real.log (Real.log (k : ℝ) ^ 4))
            ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)))) →
      ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ Tb → |t - t₁| ≤ seamRad X →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ ballSupS X ((gradeAbsConst Cb + Cfar)
                  * Real.exp (-(1 / (2 * Real.exp 1))
                      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₀, hX₀0, H⟩ := ball_sup_supplied hg t₀ t₁
  refine ⟨X₀, hX₀0, ?_⟩
  intro X N Tb Cb Cfar R T Kfar a hXlb hXe hXN hN2 hCb0 hCbound hCfar0 hsupp hDatum hmin
    hMcapX hk64 hgate hKf hfar hInt
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hXe
  exact H X N Tb (gradeAbsConst Cb + Cfar) a hXlb hXN hN2
    (by have := gradeAbsConst_nonneg hCb0; linarith) hsupp hDatum
    (hRHS_socket_of_far hg hCb0 hCbound hCfar0 hXe hmin
      (hMcapX X le_rfl (by linarith)) hk64 hgate hKf hfar hInt) hMcapX

end Salt.MR
