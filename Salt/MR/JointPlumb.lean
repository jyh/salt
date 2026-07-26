/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RHSGrade

/-!
# JOINT-PLUMB — the four `JointIntegrableAt` sockets, discharged

`RHSGrade.JointIntegrableAt` bundles `JointHead.joint_cs_factoring`'s four
interval-integrability binders (the house conditional-assembly form).  Every consumer of the
`hRHS` chain (`GradeConst.hRHS_discharged_const`, `FarStar.hRHS_socket_star`,
`FarClose`, `SeamGate`, `SupClose`) carries the bundle.  This file proves it outright at the
pin, so the socket vanishes.

## The routes, per socket

* **`hIβ` / `hIα` (the `supF·crossKer` legs) — CONTINUITY.**  `crossKer α β` is a parametric
  `t`-integral; §2 proves it is *jointly* continuous in `(α, β)` on `{0 < c₀ − α − β}` by
  dominated convergence (`continuousAt_of_dominated`).  The dominating function is the one
  `JointHead.crossKer_integrand_integrable` already exhibits, made uniform on a small square
  around the base point: the two window legs by `norm_windowSum_le_mass` at the worst line
  `c₀ − β − 1`, the kernel by its Lorentzian bound (re-derived here from `hat_mellin_bound`,
  since `HalaszPrimesCore.norm_hatKernel_le` is outside this file's import closure) at the
  worst exponent and the *smallest*
  Lorentzian width in the square.  `rhsFbound M L (β + 1/L)` is continuous for `σ = β + 1/L
  > 0` (`GradeConst.rhs_shift_integrableC`'s continuity page, re-derived), so the product is
  continuous on the box; `hIβ` is `ContinuousOn.intervalIntegrable`, and `hIα` is a second
  dominated-convergence pass (`intervalIntegral.continuousAt_of_dominated_interval`) with a
  CONSTANT dominating function — the box sup, from compactness.

* **`hIβ'` / `hIα'` (the `prop21RHS` integrand legs) — MEASURABILITY + DOMINATION.**  Here
  continuity is genuinely unavailable: the integrand carries `smoothSeries y d (s − α − β)`,
  an `LSeries` whose argument has real part `c₀ − α − β`, and at the pin that dips BELOW the
  abscissa `1` (`η = 1/(4 log L)` is far larger than `c₀ − 1 = 1/L`), where `LSeries` is the
  junk value of a divergent `tsum` — a genuine discontinuity.  So these two go by the honest
  bounded-measurable route: the parametric integral is strongly measurable
  (`Measurable.tsum` gives `Measurable (LSeries a)` outright; `hatKernel` is a quotient of
  continuous functions, hence measurable through its polar set; then
  `StronglyMeasurable.integral_prod_right'`), and it is dominated by the `hIβ` integrand
  through the LANDED `JointHead.joint_inner_factor` at `F := rhsFbound M L (β + 1/L)`
  (`RHSGrade.joint_supF_pin`).  `IntervalIntegrable.mono_fun` closes both.

## Gates

`jointIntegrableAt_of_gates` is the general form: `1 ≤ X`, `0 < h`, `0 < L`, `0 ≤ η`,
`0 < c₀ − 2η`, and the `supF` binder of `joint_cs_factoring` at `rhsFbound M L (β + 1/L)`.
`jointIntegrableAt_discharged` is its pin face: the pin equations, `e^{64} ≤ k`, `0 < h`, and
the distance floor `hMt` — exactly the data every consumer already holds (`hmin` ⟹ `hMt` by
`CenterSupply.center_dist_floor`).  `jointIntegrableAt_pin` is that face at the consumers'
byte-for-byte binder shape (`k : ℕ`, `h = k/√L`).  Nothing else is carried.

§1 measurability stones · §2 the `crossKer` continuity stone · §3 `hIβ`, `hIα` ·
§4 `hIβ'`, `hIα'` · §5 the exit.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

/-! ## §1 — measurability stones -/

/-- `LSeries a` is measurable.  The `tsum` of the (continuous) `LSeries.term`s, through
`Measurable.tsum` — no convergence hypothesis, so this is valid on the divergence region
where `LSeries` takes its junk value. -/
private lemma measurable_LSeriesP (a : ℕ → ℂ) : Measurable (LSeries a) := by
  have h : (LSeries a) = fun s : ℂ => ∑' n : ℕ, LSeries.term a s n := rfl
  rw [h]
  refine Measurable.tsum (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · simp only [LSeries.term, if_neg hn]
    exact measurable_const.div ((continuous_id.const_cpow (Or.inl (by
      exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr hn))).measurable)

/-- The hat kernel, composed with measurable `(c, u)` data, is measurable.  A quotient of
continuous functions of `(c, u)`: measurable through the polar set `{s(s+1) = 0}` by
`Measurable.div` (no non-vanishing hypothesis needed). -/
private lemma measurable_hatKernelC {Ω : Type*} [MeasurableSpace Ω] {X h : ℝ}
    (hX : 0 < X) (hXh : 0 < X + h) {c u : Ω → ℝ} (hc : Measurable c) (hu : Measurable u) :
    Measurable (fun w : Ω => hatKernel X h (c w) (u w)) := by
  have hcC : Measurable (fun w : Ω => ((c w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hc
  have huC : Measurable (fun w : Ω => ((u w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hu
  have hs : Measurable (fun w : Ω => ((c w : ℝ) : ℂ) + ((u w : ℝ) : ℂ) * I) :=
    hcC.add (huC.mul measurable_const)
  have hexp : Measurable (fun w : Ω => (((c w : ℝ) : ℂ) + ((u w : ℝ) : ℂ) * I) + 1) :=
    hs.add measurable_const
  have hpow : ∀ b : ℂ, b ≠ 0 →
      Measurable (fun w : Ω => b ^ ((((c w : ℝ) : ℂ) + ((u w : ℝ) : ℂ) * I) + 1)) := by
    intro b hb
    exact ((continuous_id.const_cpow (Or.inl hb)).measurable).comp hexp
  exact ((hpow _ (Complex.ofReal_ne_zero.mpr hXh.ne')).sub
    (hpow _ (Complex.ofReal_ne_zero.mpr hX.ne'))).div (measurable_const.mul (hs.mul hexp))

/-- The `prop21RHS` integrand, composed with measurable `(α, β, t)` data, is measurable.  The
two window legs and the shifts are continuous; the two `LSeries` legs go through
`measurable_LSeriesP`; the kernel through `measurable_hatKernelC`. -/
private lemma measurable_jointIntegrandC {Ω : Type*} [MeasurableSpace Ω] {d : ℕ → ℂ}
    {t₀ X h c₀ y : ℝ} (hX : 0 < X) (hXh : 0 < X + h) {a b u : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hu : Measurable u) :
    Measurable (fun w : Ω => jointIntegrand d t₀ X h c₀ y (a w) (b w) (u w)) := by
  simp only [jointIntegrand]
  have haC : Measurable (fun w : Ω => ((a w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp ha
  have hbC : Measurable (fun w : Ω => ((b w : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hb
  have hs : Measurable (fun w : Ω => ((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I)) :=
    measurable_const.add
      ((Complex.continuous_ofReal.measurable.comp (hu.sub measurable_const)).mul
        measurable_const)
  have hsm : Measurable (fun w : Ω =>
      ((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) - ((a w : ℝ) : ℂ) - ((b w : ℝ) : ℂ)) :=
    (hs.sub haC).sub hbC
  have hsp : Measurable (fun w : Ω =>
      ((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) + ((b w : ℝ) : ℂ)) := hs.add hbC
  have hsn : Measurable (fun w : Ω =>
      ((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) - ((b w : ℝ) : ℂ)) := hs.sub hbC
  have h1 : Measurable (fun w : Ω => smoothSeries y d
      (((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) - ((a w : ℝ) : ℂ) - ((b w : ℝ) : ℂ))) :=
    (measurable_LSeriesP _).comp hsm
  have h2 : Measurable (fun w : Ω => largeSeries y d
      (((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) + ((b w : ℝ) : ℂ))) :=
    (measurable_LSeriesP _).comp hsp
  have h3 : Measurable (fun w : Ω => windowSum d X y
      (((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) - ((b w : ℝ) : ℂ))) :=
    ((continuous_windowSum d X y).measurable).comp hsn
  have h4 : Measurable (fun w : Ω => windowSum d X y
      (((c₀ : ℂ) + ((u w - t₀ : ℝ) : ℂ) * I) + ((b w : ℝ) : ℂ))) :=
    ((continuous_windowSum d X y).measurable).comp hsp
  have h5 : Measurable (fun w : Ω =>
      hatKernel X h (c₀ - a w - b w) (u w - t₀)) :=
    measurable_hatKernelC hX hXh ((measurable_const.sub ha).sub hb)
      (hu.sub measurable_const)
  exact ((((h1.mul h2).mul h3).mul h4).mul h5)

/-! ## §2 — `crossKer` is jointly continuous in `(α, β)` on `{0 < c₀ − α − β}` -/

/-- The hat kernel's Lorentzian bound, re-derived from `hat_mellin_bound` (the
`HalaszPrimesCore.norm_hatKernel_le` page is outside this file's import closure). -/
private lemma norm_hatKernel_leP {X h c : ℝ} (hX : 1 ≤ X) (hh : 0 < h) (hc : 0 < c) (t : ℝ) :
    ‖hatKernel X h c t‖ ≤ (X + h) ^ c * (2 * (X + h) / h) * (c ^ 2 + t ^ 2)⁻¹ := by
  have hXh : (0 : ℝ) < X + h := by linarith
  have hb := hat_mellin_bound hX hh hc t
  have hnorm : ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  calc ‖hatKernel X h c t‖
      ≤ (X + h) ^ c * (2 * (X + h) / (h * ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2)) := by
        refine hb.trans ?_
        gcongr
        exact min_le_right _ _
    _ = (X + h) ^ c * (2 * (X + h) / h) * (c ^ 2 + t ^ 2)⁻¹ := by
        rw [hnorm]
        have hct : (0 : ℝ) < c ^ 2 + t ^ 2 := by positivity
        field_simp

/-- The `crossKer` `t`-integrand is continuous in `t` (the continuity page inside
`JointHead.crossKer_integrand_integrable`, re-derived). -/
private lemma continuous_crossKer_integrand {g : ℕ → ℂ} {X h y c₀ t₀ α β : ℝ}
    (hX : 0 < X) (hh : 0 < h) (hc : 0 < c₀ - α - β) :
    Continuous (fun t : ℝ =>
      ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (β : ℂ))‖
        * ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
        * ‖hatKernel X h (c₀ - α - β) (t - t₀)‖) := by
  have hs : Continuous (fun t : ℝ => ((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I)) := by fun_prop
  exact ((((continuous_windowSum g X y).comp (hs.sub continuous_const)).norm).mul
      (((continuous_windowSum g X y).comp (hs.add continuous_const)).norm)).mul
    (((continuous_hatKernel hX hh hc).comp (continuous_id.sub continuous_const)).norm)

/-- The hat kernel is continuous in its LINE parameter `c` at every `c > 0` — a ratio of
entire `cpow`s over `h·s·(s+1)`, non-vanishing there by `SW.s_ne_zero`/`SW.s1_ne_zero`. -/
private lemma continuousAt_hatKernelC {Ω : Type*} [TopologicalSpace Ω] {X h u : ℝ}
    {c : Ω → ℝ} {w₀ : Ω} (hX : 0 < X) (hXh : 0 < X + h) (hh : 0 < h)
    (hcc : ContinuousAt c w₀) (hpos : 0 < c w₀) :
    ContinuousAt (fun w : Ω => hatKernel X h (c w) u) w₀ := by
  have hcC : ContinuousAt (fun w : Ω => ((c w : ℝ) : ℂ)) w₀ :=
    Complex.continuous_ofReal.continuousAt.comp hcc
  have hs : ContinuousAt (fun w : Ω => ((c w : ℝ) : ℂ) + (u : ℂ) * I) w₀ :=
    hcC.add continuousAt_const
  have hexp : ContinuousAt (fun w : Ω => (((c w : ℝ) : ℂ) + (u : ℂ) * I) + 1) w₀ :=
    hs.add continuousAt_const
  have hpow : ∀ b : ℂ, b ≠ 0 →
      ContinuousAt (fun w : Ω => b ^ ((((c w : ℝ) : ℂ) + (u : ℂ) * I) + 1)) w₀ := by
    intro b hb
    exact ((continuous_id.const_cpow (Or.inl hb)).continuousAt).comp hexp
  refine ContinuousAt.div ((hpow _ (Complex.ofReal_ne_zero.mpr hXh.ne')).sub
    (hpow _ (Complex.ofReal_ne_zero.mpr hX.ne'))) (continuousAt_const.mul (hs.mul hexp)) ?_
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne')
    (mul_ne_zero (Salt.SW.s_ne_zero hpos u) (Salt.SW.s1_ne_zero hpos u))

/-- **THE `crossKer` CONTINUITY STONE.**  `crossKer g X h y c₀ t₀ (a w) (b w)` is continuous
at `w₀` whenever `a`, `b` are (with `0 ≤ b w₀` and `0 < c₀ − a w₀ − b w₀`) — so `crossKer` is
JOINTLY continuous in `(α, β)` on the open half-plane, in composable form.

Dominated convergence (`MeasureTheory.continuousAt_of_dominated`) on the small square
`|a w − a w₀| < r`, `|b w − b w₀| < r`, `r = min ((c₀ − a w₀ − b w₀)/4) 1`: the two window
legs are bounded by their `n^{−(c₀ − b w₀ − 1)}`-weighted coefficient mass
(`norm_windowSum_le_mass`, uniform on the square), and the kernel by the Lorentzian bound at
the LARGEST exponent and the SMALLEST width the square allows — an `L¹` dominator through
`SW.integrable_inv_c_sq_add_sq`.  Pointwise continuity is `continuousAt_hatKernelC` against
the two window legs. -/
lemma continuousAt_crossKer {Ω : Type*} [TopologicalSpace Ω] [FirstCountableTopology Ω]
    {g : ℕ → ℂ} {X h y c₀ t₀ : ℝ} {a b : Ω → ℝ} {w₀ : Ω}
    (hX : 1 ≤ X) (hh : 0 < h) (ha : ContinuousAt a w₀) (hb : ContinuousAt b w₀)
    (hβ0 : 0 ≤ b w₀) (hc : 0 < c₀ - a w₀ - b w₀) :
    ContinuousAt (fun w : Ω => crossKer g X h y c₀ t₀ (a w) (b w)) w₀ := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh : (0 : ℝ) < X + h := by linarith
  have hXh1 : (1 : ℝ) ≤ X + h := by linarith
  obtain ⟨e, he0, he⟩ : ∃ e : ℝ, 0 < e ∧ c₀ - a w₀ - b w₀ = 2 * e :=
    ⟨(c₀ - a w₀ - b w₀) / 2, by linarith, by ring⟩
  obtain ⟨r, hr0, hre, hr1⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ e / 2 ∧ r ≤ 1 :=
    ⟨min (e / 2) 1, lt_min (by linarith) one_pos, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨Mw, hMw0, hMwb⟩ : ∃ Mw : ℝ, 0 ≤ Mw ∧ ∀ z : ℂ, c₀ - b w₀ - 1 ≤ z.re →
      ‖windowSum g X y z‖ ≤ Mw :=
    ⟨∑ n ∈ Finset.Ioo ⌊y⌋₊ ⌈X / y⌉₊,
        ‖lambdaLin (restrictAbove y g) n‖ / (n : ℝ) ^ (c₀ - b w₀ - 1),
      Finset.sum_nonneg (fun n _ => by positivity),
      fun z hz => norm_windowSum_le_mass g X y (c₀ - b w₀ - 1) hz⟩
  obtain ⟨A, hA0, hAb⟩ : ∃ A : ℝ, 0 ≤ A ∧ ∀ c u : ℝ, e ≤ c → c ≤ 3 * e →
      ‖hatKernel X h c u‖ ≤ A * (e ^ 2 + u ^ 2)⁻¹ := by
    refine ⟨(X + h) ^ (3 * e) * (2 * (X + h) / h), by positivity, fun c u hce hc3 => ?_⟩
    have hcpos : 0 < c := lt_of_lt_of_le he0 hce
    refine (norm_hatKernel_leP hX hh hcpos u).trans ?_
    have h2 : (c ^ 2 + u ^ 2)⁻¹ ≤ (e ^ 2 + u ^ 2)⁻¹ := by gcongr
    refine mul_le_mul ?_ h2 (by positivity) (by positivity)
    gcongr
  have hEa : ∀ᶠ w in 𝓝 w₀, a w ∈ Ioo (a w₀ - r) (a w₀ + r) :=
    ha (Ioo_mem_nhds (by linarith) (by linarith))
  have hEb : ∀ᶠ w in 𝓝 w₀, b w ∈ Ioo (b w₀ - r) (b w₀ + r) :=
    hb (Ioo_mem_nhds (by linarith) (by linarith))
  have hEv := hEa.and hEb
  simp only [crossKer]
  refine continuousAt_of_dominated
    (bound := fun t : ℝ => Mw * Mw * (A * (e ^ 2 + (t - t₀) ^ 2)⁻¹)) ?_ ?_ ?_ ?_
  · refine hEv.mono ?_
    rintro w ⟨⟨ha1, ha2⟩, hb1, hb2⟩
    exact (continuous_crossKer_integrand (g := g) (y := y) (t₀ := t₀) (α := a w) (β := b w)
      hX0 hh (by linarith)).aestronglyMeasurable
  · refine hEv.mono ?_
    rintro w ⟨⟨ha1, ha2⟩, hb1, hb2⟩
    refine Filter.Eventually.of_forall (fun t => ?_)
    have hrem : (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - ((b w : ℝ) : ℂ)).re = c₀ - b w := by simp
    have hrep : (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + ((b w : ℝ) : ℂ)).re = c₀ + b w := by simp
    have hbm : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - ((b w : ℝ) : ℂ))‖ ≤ Mw :=
      hMwb _ (by rw [hrem]; linarith)
    have hbp : ‖windowSum g X y (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + ((b w : ℝ) : ℂ))‖ ≤ Mw :=
      hMwb _ (by rw [hrep]; linarith)
    have hk : ‖hatKernel X h (c₀ - a w - b w) (t - t₀)‖ ≤ A * (e ^ 2 + (t - t₀) ^ 2)⁻¹ :=
      hAb _ _ (by linarith) (by linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul hbm hbp (norm_nonneg _) hMw0) hk (norm_nonneg _)
      (by positivity)
  · exact (((Salt.SW.integrable_inv_c_sq_add_sq he0).comp_sub_right t₀).const_mul A).const_mul
      (Mw * Mw)
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have hbC : ContinuousAt (fun w : Ω => ((b w : ℝ) : ℂ)) w₀ :=
      Complex.continuous_ofReal.continuousAt.comp hb
    have hsm : ContinuousAt
        (fun w : Ω => ((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - ((b w : ℝ) : ℂ)) w₀ :=
      continuousAt_const.sub hbC
    have hsp : ContinuousAt
        (fun w : Ω => ((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + ((b w : ℝ) : ℂ)) w₀ :=
      continuousAt_const.add hbC
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
    · exact (((continuous_windowSum g X y).continuousAt).comp hsm).norm
    · exact (((continuous_windowSum g X y).continuousAt).comp hsp).norm
    · exact (continuousAt_hatKernelC hX0 hXh hh
        ((continuousAt_const.sub ha).sub hb) (by linarith)).norm

/-! ## §3 — the `supF·crossKer` legs (`hIβ`, `hIα`) -/
/-- `σ ↦ rhsFbound M L σ` at `σ = b w + 1/L` is continuous where `σ > 0`
(`GradeConst.rhs_shift_integrableC`'s continuity page, in composable form). -/
private lemma continuousAt_rhsFbound_shiftP {Ω : Type*} [TopologicalSpace Ω] {M L : ℝ}
    {b : Ω → ℝ} {w₀ : Ω} (hL0 : 0 < L) (hb : ContinuousAt b w₀) (hσ : 0 < b w₀ + 1 / L) :
    ContinuousAt (fun w : Ω => rhsFbound M L (b w + 1 / L)) w₀ := by
  simp only [rhsFbound]
  have hσc : ContinuousAt (fun w : Ω => b w + 1 / L) w₀ := hb.add continuousAt_const
  refine ContinuousAt.mul (continuousAt_const.mul
    (continuousAt_const.div hσc (ne_of_gt hσ))) ?_
  refine Real.continuous_exp.continuousAt.comp ?_
  refine continuousAt_const.mul ((continuousAt_const.sub ?_).sub continuousAt_const)
  exact continuousAt_const.mul (ContinuousAt.log (hσc.mul continuousAt_const)
    (ne_of_gt (mul_pos hσ hL0)))

/-- The `hIβ`/`hIα` integrand `rhsFbound M L (β + 1/L) · crossKer α β` is continuous wherever
`0 ≤ β`, `0 < c₀ − α − β` and `0 < L` — in composable form, so it serves both the `β`-slice
and the `(α, β)`-box. -/
lemma continuousAt_fbound_mul_crossKer {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] {g : ℕ → ℂ} {M L X h y c₀ t₀ : ℝ} {a b : Ω → ℝ} {w₀ : Ω}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (ha : ContinuousAt a w₀) (hb : ContinuousAt b w₀)
    (hβ0 : 0 ≤ b w₀) (hc : 0 < c₀ - a w₀ - b w₀) :
    ContinuousAt (fun w : Ω =>
      rhsFbound M L (b w + 1 / L) * crossKer g X h y c₀ t₀ (a w) (b w)) w₀ := by
  have hLi : (0 : ℝ) < 1 / L := by positivity
  exact (continuousAt_rhsFbound_shiftP hL0 hb (by linarith)).mul
    (continuousAt_crossKer hX hh ha hb hβ0 hc)

/-- **SOCKET 1 (`hIβ`).**  For each `α ∈ [0, η]`, `β ↦ rhsFbound M L (β+1/L)·crossKer α β` is
interval-integrable on `[0, η]` — continuous there, hence integrable. -/
theorem intervalIntegrable_beta_leg {g : ℕ → ℂ} {M L X h y c₀ t₀ η α : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hα : α ∈ Icc (0 : ℝ) η) :
    IntervalIntegrable (fun β => rhsFbound M L (β + 1 / L) * crossKer g X h y c₀ t₀ α β)
      volume 0 η := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hη0]
  rintro β ⟨hβ0, hβη⟩
  have hαη : α ≤ η := hα.2
  refine ContinuousAt.continuousWithinAt ?_
  exact continuousAt_fbound_mul_crossKer (Ω := ℝ) (a := fun _ => α) (b := fun x => x)
    (w₀ := β) hX hh hL0 continuousAt_const continuousAt_id hβ0
    (by linarith)


/-- The `(α, β)`-box sup of the `hIβ` integrand, on a box slightly ENLARGED in `α` (so a
neighbourhood of every `α ∈ [0, η]` still lands inside). -/
private lemma exists_box_bound {g : ℕ → ℂ} {M L X h y c₀ t₀ η : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hc2η : 0 < c₀ - 2 * η) :
    ∃ C : ℝ, ∀ α ∈ Icc (-1 : ℝ) (η + (c₀ - 2 * η) / 2), ∀ β ∈ Icc (0 : ℝ) η,
      ‖rhsFbound M L (β + 1 / L) * crossKer g X h y c₀ t₀ α β‖ ≤ C := by
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => rhsFbound M L (p.2 + 1 / L) * crossKer g X h y c₀ t₀ p.1 p.2)
      (Icc (-1 : ℝ) (η + (c₀ - 2 * η) / 2) ×ˢ Icc (0 : ℝ) η) := by
    rintro ⟨u, v⟩ ⟨⟨hu1, hu2⟩, hv1, hv2⟩
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_fbound_mul_crossKer (a := Prod.fst) (b := Prod.snd) hX hh hL0
      continuousAt_fst continuousAt_snd hv1 (by change (0 : ℝ) < c₀ - u - v; linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  exact ⟨C, fun α hα β hβ => hC (α, β) ⟨hα, hβ⟩⟩

/-- **SOCKET 3 (`hIα`).**  `α ↦ ∫₀^η rhsFbound M L (β+1/L)·crossKer α β dβ` is
interval-integrable on `[0, η]`.  A second dominated-convergence pass
(`intervalIntegral.continuousAt_of_dominated_interval`) with the CONSTANT box bound
`exists_box_bound` as dominator; the box is enlarged in `α` so a neighbourhood of every
`α ∈ [0, η]` still lands in the region `0 < c₀ − α − β`. -/
theorem intervalIntegrable_alpha_leg {g : ℕ → ℂ} {M L X h y c₀ t₀ η : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η) :
    IntervalIntegrable (fun α => ∫ β in (0 : ℝ)..η,
      rhsFbound M L (β + 1 / L) * crossKer g X h y c₀ t₀ α β) volume 0 η := by
  obtain ⟨C, hC⟩ := exists_box_bound (g := g) (M := M) (L := L) (X := X) (h := h) (y := y)
    (c₀ := c₀) (t₀ := t₀) (η := η) hX hh hL0 hc2η
  have hδ0 : (0 : ℝ) < (c₀ - 2 * η) / 2 := by linarith
  have hIoc : Set.uIoc (0 : ℝ) η = Ioc 0 η := uIoc_of_le hη0
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hη0]
  rintro α₀ ⟨hα₀0, hα₀η⟩
  refine ContinuousAt.continuousWithinAt ?_
  have hρ0 : (0 : ℝ) < min 1 ((c₀ - 2 * η) / 2) := lt_min one_pos hδ0
  have hnb : Ioo (α₀ - min 1 ((c₀ - 2 * η) / 2)) (α₀ + min 1 ((c₀ - 2 * η) / 2)) ∈ 𝓝 α₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hbox : ∀ α ∈ Ioo (α₀ - min 1 ((c₀ - 2 * η) / 2)) (α₀ + min 1 ((c₀ - 2 * η) / 2)),
      α ∈ Icc (-1 : ℝ) (η + (c₀ - 2 * η) / 2) := by
    rintro α ⟨h1, h2⟩
    have hm1 : min 1 ((c₀ - 2 * η) / 2) ≤ 1 := min_le_left _ _
    have hm2 : min 1 ((c₀ - 2 * η) / 2) ≤ (c₀ - 2 * η) / 2 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  refine intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => C) ?_ ?_ intervalIntegrable_const ?_
  · refine Filter.eventually_of_mem hnb (fun α hα => ?_)
    obtain ⟨hα1, hα2⟩ := hbox α hα
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    rw [hIoc]
    rintro β ⟨hβ0, hβη⟩
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_fbound_mul_crossKer (Ω := ℝ) (a := fun _ => α) (b := fun x => x)
      (w₀ := β) hX hh hL0 continuousAt_const continuousAt_id hβ0.le
      (by linarith)
  · refine Filter.eventually_of_mem hnb (fun α hα => ?_)
    refine Filter.Eventually.of_forall (fun β hβ => ?_)
    rw [hIoc] at hβ
    exact hC α (hbox α hα) β ⟨hβ.1.le, hβ.2⟩
  · refine Filter.Eventually.of_forall (fun β hβ => ?_)
    rw [hIoc] at hβ
    obtain ⟨hβ0, hβη⟩ := hβ
    exact continuousAt_fbound_mul_crossKer (Ω := ℝ) (a := fun x => x) (b := fun _ => β)
      (w₀ := α₀) hX hh hL0 continuousAt_id continuousAt_const hβ0.le
      (by linarith)

/-! ## §4 — the `prop21RHS` legs (`hIβ'`, `hIα'`) -/

/-- The inner `t`-integral is dominated by the `hIβ` integrand: `JointHead.joint_inner_factor`
at `F := rhsFbound M L (β + 1/L)`, with the harmless `1/(2π) ≤ 1`. -/
private lemma norm_inner_le {d : ℕ → ℂ} {M L X h y c₀ t₀ α β : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hβ0 : 0 ≤ β) (hc : 0 < c₀ - α - β)
    (hsupF : ∀ t : ℝ,
      ‖smoothSeries y d (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y d (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L)) :
    ‖(1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖
      ≤ rhsFbound M L (β + 1 / L) * crossKer d X h y c₀ t₀ α β := by
  have hLi : (0 : ℝ) < 1 / L := by positivity
  have hσ : (0 : ℝ) < β + 1 / L := by linarith
  have hF0 := rhsFbound_nonneg M L hσ
  have hkey := joint_inner_factor (g := d) (t₀ := t₀) (X := X) (h := h) (c₀ := c₀) (y := y)
    (α := α) (β := β) (F := rhsFbound M L (β + 1 / L)) hX hh hc hF0 hsupF
  have hpi : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hle1 : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  rw [norm_smul, Real.norm_of_nonneg hpi]
  calc (1 / (2 * Real.pi)) * ‖∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖
      ≤ 1 * (rhsFbound M L (β + 1 / L) * crossKer d X h y c₀ t₀ α β) :=
        mul_le_mul hle1 hkey (norm_nonneg _) zero_le_one
    _ = rhsFbound M L (β + 1 / L) * crossKer d X h y c₀ t₀ α β := one_mul _

/-- **SOCKET 2 (`hIβ'`).**  The `prop21RHS` `β`-leg.  Continuity is unavailable here (the
`smoothSeries` factor is discontinuous where its `LSeries` leaves the convergence
half-plane), so: strong measurability of the parametric integral
(`measurable_jointIntegrandC` + `StronglyMeasurable.integral_prod_right'`), dominated by the
`hIβ` integrand through `norm_inner_le`; `IntervalIntegrable.mono_fun` closes. -/
theorem intervalIntegrable_beta_leg' {d : ℕ → ℂ} {M L X h y c₀ t₀ η α : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hα : α ∈ Icc (0 : ℝ) η)
    (hsupF : ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y d (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y d (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L)) :
    IntervalIntegrable
      (fun β => ‖(1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖)
      volume 0 η := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh : (0 : ℝ) < X + h := by linarith
  have hIoc : Set.uIoc (0 : ℝ) η = Ioc 0 η := uIoc_of_le hη0
  refine (intervalIntegrable_beta_leg (g := d) (M := M) (y := y) (t₀ := t₀)
    hX hh hL0 hη0 hc2η hα).mono_fun ?_ ?_
  · have hSM : StronglyMeasurable
        (fun q : ℝ × ℝ => jointIntegrand d t₀ X h c₀ y α q.1 q.2) :=
      (measurable_jointIntegrandC hX0 hXh measurable_const measurable_fst
        measurable_snd).stronglyMeasurable
    exact ((hSM.integral_prod_right'.const_smul
      (1 / (2 * Real.pi) : ℝ)).norm).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall ?_)
    intro β hβ
    rw [hIoc] at hβ
    obtain ⟨hβ0, hβη⟩ := hβ
    have hLi : (0 : ℝ) < 1 / L := by positivity
    have hnn : 0 ≤ rhsFbound M L (β + 1 / L) * crossKer d X h y c₀ t₀ α β :=
      mul_nonneg (rhsFbound_nonneg M L (by linarith)) (crossKer_nonneg _ _ _ _ _ _ _ _)
    have hgoal : ‖‖(1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖‖
        ≤ ‖rhsFbound M L (β + 1 / L) * crossKer d X h y c₀ t₀ α β‖ := by
      rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_of_nonneg hnn]
      exact norm_inner_le hX hh hL0 hβ0.le (by linarith [hα.2]) (hsupF β ⟨hβ0.le, hβη⟩)
    exact hgoal

/-- **SOCKET 4 (`hIα'`).**  The `prop21RHS` `α`-leg.  Same route as `hIβ'`, one level up: the
double parametric integral is strongly measurable by two `integral_prod_right'` passes, and
`intervalIntegral.norm_integral_le_of_norm_le_const` bounds it by `C·|η|` with `C` the box
sup of `exists_box_bound`; `IntervalIntegrable.mono_fun` against the constant closes. -/
theorem intervalIntegrable_alpha_leg' {d : ℕ → ℂ} {M L X h y c₀ t₀ η : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hsupF : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y d (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y d (((c₀ : ℂ) + ((t - t₀ : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L)) :
    IntervalIntegrable (fun α => ‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
      ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖) volume 0 η := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hXh : (0 : ℝ) < X + h := by linarith
  have hIoc : Set.uIoc (0 : ℝ) η = Ioc 0 η := uIoc_of_le hη0
  obtain ⟨C, hC⟩ := exists_box_bound (g := d) (M := M) (L := L) (X := X) (h := h) (y := y)
    (c₀ := c₀) (t₀ := t₀) (η := η) hX hh hL0 hc2η
  refine (intervalIntegrable_const (a := (0 : ℝ)) (b := η) (c := C * |η - 0|)).mono_fun ?_ ?_
  · have hSM : StronglyMeasurable
        (fun p : (ℝ × ℝ) × ℝ => jointIntegrand d t₀ X h c₀ y p.1.1 p.1.2 p.2) :=
      (measurable_jointIntegrandC hX0 hXh measurable_fst.fst measurable_fst.snd
        measurable_snd).stronglyMeasurable
    have h1 : StronglyMeasurable
        (fun q : ℝ × ℝ => ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y q.1 q.2 t) := by
      have hp := hSM.integral_prod_right' (ν := volume)
      simpa using hp
    have h2 : StronglyMeasurable
        (fun q : ℝ × ℝ => (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
          jointIntegrand d t₀ X h c₀ y q.1 q.2 t) :=
      h1.const_smul (1 / (2 * Real.pi) : ℝ)
    have h3 := h2.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) η))
    have h4 : StronglyMeasurable (fun α : ℝ => ∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
        ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t) := by
      simp only [intervalIntegral.integral_of_le hη0]
      simpa using h3
    exact h4.norm.aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall ?_)
    intro α hα
    rw [hIoc] at hα
    obtain ⟨hα0, hαη⟩ := hα
    have hbnd : ∀ β ∈ Set.uIoc (0 : ℝ) η,
        ‖(1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖ ≤ C := by
      intro β hβ
      rw [hIoc] at hβ
      obtain ⟨hβ0, hβη⟩ := hβ
      refine le_trans (norm_inner_le hX hh hL0 hβ0.le (by linarith)
        (hsupF α ⟨hα0.le, hαη⟩ β ⟨hβ0.le, hβη⟩)) ?_
      have hbox := hC α ⟨by linarith, by linarith⟩ β ⟨hβ0.le, hβη⟩
      rw [Real.norm_eq_abs] at hbox
      exact le_trans (le_abs_self _) hbox
    have hgoal : ‖‖∫ β in (0 : ℝ)..η, (1 / (2 * Real.pi) : ℝ) •
          ∫ t : ℝ, jointIntegrand d t₀ X h c₀ y α β t‖‖ ≤ ‖C * |η - 0|‖ := by
      rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
      exact le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbnd) (le_abs_self _)
    exact hgoal

/-! ## §5 — the exit: `JointIntegrableAt`, discharged -/

/-- **THE GENERAL EXIT (`jointIntegrableAt_of_gates`).**  `RHSGrade.JointIntegrableAt` from
the five geometric gates — `1 ≤ X`, `0 < h`, `0 < L`, `0 ≤ η`, `0 < c₀ − 2η` — plus
`joint_cs_factoring`'s OWN `supF` binder at `supF α β = rhsFbound M L (β + 1/L)`.  All four
components are proved outright; nothing is carried beyond these. -/
theorem jointIntegrableAt_of_gates {d : ℕ → ℂ} {t₀' M k L c₀ y η h : ℝ}
    (hk : 1 ≤ k) (hh : 0 < h) (hL0 : 0 < L) (hη0 : 0 ≤ η) (hc2η : 0 < c₀ - 2 * η)
    (hsupF : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y d (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
        * largeSeries y d (((c₀ : ℂ) + ((t - t₀' : ℝ) : ℂ) * I) + (β : ℂ))‖
      ≤ rhsFbound M L (β + 1 / L)) :
    JointIntegrableAt d t₀' M k L c₀ y η h :=
  ⟨fun _ hα => intervalIntegrable_beta_leg hk hh hL0 hη0 hc2η hα,
   fun α hα => intervalIntegrable_beta_leg' hk hh hL0 hη0 hc2η hα (hsupF α hα),
   intervalIntegrable_alpha_leg hk hh hL0 hη0 hc2η,
   intervalIntegrable_alpha_leg' hk hh hL0 hη0 hc2η hsupF⟩

/-- **THE PIN EXIT (`jointIntegrableAt_discharged`).**  The four sockets at the corpus pin
(`L = log k`, `y = L⁴`, `η = 1/log y`, `c₀ = 1 + 1/L`, `e^{64} ≤ k`), with the `supF` binder
discharged by `RHSGrade.joint_supF_pin`.

The gates are exactly the data every consumer of the `hRHS` chain already holds: the prime
1-boundedness `hg`, the scale gate `e^{64} ≤ k`, the pin equations, `0 < h`, and the distance
floor `hMt` (which `CenterSupply.center_dist_floor` supplies from the row's minimality
`hmin`).  So `JointIntegrableAt` is no longer a socket. -/
theorem jointIntegrableAt_discharged {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀' M k L c₀ y η h : ℝ}
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : 0 < h)
    (hMt : ∀ t : ℝ, M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) k) :
    JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' M k L c₀ y η h := by
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hL64 : (64 : ℝ) ≤ L := by
    rw [hL, ← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < L := by linarith
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hlogy : Real.log y = 4 * Real.log L := by rw [hy, Real.log_pow]; norm_num
  have he2 : Real.exp 2 ≤ 64 := by
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hlogL2 : (2 : ℝ) ≤ Real.log L := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hlogy0 : (0 : ℝ) < Real.log y := by rw [hlogy]; linarith
  have hη0 : (0 : ℝ) ≤ η := by rw [hη]; positivity
  have hη8 : η ≤ 1 / 8 := by
    rw [hη, hlogy, div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 8)]
    linarith
  have hk1 : (1 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
  refine jointIntegrableAt_of_gates hk1 hh hL0 hη0 (by rw [hc₀]; linarith) ?_
  intro α hα β hβ t
  exact joint_supF_pin hg (le_trans (Real.exp_le_exp.mpr (by norm_num)) hk) hL hy hη hc₀
    hMt hα.1 hβ.1 hα.2 hβ.2 t

/-- **THE CONSUMERS' FACE (`jointIntegrableAt_pin`).**  `jointIntegrableAt_discharged` at the
exact binder shape carried by `GradeConst.hRHS_discharged_const`,
`FarStar.hRHS_socket_star`, `FarClose`, `SeamGate` and `SupClose`:
`k : ℕ`, `L = log k`, `c₀ = 1 + 1/L`, `y = L⁴`, `η = 1/log(L⁴)`, `h = k/√L`. -/
theorem jointIntegrableAt_pin {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {t₀' M : ℝ}
    {k : ℕ} (hk64 : Real.exp 64 ≤ (k : ℝ))
    (hMt : ∀ t : ℝ, M ≤ pretDistSq (ellLin (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)))
        (costwist (t - t₀')) (k : ℝ)) :
    JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-(t₀' : ℂ) * I)) t₀' M (k : ℝ)
      (Real.log (k : ℝ)) (1 + 1 / Real.log (k : ℝ)) (Real.log (k : ℝ) ^ 4)
      (1 / Real.log (Real.log (k : ℝ) ^ 4)) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk64
  have hL64 : (64 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk64
  have hh : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by
    have : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := Real.sqrt_pos.mpr (by linarith)
    positivity
  exact jointIntegrableAt_discharged hg hk64 rfl rfl rfl rfl hh hMt

end Salt.MR
