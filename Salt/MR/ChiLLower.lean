/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.ChiFloorLow
import Salt.SW.ZeroCount
import Salt.SW.ZetaLowerShallow
import Salt.SW.ThreeFourOne
import Salt.SW.Growth

/-!
# ROUTE A, the last stone — the `L`-lower bound near the 1-line (`ChiLLower`)

`Salt.MR.chi_floor_all_of_Llower` (`ChiFloorLow.lean`) closes ROUTE A for every character
modulo ONE named analytic hypothesis: a lower bound

  `−B ≤ log‖L(1 + 1/log X − it, χ)‖`

on the bounded band.  This file supplies that stone.

## What is landed here

* **Stone A (all χ, unconditional).**  `chi_Llower_trivial`:
  `B = log 32 + loglog X`, valid for EVERY `χ` and EVERY `t`.  The route is the
  monotone-modulus (horizontal FTC) argument of `ZetaPowLower`'s Block A, transplanted
  from `ζ` to `L(·,χ)`: `v ↦ log‖L(v+it,χ)‖ + log‖ζ(v)‖` has derivative
  `Re(L'/L)(v+it,χ) + ζ'/ζ(v) ≤ 0` by the Dirichlet-series comparison
  `|Re(L'/L)(v+it,χ)| ≤ −ζ'/ζ(v)`, so it is antitone on `(1,2]`; the `Re = 2` anchors
  (`Salt.SW.LFunction_center_lower`, `Salt.SW.zeta_norm_ge`, both `≥ 1/4`) and the pole
  bound `‖ζ(v)‖ ≤ 1 + 1/(v−1)` (`Salt.SW.zeta_real_upper`) then give
  `‖L(1+d+it,χ)‖ ≥ d/32`.  NO zero-free region, NO Siegel input.

* **Stone B (χ² ≠ 1, unconditional).**  `chi_Llower_341`: the SHARPER
  `B = 2log4 + (3/4)·log(1+log X) + (1/4)·log(15·q²·(1+log q))`, for every character
  with `χ² ≠ 1` — i.e. every NON-REAL character.  Route: the same antitone device applied
  to the 3-4-1 combination `Ψ(v) = 3log‖L(v,χ₀)‖ + 4log‖L(v+it,χ)‖ + log‖L(v+2it,χ²)‖`
  (derivative `≤ 0` is exactly `Salt.SW.three_four_one`), anchored at `v = 2` by three
  copies of `LFunction_center_lower`, with the two "cost" factors bounded ABOVE: the
  principal one by the pole bound, and `‖L(v+2it,χ²)‖` by the X-INDEPENDENT
  Pólya–Vinogradov growth bound `Salt.SW.LFunction_growth` (pushed from the primitive
  character to level `q` through `LFunction_changeLevel`, at the cost `2^{ω(q)} ≤ q`).

  The gain is real: the H2 floor `loglog X − B` becomes `(1/4)·loglog X − O(log q)`,
  a floor that still TENDS TO INFINITY, whereas Stone A's is a constant.

## The honest residual (the Siegel branch)

For a REAL character (`χ² = 1`, `χ ≠ 1`) the 3-4-1 device degrades exactly at `t = 0`,
which the H2 band contains: there `L(v+2it,χ²) = L(v,χ₀)` carries the ζ-POLE, and the two
cost factors together consume the whole `loglog X`.  This is not an artifact of the proof
— it IS the Siegel obstruction, in the same place `ChiFloorLow.lean`'s census (b) put it.
Removing it needs an ineffective input (`Salt.SW.siegel_L_one_exceptional`) TOGETHER with a
zero-free-region transport of it off the point `s = 1`, which is a strictly larger stone.
So for real characters this file lands only Stone A, and the honest statement of ROUTE A's
completion is the two-branch capstone below.

## The capstones

* `chi_floor_all_unconditional` — ROUTE A whole, for EVERY `χ` and EVERY `t`, with NO
  hypothesis at all: the H2 branch pays the constant `−CH2`.  The named hypothesis of
  `chi_floor_all_of_Llower` is DISCHARGED.  Be precise about what that buys: on the bounded
  band the floor is a CONSTANT, so there it is no stronger than the trivial nonnegativity of
  `𝔻²`; its value is that the interface is closed unconditionally and uniformly, and that the
  same stone upgrades the moment a better `B` is available.
* `chi_floor_all_nonreal` — for `χ² ≠ 1`: the same join with the H2 branch now
  `(1/4)loglog X − (1/4)log(15q²(1+log q)) − CH2`, i.e. a genuinely growing floor.  THIS is
  the informative half; with `chi_floor_all_principal` (χ₀, already landed) it leaves exactly
  the real nonprincipal characters without a growing bounded-band floor.
* `chi_floor_all_unconditional_twisted` / `chi_floor_all_nonreal_twisted` — the same two in
  the MRT shape `𝔻(λ, χ·n^{it}; X)²` that `M(λ; X, W) = inf_{χ,t} 𝔻(λ, χ n^{it}; X)²` ranges
  over.
-/

namespace Salt.MR

open Complex ArithmeticFunction DirichletCharacter Salt.SW
open scoped LSeries.notation

/-! ## 1. The two reusable analytic keystones -/

/-- **Keystone K (the log-modulus derivative), for an arbitrary holomorphic `F`.**
`d/dv log‖F(v+it)‖ = Re(F'/F)(v+it)` wherever `F` is differentiable and nonzero.  Built
component-wise through `Re`/`Im` (so no branch cut of the complex logarithm is touched);
this is `Salt.MR.hasDerivAt_log_norm_zeta` with `ζ` abstracted to `F`, which is what lets
the SAME lemma serve all four factors used below (`ζ`, `L(·,χ₀)`, `L(·,χ)`, `L(·,χ²)`). -/
lemma hasDerivAt_log_norm_horiz {F : ℂ → ℂ} {u : ℝ} {c : ℂ}
    (hd : DifferentiableAt ℂ F ((u : ℂ) + c))
    (hne : F ((u : ℂ) + c) ≠ 0) :
    HasDerivAt (fun v : ℝ => Real.log ‖F ((v : ℂ) + c)‖)
      ((logDeriv F ((u : ℂ) + c)).re) u := by
  set s : ℂ := (u : ℂ) + c with hs
  have he : HasDerivAt (fun v : ℝ => F ((v : ℂ) + c)) (deriv F s) u := by
    have h1 : HasDerivAt (fun w : ℂ => w + c) 1 (u : ℂ) := (hasDerivAt_id _).add_const _
    have h2 : HasDerivAt F (deriv F s) s := hd.hasDerivAt
    have hE : HasDerivAt (fun w : ℂ => F (w + c)) (deriv F s) (u : ℂ) := by
      have hcomp := h2.comp (u : ℂ) h1
      rw [mul_one] at hcomp
      exact hcomp
    exact hE.comp_ofReal
  have hre : HasDerivAt (fun v : ℝ => (F ((v : ℂ) + c)).re) ((deriv F s).re) u :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt u he
  have him : HasDerivAt (fun v : ℝ => (F ((v : ℂ) + c)).im) ((deriv F s).im) u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u he
  set g : ℝ → ℝ := fun v => (F ((v : ℂ) + c)).re * (F ((v : ℂ) + c)).re
    + (F ((v : ℂ) + c)).im * (F ((v : ℂ) + c)).im with hg
  have hgderiv : HasDerivAt g
      (((deriv F s).re * (F s).re + (F s).re * (deriv F s).re)
        + ((deriv F s).im * (F s).im + (F s).im * (deriv F s).im)) u :=
    (hre.mul hre).add (him.mul him)
  have hgu : g u = Complex.normSq (F s) := by rw [hg, Complex.normSq_apply]
  have hgne : g u ≠ 0 := by rw [hgu]; exact (Complex.normSq_pos.mpr hne).ne'
  have hlogg : HasDerivAt (fun v => Real.log (g v)) _ u := hgderiv.log hgne
  have hhalf := hlogg.const_mul (1 / 2 : ℝ)
  have hfun : (fun v : ℝ => Real.log ‖F ((v : ℂ) + c)‖)
      = fun v => (1 / 2 : ℝ) * Real.log (g v) := by
    funext v
    have hnn : (0 : ℝ) ≤ g v := by
      rw [hg]; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
    have hval : ‖F ((v : ℂ) + c)‖ = Real.sqrt (g v) := by
      rw [hg, Complex.norm_def, Complex.normSq_apply]
    rw [hval, Real.log_sqrt hnn]; ring
  rw [hfun]
  have hval : (logDeriv F s).re = 1 / 2 *
      (((deriv F s).re * (F s).re + (F s).re * (deriv F s).re
        + ((deriv F s).im * (F s).im + (F s).im * (deriv F s).im)) / g u) := by
    rw [logDeriv_apply, Complex.div_re, hgu, Complex.normSq_apply]; field_simp; ring
  rw [hval]; exact hhalf

/-- **Keystone D (the Dirichlet real-part comparison), χ-version.**  For real `u > 1`, any
`t` and any character `χ`,
`Re(L'/L)(u+it, χ) ≤ −ζ'/ζ(u)`.
On `Re s > 1` we have `−L'/L(s,χ) = ∑ Λ(n)χ(n)n^{−s}` (S0's twist identity through
`Salt.SW.neg_logDeriv_LSeries_eq`); its real part is at least `−∑ Λ(n)n^{−u}` because
`‖χ(n)‖ ≤ 1`, and the majorant is `−ζ'/ζ(u)`. -/
lemma LFunction_dirichlet_re_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u t : ℝ}
    (hu : 1 < u) :
    (logDeriv (LFunction χ) ((u : ℂ) + (t : ℂ) * I)).re
      ≤ -(logDeriv riemannZeta (u : ℂ)).re := by
  set s : ℂ := (u : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = u := by rw [hs]; simp
  have hsgt : (1 : ℝ) < s.re := by rw [hsre]; exact hu
  have hugt : (1 : ℝ) < ((u : ℂ)).re := by simpa using hu
  have hbridge : -logDeriv (LFunction χ) s = LSeries (↗χ * ↗vonMangoldt) s :=
    (neg_logDeriv_LSeries_eq χ hsgt).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist χ hsgt)
  have hzeta : (LSeries ↗vonMangoldt (u : ℂ)).re = -(logDeriv riemannZeta (u : ℂ)).re := by
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hugt, logDeriv_apply, neg_div, Complex.neg_re]
  have hSχ : Summable (LSeries.term (↗χ * ↗vonMangoldt) s) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsgt
  have hSΛ : Summable (LSeries.term ↗vonMangoldt (u : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hugt
  have hterm : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗vonMangoldt) s n‖
      ≤ ‖LSeries.term ↗vonMangoldt (u : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn, hsre,
        Complex.ofReal_re]
      have hnb : ‖χ ((n : ℕ) : ZMod q)‖ ≤ 1 := χ.norm_le_one _
      have hfac : ‖(↗χ * ↗vonMangoldt) n‖ = ‖χ ((n : ℕ) : ZMod q)‖ * ‖(↗vonMangoldt) n‖ := by
        rw [Pi.mul_apply, norm_mul]
      have hpos : (0 : ℝ) < (n : ℝ) ^ u := by
        have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        exact Real.rpow_pos_of_pos this u
      rw [hfac, div_le_div_iff_of_pos_right hpos]
      nlinarith [norm_nonneg ((↗vonMangoldt : ℕ → ℂ) n), norm_nonneg (χ ((n : ℕ) : ZMod q))]
  have hterm_re : ∀ n : ℕ, (LSeries.term ↗vonMangoldt (u : ℂ) n).re
      = ‖LSeries.term ↗vonMangoldt (u : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hn]
      have hcpow : ((n : ℂ)) ^ ((u : ℝ) : ℂ) = (((n : ℝ) ^ u : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity)]
      change (((vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ ((u : ℝ) : ℂ))).re
        = ‖((vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ ((u : ℝ) : ℂ))‖
      have hnn : (0 : ℝ) ≤ vonMangoldt n / (n : ℝ) ^ u :=
        div_nonneg vonMangoldt_nonneg (by positivity)
      rw [hcpow, ← Complex.ofReal_div, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hnn]
  have hLu_re : (LSeries ↗vonMangoldt (u : ℂ)).re
      = ∑' n, ‖LSeries.term ↗vonMangoldt (u : ℂ) n‖ := by
    rw [LSeries, Complex.re_tsum hSΛ]; exact tsum_congr hterm_re
  have hnormle : ‖LSeries (↗χ * ↗vonMangoldt) s‖ ≤ ∑' n, ‖LSeries.term ↗vonMangoldt (u : ℂ) n‖ := by
    rw [LSeries]
    calc ‖∑' n, LSeries.term (↗χ * ↗vonMangoldt) s n‖
        ≤ ∑' n, ‖LSeries.term (↗χ * ↗vonMangoldt) s n‖ := norm_tsum_le_tsum_norm hSχ.norm
      _ ≤ ∑' n, ‖LSeries.term ↗vonMangoldt (u : ℂ) n‖ := hSχ.norm.tsum_le_tsum hterm hSΛ.norm
  have hlogre : (logDeriv (LFunction χ) s).re = -(LSeries (↗χ * ↗vonMangoldt) s).re := by
    rw [← hbridge, Complex.neg_re, neg_neg]
  have hneg : -(LSeries (↗χ * ↗vonMangoldt) s).re ≤ ‖LSeries (↗χ * ↗vonMangoldt) s‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [hlogre, ← hzeta, hLu_re]
  linarith [hneg, hnormle]

/-! ## 2. Stone A — the unconditional horizontal lower bound -/

/-- Standing facts at any point of the half-plane `Re s > 1`: it is `≠ 1` (so `L(·,χ)` is
differentiable there even for `χ = χ₀`), and `L(s,χ) ≠ 0`. -/
private lemma pt_facts {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    (s ≠ 1) ∧ DifferentiableAt ℂ (LFunction χ) s ∧ LFunction χ s ≠ 0 := by
  have hne1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl 1 hs
  exact ⟨hne1, differentiableAt_LFunction χ _ (Or.inl hne1),
    χ.LFunction_ne_zero_of_one_le_re (Or.inr hne1) hs.le⟩

/-- **Stone A core — the horizontal monotone-modulus bound for `L(·,χ)`.**  For `1 < u ≤ 2`,
`log‖L(2+it,χ)‖ + log‖ζ(2)‖ − log‖ζ(u)‖ ≤ log‖L(u+it,χ)‖`.
The function `v ↦ log‖L(v+it,χ)‖ + log‖ζ(v)‖` has derivative `≤ 0` on `(1,2]` by keystone
D, hence is antitone; evaluate at the endpoints. -/
lemma LFunction_horiz_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u t : ℝ}
    (hu1 : 1 < u) (hu2 : u ≤ 2) :
    Real.log ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖ + Real.log ‖riemannZeta ((2 : ℝ) : ℂ)‖
      - Real.log ‖riemannZeta ((u : ℝ) : ℂ)‖
      ≤ Real.log ‖LFunction χ ((u : ℝ) + (t : ℂ) * I)‖ := by
  set φ : ℝ → ℝ := fun v => Real.log ‖LFunction χ ((v : ℂ) + (t : ℂ) * I)‖
    + Real.log ‖riemannZeta ((v : ℂ))‖ with hφdef
  have hφ : ∀ v : ℝ, 1 < v → HasDerivAt φ
      ((logDeriv (LFunction χ) ((v : ℂ) + (t : ℂ) * I)).re
        + (logDeriv riemannZeta ((v : ℂ))).re) v := by
    intro v hv
    obtain ⟨hne1, hdiff, hLne⟩ := pt_facts χ (s := (v : ℂ) + (t : ℂ) * I) (by simpa using hv)
    have hK1 := hasDerivAt_log_norm_horiz hdiff hLne
    have hvne1 : (v : ℂ) ≠ 1 := by
      intro h
      rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num] at h
      exact absurd (Complex.ofReal_injective h) (by linarith)
    have hvne0 : riemannZeta ((v : ℂ)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith)
    have hK2 : HasDerivAt (fun v : ℝ => Real.log ‖riemannZeta ((v : ℂ))‖)
        ((logDeriv riemannZeta ((v : ℂ))).re) v := by
      have h0 := hasDerivAt_log_norm_horiz (F := riemannZeta) (c := 0) (u := v)
        (by simpa using (differentiableAt_riemannZeta hvne1)) (by simpa using hvne0)
      simpa using h0
    exact hK1.add hK2
  have hcont : ContinuousOn φ (Set.Icc u 2) := fun v hv =>
    (hφ v (lt_of_lt_of_le hu1 hv.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Set.Icc u 2)) := by
    rw [interior_Icc]; intro v hv
    exact (hφ v (lt_trans hu1 hv.1)).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ v ∈ interior (Set.Icc u 2), deriv φ v ≤ 0 := by
    rw [interior_Icc]; intro v hv
    have hv1 : 1 < v := lt_trans hu1 hv.1
    rw [(hφ v hv1).deriv]
    linarith [LFunction_dirichlet_re_le χ (t := t) hv1]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc u 2) hcont hdiff hnonpos
  have hres := hanti (Set.left_mem_Icc.mpr hu2) (Set.right_mem_Icc.mpr hu2) hu2
  simp only [hφdef] at hres
  push_cast at hres ⊢
  linarith [hres]

/-- **Stone A — the unconditional near-1-line lower bound.**  For `0 < d ≤ 1` and every `t`,
`‖L((1+d)+it, χ)‖ ≥ d/32`.  Exponentiate `LFunction_horiz_lower` and feed the two `Re = 2`
anchors (`≥ 1/4` each) against the pole bound `‖ζ(1+d)‖ ≤ 1 + 1/d`.  This is the exact
`ζ`-side statement `Salt.MR.zeta_pow_lower_far`, now for every Dirichlet character and with
NO height restriction. -/
lemma LFunction_near_one_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {d t : ℝ}
    (hd0 : 0 < d) (hd1 : d ≤ 1) :
    (1 / 32 : ℝ) * d ≤ ‖LFunction χ (((1 + d : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  set u : ℝ := 1 + d with hu
  have hu1 : 1 < u := by rw [hu]; linarith
  have hu2 : u ≤ 2 := by rw [hu]; linarith
  have hb : (1 : ℝ) / 4 ≤ ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖ :=
    Salt.SW.LFunction_center_lower χ (by simp)
  have hc : (1 : ℝ) / 4 ≤ ‖riemannZeta ((2 : ℝ) : ℂ)‖ := Salt.SW.zeta_norm_ge (by simp)
  have hdub : ‖riemannZeta ((u : ℝ) : ℂ)‖ ≤ 1 + 1 / (u - 1) := Salt.SW.zeta_real_upper hu1
  have hbpos : 0 < ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖ := by linarith
  have hcpos : 0 < ‖riemannZeta ((2 : ℝ) : ℂ)‖ := by linarith
  have hdpos : 0 < ‖riemannZeta ((u : ℝ) : ℂ)‖ := by
    rw [norm_pos_iff]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith)
  have hapos : 0 < ‖LFunction χ ((u : ℝ) + (t : ℂ) * I)‖ := by
    rw [norm_pos_iff]
    exact (pt_facts χ (s := ((u : ℝ) : ℂ) + (t : ℂ) * I) (by simpa using hu1)).2.2
  have hlog := LFunction_horiz_lower χ (t := t) hu1 hu2
  have hlogc : Real.log ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖
      + Real.log ‖riemannZeta ((2 : ℝ) : ℂ)‖ - Real.log ‖riemannZeta ((u : ℝ) : ℂ)‖
      = Real.log (‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖ * ‖riemannZeta ((2 : ℝ) : ℂ)‖
        / ‖riemannZeta ((u : ℝ) : ℂ)‖) := by
    rw [Real.log_div (by positivity) (ne_of_gt hdpos),
      Real.log_mul (ne_of_gt hbpos) (ne_of_gt hcpos)]
  rw [hlogc] at hlog
  have hquot : ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖ * ‖riemannZeta ((2 : ℝ) : ℂ)‖
      / ‖riemannZeta ((u : ℝ) : ℂ)‖ ≤ ‖LFunction χ ((u : ℝ) + (t : ℂ) * I)‖ := by
    rwa [Real.log_le_log_iff (by positivity) hapos] at hlog
  have hd_ub : ‖riemannZeta ((u : ℝ) : ℂ)‖ ≤ 1 + 1 / d := by
    have heq : u - 1 = d := by rw [hu]; ring
    rwa [heq] at hdub
  have hquot2 : (1 / 32 : ℝ) * d ≤ ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖
      * ‖riemannZeta ((2 : ℝ) : ℂ)‖ / ‖riemannZeta ((u : ℝ) : ℂ)‖ := by
    rw [le_div_iff₀ hdpos]
    have hbc : (1 / 4 : ℝ) * (1 / 4) ≤ ‖LFunction χ ((2 : ℝ) + (t : ℂ) * I)‖
        * ‖riemannZeta ((2 : ℝ) : ℂ)‖ := mul_le_mul hb hc (by norm_num) (by linarith)
    have hprod : d * ‖riemannZeta ((u : ℝ) : ℂ)‖ ≤ d + 1 := by
      have h1 : d * ‖riemannZeta ((u : ℝ) : ℂ)‖ ≤ d * (1 + 1 / d) :=
        mul_le_mul_of_nonneg_left hd_ub hd0.le
      have h2 : d * (1 + 1 / d) = d + 1 := by field_simp
      linarith [h1, h2]
    nlinarith [hbc, hprod, hd1]
  linarith [hquot, hquot2]

/-- **Stone A, the exit — the unconditional `L`-lower at the bridge point.**  For `X ≥ e` and
EVERY real `t` and EVERY character `χ`,

  `−(log 32 + loglog X) ≤ log‖L(1 + 1/log X − it, χ)‖`.

This is EXACTLY the hypothesis shape of `chi_floor_all_of_Llower` (sign-pinned argument
`1 + 1/log X − it`), with `B = log 32 + loglog X`.  Unconditional, no zero-free region, no
Siegel input; the price is that `B` grows like `loglog X`, so the H2 floor it buys is only
a CONSTANT (see `chi_floor_all_unconditional`).  Stone B sharpens it for `χ² ≠ 1`. -/
theorem chi_Llower_trivial {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ)
    (hX : Real.exp 1 ≤ X) :
    -(Real.log 32 + Real.log (Real.log X))
      ≤ Real.log ‖DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  have h := LFunction_near_one_lower χ (t := -t) hd0 hd1
  have hpt : ((1 + 1 / Real.log X : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I := by push_cast; ring
  rw [hpt] at h
  have hpos : (0 : ℝ) < (1 / 32 : ℝ) * (1 / Real.log X) := by positivity
  have hmono := Real.log_le_log hpos h
  have heq : Real.log ((1 / 32 : ℝ) * (1 / Real.log X))
      = -(Real.log 32 + Real.log (Real.log X)) := by
    rw [show (1 / 32 : ℝ) * (1 / Real.log X) = ((32 : ℝ) * Real.log X)⁻¹ by
      rw [mul_inv]; ring, Real.log_inv,
      Real.log_mul (by norm_num) (ne_of_gt hlogXpos)]
  rw [heq] at hmono
  exact hmono

/-! ## 3. Stone B — the 3-4-1 lower bound for non-real characters -/

/-- **The 3-4-1 inequality in `LFunction` log-derivative form.**  For real `σ > 1` and any `t`,
`3·Re(L'/L)(σ,χ₀) + 4·Re(L'/L)(σ+it,χ) + Re(L'/L)(σ+2it,χ²) ≤ 0`.
This is `Salt.SW.three_four_one` (the Dirichlet-series positivity `3 + 4cos θ + cos 2θ ≥ 0`)
transported onto the `LFunction` objects through the S0/S1 bridge
`Salt.SW.neg_logDeriv_LSeries_eq`. -/
lemma three_four_one_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) (t : ℝ) :
    3 * (logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℂ))).re
      + 4 * (logDeriv (LFunction χ) ((σ : ℂ) + (t : ℂ) * I)).re
      + (logDeriv (LFunction (χ ^ 2)) ((σ : ℂ) + 2 * (t : ℂ) * I)).re ≤ 0 := by
  have h0 : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have h1 : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * I).re := by
    have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
    rw [hre]; exact hσ
  have h2 : (1 : ℝ) < ((σ : ℂ) + 2 * (t : ℂ) * I).re := by
    have hre : ((σ : ℂ) + 2 * (t : ℂ) * I).re = σ := by simp
    rw [hre]; exact hσ
  have b0 : -logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℂ))
      = LSeries (↗(1 : DirichletCharacter ℂ q) * ↗vonMangoldt) ((σ : ℂ)) :=
    (neg_logDeriv_LSeries_eq _ h0).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist _ h0)
  have b1 : -logDeriv (LFunction χ) ((σ : ℂ) + (t : ℂ) * I)
      = LSeries (↗χ * ↗vonMangoldt) ((σ : ℂ) + (t : ℂ) * I) :=
    (neg_logDeriv_LSeries_eq _ h1).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist _ h1)
  have b2 : -logDeriv (LFunction (χ ^ 2)) ((σ : ℂ) + 2 * (t : ℂ) * I)
      = LSeries (↗(χ ^ 2) * ↗vonMangoldt) ((σ : ℂ) + 2 * (t : ℂ) * I) :=
    (neg_logDeriv_LSeries_eq _ h2).symm.trans (neg_logDeriv_LSeries_eq_LSeries_twist _ h2)
  have key := three_four_one χ hσ t
  rw [← b0, ← b1, ← b2, Complex.neg_re, Complex.neg_re, Complex.neg_re] at key
  linarith

/-- **Stone B core — the 3-4-1 monotone-modulus bound.**  For `1 < u ≤ 2` the combination
`Ψ(v) = 3log‖L(v,χ₀)‖ + 4log‖L(v+it,χ)‖ + log‖L(v+2it,χ²)‖`
is antitone on `[u,2]` — its derivative is exactly the 3-4-1 expression — so `Ψ(2) ≤ Ψ(u)`. -/
lemma LFunction_341_horiz {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u t : ℝ}
    (hu1 : 1 < u) (hu2 : u ≤ 2) :
    3 * Real.log ‖LFunction (1 : DirichletCharacter ℂ q) (((2 : ℝ) : ℂ))‖
        + 4 * Real.log ‖LFunction χ (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖
        + Real.log ‖LFunction (χ ^ 2) (((2 : ℝ) : ℂ) + 2 * (t : ℂ) * I)‖
      ≤ 3 * Real.log ‖LFunction (1 : DirichletCharacter ℂ q) (((u : ℝ) : ℂ))‖
        + 4 * Real.log ‖LFunction χ (((u : ℝ) : ℂ) + (t : ℂ) * I)‖
        + Real.log ‖LFunction (χ ^ 2) (((u : ℝ) : ℂ) + 2 * (t : ℂ) * I)‖ := by
  set φ : ℝ → ℝ := fun v =>
      3 * Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((v : ℂ))‖
        + 4 * Real.log ‖LFunction χ ((v : ℂ) + (t : ℂ) * I)‖
        + Real.log ‖LFunction (χ ^ 2) ((v : ℂ) + 2 * (t : ℂ) * I)‖ with hφdef
  have hφ : ∀ v : ℝ, 1 < v → HasDerivAt φ
      (3 * (logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((v : ℂ))).re
        + 4 * (logDeriv (LFunction χ) ((v : ℂ) + (t : ℂ) * I)).re
        + (logDeriv (LFunction (χ ^ 2)) ((v : ℂ) + 2 * (t : ℂ) * I)).re) v := by
    intro v hv
    obtain ⟨-, hd0, hn0⟩ :=
      pt_facts (1 : DirichletCharacter ℂ q) (s := ((v : ℂ))) (by simpa using hv)
    obtain ⟨-, hd1, hn1⟩ := pt_facts χ (s := ((v : ℂ) + (t : ℂ) * I)) (by simpa using hv)
    obtain ⟨-, hd2, hn2⟩ := pt_facts (χ ^ 2) (s := ((v : ℂ) + 2 * (t : ℂ) * I)) (by simpa using hv)
    have k0 : HasDerivAt
        (fun v : ℝ => Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((v : ℂ))‖)
        ((logDeriv (LFunction (1 : DirichletCharacter ℂ q)) ((v : ℂ))).re) v := by
      have h := hasDerivAt_log_norm_horiz (F := LFunction (1 : DirichletCharacter ℂ q)) (c := 0)
        (u := v) (by simpa using hd0) (by simpa using hn0)
      simpa using h
    have k1 := hasDerivAt_log_norm_horiz hd1 hn1
    have k2 := hasDerivAt_log_norm_horiz hd2 hn2
    exact ((k0.const_mul 3).add (k1.const_mul 4)).add k2
  have hcont : ContinuousOn φ (Set.Icc u 2) := fun v hv =>
    (hφ v (lt_of_lt_of_le hu1 hv.1)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Set.Icc u 2)) := by
    rw [interior_Icc]; intro v hv
    exact (hφ v (lt_trans hu1 hv.1)).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ v ∈ interior (Set.Icc u 2), deriv φ v ≤ 0 := by
    rw [interior_Icc]; intro v hv
    have hv1 : 1 < v := lt_trans hu1 hv.1
    rw [(hφ v hv1).deriv]
    exact three_four_one_LFunction χ hv1 t
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc u 2) hcont hdiff hnonpos
  have hres := hanti (Set.left_mem_Icc.mpr hu2) (Set.right_mem_Icc.mpr hu2) hu2
  simp only [hφdef] at hres
  push_cast at hres ⊢
  linarith [hres]

/-- **The principal-character upper bound at a real point.**  `‖L(u,χ₀)‖ ≤ 1 + 1/(u−1)` for
real `u > 1`: mathlib's `LFunctionTrivChar_eq_mul_riemannZeta` factors `L(·,χ₀)` as
`∏_{p|q}(1−p^{−u})·ζ(u)`, the product has every factor in `(0,1]`, and `Salt.SW.zeta_real_upper`
bounds `ζ`. -/
lemma LFunction_one_real_upper {q : ℕ} [NeZero q] {u : ℝ} (hu : 1 < u) :
    ‖LFunction (1 : DirichletCharacter ℂ q) ((u : ℝ) : ℂ)‖ ≤ 1 + 1 / (u - 1) := by
  have hne1 : ((u : ℝ) : ℂ) ≠ 1 := by
    intro h
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num] at h
    exact absurd (Complex.ofReal_injective h) (by linarith)
  have hfac : LFunction (1 : DirichletCharacter ℂ q) ((u : ℝ) : ℂ)
      = (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-((u : ℝ) : ℂ)))) * riemannZeta ((u : ℝ) : ℂ) :=
    LFunctionTrivChar_eq_mul_riemannZeta hne1
  rw [hfac, norm_mul]
  have hprod : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-((u : ℝ) : ℂ)))‖ ≤ 1 := by
    rw [norm_prod]
    refine Finset.prod_le_one (fun p _ => norm_nonneg _) (fun p hp => ?_)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
    have hval : (p : ℂ) ^ (-((u : ℝ) : ℂ)) = (((p : ℝ) ^ (-u) : ℝ) : ℂ) := by
      rw [show (-((u : ℝ) : ℂ)) = (((-u : ℝ)) : ℂ) by push_cast; ring,
        ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (by positivity)]
    have hle1 : ((p : ℝ)) ^ (-u) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    have hpos : (0 : ℝ) < ((p : ℝ)) ^ (-u) := Real.rpow_pos_of_pos (by linarith) _
    rw [hval, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  have hz : ‖riemannZeta ((u : ℝ) : ℂ)‖ ≤ 1 + 1 / (u - 1) := Salt.SW.zeta_real_upper hu
  calc ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-((u : ℝ) : ℂ)))‖ * ‖riemannZeta ((u : ℝ) : ℂ)‖
      ≤ 1 * ‖riemannZeta ((u : ℝ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ‖riemannZeta ((u : ℝ) : ℂ)‖ := one_mul _
    _ ≤ 1 + 1 / (u - 1) := hz

/-- **The level-`q` growth bound.**  For a NONPRINCIPAL character `ψ mod q` and `1/2 ≤ Re s ≤ 4`,
`‖L(s,ψ)‖ ≤ q·3(1+‖s‖)·√q·(1 + log q)` — an `X`-INDEPENDENT polynomial bound.
`Salt.SW.LFunction_growth` (Pólya–Vinogradov + Abel summation) gives this for the PRIMITIVE
character inducing `ψ`; `LFunction_changeLevel` re-attaches the finitely many Euler factors
at the primes dividing `q`, each of norm `≤ 2`, and `2^{ω(q)} ≤ ∏_{p|q} p ≤ q`. -/
lemma LFunction_norm_le_level {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {s : ℂ} (hs1 : (1 : ℝ) / 2 ≤ s.re) (hs2 : s.re ≤ 4) :
    ‖LFunction ψ s‖ ≤ (q : ℝ) * (3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q)) := by
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  haveI : NeZero ψ.conductor := ⟨ψ.conductor_ne_zero⟩
  have hf1 : ψ.conductor ≠ 1 := fun h => hψ (eq_one_iff_conductor_eq_one.mpr h)
  have hf0 : ψ.conductor ≠ 0 := ψ.conductor_ne_zero
  have hf2 : 2 ≤ ψ.conductor := by omega
  have hprim : ψ.primitiveCharacter.IsPrimitive := ψ.primitiveCharacter_isPrimitive
  have hprim' : ψ.primitiveCharacter.conductor = ψ.conductor := hprim
  have hpne : ψ.primitiveCharacter ≠ 1 := by
    intro h
    exact hf1 (by rw [← hprim']; exact eq_one_iff_conductor_eq_one.mp h)
  have hLfac : LFunction ψ s
      = LFunction ψ.primitiveCharacter s
        * ∏ p ∈ q.primeFactors, (1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
    conv_lhs => rw [← ψ.changeLevel_primitiveCharacter]
    exact LFunction_changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter (Or.inl hpne)
  have hfqR : (ψ.conductor : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hqpos ψ.conductor_dvd_level
  have hf0R : (0 : ℝ) < (ψ.conductor : ℝ) := by
    have : 0 < ψ.conductor := Nat.pos_of_ne_zero hf0
    exact_mod_cast this
  -- the primitive-level growth bound, weakened from the conductor to `q`
  have hA : ‖LFunction ψ.primitiveCharacter s‖
      ≤ 3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q) := by
    refine le_trans (LFunction_growth ψ.primitiveCharacter hprim hf2 hs1 hs2) ?_
    have hsq : Real.sqrt (ψ.conductor : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hfqR
    have hlg : Real.log (ψ.conductor : ℝ) ≤ Real.log (q : ℝ) := Real.log_le_log hf0R hfqR
    have hlgf : (0 : ℝ) ≤ Real.log (ψ.conductor : ℝ) := by
      refine Real.log_nonneg ?_
      have : (2 : ℕ) ≤ ψ.conductor := hf2
      have : (2 : ℝ) ≤ (ψ.conductor : ℝ) := by exact_mod_cast this
      linarith
    have hcoef : (0 : ℝ) ≤ 3 * (1 + ‖s‖) := by positivity
    have h1 : 3 * (1 + ‖s‖) * Real.sqrt (ψ.conductor : ℝ)
        ≤ 3 * (1 + ‖s‖) * Real.sqrt (q : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsq hcoef
    nlinarith [Real.sqrt_nonneg ((ψ.conductor : ℝ)), Real.sqrt_nonneg ((q : ℝ)), hlgf, hlg, h1,
      hcoef, mul_nonneg hcoef (Real.sqrt_nonneg ((q : ℝ)))]
  -- the Euler-factor product costs at most `q`
  have hprodle : ‖∏ p ∈ q.primeFactors,
      (1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s))‖ ≤ (q : ℝ) := by
    rw [norm_prod]
    have hstep : ∀ p ∈ q.primeFactors,
        ‖1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hcp : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [norm_natCast_cpow_of_pos hpp.pos]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpp.one_le)
          (by rw [Complex.neg_re]; linarith)
      have hchi : ‖ψ.primitiveCharacter ((p : ℕ) : ZMod ψ.conductor)‖ ≤ 1 :=
        ψ.primitiveCharacter.norm_le_one _
      have hmul : ‖ψ.primitiveCharacter ((p : ℕ) : ZMod ψ.conductor) * (p : ℂ) ^ (-s)‖ ≤ 1 := by
        rw [norm_mul]
        nlinarith [norm_nonneg ((p : ℂ) ^ (-s)),
          norm_nonneg (ψ.primitiveCharacter ((p : ℕ) : ZMod ψ.conductor))]
      calc ‖1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s)‖
          ≤ ‖(1 : ℂ)‖ + ‖ψ.primitiveCharacter ((p : ℕ) : ZMod ψ.conductor) * (p : ℂ) ^ (-s)‖ :=
            norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one]; linarith
        _ ≤ (p : ℝ) := by linarith
    calc ∏ p ∈ q.primeFactors, ‖1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s)‖
        ≤ ∏ p ∈ q.primeFactors, (p : ℝ) := Finset.prod_le_prod (fun p _ => norm_nonneg _) hstep
      _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (q : ℝ) := by exact_mod_cast Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd q)
  rw [hLfac, norm_mul]
  have hBnn : (0 : ℝ) ≤ 3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q) := by positivity
  calc ‖LFunction ψ.primitiveCharacter s‖
        * ‖∏ p ∈ q.primeFactors, (1 - ψ.primitiveCharacter p * (p : ℂ) ^ (-s))‖
      ≤ (3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q)) * (q : ℝ) :=
        mul_le_mul hA hprodle (norm_nonneg _) hBnn
    _ = (q : ℝ) * (3 * (1 + ‖s‖) * Real.sqrt q * (1 + Real.log q)) := by ring

/-- **CAPSTONE A — ROUTE A, WHOLE AND UNCONDITIONAL, FOR EVERY CHARACTER.**  There are
constants `CH1`, `CH2` such that for every `q ≠ 0`, every `χ mod q`, every `X ≥ e` and EVERY
real `t`,

  `min( −CH2,`
  `     [loglog X − (3/4)loglog(|kt|+3) − 5·logloglog(|kt|+16) − CH1 − ∑_{p|q,p≤X}1/p]/k² )`
  `  ≤ 𝔻(λ·χ̄, n^{it}; X)²`     (`k = 2·orderOf χ`).

The named hypothesis of `chi_floor_all_of_Llower` is DISCHARGED by `chi_Llower_trivial`;
nothing is assumed beyond `X ≥ e`.  The H2 branch is a CONSTANT because Stone A's `B`
absorbs the whole `loglog X` — so on the bounded band this statement is not stronger than
`0 ≤ 𝔻²`; what it settles is the INTERFACE (ROUTE A needs no hypothesis at all).
`chi_floor_all_nonreal` replaces the constant by a growing floor whenever `χ² ≠ 1`. -/
theorem chi_floor_all_unconditional :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ),
      Real.exp 1 ≤ X →
        min (-CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_of_Llower
  refine ⟨CH1, Real.log 32 + CH2, ?_⟩
  intro q _ χ X t hX
  have h := hC q χ X t (Real.log 32 + Real.log (Real.log X)) hX
    (fun _ => chi_Llower_trivial χ X t hX)
  have heq : Real.log (Real.log X) - (Real.log 32 + Real.log (Real.log X)) - CH2
      = -(Real.log 32 + CH2) := by ring
  rw [← heq]
  exact h

/-! ## 4. Stone B, the exit, and the non-real capstone -/

/-- **Stone B, the exit — the SHARP `L`-lower at the bridge point, for `χ² ≠ 1`.**  For
`X ≥ e`, `|t| ≤ 1` and any character with `χ² ≠ 1` (i.e. any NON-REAL character),

  `−[2log4 + (3/4)·log(1+log X) + (1/4)·log(15q²(1+log q))] ≤ log‖L(1 + 1/log X − it, χ)‖`.

The `loglog X` cost is now only `3/4` of what Stone A pays, because the 3-4-1 device makes
the ζ-pole enter with exponent `3/4` instead of `1`, and the remaining factor `L(·,χ²)` is
bounded `X`-independently.  Consequently the H2 floor `loglog X − B` GROWS, like
`(1/4)·loglog X − (1/4)log(15q²(1+log q)) − 2log4`. -/
theorem chi_Llower_341 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 ≠ 1)
    (X t : ℝ) (hX : Real.exp 1 ≤ X) (ht : |t| ≤ 1) :
    -(2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
        + (1 / 4) * Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q)))
      ≤ Real.log ‖DirichletCharacter.LFunction χ
          (((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I)‖ := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogXpos : (0 : ℝ) < Real.log X := by linarith
  have hd0 : (0 : ℝ) < 1 / Real.log X := one_div_pos.mpr hlogXpos
  have hd1 : 1 / Real.log X ≤ 1 := by rw [div_le_one hlogXpos]; linarith
  have hu1 : (1 : ℝ) < 1 + 1 / Real.log X := by linarith
  have hu2 : 1 + 1 / Real.log X ≤ 2 := by linarith
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlogq : (0 : ℝ) ≤ Real.log q := Real.log_nonneg hq1R
  have hlog4 : Real.log (1 / 4 : ℝ) = -Real.log 4 := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have h341 := LFunction_341_horiz χ (u := 1 + 1 / Real.log X) (t := -t) hu1 hu2
  have hpt : ((1 + 1 / Real.log X : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I
      = ((1 + 1 / Real.log X : ℝ) : ℂ) - (t : ℝ) * Complex.I := by push_cast; ring
  rw [hpt] at h341
  -- the three `Re = 2` anchors
  have a0 : -Real.log 4 ≤ Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((2 : ℝ) : ℂ)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by norm_num))
  have a1 : -Real.log 4
      ≤ Real.log ‖LFunction χ (((2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by simp))
  have a2 : -Real.log 4
      ≤ Real.log ‖LFunction (χ ^ 2) (((2 : ℝ) : ℂ) + 2 * ((-t : ℝ) : ℂ) * I)‖ := by
    rw [← hlog4]
    exact Real.log_le_log (by norm_num) (Salt.SW.LFunction_center_lower _ (by simp))
  -- the principal-character cost at `v = u`
  have hb0 : Real.log ‖LFunction (1 : DirichletCharacter ℂ q) ((1 + 1 / Real.log X : ℝ) : ℂ)‖
      ≤ Real.log (1 + Real.log X) := by
    have hpos : (0 : ℝ) < ‖LFunction (1 : DirichletCharacter ℂ q)
        (((1 + 1 / Real.log X : ℝ) : ℂ))‖ := by
      rw [norm_pos_iff]
      exact (pt_facts (1 : DirichletCharacter ℂ q)
        (s := (((1 + 1 / Real.log X : ℝ) : ℂ))) (by simpa using hu1)).2.2
    refine Real.log_le_log hpos ?_
    have hbnd := LFunction_one_real_upper (q := q) (u := 1 + 1 / Real.log X) hu1
    have heq : (1 : ℝ) + 1 / ((1 + 1 / Real.log X) - 1) = 1 + Real.log X := by
      rw [show (1 + 1 / Real.log X) - 1 = 1 / Real.log X by ring, one_div_one_div]
    linarith [hbnd, heq.symm.le, heq.le]
  -- the `χ²` cost at `v = u`, bounded X-INDEPENDENTLY
  have hs2re : ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I).re
      = 1 + 1 / Real.log X := by simp
  have hnorms : ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I‖ ≤ 4 := by
    have h1 : ‖(((1 + 1 / Real.log X : ℝ) : ℂ))‖ = |1 + 1 / Real.log X| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(2 : ℂ) * ((-t : ℝ) : ℂ) * I‖ = 2 * |t| := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_neg]
      norm_num
    calc ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I‖
        ≤ ‖(((1 + 1 / Real.log X : ℝ) : ℂ))‖ + ‖(2 : ℂ) * ((-t : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |1 + 1 / Real.log X| + 2 * |t| := by rw [h1, h2]
      _ ≤ 2 + 2 * 1 := by
          have habs : |1 + 1 / Real.log X| = 1 + 1 / Real.log X :=
            abs_of_nonneg (by linarith)
          rw [habs]; linarith
      _ ≤ 4 := by norm_num
  have hb2 : Real.log ‖LFunction (χ ^ 2)
        ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I)‖
      ≤ Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q)) := by
    have hpos : (0 : ℝ) < ‖LFunction (χ ^ 2)
        ((((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I)‖ := by
      rw [norm_pos_iff]
      exact (pt_facts (χ ^ 2) (by rw [hs2re]; linarith)).2.2
    refine Real.log_le_log hpos ?_
    have hbnd := LFunction_norm_le_level (χ ^ 2) hχ2
      (s := (((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I)
      (by rw [hs2re]; linarith) (by rw [hs2re]; linarith)
    refine le_trans hbnd ?_
    have hsq : Real.sqrt (q : ℝ) ≤ (q : ℝ) := by
      nlinarith [Real.sq_sqrt (le_trans zero_le_one hq1R), Real.sqrt_nonneg ((q : ℝ))]
    have ha : 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I‖)
        * Real.sqrt q ≤ 15 * (q : ℝ) := by
      have h15 : 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I‖) ≤ 15 := by
        linarith [hnorms]
      nlinarith [Real.sqrt_nonneg ((q : ℝ)), h15, hsq]
    have e1 : 3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I‖)
          * Real.sqrt q * (1 + Real.log q) ≤ 15 * (q : ℝ) * (1 + Real.log q) := by
      nlinarith [ha, hlogq]
    calc (q : ℝ) * (3 * (1 + ‖(((1 + 1 / Real.log X : ℝ) : ℂ)) + 2 * ((-t : ℝ) : ℂ) * I‖)
          * Real.sqrt q * (1 + Real.log q))
        ≤ (q : ℝ) * (15 * (q : ℝ) * (1 + Real.log q)) :=
          mul_le_mul_of_nonneg_left e1 (by linarith)
      _ = 15 * (q : ℝ) ^ 2 * (1 + Real.log q) := by ring
  linarith [h341, a0, a1, a2, hb0, hb2]

/-- **CAPSTONE B — ROUTE A for every NON-REAL character, unconditionally, with a GROWING
H2 floor.**  For every `q ≠ 0`, every `χ mod q` with `χ² ≠ 1`, every `X ≥ e` and EVERY real
`t`,

  `min( loglog X − (3/4)log(1+log X) − (1/4)log(15q²(1+log q)) − CH2,`
  `     [loglog X − (3/4)loglog(|kt|+3) − 5·logloglog(|kt|+16) − CH1 − ∑_{p|q,p≤X}1/p]/k² )`
  `  ≤ 𝔻(λ·χ̄, n^{it}; X)²`.

The H2 branch is `(1/4)loglog X − O(log q)` — unbounded, unlike `chi_floor_all_unconditional`'s
constant.  Together with `chi_floor_all_principal` (`χ = χ₀`, `ChiFloorLow.lean`) this leaves
exactly ONE case with a merely-constant floor: the REAL nonprincipal characters, which is
precisely Siegel territory. -/
theorem chi_floor_all_nonreal :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ),
      χ ^ 2 ≠ 1 → Real.exp 1 ≤ X →
        min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
              - (1 / 4) * Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q)) - CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_of_Llower
  refine ⟨CH1, 2 * Real.log 4 + CH2, ?_⟩
  intro q _ χ X t hχ2 hX
  have hB := hC q χ X t (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
      + (1 / 4) * Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q))) hX (fun hkt => ?_)
  · have heq : Real.log (Real.log X)
        - (2 * Real.log 4 + (3 / 4) * Real.log (1 + Real.log X)
            + (1 / 4) * Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q))) - CH2
        = Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
            - (1 / 4) * Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q))
            - (2 * Real.log 4 + CH2) := by ring
    rw [← heq]
    exact hB
  · have hord : 0 < orderOf χ := MulChar.orderOf_pos χ
    have hk2 : (2 : ℝ) ≤ ((2 * orderOf χ : ℕ) : ℝ) := by
      have h2 : 2 ≤ 2 * orderOf χ := by omega
      exact_mod_cast h2
    have ht1 : |t| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ((2 * orderOf χ : ℕ) : ℝ))] at hkt
      nlinarith [abs_nonneg t]
    exact chi_Llower_341 χ hχ2 X t hX ht1

/-- **CAPSTONE A, MRT shape.**  `chi_floor_all_unconditional` moved to the `g`-side twist
`𝔻(λ, χ·n^{it}; X)²` — the object the quality infimum `M(λ; X, W)` ranges over. -/
theorem chi_floor_all_unconditional_twisted :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ),
      Real.exp 1 ≤ X →
        min (-CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_unconditional
  refine ⟨CH1, CH2, ?_⟩
  intro q _ χ X t hX
  rw [pretDistSq_lam_chi_twist χ t X]
  exact hC q χ X t hX

/-- **CAPSTONE B, MRT shape.**  `chi_floor_all_nonreal` on the `g`-side twist — the growing
bounded-band floor in the form `M(λ; X, W)` consumes. -/
theorem chi_floor_all_nonreal_twisted :
    ∃ CH1 CH2 : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ),
      χ ^ 2 ≠ 1 → Real.exp 1 ≤ X →
        min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
              - (1 / 4) * Real.log (15 * (q : ℝ) ^ 2 * (1 + Real.log q)) - CH2)
            ((Real.log (Real.log X)
                - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
          ≤ pretDistSq lam (fun n => χ (n : ZMod q) * costwist t n) X := by
  obtain ⟨CH1, CH2, hC⟩ := chi_floor_all_nonreal
  refine ⟨CH1, CH2, ?_⟩
  intro q _ χ X t hχ2 hX
  rw [pretDistSq_lam_chi_twist χ t X]
  exact hC q χ X t hχ2 hX

end Salt.MR
