/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.HalaszCore

/-!
# S8/`thm_A2′` ladder, node A2-0 — the opening stone (`ThmA2Open`)

The S8 rescope freeze (`docs/exploration/s8-freeze-0727.md` + amendments A/B) opens
the `thm_A2′` ladder with three check-independent pieces — needed on every branch and
under every outcome of the two kill-checks.  This file holds all three.

## §1 — Lemma A.8 (MRT p. 27), `exp_add_exp_sub_two_cos_le`

`eᵅ + e⁻ᵅ − 2 cos θ ≤ e^{√(α²+θ²)}`.

**CENSUS FINDING (A2-0, 2026-07-27): this stone was already landed.**  The freeze's
A.8 row is stale — the inequality is `HalaszCore.halasz_cosh_ineq`, kernel-checked
since 2026-07-19 (S8-E5/K1, one attempt, by exactly the MVT route the A2-0 brief
re-derived: `x ↦ e^{√x}` has derivative `≥ e/2` on `(0,∞)`, so
`e^{√(b²+t²)} ≥ e^b + (e/2)t²`, then `cos θ ≥ 1 − θ²/2`; the `α < 0` side by the
evenness of `eᵅ + e⁻ᵅ`, the `θ = 0` MVT degeneracy absorbed because the corpus proof
runs the monotonicity of `H(x) = e^{√x} − (e/2)x` on `[0,∞)` rather than an MVT on a
possibly-degenerate interval).  The complex face `‖e^{z/2} − e^{−z/2}‖² = eᵅ + e⁻ᵅ −
2cos θ` is landed too (`JFactor.norm_exp_half_sub_sq`/`norm_exp_half_sub_le`).  We
therefore publish the A2-ladder *name* as a one-line re-export rather than duplicating
a proof: nothing here is a second copy of the analysis.

## §2 — the S1b join (S8-SRC demand D-2), `parseval_a3_join`

The arithmetic that glues the single-`h` Parseval exit (A2-1, the `Lemma14` shape:
a `(log X)^{−2/15}` head, a mid-band integral, and the weighted max-term `Msup`) to the
Prop A.3 shape (a `(T/(X/Q₁) + 1)` prefactor times a grade `G`).  Stated ABSTRACTLY
over the two bound-shapes: no Dirichlet series, no contour, no measure theory — the
analytic ends plug in later.  The point of the node is that the three
`[P₁,Q₁] ⊆ [1,h]` consumptions become EXPLICIT hypotheses:

* `hQ1h : Q₁ ≤ h` at the mid band — `(X/h)/(X/Q₁) + 1 = Q₁/h + 1 ≤ 2`;
* `hQ1h` again at the max-term, together with `hT : X/h ≤ T` —
  `(X/h)/T · (2T/(X/Q₁) + 1) = 2Q₁/h + (X/h)/T ≤ 3`;
* `hQ1h` a third time through the log-monotone `(log Q₁)^{1/3} ≤ (log h)^{1/3}`
  (`a3_logQ_third_mono`, and its `/P₁^{1/6−η}` face `a3_logQ_term_mono`), which is how
  the A.2 interface's second term is allowed to read in `h` rather than `Q₁`.

The `(log X)^{−2/15}` head lands inside the A.2 interface's THIRD term at the landed
`(log X)^{−1/500}` grade (`−2/15 ≤ −1/500`, so the head is the smaller of the two once
`log X ≥ 1`) — the exponent ruling of the freeze, not a numerology choice.

## §3 — the sup→inf pin (S8-SRC source defect D2), `ball_inf_floor_of_mem_far`

MRT p. 23 prints a `sup` where the argument needs an `inf` (a supremum lower bound is
vacuous; [10, Cor 1] wants the minimum over the ball, and A.4(ii) proves the inf form).
The repair is a reverse-triangle one-liner: if the ball centre `t` is at distance
`> 2r` from `t₁`, then EVERY point of the closed `r`-ball around `t` is at distance
`> r` from `t₁`, so a far-field floor transfers to a floor on the infimum over the
ball.  Stated in the corpus's `setOf`/`sInf` idiom (the `M_range` shape) so it seeds
A2-3b's geometry as well.

Naming note carried from the freeze: the corpus's `TLeg*` names are MR's `𝒯₁` ladder,
NOT MRT's `𝒯₁` — the two share a glyph and are different objects.  Nothing in this
file touches either.
-/

namespace Salt.MR

/-! ## §1 — Lemma A.8, the A2-ladder face -/

/-- **Lemma A.8 (MRT p. 27), the A2-ladder name.**  For real `α, θ`,
`eᵅ + e⁻ᵅ − 2 cos θ ≤ e^{√(α²+θ²)}`.

This is `HalaszCore.halasz_cosh_ineq` verbatim — LANDED 2026-07-19 by the MVT route.
The A2-0 row of the S8 freeze asked for a fresh proof; the census caught the duplicate
before any bytes were spent (see the file docstring).  The name exists so the
`thm_A2′` assembly can cite an A2-ladder identifier without importing the Halász core's
naming, and so the ladder's audit finds a row here. -/
theorem exp_add_exp_sub_two_cos_le (α θ : ℝ) :
    Real.exp α + Real.exp (-α) - 2 * Real.cos θ
      ≤ Real.exp (Real.sqrt (α ^ 2 + θ ^ 2)) :=
  halasz_cosh_ineq α θ

/-! ## §2 — the S1b join (D-2)

Four arithmetic stones and the join.  Every quantity is a real; every constant is
explicit; the `[P₁,Q₁] ⊆ [1,h]` consumptions are hypotheses, never side conditions
hidden in a definition. -/

/-- **S1b, consumption 1 — the mid-band prefactor.**  The Prop A.3 prefactor
`(T/(X/Q₁) + 1)` evaluated at the band endpoint `T = X/h` is `Q₁/h + 1`, which the
containment `Q₁ ≤ h` caps at `2`. -/
theorem a3_prefactor_band_le_two {X h Q₁ : ℝ} (hX : 0 < X) (hh : 0 < h) (hQ₁ : 0 < Q₁)
    (hQ1h : Q₁ ≤ h) :
    X / h / (X / Q₁) + 1 ≤ 2 := by
  have hkey : X / h / (X / Q₁) = Q₁ / h := by
    field_simp
  have hle : Q₁ / h ≤ 1 := (div_le_one hh).mpr hQ1h
  rw [hkey]
  linarith

/-- **S1b, consumption 2 — the max-term prefactor.**  The Lemma-14 max-term carries the
weight `(X/h)/T` and consumes Prop A.3 at height `2T`; the product of weight and
prefactor is `2Q₁/h + (X/h)/T`, which the containment `Q₁ ≤ h` and the max-term's own
range gate `X/h ≤ T` cap at `3`. -/
theorem a3_prefactor_max_le_three {X h Q₁ T : ℝ} (hX : 0 < X) (hh : 0 < h) (hQ₁ : 0 < Q₁)
    (hQ1h : Q₁ ≤ h) (hT : X / h ≤ T) :
    X / h / T * (2 * T / (X / Q₁) + 1) ≤ 3 := by
  have hXh : 0 < X / h := div_pos hX hh
  have hTpos : 0 < T := lt_of_lt_of_le hXh hT
  have hkey : X / h / T * (2 * T / (X / Q₁) + 1) = 2 * (Q₁ / h) + X / h / T := by
    field_simp
  have h1 : Q₁ / h ≤ 1 := (div_le_one hh).mpr hQ1h
  have h2 : X / h / T ≤ 1 := (div_le_one hTpos).mpr hT
  rw [hkey]
  linarith

/-- **S1b, consumption 3 — the log-monotone.**  `(log Q₁)^{1/3} ≤ (log h)^{1/3}` under
`1 ≤ Q₁ ≤ h`.  This is the step that lets the A.2 interface's second term be read at
`h` instead of `Q₁` (the freeze's `log_calQK_door_one` identity on the door side). -/
theorem a3_logQ_third_mono {Q₁ h : ℝ} (hQ₁ : 1 ≤ Q₁) (hQ1h : Q₁ ≤ h) :
    Real.log Q₁ ^ ((1 : ℝ) / 3) ≤ Real.log h ^ ((1 : ℝ) / 3) :=
  Real.rpow_le_rpow (Real.log_nonneg hQ₁)
    (Real.log_le_log (lt_of_lt_of_le zero_lt_one hQ₁) hQ1h) (by norm_num)

/-- **S1b, consumption 3 (the interface face).**  The A.2 second term
`(log Q₁)^{1/3}/P₁^{1/6−η}` is dominated by its `h`-form.  The exponent `1/6 − η` is
carried as an abstract real `e` — at the frozen `η = 1/12` it is `1/12`, but the
arithmetic never needs the value. -/
theorem a3_logQ_term_mono {Q₁ h P₁ e : ℝ} (hQ₁ : 1 ≤ Q₁) (hQ1h : Q₁ ≤ h) (hP₁ : 0 < P₁) :
    Real.log Q₁ ^ ((1 : ℝ) / 3) / P₁ ^ e ≤ Real.log h ^ ((1 : ℝ) / 3) / P₁ ^ e := by
  have hden : 0 < P₁ ^ e := Real.rpow_pos_of_pos hP₁ e
  exact div_le_div_of_nonneg_right (a3_logQ_third_mono hQ₁ hQ1h) hden.le

/-- **S1b, the head-term exponent ruling.**  The Lemma-14 head `(log X)^{−2/15}` sits
under the A.2 interface's third term `(log X)^{−1/500}` once `X ≥ e` (so `log X ≥ 1`):
`rpow` is monotone in the exponent at base `≥ 1`, and `−2/15 ≤ −1/500`. -/
theorem a3_head_le_third_grade {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.log X ^ (-(2 / 15 : ℝ)) ≤ Real.log X ^ (-(1 / 500 : ℝ)) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL1 : (1 : ℝ) ≤ Real.log X := (Real.le_log_iff_exp_le hXpos).mpr hX
  exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)

/-- **`parseval_a3_join` — the S1b join (S8-SRC demand D-2).**

Input shapes, both abstract:

* `hpar` — the single-`h` Parseval exit (A2-1) in the landed `Lemma14` form: a
  `Cpar·(log X)^{−2/15}` head, `Cker` times a mid-band integral `Iband`, and `Cker`
  times the weighted max-term datum `Msup`;
* `hband` — Prop A.3 at the band endpoint `T = X/h`, prefactor `(X/h)/(X/Q₁) + 1`,
  grade `GM + GP` (the M-term and the `P₁`-term of the A.2 right-hand side);
* `hmax` — Prop A.3 at height `2T` against the max-term's `(X/h)/T` weight, same grade.

Output: the three-term A.2 right-hand side with explicit constants —
`5·Cker·GM + 5·Cker·GP + Cpar·(log X)^{−1/500}` (the `5 = 2 + 3` is exactly the two
prefactor caps).  The three `[P₁,Q₁] ⊆ [1,h]` consumptions are `hQ1h` (twice, here) and
the log-monotone `a3_logQ_term_mono` (once, applied by the consumer inside `GP`); the
max-term's range gate is `hT : X/h ≤ T`.

Scope note (freeze Amendment A): the interface's FOURTH summand
`C₄·(log X)^{−7/8+o(1)}` is the ball-error residue through the `8S²` squaring — it does
NOT arise here, and a consumer that carries it folds it into `GM` (or absorbs it above
the `X`-threshold at A2-7).  This join is the Parseval↔A.3 arithmetic only. -/
theorem parseval_a3_join {Bpar Iband Msup GM GP X h Q₁ T Cpar Cker : ℝ}
    (hX : Real.exp 1 ≤ X) (hh : 0 < h) (hQ₁ : 0 < Q₁)
    (hQ1h : Q₁ ≤ h) (hT : X / h ≤ T)
    (hGM : 0 ≤ GM) (hGP : 0 ≤ GP) (hCpar : 0 ≤ Cpar) (hCker : 0 ≤ Cker)
    (hpar : Bpar ≤ Cpar * Real.log X ^ (-(2 / 15 : ℝ)) + Cker * Iband + Cker * Msup)
    (hband : Iband ≤ (X / h / (X / Q₁) + 1) * (GM + GP))
    (hmax : Msup ≤ X / h / T * ((2 * T / (X / Q₁) + 1) * (GM + GP))) :
    Bpar ≤ 5 * Cker * GM + 5 * Cker * GP + Cpar * Real.log X ^ (-(1 / 500 : ℝ)) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hGpos : 0 ≤ GM + GP := by linarith
  -- consumption 1: the mid band
  have hband2 : Iband ≤ 2 * (GM + GP) :=
    le_trans hband
      (mul_le_mul_of_nonneg_right (a3_prefactor_band_le_two hXpos hh hQ₁ hQ1h) hGpos)
  -- consumption 2: the weighted max-term
  have hmax2 : Msup ≤ 3 * (GM + GP) := by
    have hassoc : X / h / T * ((2 * T / (X / Q₁) + 1) * (GM + GP))
        = (X / h / T * (2 * T / (X / Q₁) + 1)) * (GM + GP) := by ring
    rw [hassoc] at hmax
    exact le_trans hmax
      (mul_le_mul_of_nonneg_right (a3_prefactor_max_le_three hXpos hh hQ₁ hQ1h hT) hGpos)
  -- the head term drops into the third A.2 summand
  have hhead : Cpar * Real.log X ^ (-(2 / 15 : ℝ))
      ≤ Cpar * Real.log X ^ (-(1 / 500 : ℝ)) :=
    mul_le_mul_of_nonneg_left (a3_head_le_third_grade hX) hCpar
  have h1 : Cker * Iband ≤ Cker * (2 * (GM + GP)) :=
    mul_le_mul_of_nonneg_left hband2 hCker
  have h2 : Cker * Msup ≤ Cker * (3 * (GM + GP)) :=
    mul_le_mul_of_nonneg_left hmax2 hCker
  linarith

/-! ## §3 — the sup→inf pin (source defect D2)

The reverse-triangle geometry that licenses an inf-over-ball floor from a `𝒯₁`-distance
hypothesis.  Three lines of content, stated three ways so consumers can pick the shape
they need (pointwise, set inclusion, `sInf` floor). -/

/-- **The far-ball core.**  If the centre `t` is farther than `2r` from `t₁`, every
point `t'` of the closed `r`-ball around `t` is farther than `r` from `t₁`.  Reverse
triangle: `|t' − t₁| ≥ |t − t₁| − |t' − t| > 2r − r = r`. -/
theorem far_of_mem_closedBall {t t₁ r t' : ℝ} (ht : 2 * r < |t - t₁|)
    (ht' : |t' - t| ≤ r) : r < |t' - t₁| := by
  have htri : |t - t₁| ≤ |t - t'| + |t' - t₁| := abs_sub_le t t' t₁
  have hcomm : |t - t'| = |t' - t| := abs_sub_comm t t'
  linarith [htri, hcomm.le, hcomm.ge]

/-- **The far-ball inclusion.**  The closed `r`-ball around a `2r`-far centre is
contained in the far field of `t₁` at radius `r`. -/
theorem closedBall_subset_far {t t₁ r : ℝ} (ht : 2 * r < |t - t₁|) :
    {u : ℝ | |u - t| ≤ r} ⊆ {u : ℝ | r < |u - t₁|} := fun _ hu =>
  far_of_mem_closedBall ht hu

/-- **`ball_inf_floor_of_mem_far` — the D2 repair.**  MRT p. 23's printed `sup` must be
read as an `inf` (a supremum lower bound is vacuous where the argument needs the
minimum over the ball).  This is the licence: a datum `D` with a floor `c` on the far
field of `t₁` at radius `r` has that same floor on the INFIMUM over the closed `r`-ball
around any centre `t` with `|t − t₁| > 2r`.  The `sInf`/image idiom matches the
corpus's `M_range`-shaped infima, so the stone plugs in unchanged; `hr : 0 ≤ r` is the
nonemptiness gate (`le_csInf` is vacuous-false without it, the house creed's sixth
vacuity catch). -/
theorem ball_inf_floor_of_mem_far {t t₁ r c : ℝ} {D : ℝ → ℝ} (hr : 0 ≤ r)
    (ht : 2 * r < |t - t₁|) (hD : ∀ u : ℝ, r < |u - t₁| → c ≤ D u) :
    c ≤ sInf (D '' {u : ℝ | |u - t| ≤ r}) := by
  have hne : ({u : ℝ | |u - t| ≤ r}).Nonempty := by
    refine ⟨t, ?_⟩
    simpa using hr
  refine le_csInf (hne.image _) ?_
  rintro b ⟨u, hu, rfl⟩
  exact hD u (far_of_mem_closedBall ht hu)

end Salt.MR
