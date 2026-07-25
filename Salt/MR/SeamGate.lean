/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CenterCore
import Salt.MR.SupClose

/-!
# SEAM-GATE — the overhang gate closed by annulus geometry (`SeamGate`)

**Route (b) of `docs/exploration/hsup-design.md`, ⟦V3d — Z2-SCOPE VERDICT: THE NO-GAP ROUTE
(b) ADOPTED⟧.**  `SupClose.rhs_grade_at_scale_trunc` carries the recentring gate

  `hgate : |t₁| + T ≤ R`

(`T` = the contour truncation height `L⁴`, `R` = the compact-minimality radius), which
`CompactMin.exists_min_dist_abs` alone cannot discharge: it supplies `|t₁| ≤ R`, never
`|t₁| ≤ R − T`.  ⟦V3c⟧ called this the "overhang" and priced a localization route through
`compact_min_package`'s `hgap` — which the frozen live-band numeral fails.

**The finding this file implements: no `hgap` is needed.**  The ball leg's own integration
domain is `seamAnn X T_ann ∩ seamBall X t₁`, and on it the geometry bounds the CENTRE:

* if the intersection is NONEMPTY, a witness `t` has `|t| ≤ T_ann` (the annulus's OUTER cut)
  and `|t − t₁| ≤ seamRad X` (the ball), so `|t₁| ≤ T_ann + seamRad X` — the outer companion
  of the landed inner cut `CenterCore.seamAnn_inter_seamBall_eq_empty` (:490);
* if it is EMPTY, the row's `hSup` binder is VACUOUS (its three guards ARE membership in the
  intersection, `SeamBallWeighted.ball_leg_of_sup_weighted` :166–167) and the ball leg is `0`,
  so the row holds with any `S`.

Instantiating the minimizer at

  `R := seamGateR X T_ann = T_ann + seamRad X + (log 2X)⁴ + 1`

then discharges `hgate` outright for every truncation height `T = (log k)⁴` with `k ≤ 2X`
(the row's dyadic scale).  **The gate never references `X` as a bound on `|t₁|`**, so it
survives the `T_ann ≈ X` regime of the L14 row, where the B-2 counterexample's minimizer sits
exactly where `|t₁| ≤ X` fails.

## What is here

* `seamAnn_inter_seamBall_center_le` (G-1) — the OUTER cut.
* `ball_center_dichotomy_two_sided` (G-2) — `CenterCore.ball_center_dichotomy` with the upper
  bound adjoined: empty, or `seamT0 X − seamRad X ≤ |t₁| ≤ T_ann + seamRad X`.
* `seamGateR` + `seam_gate_of_nonempty` / `_nat` (G-3 i) — the gate at the pinned radius.
* `exists_min_gate` / `seam_gate_package` (G-3 ii) — the minimizer at that radius, and the
  two facts bundled at ONE `t₁`.
* `rhs_grade_at_scale_seam_gate` (G-3 iii) — the byte-exactness certificate: the compile of
  `SupClose.rhs_grade_at_scale_trunc` with `T := L⁴`, `R := seamGateR X T_ann` and `hgate`
  supplied from the geometry.  Its far binders (`hFar`, `hKfar`, `hInt`) are threaded
  VERBATIM, not discharged — that is FARCLOSE's business.
* `seam_sup_binder_of_inter_empty` / `ball_leg_of_inter_empty` — the vacuous arm, in
  `ball_leg_of_sup_weighted`'s exact binder and conclusion shapes.

**No statement anywhere is changed** (Iron rule 1): every stone below is new, and the two
consumers are hit through their existing binders.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory Set

/-! ## §1 — G-1: the OUTER cut

`CenterCore` :490 reads the annulus's INNER cut (`seamT0 X ≤ |t|`) against the ball and gets
emptiness for small centres.  Read the OUTER cut (`|t| ≤ T`) against the same ball and you get
the complementary fact: a nonempty intersection pins the centre from ABOVE. -/

/-- **G-1 — the outer cut (`seamAnn_inter_seamBall_center_le`).**  If the ball leg's
integration domain is nonempty then the centre satisfies

  `|t₁| ≤ T + seamRad X`.

One witness suffices: `t ∈ seamAnn X T` gives `|t| ≤ T`, `t ∈ seamBall X t₁` gives
`|t − t₁| ≤ seamRad X`, and `|t₁| − |t| ≤ |t₁ − t| = |t − t₁|`.  No hypothesis on `X`, `T`. -/
lemma seamAnn_inter_seamBall_center_le {X T t₁ : ℝ}
    (hne : (seamAnn X T ∩ seamBall X t₁).Nonempty) :
    |t₁| ≤ T + seamRad X := by
  obtain ⟨t, ht⟩ := hne
  have h1 : |t| ≤ T := ht.1.2
  have h2 : |t - t₁| ≤ seamRad X := ht.2
  have h3 : |t₁| - |t| ≤ |t₁ - t| := abs_sub_abs_le_abs_sub t₁ t
  have h4 : |t₁ - t| = |t - t₁| := abs_sub_comm t₁ t
  linarith

/-- **G-2 — the TWO-SIDED ball-centre dichotomy (`ball_center_dichotomy_two_sided`).**
`CenterCore.ball_center_dichotomy` (:531) with G-1 adjoined: for ANY `X`, `T`, `t₁`,

  `seamAnn X T ∩ seamBall X t₁ = ∅  ∨  (seamT0 X − seamRad X ≤ |t₁| ∧ |t₁| ≤ T + seamRad X)`.

The live branch now confines the centre to the ANNULAR SHELL thickened by the ball radius —
which is exactly the band on which the overhang gate is affordable.  Still no hypotheses. -/
theorem ball_center_dichotomy_two_sided (X T t₁ : ℝ) :
    seamAnn X T ∩ seamBall X t₁ = ∅ ∨
      (seamT0 X - seamRad X ≤ |t₁| ∧ |t₁| ≤ T + seamRad X) := by
  rcases Set.eq_empty_or_nonempty (seamAnn X T ∩ seamBall X t₁) with hE | hne
  · exact Or.inl hE
  · refine Or.inr ⟨?_, seamAnn_inter_seamBall_center_le hne⟩
    rcases ball_center_dichotomy X T t₁ with hE | hlow
    · exact absurd hE (Set.nonempty_iff_ne_empty.mp hne)
    · exact hlow

/-! ## §2 — G-3(i): the pinned radius and the gate -/

/-- **The gate radius.**  `R := T_ann + seamRad X + (log 2X)⁴ + 1` — the annular shell's
outer reach (G-1), plus the largest truncation height the row can present (`(log k)⁴` at
`k ≤ 2X`), plus a unit of slack so the radius is positive with no hypothesis on `T_ann`
beyond `0 ≤ T_ann`.

`T_ann` is the ANNULUS's outer cut (`seamAnn X T_ann`), NOT the contour truncation height
`T = L⁴` of `SupClose.rhs_grade_at_scale_trunc`; the two are distinct parameters that the
gate `|t₁| + T ≤ R` relates. -/
def seamGateR (X T : ℝ) : ℝ := T + seamRad X + Real.log (2 * X) ^ 4 + 1

lemma seamGateR_nonneg {X T : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ Real.log X) :
    0 ≤ seamGateR X T := by
  have hr : (0 : ℝ) ≤ seamRad X := seamRad_nonneg hL
  have h4 : (0 : ℝ) ≤ Real.log (2 * X) ^ 4 := by positivity
  unfold seamGateR
  linarith

/-- The truncation height is monotone in the scale, on the row's own range `1 ≤ k ≤ 2X`.
(`Real.log_le_log` needs the positivity, hence the `1 ≤ k`; `pow_le_pow_left₀` needs the
nonnegativity of `log k`, which is the same hypothesis.) -/
lemma log_pow_four_le_of_le_two_mul {X k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * X) :
    Real.log k ^ 4 ≤ Real.log (2 * X) ^ 4 :=
  pow_le_pow_left₀ (Real.log_nonneg hk1) (Real.log_le_log (by linarith) hk) 4

/-- **G-3(i) — THE GATE (`seam_gate_of_nonempty`).**  On the ball leg's own domain, with the
minimality radius pinned at `seamGateR X T_ann`, the recentring gate of
`SupClose.center_dist_floor_recentred` / `rhs_grade_at_scale_trunc` holds for every
truncation height `(log k)⁴` with `1 ≤ k ≤ 2X`:

  `|t₁| + (log k)⁴ ≤ seamGateR X T_ann`.

Proof: G-1 bounds `|t₁|` by `T_ann + seamRad X`, monotonicity bounds `(log k)⁴` by
`(log 2X)⁴`, and the radius is their sum plus `1`.  **No `hgap`, no localization, no numeral
shift** — and no reference to `X` as a bound on `|t₁|`. -/
theorem seam_gate_of_nonempty {X T t₁ k : ℝ} (hk1 : 1 ≤ k) (hk : k ≤ 2 * X)
    (hne : (seamAnn X T ∩ seamBall X t₁).Nonempty) :
    |t₁| + Real.log k ^ 4 ≤ seamGateR X T := by
  have h1 := seamAnn_inter_seamBall_center_le hne
  have h2 := log_pow_four_le_of_le_two_mul hk1 hk
  unfold seamGateR
  linarith

/-- **G-3(i), ℕ-scale form.**  The same gate for a natural scale `k ≤ 2X`, with NO lower
bound needed: at `k = 0` the truncation height `(log 0)⁴ = 0` is free. -/
theorem seam_gate_of_nonempty_nat {X T t₁ : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ 2 * X)
    (hne : (seamAnn X T ∩ seamBall X t₁).Nonempty) :
    |t₁| + Real.log (k : ℝ) ^ 4 ≤ seamGateR X T := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have h0 : Real.log ((0 : ℕ) : ℝ) ^ 4 = 0 := by simp
    rw [h0, add_zero]
    have h1 := seamAnn_inter_seamBall_center_le hne
    have h4 : (0 : ℝ) ≤ Real.log (2 * X) ^ 4 := by positivity
    unfold seamGateR
    linarith
  · exact seam_gate_of_nonempty (by exact_mod_cast hpos) hk hne

/-! ## §3 — G-3(ii): the minimizer at the pinned radius -/

/-- **G-3(ii) — the minimizer at the gate radius (`exists_min_gate`).**
`CompactMin.exists_min_dist_abs` instantiated at `R := seamGateR X T_ann`; the positivity of
the radius is free (`0 ≤ T_ann`, `0 ≤ log X`, an even power, `+1`).  The `hmin` produced is
the NON-VACUOUS compact form (`|v| ≤ R` only) that `rhs_grade_at_scale_trunc` consumes. -/
theorem exists_min_gate (f : ℕ → ℂ) {X T : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ Real.log X) :
    ∃ t₁ : ℝ, |t₁| ≤ seamGateR X T ∧ ∀ v : ℝ, |v| ≤ seamGateR X T →
      pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X :=
  exists_min_dist_abs f X (seamGateR_nonneg hT hL)

/-- **G-3(ii), the bundle (`seam_gate_package`).**  ONE centre `t₁` carrying both halves of
what the truncated grade needs: the compact minimality at radius `seamGateR X T_ann`, and —
on the ball leg's own domain — the recentring gate at every truncation height `(log k)⁴`,
`1 ≤ k ≤ 2X`.

The second component is stated as an IMPLICATION from nonemptiness, which is the honest
shape: when the intersection is empty the ball leg is `0` and the gate is not needed at all
(`seam_sup_binder_of_inter_empty` / `ball_leg_of_inter_empty` below). -/
theorem seam_gate_package (f : ℕ → ℂ) {X T : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ Real.log X) :
    ∃ t₁ : ℝ,
      (∀ v : ℝ, |v| ≤ seamGateR X T →
        pretDistSq f (costwist t₁) X ≤ pretDistSq f (costwist v) X)
      ∧ ∀ k : ℝ, 1 ≤ k → k ≤ 2 * X →
          (seamAnn X T ∩ seamBall X t₁).Nonempty → |t₁| + Real.log k ^ 4 ≤ seamGateR X T := by
  obtain ⟨t₁, -, hmin⟩ := exists_min_gate f hT hL
  exact ⟨t₁, hmin, fun k hk1 hk hne => seam_gate_of_nonempty hk1 hk hne⟩

/-! ## §4 — the vacuous arm

The empty branch costs nothing: `ball_leg_of_sup_weighted`'s three guards on `hSup` ARE
membership in `seamAnn X T ∩ seamBall X t₁`, so on an empty intersection the binder holds for
EVERY `S` and the ball leg's integral is `0`.  (`CenterCore.ball_leg_of_center_small` is the
same conclusion from the STRONGER small-centre hypothesis; these two are its companions from
the emptiness itself, which is what `ball_center_dichotomy_two_sided` hands the consumer.) -/

/-- **The vacuous binder.**  `SeamBallWeighted.ball_leg_of_sup_weighted`'s `hSup` (:166–167)
byte-for-byte, discharged with NO analysis, at an arbitrary `S`, from the emptiness alone. -/
theorem seam_sup_binder_of_inter_empty {N : ℕ} {a : ℕ → ℂ} {X T t₁ S : ℝ}
    (hE : seamAnn X T ∩ seamBall X t₁ = ∅) :
    ∀ t : ℝ, seamT0 X ≤ |t| → |t| ≤ T → |t - t₁| ≤ seamRad X →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t - t₁|) := by
  intro t h1 h2 h3 _ _
  exact absurd (⟨⟨h1, h2⟩, h3⟩ : t ∈ seamAnn X T ∩ seamBall X t₁)
    (Set.eq_empty_iff_forall_notMem.mp hE t)

/-- The empty branch in `ball_leg_of_sup_weighted`'s EXACT conclusion shape (:168), from the
emptiness of the domain: the ball leg is `0 ≤ 8·S²` for every `S`. -/
theorem ball_leg_of_inter_empty {N : ℕ} {a : ℕ → ℂ} {X T t₁ S : ℝ}
    (hE : seamAnn X T ∩ seamBall X t₁ = ∅) :
    (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2) ≤ 8 * S ^ 2 := by
  rw [hE, setIntegral_empty]
  positivity

/-! ## §5 — G-3(iii): the byte-exactness certificate

`SupClose.rhs_grade_at_scale_trunc` (:334) with its two frequency hypotheses supplied from
§2/§3: `T := L⁴` (the contour truncation height), `R := seamGateR X T_ann`.  Everything else
— `hFar`, `hKfar`, `hInt`, the pin equations — is threaded VERBATIM.  That this compiles IS
the proof that the gate's shape fits the consumer's slots. -/

/-- **G-3(iii) — the gated truncated grade (`rhs_grade_at_scale_seam_gate`).**
`rhs_grade_at_scale_trunc`'s conclusion with `hgate` GONE: on the ball leg's own domain
(`hne`), at the row's own scale (`k ≤ 2X`), the geometry discharges it.

The far remainder `(1/π)·η²·(Ffar·Kfar)` is UNCHANGED and UNABSORBED — its numerals are
FARCLOSE's business; this stone only removes the overhang. -/
theorem rhs_grade_at_scale_seam_gate {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Cb t₀ t₁ X k L c₀ y η h Tann Ffar Kfar : ℝ}
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ k) (hL : L = Real.log k) (hy : y = L ^ 4) (hη : η = 1 / Real.log y)
    (hc₀ : c₀ = 1 + 1 / L) (hh : h = k / Real.sqrt L)
    (hXk : ⌊X⌋₊ ≤ ⌊k⌋₊) (hkX : k ≤ 2 * X)
    (hne : (seamAnn X Tann ∩ seamBall X t₁).Nonempty)
    (hmin : ∀ v : ℝ, |v| ≤ seamGateR X Tann →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
        ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X)
    (hFfar0 : 0 ≤ Ffar)
    (hFar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η, ∀ t : ℝ,
      ‖smoothSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) - (α : ℂ) - (β : ℂ))
          * largeSeries y (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I))
            (((c₀ : ℂ) + ((t - (t₀ + t₁) : ℝ) : ℂ) * I) + (β : ℂ))‖ ≤ Ffar)
    (hKfar : ∀ α ∈ Icc (0 : ℝ) η, ∀ β ∈ Icc (0 : ℝ) η,
      crossKerFar (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) k h y c₀ (t₀ + t₁)
        α β (L ^ 4) ≤ Kfar)
    (hInt : JointIntegrableAt (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
      (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) k L c₀ y η h) :
    ‖prop21RHS (fun q => g q * (q : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁) k h c₀ y η‖
      ≤ gradeAbsConst Cb * k
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
        + (1 / Real.pi) * (η ^ 2 * (Ffar * Kfar)) := by
  have hk1 : (1 : ℝ) ≤ k := by
    have h65 : (65 : ℝ) ≤ k := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hgate : |t₁| + L ^ 4 ≤ seamGateR X Tann := by
    rw [hL]
    exact seam_gate_of_nonempty hk1 hkX hne
  exact rhs_grade_at_scale_trunc hg hCb0 hCbound hk hL hy hη hc₀ hh hXk hgate hmin hFfar0
    hFar hKfar hInt

end Salt.MR
