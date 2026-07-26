/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.CofactorBall
import Salt.MR.GradeWindowC
import Salt.MR.FarStar

/-!
# CofactorGrade — CASE A of the co-factor dichotomy (U7-E)

The `⟦V5⟧` ladder's **U7-E** (`docs/exploration/hsup-design.md`): the *window-floor* arm of
the U-7 dichotomy, at the shifted scale.  Here the damped co-factor datum `ℓ(g_x)` has NO
pretentious pocket — the floor

  `𝔻²(ℓ(g_x)·p^{−iτ}, p^{i(v−τ)}; k) ≥ M`   for every `v` in the contour window `|v−τ| ≤ T*`

holds at every damping parameter `x ∈ [0,1]` and every scale `k` of the co-factor window —
and the `c`-generic grade machinery of `GradeWindowC` prices the partial sums at `c = 1/e`,
where all three of its gates pass (`0 < 1/e`, `1/e ≤ 1/e`, `2/e < 1`).  Via the Abel bridge
(`RamRAdapter.ramR_abel_sup`) that becomes a pointwise bound on the co-factor itself.

## The mathematics, in one paragraph

At each scale `k` of the co-factor window `[X_j, 2X_j]` the `c`-generic grade at scale
(`GradeWindowC.rhs_grade_at_scale_windowC`) prices `prop21RHS` of the twisted damped datum by
`gradeAbsConstC c Cb·k·e^{−cM}` plus the far remainder, and the far remainder is priced
ADDITIVELY by `FarStar.hfar_star` at the truncation height `T* = T*(k, log k)`:
`farCStar·k·(log W)^{−1/(32e)}`, `W` the window bottom.  The centre supply
(§1, the datum-uniform clone of `GradeWindowC.center_halasz_supply_B_uniform`) turns that into
a LINEAR bound on the twisted partial sums of the damped datum, with the extra desmooth/`E`
error `4(log W)^{−1/2+1/1000}`.  The co-factor's own partial sums are the window difference of
two of those (`CofactorBall.spolyA_window_split`), costing a factor `2`; the `[0,1]` average
(`CofactorBall.spolyA_ramRcoeff_le_of_damp`) is free; and `ramR_abel_sup` costs the factor `3`
(`2` from Abel, `1` for the half-open endpoint).  Exit: `‖ramR‖ ≤ 6·S`, with

  `S = caseAS c Cb M W = gradeAbsConstC c Cb·e^{−cM} + farCStar·(log W)^{−1/(32e)}
        + 4·(log W)^{−1/2+1/1000}`.

At `c = 1/e` and the CASE-A floor `M = (1/32 − θ)·loglog W` the leading term is
`(log W)^{−ρ}` with `ρ = (1/32 − θ)/e = ρ_eff = 3θ` — `CofactorDist.balance_exponent_293`,
the ⟦V5⟧ pin.  That is `caseA_ramR_bound_293`.

## What is proved here

* **§1 `center_halasz_supply_A`** — the centre supply with the `∃ X₀` hoisted over the DATUM.
  `GradeWindowC.center_halasz_supply_B_uniform`'s own proof: its witness
  `max (max (XA+1) XB) (e⁸)` mentions neither `g`, `t₀` nor `t₁` (`XA` is
  `LambdaMass.prop21_uniform_at_scale_absC`'s datum-free threshold, `XB` is
  `BridgeAdapt.loglog_absorb_pow_pin`'s), so hoisting the `refine` past the datum is the whole
  edit.  **This hoisting is FORCED here and is not decoration**: CASE A consumes the supply at
  the one-parameter family `g_x = gxDatum g P Q x`, `x ∈ [0,1]`, and the `[0,1]` average
  (`spolyA_ramRcoeff_le_of_damp`) needs ONE threshold for the whole family — `∀x ∃X₀` does not
  average.  The four arithmetic helpers are `private` both in `CenterSupply` and in
  `GradeWindowC` (and in `SupStation`'s `_st` re-derivation), so they are re-derived here
  verbatim under an `_A` suffix, per the house convention.
* **§2 (E-1a) `caseA_rhs_socket`** — the per-scale `prop21RHS` socket at a free `c`, in
  window-floor form, with the far arm at `T*`: `rhs_grade_at_scale_windowC` ∘
  `FarClose.far_supF_bound` ∘ `FarStar.far_kernel_bound_star` ∘ `FarStar.hfar_star` ∘
  `GradeWindowC.jointIntegrableAtC_pin_free`.  Exit shape `B·k` with `B` scale-free —
  the supply's `hRHS` binder byte-for-byte.
* **§3 (E-1b) `caseA_partial_supply`** — §1 ∘ §2 at the damped datum: the twisted partial sums
  of `ℓ(g_x)` are `≤ caseAS c Cb M W · k`, **uniformly over `x ∈ [0,1]`**.
* **§4 (E-2) `caseA_damped_partial` / `caseA_ramR_of_supplied`** — the window split at the
  `spolyA` level, the `[0,1]` average, and `ramR_abel_sup`.
* **§5 (E-3) `caseA_ramR_bound`** — the assembled CASE-A `Rbd` in `USetThinTL.tL_main_sumsq`'s
  binder shape, with the floor `M` ABSTRACT; `caseA_ramR_bound_293` is the numeral instance at
  `c = 1/e`, `M = (1/32 − θ₂₉₃)·loglog W`, exiting at `(log W)^{−ρ₂₉₃}`.

## THE SCALE DESCENT (law #253 — stated, never absorbed)

Everything in §§2–5 runs at the **shifted scale**: the window bottom `W := k₀ ≈ X_j =
X·e^{−j/H}`, not the global `X`.  The three descent gates are IN-STATEMENT and are the
consumer's (U7-F's), exactly as in `CofactorBall`:

1. `hX₀ : X₀ ≤ (k₀ : ℝ)` — the supply's threshold, at the SHIFTED scale;
2. `hk₀64 : e^{64} ≤ (k₀ : ℝ)` — the corpus scale gate, at the SHIFTED scale;
3. the floor binder `hMwin` is stated at the scales `k ∈ [k₀, M]` of the co-factor window —
   the descent of the U7-C floor from `loglog X` to `loglog X_j` (monotonicity of `pretDistSq`
   in the scale plus the `loglog` numeral) is NOT performed here.

The `j/H` numeral that turns `X_j ≥ e^{64}` (and `X_j ≥ X₀`) into a condition on `j` is
U7-F's; nothing here commits to it.

## THE `t`-CONVENTION

As in `RamRAdapter` and `CofactorBall`: everything is at the SAME `t` that `ramR` is evaluated
at, twist `n^{−it}` (`spolyA`).  **No `dpoly`, no `−𝒯` flip, no ordinate-set negation appears
in this file.**  The supply is consumed at `t₀ := 0`, `t₁ := t`, so its centre `t₀ + t₁` is
`0 + t` and its seam coefficient `seamCoeff (ellLin g_x) 1 0` is the bare datum
(`sum_seamCoeff_zero_center`).

## Named hypotheses (each a real socket — none forced closed)

* `hMwin` — CASE A's DEFINING hypothesis: the window floor, uniform over `x ∈ [0,1]` and over
  the window scales.  It is the complement of `CofactorBall`'s pocket **after three
  transports, all of them U7-F's**: (i) the twist slot
  (`CenterSupply.pretDistSq_twist_slot`, which moves `𝔻²(ℓ(g_x)·p^{−iτ}, 1)` to
  `𝔻²(ℓ(g_x), p^{iτ})`); (ii) the scale descent `X ↝ X_j` (CASE B's pocket is stated at the
  global scale); (iii) the contour-window restriction `|v − t| ≤ T*` (CASE B's pocket is a
  single frequency).  None of the three is performed in this file.
* `hend : 2/X_j ≤ 2S` — `ramR_abel_sup`'s half-open endpoint charge (free in the regime).
* `hMN : M ≤ N` — the sharp Abel length inside the dyadic length.
* `hk₀lo/hk₀hi` — the window cut `k₀ < X_j ≤ k₀+1` (`CofactorBall.exists_window_cut`), and
  `hlow/hhigh/hMtop` the Abel window (`CofactorBall.caseB_window_geometry` builds all five).
* `hCb0`/`hCbound` — the short-interval Chebyshev datum, the amplitude side's own.
-/

noncomputable section

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the centre supply, UNIFORM IN THE DATUM

`GradeWindowC.center_halasz_supply_B_uniform` with the `∃ X₀` hoisted over `g` (and hence over
the damping parameter `x`, which is what CASE A needs).  The four arithmetic helpers are
`private` upstream, so they are re-derived verbatim under an `_A` suffix. -/

/-- `L^{−1/2} = 1/√L`.  (`GradeWindowC.rpow_neg_half_eq_B`, `private` there.) -/
private lemma rpow_neg_half_eq_A {L : ℝ} (hL : 0 < L) :
    L ^ (-(1 : ℝ) / 2) = (Real.sqrt L)⁻¹ := by
  rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) from by norm_num, Real.rpow_neg hL.le,
    Real.sqrt_eq_rpow]

/-- `2·log X ≤ X` for `X ≥ 16`.  (`GradeWindowC.two_log_le_self_B`, `private` there.) -/
private lemma two_log_le_self_A {X : ℝ} (hX : 16 ≤ X) : 2 * Real.log X ≤ X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hs4 : (4 : ℝ) ≤ Real.sqrt X := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hX
  have hlog : Real.log (Real.sqrt X) ≤ Real.sqrt X - 1 := Real.log_le_sub_one_of_pos hs0
  have hhalf : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX0.le
  have hsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  nlinarith [hs4, hlog, hsq, hhalf]

/-- `25 ≤ exp 8`.  (`GradeWindowC.twentyfive_le_exp_eight_B`, `private` there.) -/
private lemma twentyfive_le_exp_eight_A : (25 : ℝ) ≤ Real.exp 8 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  rw [show (8 : ℝ) = 4 + 4 from by norm_num, Real.exp_add]
  nlinarith

/-- **THE GRADE PAGE** (`GradeWindowC.center_error_grade_B`, `private` there).  The two error
legs of the centre composition — the desmooth cost `k/√(log k) + 1` and the S1′ `E`-error,
already reduced to `D·k·loglog k/log k` — become the single `X`-scale term
`4·k·(log X)^{−1/2+1/1000}`, uniformly over the dyadic window `X−1 < k ≤ 2X`.  DATUM-FREE
arithmetic: this is why the hoisting of §1 costs no analysis. -/
private lemma center_error_grade_A {D X : ℝ} {k : ℕ} (hD0 : 0 ≤ D)
    (hX8 : Real.exp 8 ≤ X) (hk1 : X - 1 < (k : ℝ)) (hk2 : (k : ℝ) ≤ 2 * X)
    (hB : 4 * D * Real.log (Real.log X) * Real.log X ^ (-(1 : ℝ))
        ≤ Real.log X ^ (-(1 : ℝ) + 1 / 1000)) :
    D * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
        + ((k : ℝ) / Real.sqrt (Real.log (k : ℝ)) + 1)
      ≤ 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_A hX8
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hkX2 : X / 2 ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  set L := Real.log X with hLdef
  have hL8 : (8 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos 8) hX8
  have hL0 : (0 : ℝ) < L := by linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  set Lk := Real.log (k : ℝ) with hLkdef
  have hLklo : L - Real.log 2 ≤ Lk := by
    have h1 : Real.log (X / 2) ≤ Lk := Real.log_le_log (by linarith) hkX2
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLkhi : Lk ≤ L + Real.log 2 := by
    have h1 : Lk ≤ Real.log (2 * X) := Real.log_le_log hk0 hk2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    linarith
  have hLk1 : (1 : ℝ) ≤ Lk := by linarith
  have hLk0 : (0 : ℝ) < Lk := by linarith
  have hLkhalf : L / 2 ≤ Lk := by linarith
  have hLk2L : Lk ≤ 2 * L := by linarith
  have hlogLk0 : (0 : ℝ) ≤ Real.log Lk := Real.log_nonneg hLk1
  have hlogL0 : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
  -- STEP A/B/C — `loglog k / log k ≤ 4·loglog X / log X`
  have hlogLk : Real.log Lk ≤ 2 * Real.log L := by
    have h1 : Real.log Lk ≤ Real.log (2 * L) := Real.log_le_log hLk0 hLk2L
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hstepC : Real.log Lk / Lk ≤ 4 * (Real.log L / L) := by
    have hq0 : (0 : ℝ) ≤ 4 * (Real.log L / L) := by positivity
    have h1 : 4 * (Real.log L / L) * (L / 2) ≤ 4 * (Real.log L / L) * Lk :=
      mul_le_mul_of_nonneg_left hLkhalf hq0
    have h2 : 4 * (Real.log L / L) * (L / 2) = 2 * Real.log L := by
      field_simp
      ring
    rw [div_le_iff₀ hLk0]
    linarith
  -- STEP D — the A-6 absorption at the pin
  have hLinv : L ^ (-(1 : ℝ)) = 1 / L := by rw [Real.rpow_neg_one, one_div]
  have hPmono : L ^ (-(1 : ℝ) + 1 / 1000) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hstepD : D * (Real.log Lk / Lk) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h1 : D * (Real.log Lk / Lk) ≤ D * (4 * (Real.log L / L)) :=
      mul_le_mul_of_nonneg_left hstepC hD0
    have h2 : D * (4 * (Real.log L / L)) = 4 * D * Real.log L * L ^ (-(1 : ℝ)) := by
      rw [hLinv]; field_simp
    linarith
  -- STEP E — the desmooth leg
  have hsqL0 : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsqL2 : Real.sqrt L / 2 ≤ Real.sqrt Lk := by
    have hq : Real.sqrt (L / 4) = Real.sqrt L / 2 := by
      rw [show L / 4 = L * (1 / 2) ^ 2 from by ring, Real.sqrt_mul hL0.le,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    calc Real.sqrt L / 2 = Real.sqrt (L / 4) := hq.symm
      _ ≤ Real.sqrt Lk := Real.sqrt_le_sqrt (by linarith)
  have hsqL20 : (0 : ℝ) < Real.sqrt L / 2 := by linarith
  have hdes : (k : ℝ) / Real.sqrt Lk ≤ 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
    have h1 : (k : ℝ) / Real.sqrt Lk ≤ (k : ℝ) / (Real.sqrt L / 2) :=
      div_le_div_of_nonneg_left hk0.le hsqL20 hsqL2
    have h2 : (k : ℝ) / (Real.sqrt L / 2) = 2 * ((k : ℝ) * L ^ (-(1 : ℝ) / 2)) := by
      rw [rpow_neg_half_eq_A hL0]
      field_simp
    linarith
  -- STEP F — `1 ≤ k·L^{−1/2}`
  have hone : (1 : ℝ) ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2) := by
    have hsq1 : (1 : ℝ) ≤ Real.sqrt L := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hL1
    have hsL : Real.sqrt L ≤ L := by nlinarith [Real.mul_self_sqrt hL0.le, hsq1]
    have h2L : 2 * L ≤ X := by rw [hLdef]; exact two_log_le_self_A (by linarith)
    have hsk : Real.sqrt L ≤ (k : ℝ) := by linarith
    rw [rpow_neg_half_eq_A hL0, ← div_eq_mul_inv, le_div_iff₀ hsqL0]
    linarith
  -- STEP G — assemble
  have hPnn : (0 : ℝ) ≤ L ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  have hGmono : L ^ (-(1 : ℝ) / 2) ≤ L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hterm1 : D * ((k : ℝ) * (Real.log Lk / Lk))
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h := mul_le_mul_of_nonneg_left hstepD hk0.le
    calc D * ((k : ℝ) * (Real.log Lk / Lk)) = (k : ℝ) * (D * (Real.log Lk / Lk)) := by ring
      _ ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) := h
  have hterm2 : (k : ℝ) * L ^ (-(1 : ℝ) / 2)
      ≤ (k : ℝ) * L ^ (-(1 : ℝ) / 2 + 1 / 1000) :=
    mul_le_mul_of_nonneg_left hGmono hk0.le
  linarith

/-- **§1 — THE CENTRE SUPPLY, UNIFORM IN THE DATUM** (`center_halasz_supply_A`).
`GradeWindowC.center_halasz_supply_B_uniform` with the `∃ X₀` quantified BEFORE the datum `g`
(and before the two centres).  The proof is that theorem's own: its witness
`max (max (XA+1) XB) (e⁸)` mentions neither `g`, `t₀` nor `t₁` — `XA` comes from
`prop21_uniform_at_scale_absC`, whose `(X₀, C_E, C_R)` already precede the datum, and `XB`
from `loglog_absorb_pow_pin`, which has no datum at all.  Hoisting the `refine` past `g` is
the whole edit.

**Why CASE A cannot use the un-hoisted form.**  The Ramaré weight is paid by the `[0,1]`
average of the damped data `g_x = gxDatum g P Q x` (⟦V5⟧'s W2), so the supply is consumed at an
uncountable family of data at once; `spolyA_ramRcoeff_le_of_damp` needs ONE threshold valid for
every `x ∈ [0,1]`, and `∀x ∃X₀` does not average. -/
theorem center_halasz_supply_A :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ t₁ X : ℝ) (N : ℕ) (B : ℝ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ B →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * Complex.I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
              ≤ B * (k : ℝ)) →
      ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
        ‖∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n‖
          ≤ (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ) := by
  obtain ⟨XA, C_E, C_R, hCE0, hCR0, hrep⟩ := prop21_uniform_at_scale_absC
  obtain ⟨XB, _hXB0, hB⟩ :=
    loglog_absorb_pow_pin (C := 4 * (8 * C_E + 4 * C_R)) (by positivity) 1
  refine ⟨max (max (XA + 1) XB) (Real.exp 8),
    lt_of_lt_of_le (Real.exp_pos 8) (le_max_right _ _), ?_⟩
  intro g hg t₀ t₁ X N B hXlb _hXN hN2 _hB0 hRHS k hkfl hkN
  -- the threshold split
  have hX8 : Real.exp 8 ≤ X := le_trans (le_max_right _ _) hXlb
  have hXA1 : XA + 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXlb
  have hXB : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXlb
  have hX25 : (25 : ℝ) ≤ X := le_trans twentyfive_le_exp_eight_A hX8
  have hX0 : (0 : ℝ) < X := by linarith
  -- the dyadic `k`-window
  have hfl : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hk1 : X - 1 < (k : ℝ) := by
    have h : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hkfl
    linarith
  have hk2 : (k : ℝ) ≤ 2 * X := le_trans (Nat.cast_le.mpr hkN) hN2
  have hkXA : XA ≤ (k : ℝ) := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk1le : (1 : ℝ) ≤ (k : ℝ) := by linarith
  -- `log k ≥ 1` (the window: `log k ≥ log X − log 2 ≥ 8 − 0.7`)
  have hlog2hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL8 : (8 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8]; exact Real.log_le_log (Real.exp_pos 8) hX8
  have hLklo : Real.log X - Real.log 2 ≤ Real.log (k : ℝ) := by
    have h1 : Real.log (X / 2) ≤ Real.log (k : ℝ) :=
      Real.log_le_log (by linarith) (by linarith)
    rwa [Real.log_div (by linarith) (by norm_num)] at h1
  have hLk1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by linarith
  have hLk0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  have hsqLk1 : (1 : ℝ) ≤ Real.sqrt (Real.log (k : ℝ)) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hLk1
  have hsqLk0 : (0 : ℝ) < Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hh0 : (0 : ℝ) < (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by positivity
  have hhX : (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) ≤ (k : ℝ) := by
    rw [div_le_iff₀ hsqLk0]; nlinarith
  -- the two landed legs, at scale `k`
  have hdes := prop21_desmooth_reduction (f := ellLin g) (gJ := fun _ => 1) (t₀ + t₁)
    (fun n => ellLin_norm_le_one g hg n) (fun _ => by simp)
    (X := (k : ℝ)) (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) hk1le hh0 hhX
  rw [Nat.floor_natCast] at hdes
  have hr := hrep g hg (t₀ + t₁) (k : ℝ) hkXA
  have hR := hRHS k hkfl hkN
  -- the twist combine
  have hsum : (∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
      = ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n :=
    Finset.sum_congr rfl (fun n _ => seamCoeff_twist_combine _ _ t₀ t₁ n)
  rw [hsum]
  -- the triangle chain
  set A := ∑ n ∈ Finset.Icc 1 k, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n with hAdef
  set Bs := ∑' n, seamCoeff (ellLin g) (fun _ => 1) (t₀ + t₁) n
    * (hatK (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) n : ℂ) with hBsdef
  set R := prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * Complex.I)) (t₀ + t₁)
    (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
    (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4)) with hRdef
  have hid : A = (A - Bs) + ((Bs - R) + R) := by ring
  have htri : ‖A‖ ≤ ‖A - Bs‖ + (‖Bs - R‖ + ‖R‖) := by
    calc ‖A‖ = ‖(A - Bs) + ((Bs - R) + R)‖ := by rw [← hid]
      _ ≤ ‖A - Bs‖ + ‖(Bs - R) + R‖ := norm_add_le _ _
      _ ≤ ‖A - Bs‖ + (‖Bs - R‖ + ‖R‖) := by
          linarith [norm_add_le (Bs - R) R]
  -- the `E`-error, reduced to the `D·k·loglog k/log k` shape
  have hlogpow : Real.log (Real.log (k : ℝ) ^ 4) = 4 * Real.log (Real.log (k : ℝ)) := by
    rw [Real.log_pow]; norm_num
  have hlogLk0 : (0 : ℝ) ≤ Real.log (Real.log (k : ℝ)) := Real.log_nonneg hLk1
  have hu0 : (0 : ℝ) < (k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)) := by linarith
  have hulogb : Real.log (k : ℝ) ≤ Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) :=
    Real.log_le_log hk0 (by linarith)
  have huq : ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
        / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
      ≤ 2 * (k : ℝ) / Real.log (k : ℝ) := by
    rw [div_le_div_iff₀ (by linarith) hLk0]
    nlinarith
  have hEle : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
          / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
        * Real.log (Real.log (k : ℝ) ^ 4)
      + C_R * ((k : ℝ) / Real.log (k : ℝ)) * Real.log (Real.log (k : ℝ) ^ 4)
      ≤ (8 * C_E + 4 * C_R)
          * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
    rw [hlogpow]
    have h1 : C_E * (((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ)))
            / Real.log ((k : ℝ) + (k : ℝ) / Real.sqrt (Real.log (k : ℝ))))
          * (4 * Real.log (Real.log (k : ℝ)))
        ≤ C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ))) := by
      have hq : (0 : ℝ) ≤ 4 * Real.log (Real.log (k : ℝ)) := by linarith
      have := mul_le_mul_of_nonneg_left huq hCE0
      exact mul_le_mul_of_nonneg_right this hq
    have h2 : C_E * (2 * (k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
          + C_R * ((k : ℝ) / Real.log (k : ℝ)) * (4 * Real.log (Real.log (k : ℝ)))
        = (8 * C_E + 4 * C_R)
            * ((k : ℝ) * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) := by
      field_simp
      ring
    linarith
  -- the grade page
  have hgrade := center_error_grade_A (D := 8 * C_E + 4 * C_R) (X := X) (k := k)
    (by positivity) hX8 hk1 hk2 (hB X hXB)
  have hexpand : (B + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * (k : ℝ)
      = B * (k : ℝ) + 4 * ((k : ℝ) * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by ring
  rw [hexpand]
  linarith

/-! ## §2 (E-1a) — the `prop21RHS` socket at a free `c`, window floor, far arm at `T*` -/

/-- **THE CASE-A EXIT CONSTANT.**  `S = caseAS c Cb M W`: the `c`-generic grade at the floor
`M`, plus the far arm at the truncation height `T*` (additive, `FarStar.hfar_star`), plus the
centre supply's own desmooth/`E` error — all at the window bottom `W` (the SHIFTED scale).

At `c = 1/e` and `M = (1/32 − θ)·loglog W` the first term is `gradeAbsConstC·(log W)^{−ρ}`,
`ρ = (1/32 − θ)/e = 3θ` (`caseA_grade_numeral`), and it dominates: the far exponent
`1/(32e) ≈ 0.0115` and `1/2 − 1/1000` are both larger than `ρ₂₉₃ ≈ 0.0102`, so the exit is
`(log W)^{−ρ_eff}`-shaped with a constant, as ⟦V5⟧ requires. -/
def caseAS (c Cb M W : ℝ) : ℝ :=
  gradeAbsConstC c Cb * Real.exp (-c * M)
    + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))
    + 4 * Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000)

lemma caseAS_nonneg {c Cb M W : ℝ} (hc1 : 2 * c < 1) (hCb0 : 0 ≤ Cb) (hW : 1 ≤ W) :
    0 ≤ caseAS c Cb M W := by
  have h1 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
  have hlogW : (0 : ℝ) ≤ Real.log W := Real.log_nonneg hW
  have h2 : (0 : ℝ) ≤ farCStar := farCStar_nonneg
  have h3 : (0 : ℝ) ≤ Real.log W ^ (-(1 / (32 * Real.exp 1))) := Real.rpow_nonneg hlogW _
  have h4 : (0 : ℝ) ≤ Real.log W ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hlogW _
  have h5 : (0 : ℝ) ≤ Real.exp (-c * M) := (Real.exp_pos _).le
  unfold caseAS
  have h6 : (0 : ℝ) ≤ gradeAbsConstC c Cb * Real.exp (-c * M) := mul_nonneg h1 h5
  have h7 : (0 : ℝ) ≤ farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1))) := mul_nonneg h2 h3
  linarith

/-- **E-1a — THE `prop21RHS` SOCKET AT A FREE `c`, IN WINDOW-FLOOR FORM**
(`caseA_rhs_socket`).  `GradeWindowC.rhs_grade_at_scale_windowC` at the damped datum
`g_x = gxDatum g P Q x`, with

* the integrability bundle from `GradeWindowC.jointIntegrableAtC_pin_free` (no `c`-gate, only
  `e^{64} ≤ k`),
* the far `supF` binder from `FarClose.far_supF_bound` (`Ffar := farFbound (log k)`, the free
  `M = 0` majorant),
* the far kernel binder from `FarStar.far_kernel_bound_star` at `T := T*(k, log k)`,
* and the far REMAINDER priced by `FarStar.hfar_star` — ADDITIVELY, never absorbed —

so that the two-term exit of the window-floor grade collapses into the supply's own binder
shape `‖prop21RHS‖ ≤ B·k` with `B` scale-free.

The floor binder is the window one alone, at the contour's own centre `τ`:
`hMwin : ∀ v, |v − τ| ≤ T*(k, log k) → M ≤ 𝔻²(ℓ(g_x·p^{−iτ}), p^{i(v−τ)}; k)`.

`hW2k : W ≤ 2k` is `hfar_star`'s own scale relation (free on the window: `W ≤ ⌊W⌋₊ + 1 ≤ k+1`),
and `W` is the SHIFTED scale — the far numeral is `(log W)^{−1/(32e)}`, not `(log X)^{…}`. -/
theorem caseA_rhs_socket {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (P Q : ℕ)
    {c Cb x τ W M : ℝ} {k : ℕ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1) (hc1 : 2 * c < 1)
    (hCb0 : 0 ≤ Cb) (hCbound : ShortIntervalDatum Cb)
    (hk : Real.exp 64 ≤ (k : ℝ)) (hWe : Real.exp 1 ≤ W) (hW2k : W ≤ 2 * (k : ℝ))
    (hM0 : 0 ≤ M)
    (hMwin : ∀ v : ℝ, |v - τ| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
      M ≤ pretDistSq (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * Complex.I)))
        (costwist (v - τ)) (k : ℝ)) :
    ‖prop21RHS (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * Complex.I)) τ (k : ℝ)
        ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
        (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
      ≤ (gradeAbsConstC c Cb * Real.exp (-c * M)
          + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ) := by
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx0 hx1 hg p hp
  have hgtw : ∀ p : ℕ, p.Prime →
      ‖(fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * Complex.I)) p‖ ≤ 1 := by
    intro p hp
    simp only
    rw [norm_mul, norm_twist τ hp.one_lt.le, mul_one]
    exact hgx p hp
  have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk
  have hk3 : Real.exp 3 ≤ (k : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hk
  have hL64 : (64 : ℝ) ≤ Real.log (k : ℝ) := by
    rw [← Real.log_exp 64]; exact Real.log_le_log (Real.exp_pos 64) hk
  have hL0 : (0 : ℝ) < Real.log (k : ℝ) := by linarith
  -- the window-floor grade at a free `c`, far arm carried additively
  have hmain := rhs_grade_at_scale_windowC (g := gxDatum g P Q x) (c := c) (Cb := Cb)
    (t₀' := τ) (M := M) (k := (k : ℝ)) (L := Real.log (k : ℝ))
    (c₀ := 1 + 1 / Real.log (k : ℝ)) (y := Real.log (k : ℝ) ^ 4)
    (η := 1 / Real.log (Real.log (k : ℝ) ^ 4))
    (h := (k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (T := Tstar (k : ℝ) (Real.log (k : ℝ)))
    (Ffar := farFbound (Real.log (k : ℝ)))
    (Kfar := farKfarStar (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(τ : ℂ) * Complex.I))
      (k : ℝ) (Real.log (k : ℝ)))
    hgx hc0 hce hc1 hCb0 hCbound hk rfl rfl rfl rfl rfl hM0 hMwin
    (farFbound_nonneg hL0.le) (far_supF_bound hgx hk3 rfl rfl rfl rfl)
    (far_kernel_bound_star hk rfl rfl rfl rfl)
    (jointIntegrableAtC_pin_free hgx c τ M hk)
  -- the far remainder, priced at `T*` and at the SHIFTED scale `W`
  have hfar := hfar_star hgtw hk (L := Real.log (k : ℝ)) rfl rfl rfl hWe hW2k
  have hring : (gradeAbsConstC c Cb * Real.exp (-c * M)
        + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ)
      = gradeAbsConstC c Cb * (k : ℝ) * Real.exp (-c * M)
        + farCStar * (k : ℝ) * Real.log W ^ (-(1 / (32 * Real.exp 1))) := by ring
  rw [hring]
  linarith

/-! ## §3 (E-1b) — the partial-sum supply at the damped datum, UNIFORM IN `x` -/

/-- At the centre `t₀ = 0` the seam coefficient is the bare datum (on `n ≥ 1`, which is all the
partial sum sees).  This is how CASE A consumes the supply: `t₀ := 0`, `t₁ := t`. -/
lemma sum_seamCoeff_zero_center (f : ℕ → ℂ) (t : ℝ) (k : ℕ) :
    (∑ n ∈ Finset.Icc 1 k, seamCoeff f (fun _ => 1) 0 n * eIu (-t) n)
      = ∑ n ∈ Finset.Icc 1 k, f n * eIu (-t) n := by
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : n ≠ 0 := by omega
  rw [seamCoeff, if_neg hn0]
  simp

/-- **E-1b — THE CASE-A PARTIAL-SUM SUPPLY** (`caseA_partial_supply`).  §1 ∘ §2: under the
window floor, the twisted partial sums of the DAMPED datum are linear with the CASE-A constant,

  `‖∑_{n≤k} ℓ(g_x)(n)·n^{−it}‖ ≤ caseAS c Cb M W · k`,   `⌊W⌋₊ ≤ k ≤ N`,

**uniformly over the damping parameter `x ∈ [0,1]`** — which is what the `[0,1]` average of
§4 consumes, and which is why §1's datum-uniform hoisting is needed.

**THE `hMwin` BINDER, verbatim** (CASE A's defining hypothesis; one binder, stated at once over
the damping parameter, the window scales and the contour window):

  `∀ x ∈ Icc 0 1, ∀ k, ⌊W⌋₊ ≤ k → k ≤ N → ∀ v, |v − t| ≤ T*(k, log k) →`
  `  M ≤ 𝔻²(ℓ(g_x · p^{−it}), p^{i(v−t)}; k)`.

Every constant on the exit is `x`-free and `k`-free.  `W` is the SHIFTED scale: the two
threshold gates `X₀ ≤ W` and the scale gate `hk64` are stated there (law #253). -/
theorem caseA_partial_supply :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) → ∀ (P Q : ℕ) (c Cb t W M : ℝ) (N : ℕ),
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ W → Real.exp 1 ≤ W → W ≤ (N : ℝ) → (N : ℝ) ≤ 2 * W →
        (∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N → Real.exp 64 ≤ (k : ℝ)) → 0 ≤ M →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
          ∀ v : ℝ, |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
            M ≤ pretDistSq
                (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * Complex.I)))
                (costwist (v - t)) (k : ℝ)) →
        ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
          ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
            ≤ caseAS c Cb M W * (k : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := center_halasz_supply_A
  refine ⟨max X₀ (Real.exp 1), lt_of_lt_of_le hX₀0 (le_max_left _ _), ?_⟩
  intro g hg P Q c Cb t W M N hc0 hce hc1 hCb0 hCbound hWlb hWe hWN hN2 hk64 hM0 hMwin x hx
  have hX₀W : X₀ ≤ W := le_trans (le_max_left _ _) hWlb
  have hW1 : (1 : ℝ) ≤ W := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hgx : ∀ p : ℕ, p.Prime → ‖gxDatum g P Q x p‖ ≤ 1 :=
    fun p hp => gxDatum_norm_le_one hx.1 hx.2 hg p hp
  -- the far/grade constant is nonneg
  have hB0 : (0 : ℝ) ≤ gradeAbsConstC c Cb * Real.exp (-c * M)
      + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1))) := by
    have h1 : (0 : ℝ) ≤ gradeAbsConstC c Cb := gradeAbsConstC_nonneg hc1 hCb0
    have h2 : (0 : ℝ) ≤ Real.log W ^ (-(1 / (32 * Real.exp 1))) :=
      Real.rpow_nonneg (Real.log_nonneg hW1) _
    have h3 : (0 : ℝ) ≤ farCStar := farCStar_nonneg
    have h4 : (0 : ℝ) ≤ Real.exp (-c * M) := (Real.exp_pos _).le
    nlinarith
  -- the `hRHS` binder: §2 at each scale of the window
  have hRHS : ∀ k : ℕ, ⌊W⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => gxDatum g P Q x p
            * (p : ℂ) ^ (-((0 + t : ℝ) : ℂ) * Complex.I)) (0 + t)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (Real.log (k : ℝ) ^ 4) (1 / Real.log (Real.log (k : ℝ) ^ 4))‖
        ≤ (gradeAbsConstC c Cb * Real.exp (-c * M)
            + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))) * (k : ℝ) := by
    intro k hk1 hk2
    have hk := hk64 k hk1 hk2
    have hk0 : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk
    have hk1R : (1 : ℝ) ≤ (k : ℝ) := by
      have h65 : (65 : ℝ) ≤ (k : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
      linarith
    have hW2k : W ≤ 2 * (k : ℝ) := by
      have h1 : W < (⌊W⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one W
      have h2 : ((⌊W⌋₊ : ℕ) : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk1
      linarith
    simp only [zero_add]
    exact caseA_rhs_socket hg P Q hx.1 hx.2 hc0 hce hc1 hCb0 hCbound hk hWe hW2k hM0
      (hMwin x hx k hk1 hk2)
  -- the supply, at `t₀ = 0`, `t₁ = t`, at the damped datum
  have hsup := hsupply (gxDatum g P Q x) hgx 0 t W N
    (gradeAbsConstC c Cb * Real.exp (-c * M)
      + farCStar * Real.log W ^ (-(1 / (32 * Real.exp 1)))) hX₀W hWN hN2 hB0 hRHS
  intro k hk1 hk2
  have h := hsup k hk1 hk2
  rw [sum_seamCoeff_zero_center] at h
  refine h.trans (le_of_eq ?_)
  unfold caseAS
  ring

/-! ## §4 (E-2) — the window split, the `[0,1]` average, and the Abel bridge -/

/-- **E-2a — the damped co-factor partial sums.**  The co-factor coefficient is supported in
the window `(k₀, M]`, where it IS `ℓ(g_x)` (`CofactorBall.ramRdampCoeff_ellLin`), so its
twisted partial sum is the DIFFERENCE of two of the supply's
(`CofactorBall.spolyA_window_split`) — the factor `2` of the exit.

The window binders are `CofactorBall`'s own (`hk₀lo/hk₀hi`, `hhigh`, `hMN`); nothing here
touches the half-open endpoint, which `ramR_abel_sup` owns. -/
theorem caseA_damped_partial {g : ℕ → ℂ}
    {H : ℝ} {N Xn P Q j M k₀ : ℕ} {x t S : ℝ}
    (hS0 : 0 ≤ S) (hMN : M ≤ N) (hk₀M : k₀ ≤ M)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1))
    (hsup : ∀ k : ℕ, k₀ ≤ k → k ≤ M →
      ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖ ≤ S * (k : ℝ)) :
    ∀ m : ℕ, m ≤ M →
      ‖spolyA (ramRdampCoeff H N Xn P Q j (ellLin g) x) t m‖ ≤ 2 * S * (m : ℝ) := by
  have hMtop2 : (M : ℝ) ≤ 2 * ramRbot H Xn j := by linarith
  have hsupp : ∀ n : ℕ, n ≤ k₀ → ramRdampCoeff H N Xn P Q j (ellLin g) x n = 0 := by
    intro n hn
    have hlt : (n : ℝ) < ramRbot H Xn j := by
      have : (n : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hn
      linarith
    rw [ramRdampCoeff, if_neg (notMem_ramRrange_of_lt hlt)]
  have hDatum : ∀ n : ℕ, k₀ < n → n ≤ M →
      ramRdampCoeff H N Xn P Q j (ellLin g) x n = ellLin (gxDatum g P Q x) n := by
    intro n hn1 hn2
    have hmem : n ∈ ramRrange H N Xn j := by
      have hnk : (k₀ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn1
      have hnM : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn2
      rw [ramRrange, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, le_trans hn2 hMN⟩, ?_, ?_⟩
      · have : ramRbot H Xn j ≤ (n : ℝ) := by linarith
        rwa [ramRbot] at this
      · have : (n : ℝ) ≤ 2 * ramRbot H Xn j := le_trans hnM hMtop2
        rw [ramRbot] at this
        linarith
    rw [ramRdampCoeff_ellLin, if_pos hmem]
  intro m hm
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rcases le_or_gt m k₀ with hcase | hcase
  · -- below the cut the polynomial is empty
    have hz : spolyA (ramRdampCoeff H N Xn P Q j (ellLin g) x) t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero (fun n hn => ?_)
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      rw [hsupp n (le_trans hnm hcase), zero_div]
    rw [hz, norm_zero]
    exact mul_nonneg (by linarith) hm0
  · have hkm : k₀ ≤ m := hcase.le
    have hk₀m : (k₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
    have hsplit := spolyA_window_split hsupp hDatum t hkm hm
    have h1 := hsup m hkm hm
    have h2 := hsup k₀ le_rfl hk₀M
    rw [hsplit]
    calc ‖(∑ n ∈ Finset.Icc 1 m, ellLin (gxDatum g P Q x) n * eIu (-t) n)
            - ∑ n ∈ Finset.Icc 1 k₀, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, ellLin (gxDatum g P Q x) n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 k₀, ellLin (gxDatum g P Q x) n * eIu (-t) n‖ :=
          norm_sub_le _ _
      _ ≤ S * (m : ℝ) + S * (k₀ : ℝ) := add_le_add h1 h2
      _ ≤ 2 * S * (m : ℝ) := by nlinarith

/-- **E-2b — THE CASE-A `ramR` BOUND FROM THE SUPPLY** (`caseA_ramR_of_supplied`).  The
`[0,1]` average (`CofactorBall.spolyA_ramRcoeff_le_of_damp`, free: the unit interval has
length `1`) and the Abel bridge (`RamRAdapter.ramR_abel_sup`, factor `3 = 2 + 1`):

  `‖R_{j,H}(1+it)‖ ≤ 3·(2S) = 6S`.

`hend : 2/X_j ≤ 2S` is the half-open endpoint charge, free in the regime
(`X_j` is a power of `X`, `S ≍ (log X)^{−ρ}`). -/
theorem caseA_ramR_of_supplied {g : ℕ → ℂ} (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    {H : ℝ} {N Xn P Q j M k₀ : ℕ} {t S : ℝ}
    (hS0 : 0 ≤ S) (hMN : M ≤ N) (hk₀M : k₀ ≤ M)
    (hk₀lo : (k₀ : ℝ) < ramRbot H Xn j) (hk₀hi : ramRbot H Xn j ≤ (k₀ : ℝ) + 1)
    (hbot : 1 < ramRbot H Xn j) (hlow : ramRbot H Xn j - 1 ≤ (M : ℝ))
    (hhigh : (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1)) (hMtop : 2 * ramRbot H Xn j < (M : ℝ) + 3)
    (hend : 2 / ramRbot H Xn j ≤ 2 * S)
    (hsup : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, k₀ ≤ k → k ≤ M →
      ‖∑ n ∈ Finset.Icc 1 k, ellLin (gxDatum g P Q x) n * eIu (-t) n‖ ≤ S * (k : ℝ)) :
    ‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 6 * S := by
  have habel : ‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 3 * (2 * S) := by
    refine ramR_abel_sup (fun n => ellLin_norm_le_one g hg n) hbot hlow hhigh hMtop hend ?_
    intro m hm
    refine spolyA_ramRcoeff_le_of_damp ?_
    intro x hx
    exact caseA_damped_partial hS0 hMN hk₀M hk₀lo hk₀hi hhigh (hsup x hx) m hm
  linarith

/-! ## §5 (E-3) — THE CASE-A `Rbd`, and the numeral instance -/

/-- **E-3 — THE CASE-A `Rbd`** (`caseA_ramR_bound`).  What is assumed is exactly the CASE-A
hypothesis — the window floor `M` for the damped datum at every damping parameter `x ∈ [0,1]`
and every scale of the co-factor window — and what comes out is `USetThinTL.tL_main_sumsq`'s
`Rbd` binder

  `‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 6·caseAS c Cb M (k₀ : ℝ)`.

Nonnegativity of the `Rbd` (the other half of `tL_main_sumsq`'s socket) is `caseAS_nonneg`.

**The carried hypotheses, ENUMERATED** (this is the whole list):
1. `hg` — the primes' norm bound on the row's datum;
2. the `c`-contract `0 < c`, `c ≤ 1/e`, `2c < 1` (at `c = 1/e` all three hold);
3. `0 ≤ Cb` and `ShortIntervalDatum Cb` — the amplitude side's short-interval datum;
4. **THE SCALE-DESCENT GATES** (law #253): `X₀ ≤ (k₀ : ℝ)` (the supply's threshold AT THE
   SHIFTED SCALE) and `e^{64} ≤ (k₀ : ℝ)` (the corpus scale gate, likewise).  The `j/H`
   numeral that turns these into a condition on `j` is U7-F's and is NOT resolved here;
5. the co-factor window geometry `hMN`, `hk₀lo`, `hk₀hi`, `hbot`, `hlow`, `hhigh`, `hMtop` —
   `CofactorBall.caseB_window_geometry` builds the last five from `4 ≤ X_j`, and
   `CofactorBall.exists_window_cut` the cut;
6. `hM0 : 0 ≤ M` and the endpoint charge `hend : 2/X_j ≤ 2·caseAS …`;
7. `hMwin` — CASE A's defining hypothesis, in the one binder of `caseA_partial_supply`; its
   own scale descent (`loglog X ↝ loglog X_j`) is the consumer's, as in `CofactorBall`.

Gone versus the seam original: `hmin`, `hgate`, `hMt`, the annulus geometry, the seam radius —
`GradeWindowC`'s window-floor form carries none of them. -/
theorem caseA_ramR_bound :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (c Cb t Mfl : ℝ),
        -- the `c`-contract
        0 < c → c ≤ 1 / Real.exp 1 → 2 * c < 1 → 0 ≤ Cb → ShortIntervalDatum Cb →
        -- THE SCALE-DESCENT GATES, at the SHIFTED scale
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) →
        -- the co-factor window geometry
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        -- the floor value and the half-open endpoint charge
        0 ≤ Mfl → 2 / ramRbot H Xn j ≤ 2 * caseAS c Cb Mfl (k₀ : ℝ) →
        -- CASE A: THE WINDOW FLOOR, uniform over the damping parameter and the window
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, k₀ ≤ k → k ≤ M →
          ∀ v : ℝ, |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
            Mfl ≤ pretDistSq
                (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * Complex.I)))
                (costwist (v - t)) (k : ℝ)) →
        ‖ramR H N Xn P Q j (ellLin g) t‖ ≤ 6 * caseAS c Cb Mfl (k₀ : ℝ) := by
  obtain ⟨X₀, hX₀0, hsupply⟩ := caseA_partial_supply
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg H N Xn P Q j M k₀ c Cb t Mfl hc0 hce hc1 hCb0 hCbound hX₀k hk₀64 hMN hk₀lo hk₀hi
    hbot hlow hhigh hMtop hM0 hend hMwin
  -- the window arithmetic: `k₀ ≥ 3`, `k₀ ≤ M ≤ 2k₀`
  have hk₀0 : (0 : ℝ) < (k₀ : ℝ) := lt_of_lt_of_le (Real.exp_pos 64) hk₀64
  have hk₀3 : (3 : ℝ) ≤ (k₀ : ℝ) := by
    have h65 : (65 : ℝ) ≤ (k₀ : ℝ) := by linarith [Real.add_one_le_exp (64 : ℝ)]
    linarith
  have hk₀e : Real.exp 1 ≤ (k₀ : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hk₀64
  have hk₀MR : (k₀ : ℝ) ≤ (M : ℝ) := by linarith
  have hk₀M : k₀ ≤ M := by exact_mod_cast hk₀MR
  have hM2k₀ : (M : ℝ) ≤ 2 * (k₀ : ℝ) := by linarith
  have hfl : ⌊((k₀ : ℕ) : ℝ)⌋₊ = k₀ := Nat.floor_natCast k₀
  -- the scale gate on the window: `e^{64} ≤ k₀ ≤ k`
  have hk64 : ∀ k : ℕ, ⌊((k₀ : ℕ) : ℝ)⌋₊ ≤ k → k ≤ M → Real.exp 64 ≤ (k : ℝ) := by
    intro k hk1 _
    rw [hfl] at hk1
    have : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    linarith
  -- the floor binder, transported to the supply's `⌊·⌋₊` frame
  have hMwin' : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, ⌊((k₀ : ℕ) : ℝ)⌋₊ ≤ k → k ≤ M →
      ∀ v : ℝ, |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
        Mfl ≤ pretDistSq
            (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * Complex.I)))
            (costwist (v - t)) (k : ℝ) := by
    intro x hx k hk1 hk2
    rw [hfl] at hk1
    exact hMwin x hx k hk1 hk2
  -- the supply at the shifted scale `W := k₀`, dyadic length `N := M`
  have hsup := hsupply g hg P Q c Cb t (k₀ : ℝ) Mfl M hc0 hce hc1 hCb0 hCbound hX₀k hk₀e
    hk₀MR hM2k₀ hk64 hM0 hMwin'
  refine caseA_ramR_of_supplied hg (caseAS_nonneg hc1 hCb0 (by linarith)) hMN hk₀M hk₀lo
    hk₀hi hbot hlow hhigh hMtop hend ?_
  intro x hx k hk1 hk2
  exact hsup x hx k (by rw [hfl]; exact hk1) hk2

/-! ### The numeral instance: `c = 1/e`, `M = (1/32 − θ₂₉₃)·loglog W` -/

/-- **THE GRADE NUMERAL** (`caseA_grade_numeral`).  At `c = 1/e` and the CASE-A floor
`M = (1/32 − θ)·loglog W` the grade factor IS the `(log W)^{−ρ}` of the ⟦V5⟧ pin:

  `e^{−(1/e)·(1/32 − θ₂₉₃)·loglog W} = (log W)^{−ρ₂₉₃}`,  `ρ₂₉₃ = 3θ₂₉₃`.

The identity is `CofactorDist.balance_exponent_293` (`ρ = (1/32 − θ)/e`) read through
`Real.rpow_def_of_pos`; nothing is estimated. -/
theorem caseA_grade_numeral {W : ℝ} (hW : Real.exp 1 ≤ W) :
    Real.exp (-(1 / Real.exp 1) * ((1 / 32 - theta293) * Real.log (Real.log W)))
      = Real.log W ^ (-rho293) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le (Real.exp_pos 1) hW
  have hlogW1 : (1 : ℝ) ≤ Real.log W := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hW
  have hlogW0 : (0 : ℝ) < Real.log W := by linarith
  rw [Real.rpow_def_of_pos hlogW0, balance_exponent_293]
  congr 1
  field_simp

/-- **E-3, THE NUMERAL INSTANCE** (`caseA_ramR_bound_293`).  `caseA_ramR_bound` at the ⟦V5⟧
pin: the exponent `c = 1/e` (where the `c`-contract's three gates pass — `0 < 1/e`,
`1/e ≤ 1/e`, `2/e < 1`) and the CASE-A floor `M = (1/32 − θ₂₉₃)·loglog W` at the SHIFTED scale
`W = k₀`.  The exit is the `(log W)^{−ρ_eff}` shape, `ρ_eff = ρ₂₉₃ = 3θ₂₉₃`:

  `‖ramR‖ ≤ 6·(C₁(1/e, Cb)·(log k₀)^{−ρ₂₉₃} + farCStar·(log k₀)^{−1/(32e)}
              + 4·(log k₀)^{−1/2+1/1000})`.

Both additive terms have LARGER exponents than `ρ₂₉₃ ≈ 0.01024` (`1/(32e) ≈ 0.01150` and
`0.499`), so the leading behaviour is `(log k₀)^{−ρ₂₉₃}` exactly as ⟦V5⟧'s ladder requires;
the comparison of the three numerals is arithmetic and is left to U7-F, which owns the
`X ↝ X_j` descent that turns `(log k₀)^{−ρ}` into `(log X)^{−ρ_eff}`. -/
theorem caseA_ramR_bound_293 :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (g : ℕ → ℂ), (∀ p, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (H : ℝ) (N Xn P Q j M k₀ : ℕ) (Cb t : ℝ),
        0 ≤ Cb → ShortIntervalDatum Cb →
        X₀ ≤ (k₀ : ℝ) → Real.exp 64 ≤ (k₀ : ℝ) →
        M ≤ N → (k₀ : ℝ) < ramRbot H Xn j → ramRbot H Xn j ≤ (k₀ : ℝ) + 1 →
        1 < ramRbot H Xn j → ramRbot H Xn j - 1 ≤ (M : ℝ) →
        (M : ℝ) ≤ 2 * (ramRbot H Xn j - 1) → 2 * ramRbot H Xn j < (M : ℝ) + 3 →
        2 / ramRbot H Xn j ≤ 2 * (gradeAbsConstC (1 / Real.exp 1) Cb
            * Real.log (k₀ : ℝ) ^ (-rho293)
          + farCStar * Real.log (k₀ : ℝ) ^ (-(1 / (32 * Real.exp 1)))
          + 4 * Real.log (k₀ : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)) →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ k : ℕ, k₀ ≤ k → k ≤ M →
          ∀ v : ℝ, |v - t| ≤ Tstar (k : ℝ) (Real.log (k : ℝ)) →
            (1 / 32 - theta293) * Real.log (Real.log (k₀ : ℝ))
              ≤ pretDistSq
                (ellLin (fun q => gxDatum g P Q x q * (q : ℂ) ^ (-(t : ℂ) * Complex.I)))
                (costwist (v - t)) (k : ℝ)) →
        ‖ramR H N Xn P Q j (ellLin g) t‖
          ≤ 6 * (gradeAbsConstC (1 / Real.exp 1) Cb * Real.log (k₀ : ℝ) ^ (-rho293)
            + farCStar * Real.log (k₀ : ℝ) ^ (-(1 / (32 * Real.exp 1)))
            + 4 * Real.log (k₀ : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000)) := by
  obtain ⟨X₀, hX₀0, hmain⟩ := caseA_ramR_bound
  refine ⟨X₀, hX₀0, ?_⟩
  intro g hg H N Xn P Q j M k₀ Cb t hCb0 hCbound hX₀k hk₀64 hMN hk₀lo hk₀hi hbot hlow hhigh
    hMtop hend hMwin
  -- the `c`-contract at `c = 1/e`
  have he2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hc1 : 2 * (1 / Real.exp 1) < 1 := by
    rw [show 2 * (1 / Real.exp 1) = 2 / Real.exp 1 from by ring,
      div_lt_one (Real.exp_pos 1)]
    exact he2
  -- the floor value and its numeral
  have hk₀e : Real.exp 1 ≤ (k₀ : ℝ) :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hk₀64
  have hlogk1 : (1 : ℝ) ≤ Real.log (k₀ : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hk₀e
  have hloglog0 : (0 : ℝ) ≤ Real.log (Real.log (k₀ : ℝ)) := Real.log_nonneg hlogk1
  have hθ : theta293 < 1 / 32 := theta293_lt_one_div_32
  have hM0 : (0 : ℝ) ≤ (1 / 32 - theta293) * Real.log (Real.log (k₀ : ℝ)) :=
    mul_nonneg (by linarith) hloglog0
  have hnum := caseA_grade_numeral hk₀e
  have hSeq : caseAS (1 / Real.exp 1) Cb
        ((1 / 32 - theta293) * Real.log (Real.log (k₀ : ℝ))) (k₀ : ℝ)
      = gradeAbsConstC (1 / Real.exp 1) Cb * Real.log (k₀ : ℝ) ^ (-rho293)
        + farCStar * Real.log (k₀ : ℝ) ^ (-(1 / (32 * Real.exp 1)))
        + 4 * Real.log (k₀ : ℝ) ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    unfold caseAS
    rw [hnum]
  have h := hmain g hg H N Xn P Q j M k₀ (1 / Real.exp 1) Cb t
    ((1 / 32 - theta293) * Real.log (Real.log (k₀ : ℝ)))
    hc0 le_rfl hc1 hCb0 hCbound hX₀k hk₀64 hMN hk₀lo hk₀hi hbot hlow hhigh hMtop hM0
    (by rw [hSeq]; exact hend) hMwin
  rwa [hSeq] at h

end Salt.MR
