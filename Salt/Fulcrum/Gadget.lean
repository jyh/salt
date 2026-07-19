/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SiegelTwin
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Data.Fintype.Lattice

/-!
# The compactness gadget — Siegel zeros isolated below `1` (FULCRUM)

Design: `docs/exploration/fulcrum-pass1.md` (refuter R2, load-bearing twice),
`docs/exploration/fulcrum_audit_glue.md`.

This module lands the **compactness gadget**: from finitely many characters of
modulus `≤ Q`, the real zeros of their `L`-functions are isolated away from `1`,
uniformly over the (finite) family. Two consequences:

* `siegel_zeros_isolated_below` — for every `Q` there is a `c > 0` with **no**
  real zero `β ∈ (1 − c, 1)` for any primitive quadratic `χ ≠ 1` of modulus
  `q ≤ Q`. (The additive-gap "isolation" form.)
* `imsz_gives_fulcrum_witnesses` — `InfinitelyManySiegelZeros → ∀ C > 0,
  FulcrumQualityMin C` (stated in unfolded form; **defeq** to
  `∀ C, 0 < C → FulcrumQualityMin C`). The `∀c` binder of IMSZ is consumed by
  choosing `c` below both the isolation radius (forcing `q > Q`) and `1/C`
  (delivering the fulcrum ball).

## The route (CHEAP BALL, not the identity theorem)

The per-character isolation uses only the landed corpus facts:
`DirichletCharacter.LFunction_apply_one_ne_zero` (`L(χ,1) ≠ 0` for `χ ≠ 1`) and
`DirichletCharacter.differentiableAt_LFunction` (hence continuity at `1`). A
continuous function nonzero at `1` is nonzero on a neighborhood — that ball is
the isolation. No discreteness-of-zeros / identity-theorem machinery is needed:
isolation only needs *some* ball, not the optimal one. The finite family
(`Finite (DirichletCharacter ℂ q)` via `MulChar.finite`, and induction on `Q`)
gives a uniform radius.
-/

open Complex DirichletCharacter Salt.TwinBar

namespace Salt.Fulcrum

/-- **Per-character isolation** (the analytic core, CHEAP-BALL route). For a
nontrivial Dirichlet character `χ` mod `q`, `L(·,χ)` is continuous at `1` and
nonzero there, so it is nonzero on a real interval `(1 − r, 1]`: every real zero
`β < 1` satisfies `β ≤ 1 − r`. -/
theorem isolation_char (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ β : ℝ, LFunction χ β = 0 → β < 1 → β ≤ 1 - r := by
  have h1 : LFunction χ 1 ≠ 0 := LFunction_apply_one_ne_zero hχ
  have hcont : ContinuousAt (LFunction χ) 1 :=
    (differentiableAt_LFunction χ 1 (Or.inr hχ)).continuousAt
  have hev : ∀ᶠ s in nhds (1 : ℂ), LFunction χ s ≠ 0 := hcont.eventually_ne h1
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε, hε, ?_⟩
  intro β hβ0 hβ1
  by_contra hcon
  rw [not_le] at hcon
  -- `hcon : 1 - ε < β`; then `dist ↑β 1 < ε`, so `L(χ,↑β) ≠ 0` — contradiction.
  have hdist : dist (↑β : ℂ) 1 < ε := by
    rw [Complex.dist_eq, show (↑β : ℂ) - 1 = ((β - 1 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  exact (hball hdist) hβ0

/-- **Single-modulus isolation**: a uniform `c > 0` over all characters mod `q`
(finite family via `MulChar.finite`). -/
theorem isolation_single (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧ ∀ (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → ∀ β : ℝ, LFunction χ β = 0 → β < 1 → β ≤ 1 - c := by
  haveI : Nonempty (DirichletCharacter ℂ q) := ⟨1⟩
  have hchoice : ∀ χ : DirichletCharacter ℂ q, ∃ r : ℝ, 0 < r ∧
      (χ ≠ 1 → ∀ β : ℝ, LFunction χ β = 0 → β < 1 → β ≤ 1 - r) := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨1, one_pos, fun h => absurd hχ h⟩
    · obtain ⟨r, hr, hprop⟩ := isolation_char q χ hχ
      exact ⟨r, hr, fun _ => hprop⟩
  choose f hf hfprop using hchoice
  obtain ⟨χ₀, hχ₀⟩ := Finite.exists_min f
  refine ⟨f χ₀, hf χ₀, ?_⟩
  intro χ hχ β hβ0 hβ1
  have hle : f χ₀ ≤ f χ := hχ₀ χ
  have := hfprop χ hχ β hβ0 hβ1
  linarith

/-- **The compactness gadget** (additive-gap "isolation" form): for every `Q`
there is a `c > 0` such that **no** primitive quadratic `χ ≠ 1` of modulus
`q ≤ Q` has a real zero `β` with `1 − c < β < 1`. Proven by induction on `Q`
(each new modulus contributes `isolation_single`; take the running min). -/
theorem siegel_zeros_isolated_below (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q ≤ Q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      ∀ β : ℝ, LFunction χ β = 0 → β < 1 → β ≤ 1 - c := by
  induction Q with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    intro q hq0 χ hq _ _ _ β _ _
    haveI := hq0
    have : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    omega
  | succ Q ih =>
    obtain ⟨c₀, hc₀, hprop₀⟩ := ih
    haveI : NeZero (Q + 1) := ⟨Nat.succ_ne_zero Q⟩
    obtain ⟨c₁, hc₁, hprop₁⟩ := isolation_single (Q + 1)
    refine ⟨min c₀ c₁, lt_min hc₀ hc₁, ?_⟩
    intro q hq0 χ hq hprim hsq hne β hβ0 hβ1
    haveI := hq0
    rcases Nat.lt_or_ge q (Q + 1) with hlt | hge
    · have hqQ : q ≤ Q := Nat.lt_succ_iff.mp hlt
      have hb := hprop₀ q χ hqQ hprim hsq hne β hβ0 hβ1
      have : min c₀ c₁ ≤ c₀ := min_le_left _ _
      linarith
    · have hqe : q = Q + 1 := le_antisymm hq hge
      subst hqe
      have hb := hprop₁ χ hne β hβ0 hβ1
      have : min c₀ c₁ ≤ c₁ := min_le_right _ _
      linarith

/-- **The fulcrum corollary**: `InfinitelyManySiegelZeros` delivers
`FulcrumQualityMin C` at every fixed `C > 0`. (Stated in unfolded form — defeq
to `∀ C, 0 < C → FulcrumQualityMin C`.) Given `Q` and `C`, choose the IMSZ
quality `c := min (c_iso · log 2) (1/C)`: the `c_iso · log 2` arm forces the
witness modulus `q > Q` (the gadget), the `1/C` arm places the real zero in the
fulcrum ball `‖1 − ρ‖ · (C · log q) ≤ 1` with `ρ := ↑β`. -/
theorem imsz_gives_fulcrum_witnesses (h : InfinitelyManySiegelZeros) :
    ∀ C : ℝ, 0 < C → ∀ Q : ℕ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), Q < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
      LFunction χ ρ = 0 ∧ ‖(1 : ℂ) - ρ‖ * (C * Real.log q) ≤ 1 := by
  intro C hC Q
  obtain ⟨c_iso, hc_iso, hiso⟩ := siegel_zeros_isolated_below Q
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := min (c_iso * Real.log 2) (1 / C) with hc_def
  have hc_pos : 0 < c := lt_min (mul_pos hc_iso hlog2) (by positivity)
  obtain ⟨q, hq0, χ, β, h1q, hprim, hsq, hne, hL, hqual, hβ1⟩ := h c hc_pos
  haveI := hq0
  have hq1R : (1 : ℝ) < (q : ℝ) := by exact_mod_cast h1q
  have hlogq : 0 < Real.log q := Real.log_pos hq1R
  have hlogne : Real.log q ≠ 0 := ne_of_gt hlogq
  -- Force `q > Q`: else the gadget bounds `β ≤ 1 − c_iso`, contradicting IMSZ.
  have hqQ : Q < q := by
    by_contra hle
    rw [not_lt] at hle
    have hiso' := hiso q χ hle hprim hsq hne β hL hβ1
    have hq2N : (2 : ℕ) ≤ q := by omega
    have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2N
    have hlog2q : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) hq2R
    have hkey : c_iso < c / Real.log q := by
      have h' : 1 - c / Real.log q < 1 - c_iso := lt_of_lt_of_le hqual hiso'
      linarith
    have hkey2 : c_iso * Real.log q < c := by
      have h' := mul_lt_mul_of_pos_right hkey hlogq
      rwa [div_mul_cancel₀ c hlogne] at h'
    have hc_le : c ≤ c_iso * Real.log 2 := min_le_left _ _
    have hmono : c_iso * Real.log 2 ≤ c_iso * Real.log q :=
      mul_le_mul_of_nonneg_left hlog2q hc_iso.le
    linarith
  -- The fulcrum ball at `ρ := ↑β`.
  refine ⟨q, hq0, χ, (↑β : ℂ), hqQ, hprim, hsq, hne, hL, ?_⟩
  have hnorm : ‖(1 : ℂ) - (↑β : ℂ)‖ = 1 - β := by
    rw [show (1 : ℂ) - (↑β : ℂ) = ((1 - β : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hnorm]
  have hc_le2 : c ≤ 1 / C := min_le_right _ _
  have hb : (1 - β) * Real.log q < c := by
    have h1 : 1 - β < c / Real.log q := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 hlogq
    rwa [div_mul_cancel₀ c hlogne] at h2
  have hcC : c * C ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hc_le2 hC.le
    rwa [one_div, inv_mul_cancel₀ (ne_of_gt hC)] at this
  have hexpand : (1 - β) * (C * Real.log q) = ((1 - β) * Real.log q) * C := by ring
  rw [hexpand]
  have hlt : ((1 - β) * Real.log q) * C < c * C := mul_lt_mul_of_pos_right hb hC
  linarith

end Salt.Fulcrum
