/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.HeadlineW2

/-!
# PACK-B — the ledger-side packaging rows at the operating point

Design: `docs/blueprints/flags.md`, the `2026-07-15 fin8c` scoping finding (the Step-3 gap
list) and the `2026-07-14 GLU-1` entry (the ledger discharge map).  This file packages the
five ledger-side rows that `normalized_package` (`Salt/Chen/GlueNormalized.lean`) and
`hledger_at_certs` (`Salt/Chen/RazorClose.lean`) consume, instantiated at the frozen operating
point (`opQ`/`opA`/`opZ`/`opY`/`opD`/`opP`/`opPs`, `Salt/Chen/HeadlineW2.lean`).

The five deliverables (each independently valuable).  LANDED here (clean packaging):

1. **`twinA1SieveW_W_eq`** — the `rfl` W-bridge `W(twinA1SieveW) = W(twinA1Sieve)` (the
   AP filter touches only `support`/`totalMass`; `W` sees `prodPrimes = P`, `nu = nuChen`),
   plus **`hWy_at_op`** — `W_ratio_upper` at the operating windows (`Wy ≤ Wz·ρ`, `ρ → 3/8`).
   Helper: **`opf_window_sdiff`** (the operating switch window is `primesInWindow (opZ x) (opY x)`).
4. **`XW_pos_at_op`** — `0 < X_W = totalMass·W` (window Λ-mass `> 0` via `lambda_mass_lower`,
   `W > 0` via `BrunLower.W_pos`).

DEFERRED (design-tier — genuine analytic work, NOT packaging; confirms the fin8c gap list):

2. **`hcount_at_op`** — a LARGE composition: `tripleSum_le_cbar_final` (whose exact-geometry
   `log zR = log x/8`, `log yR = log x/3` IS dischargeable at op via `zR = x^{1/8}`, `yR = x^{1/3}`
   + the floor brackets) → `/φ(Q)` (`tripleSumW_equidist_mertens`) → `∑Λ/φ(Q)` lower
   (`lambda_mass_lower`).  Blocker: bounding the Ifun/hbjs error sums + the `(1+O(1/log Lval))²`
   prefactors into an explicit `ecount`, AND the un-packaged rows `∀ p prime ∣ opQ → p < opZ x`,
   the `Lval` floors, `opQ ≤ (log Lval)^C` (with `opQ ≈ exp(2·10⁹)`, a finite but tower-scale x₀).
3. **`hcertA2_at_op`** — `A2grid_sharp_le` (A2Weighted:461) requires the EXACT geometry
   `log Dtot = 4·log z` with `Dtot, z : ℕ`.  At op `Dtot = opD x = ⌊x^{0.49991}⌋`, so
   `log(opD x) = 0.49991 log x ≠ 0.5 log x = 4·log(opZ x)` — a genuine mismatch (`A2weight`
   depends on `log Dtot − log t`).  Needs a perturbation-tolerant restatement with
   `log Dtot ≥ 4·log z` (or a monotonicity bridge to the ideal geometry).  `Cmass = 43/75`
   is landed (`A2massSum_le_final`).
5. **`hEbundle_at_op`** — the `1/200` split; assembled by `errorBundle_le` (GlueNormalized:210)
   from four shares.  `e4` (strip) is `x^{-1/8}`-small given `X_W`'s lower bound (composable from
   deliverable 4 + `W_twinA1_ge`), but `e2` (wtail) needs deliverable 3 and `e3` (count/W) needs
   deliverable 2 — so the bundle cannot close before 2 and 3.

No `sorry`, no `native_decide`, no new axioms.
-/

open Finset

namespace Salt.Chen

/-! ## Deliverable 1a — the `rfl` W-bridge for the AP-restricted `A₁` instance -/

/-- **`twinA1SieveW_W_eq`** — the density product `W` is blind to the AP restriction.
`W(twinA1SieveW Q a x P) = W(twinA1Sieve x P)` by `rfl`: `W` reads only `prodPrimes = P` and
`nu = nuChen`, both shared between the two instances (the `Q, a` filter touches only
`support`/`totalMass`).  Mirror of `switchSieveW_W_eq` (`Salt/Chen/SwitchW.lean`). -/
theorem twinA1SieveW_W_eq (Q a x P : ℕ) (hP : Squarefree P)
    (hPodd : ∀ p ∈ P.primeFactors, 3 ≤ p) :
    Salt.BrunLower.W (twinA1SieveW Q a x P hP hPodd)
      = Salt.BrunLower.W (twinA1Sieve x P hP hPodd) := rfl

/-! ## Deliverable 4 — the operating-point normalisation is positive

`X_W = totalMass(twinA1SieveW opQ opA x (opP x))·W(…)`.  `W > 0` always (`BrunLower.W_pos`);
`totalMass = (Σ_{n∈twinWindow x} Λ n)/φ(opQ) > 0` for large `x` (`lambda_mass_lower`: the window
Λ-mass exceeds `x/2 − 1 − 2K·x/log x`, which is positive once `log x ≥ 8K`). -/

/-- **`XW_pos_at_op`** — `0 < X_W` at the operating point.  The window Λ-mass is positive past
`x₁` (PNT lower bound minus `O(x/log x)`), `φ(opQ) > 0`, and `W > 0`. -/
theorem XW_pos_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    ∀ (hP : Squarefree (opP x)) (hPodd : ∀ p ∈ (opP x).primeFactors, 3 ≤ p),
    0 < (twinA1SieveW opQ opA x (opP x) hP hPodd).totalMass
          * Salt.BrunLower.W (twinA1SieveW opQ opA x (opP x) hP hPodd) := by
  obtain ⟨K, hK0, hmass⟩ := lambda_mass_lower
  -- threshold: log x ≥ max(8·K, 1) so that x/2 − 1 − 2K·x/log x > 0, and x ≥ 8
  obtain ⟨xL, hxL⟩ := a12_log_ge (max (8 * K) 1)
  refine ⟨max xL 8, fun x hx hP hPodd => ?_⟩
  have hx8 : 8 ≤ x := le_trans (le_max_right _ _) hx
  have hxL' : xL ≤ x := le_trans (le_max_left _ _) hx
  obtain ⟨hexp, hlog⟩ := hxL x hxL'
  have hlog8K : 8 * K ≤ Real.log x := le_trans (le_max_left _ _) hlog
  have hlog1 : (1 : ℝ) ≤ Real.log x := le_trans (le_max_right _ _) hlog
  have hlogpos : (0 : ℝ) < Real.log x := by linarith
  have hxR : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx8
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  -- the window Λ-mass is positive
  have hlow := hmass x hx8
  have hmasspos : 0 < ∑ n ∈ twinWindow x, ArithmeticFunction.vonMangoldt n := by
    have hkey : 2 * K * (x : ℝ) / Real.log x ≤ (x : ℝ) / 4 := by
      rw [div_le_div_iff₀ hlogpos (by norm_num)]
      nlinarith [hlog8K, hxpos]
    have : (x : ℝ) / 2 - 1 - 2 * K * (x : ℝ) / Real.log x > 0 := by
      have : (x : ℝ) / 2 - 1 - (x : ℝ) / 4 ≥ (8 : ℝ) / 4 - 1 := by
        have : (x : ℝ) / 4 ≥ 2 := by linarith
        linarith
      linarith
    linarith [hlow]
  -- totalMass = (Σ Λ)/φ(opQ) > 0, W > 0
  have hφ : (0 : ℝ) < (opQ.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr opf_Q_pos
  rw [twinA1SieveW_totalMass]
  apply mul_pos
  · exact div_pos hmasspos hφ
  · exact Salt.BrunLower.W_pos _

/-! ## Deliverable 1b — `hWy_at_op`: the `W`-ratio at the operating windows

`W_ratio_upper` (`Salt/Chen/WRatioSharp.lean`) instantiated at `P = opP x`, `Ps = opPs x`,
`zr = opZ x`, `yr = opY x`.  The window identity `opPs.primeFactors \ opP.primeFactors =
primesInWindow (opZ x) (opY x)` is `opf_window_sdiff`; the divisor nesting is `opf_PdvdPs`;
`38 ≤ log(opZ x)` comes from `w0R opEps ≤ opZ x` (`opf_tower`) with `log(w0R opEps) =
40/log(1+opEps) ≥ 38`.  The ratio `ρ = (log z/log y)(1 + 38/log z) → 3/8` at the tower. -/

/-- **`opf_window_sdiff`** — the operating switch window is exactly the `[opZ x, opY x)` prime
window.  `(opPs x).primeFactors \ (opP x).primeFactors = primesInWindow (opZ x) (opY x)` once
`opZ x ≤ opY x` (nonempty nesting) and `opW' ≤ opZ x` (the `opW'`-floor of `opPs` is subsumed
by the `opZ`-floor of the window). -/
theorem opf_window_sdiff (x : ℕ) (hzy : opZ x ≤ opY x) (hwz : opW' ≤ opZ x) :
    (opPs x).primeFactors \ (opP x).primeFactors
      = Salt.BrunLower.primesInWindow (opZ x : ℝ) (opY x : ℝ) := by
  rw [opf_Ps_primeFactors, opf_P_primeFactors]
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ico,
    Salt.BrunLower.primesInWindow, Finset.mem_range]
  constructor
  · rintro ⟨⟨⟨hw, hpy⟩, hpp⟩, hnot⟩
    have hzp : opZ x ≤ p := by
      by_contra h
      push_neg at h
      exact hnot ⟨⟨hw, h⟩, hpp⟩
    refine ⟨?_, hpp, ?_⟩
    · rw [Nat.lt_ceil]; exact_mod_cast hpy
    · exact_mod_cast hzp
  · rintro ⟨hlt, hpp, hzp⟩
    have hzp' : opZ x ≤ p := by exact_mod_cast hzp
    have hpy : p < opY x := by rw [Nat.lt_ceil] at hlt; exact_mod_cast hlt
    have hw : opW' ≤ p := le_trans hwz hzp'
    exact ⟨⟨⟨hw, hpy⟩, hpp⟩, fun h => by omega⟩

/-- **`hWy_at_op`** — the operating `W`-ratio in the `normalized_package`/`hledger` shape.
`W(switch) ≤ W(twinA1)·ρ` with `ρ = (log(opZ x)/log(opY x))·(1 + 38/log(opZ x))`; the ratio
`log(opZ x)/log(opY x) → (1/8)/(1/3) = 3/8` at the tower (the certified `3/8`-form). -/
theorem hWy_at_op : ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
    Salt.BrunLower.W (switchSieve x (opZ x) (opY x) (opPs x) (opf_Ps_sq x) (opf_Psodd x))
      ≤ Salt.BrunLower.W (twinA1Sieve x (opP x) (opf_P_sq x) (opf_Podd x))
        * ((Real.log (opZ x) / Real.log (opY x))
            * (1 + 38 / Real.log (opZ x))) := by
  obtain ⟨x₁, -, htower⟩ := opf_tower
  refine ⟨x₁, fun x hx => ?_⟩
  obtain ⟨_, hwz, hw'z, hz3, _, _, hzy, _, _, _, _, _, _, _, _, _, _⟩ := htower x hx
  -- 3 ≤ (opZ x : ℝ) and (opZ x : ℝ) ≤ (opY x : ℝ)
  have hz3R : (3 : ℝ) ≤ (opZ x : ℝ) := by exact_mod_cast hz3
  have hzyR : (opZ x : ℝ) ≤ (opY x : ℝ) := by exact_mod_cast hzy
  -- 38 ≤ log(opZ x) via w0R opEps ≤ opZ x and log(w0R opEps) = 40/log(1+opEps) ≥ 38
  have hz38 : (38 : ℝ) ≤ Real.log (opZ x) := by
    have hεpos : (0 : ℝ) < opEps := opf_eps_pos
    have h1e_pos : (0 : ℝ) < 1 + opEps := by linarith
    have hlog1e_pos : (0 : ℝ) < Real.log (1 + opEps) :=
      Real.log_pos (by linarith)
    have hlog1e_le : Real.log (1 + opEps) ≤ opEps := by
      have := Real.log_le_sub_one_of_pos h1e_pos
      linarith
    have hw0pos : (0 : ℝ) < w0R opEps := Real.exp_pos _
    have h38w0 : (38 : ℝ) ≤ Real.log (w0R opEps) := by
      rw [w0R, Real.log_exp, le_div_iff₀ hlog1e_pos]
      nlinarith [hlog1e_le, opf_eps1000]
    have hmono : Real.log (w0R opEps) ≤ Real.log (opZ x) :=
      Real.log_le_log hw0pos hwz
    linarith
  exact W_ratio_upper x (opZ x) (opY x) (opP x) (opPs x) (opf_P_sq x) (opf_Podd x)
    (opf_Ps_sq x) (opf_Psodd x) (opf_PdvdPs x hzy) hz3R hzyR hz38
    (opf_window_sdiff x hzy hw'z)

end Salt.Chen
