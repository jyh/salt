/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.TwinBar.SiegelTwin
import Salt.SW.ZeroFreeReal
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# THE FULCRUM — the weakest twin-prime hypothesis, in Lean (`fulcrum`)

Design / provenance: `docs/exploration/fulcrum-pass1.md` (Pass 1 VERDICT: the
refuter-survived `F_min`, quality angle, survived both refuters) and
`docs/exploration/fulcrum_audit_glue.md` (the consumer-side shape). This module
lands the STATEMENT layer of the fulcrum BESIDE the landed Heath-Brown statement
(`Salt/TwinBar/SiegelTwin.lean`), additively — it does not touch it.

`FulcrumQualityMin C` is the weakest hypothesis from which the Heath-Brown engine
can still manufacture twin primes: infinitely many real primitive quadratic
characters whose `L`-function carries a zero within `1/(C·log q)` of `1`, at ONE
fixed effective constant `C = C⋆`. Everything a Siegel zero classically supplies
beyond that — reality, `β < 1`, `1/2 ≤ β` — is DERIVED here, not assumed
(`fulcrum_zero_real`).

## The weakening ledger (condensed — full text: fulcrum-pass1.md §"WEAKENING LEDGER")

* **W1 — QUALITY BINDER** (the one genuine strict weakening vs the frozen
  `InfinitelyManySiegelZeros`): IMSZ demands witnesses at EVERY `c > 0`; the
  engine consumes ONE strength `η ≥ C⁽¹⁾` (HB Corollary 2). `F(C)` fixes that one
  constant. `IMSZ → F(C)` for every `C` (see `imsz_implies_fulcrum_of_gadget`);
  the converse is open (a fixed→arbitrary quality bootstrap for Siegel zeros).
* **W2 — ASYMPTOTIC DROPPED**: no `η → ∞`, no `(log log η)⁻¹` demand — only the
  infinitude of twins is targeted, not HB's asymptotic (1.1).
* **W3 — NORMALIZATION DROPPED**: HB's `η ≥ 3` in (1.11) is not demanded; the
  ball constant is `C⋆`.
* **W4 — ZERO-TYPE STRIPPED** (packaging, not weakening): F demands only a
  COMPLEX zero in the norm ball; reality / `β < 1` / `1/2 ≤ β` are derived
  (`fulcrum_zero_real`) from the landed `Salt.SW.zero_free_region_all` carve-out
  plus mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.
* **W5 — QUANTITY AT THE FLOOR**: bare `∀ Q, ∃ q > Q` — weaker than any density,
  spacing, or growth law; IMSZ never demanded those either.
* **W6 — ONE ZERO PER MODULUS, ANY QUALIFYING ZERO**: no uniqueness, no
  maximality, multiplicity irrelevant.

The primitive quadratic `χ ≠ 1` forces `q ≥ 3` (mod 1, 2 carry only trivial
characters); `fulcrum_zero_real` takes `3 ≤ q` as an explicit hypothesis (the
A-class hygiene node supplies it).
-/

open Complex DirichletCharacter

namespace Salt.Fulcrum

/-- **THE FULCRUM** (`F_min`, quality angle — fulcrum-pass1.md §F_MIN, verbatim).
The parametric family the Heath-Brown engine consumes at exactly one instance
`C = C⋆`. For every bound `Q` there is a modulus `q > Q` carrying a primitive
quadratic character `χ ≠ 1` whose `L`-function has a zero `ρ` inside the norm
ball `‖1 − ρ‖ · (C · log q) ≤ 1`. NOT assumed: `ρ` real, `Re ρ < 1`,
`Re ρ > 1/2`, maximality, multiplicity. -/
def FulcrumQualityMin (C : ℝ) : Prop :=
  ∀ Q : ℕ, ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    Q < q ∧ χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1 ∧
    LFunction χ ρ = 0 ∧ ‖(1 : ℂ) - ρ‖ * (C * Real.log q) ≤ 1

/-- **The compactness gadget interface** (FULCRUM-S2's node — stated here,
consumed abstractly by `imsz_implies_fulcrum_of_gadget`). For every bound `Q`
there is a quality threshold `c > 0` such that every real primitive quadratic
Siegel zero of quality finer than `c` has modulus exceeding `Q`. This is the
zero-isolation statement: finitely many `χ` of modulus `≤ Q`, each `L(·,χ)`
analytic with `L(1,χ) ≠ 0`, so its real zeros stay a fixed distance below `1`
(refuter R2, load-bearing for `IMSZ → F` and the dichotomy sharpening). -/
def SiegelModulusUnbounded : Prop :=
  ∀ Q : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ),
      1 < q → χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
      LFunction χ β = 0 → 1 - c / Real.log q < β → β < 1 → Q < q

/-- **The reality derivation** (`F_min` DEMAND MAP L1 — the one new B-class glue).
Given the `Salt.SW.zero_free_region_all` conclusion at constant `c₀` (hypothesis
`hZFR`, with `hc₀le : c₀ ≤ 1`) and a fulcrum witness at `C ≥ 2/c₀`
(`hC : 2 ≤ C · c₀`) with `q ≥ 3`, the zero `ρ` is REAL with `1/2 ≤ Re ρ < 1`.
Mechanism: at that quality the ball radius `1/(C·log q) < 1/2`, so `|Im ρ| < 1`
and `|Im ρ| + 2 < 3 ≤ q`; a non-real `ρ` would fire the zero-free region
(`χ² = 1 ∨ Im ρ ≠ 0` disjunction) forcing `q ≤ |Im ρ| + 2`, contradiction —
STRICTLY, from `|Im ρ| + 2 < 3` (refuter R5: no equality corner at `q = 3`).
Then `Re ρ < 1` by `LFunction_ne_zero_of_one_le_re`. -/
-- Off-trivial validation (catch #163). Fake COMPLEX witness at `q = 3`,
-- `C·log 3 ≥ 2`, hypothetical zero `ρ = (1 − 10⁻⁶) + (0.4)·i` in the ball: the
-- ball forces `|Im ρ| ≤ 1/(C·log 3) ≤ 1/2`, and the ZFR-combination forces
-- `q ≤ |Im ρ| + 2 ≤ 2.4 < 3 = q` — the fake is REJECTED, so any surviving
-- witness is real. The real segment `ρ = 1 − ε` survives untouched.
theorem fulcrum_zero_real
    (C c₀ : ℝ) (hc₀pos : 0 < c₀) (hc₀le : c₀ ≤ 1) (hC : 2 ≤ C * c₀)
    (hZFR : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      χ ≠ 1 → ∀ {ρ : ℂ}, LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re →
        (χ ^ 2 ≠ 1 ∨ ρ.im ≠ 0) →
        ρ.re ≤ 1 - c₀ / Real.log ((q : ℝ) * (|ρ.im| + 2)))
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hq3 : 3 ≤ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hzero : LFunction χ ρ = 0)
    (hball : ‖(1 : ℂ) - ρ‖ * (C * Real.log q) ≤ 1) :
    ρ.im = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
  have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hq1R : (1 : ℝ) < (q : ℝ) := by linarith
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by
    have hexp3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h3q : Real.exp 1 ≤ (q : ℝ) := le_trans hexp3.le hq3R
    have hmono : Real.log (Real.exp 1) ≤ Real.log (q : ℝ) :=
      (Real.log_le_log_iff (Real.exp_pos 1) (by linarith)).mpr h3q
    rw [Real.log_exp] at hmono
    rw [hLdef]; exact hmono
  have hLpos : (0 : ℝ) < L := by linarith
  have hCpos : (0 : ℝ) < C := by
    by_contra hle
    rw [not_lt] at hle
    nlinarith [hC, hc₀pos, hle]
  have hC2 : (2 : ℝ) ≤ C := by
    have h := mul_le_mul_of_nonneg_left hc₀le hCpos.le
    rw [mul_one] at h; linarith [hC, h]
  have hCLpos : (0 : ℝ) < C * L := mul_pos hCpos hLpos
  have hCL2 : (2 : ℝ) ≤ C * L := by
    have h := mul_le_mul hC2 hL1 (by norm_num) hCpos.le
    linarith [h]
  have hN_le : ‖(1 : ℂ) - ρ‖ ≤ 1 / (C * L) := (le_div_iff₀ hCLpos).mpr hball
  have hinv_half : (1 : ℝ) / (C * L) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hCL2
  have hre_le : 1 - ρ.re ≤ ‖(1 : ℂ) - ρ‖ := by
    have h := Complex.abs_re_le_norm (1 - ρ)
    rw [Complex.sub_re, Complex.one_re] at h
    exact le_trans (le_abs_self _) h
  have him_le : |ρ.im| ≤ ‖(1 : ℂ) - ρ‖ := by
    have h := Complex.abs_im_le_norm (1 - ρ)
    simpa [Complex.sub_im, Complex.one_im] using h
  have hre : (1 : ℝ) / 2 ≤ ρ.re := by linarith [hre_le, hN_le, hinv_half]
  have him_small : |ρ.im| + 2 < 3 := by linarith [him_le, hN_le, hinv_half]
  have him0 : ρ.im = 0 := by
    by_contra hIm
    have hzfr := hZFR q χ hprim hne hzero hre (Or.inr hIm)
    have hq0R : (q : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have h2ne : (|ρ.im| + 2 : ℝ) ≠ 0 := by positivity
    have hMpos : (0 : ℝ) < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hDpos : (0 : ℝ) < L + Real.log (|ρ.im| + 2) := by linarith
    rw [Real.log_mul hq0R h2ne, ← hLdef] at hzfr
    have hlow' : c₀ / (L + Real.log (|ρ.im| + 2)) ≤ 1 - ρ.re := by linarith [hzfr]
    have hcomb : c₀ / (L + Real.log (|ρ.im| + 2)) ≤ 1 / (C * L) :=
      le_trans hlow' (le_trans hre_le hN_le)
    have hcross := (div_le_div_iff₀ hDpos hCLpos).mp hcomb
    have hstep : 2 * L ≤ c₀ * (C * L) := by
      have h := mul_le_mul_of_nonneg_right hC hLpos.le
      nlinarith [h]
    have hLM : L ≤ Real.log (|ρ.im| + 2) := by linarith [hcross, hstep]
    rw [hLdef] at hLM
    have hqle : (q : ℝ) ≤ |ρ.im| + 2 :=
      (Real.log_le_log_iff (by linarith) (by positivity)).mp hLM
    linarith [hqle, him_small, hq3R]
  have hre1 : ρ.re < 1 := by
    by_contra h
    rw [not_lt] at h
    exact (LFunction_ne_zero_of_one_le_re χ (Or.inl hne) h) hzero
  exact ⟨him0, hre, hre1⟩

/-- **Reality from the LANDED zero-free region.** `fulcrum_zero_real` composed
with `Salt.SW.zero_free_region_all`: the only residual is the calibration `hcal`
— that `C⋆` dominates `2/c₀` for the region's OWN constant `c₀` (with `c₀ ≤ 1`).
The `c₀` never escapes; discharging `hcal` needs the owed A-class numeral
extraction (`c₀ = 1/126848`, fulcrum-pass1.md risk R6). -/
theorem fulcrum_zero_real_zfr (C : ℝ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hcal : ∀ c₀ : ℝ, 0 < c₀ →
      (∀ (q' : ℕ) [NeZero q'] (χ' : DirichletCharacter ℂ q'), χ'.IsPrimitive →
        χ' ≠ 1 → ∀ {ρ' : ℂ}, LFunction χ' ρ' = 0 → 1 / 2 ≤ ρ'.re →
          (χ' ^ 2 ≠ 1 ∨ ρ'.im ≠ 0) →
          ρ'.re ≤ 1 - c₀ / Real.log ((q' : ℝ) * (|ρ'.im| + 2))) →
        c₀ ≤ 1 ∧ 2 ≤ C * c₀)
    (hq3 : 3 ≤ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    (hzero : LFunction χ ρ = 0)
    (hball : ‖(1 : ℂ) - ρ‖ * (C * Real.log q) ≤ 1) :
    ρ.im = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
  obtain ⟨c₀, hc₀pos, hZFR⟩ := Salt.SW.zero_free_region_all
  obtain ⟨hle, hCc₀⟩ := hcal c₀ hc₀pos hZFR
  exact fulcrum_zero_real C c₀ hc₀pos hle hCc₀ hZFR hq3 hprim hne hzero hball

/-- **`InfinitelyManySiegelZeros → FulcrumQualityMin C`** (fulcrum-pass1.md
"Relation to the frozen target"), conditional on the compactness gadget
`SiegelModulusUnbounded` (FULCRUM-S2's node, consumed abstractly). Fixing the
target `C > 0`: run the `∀c∃` witnesses at `c := min (1/C) c_Q`; the ball closes
because a real `β < 1` at that quality has `(1 − β) · C · log q < 1`, and the
gadget pushes the modulus past `Q`. Recovers the landed `HeathBrownStatement` as
a corollary once the gadget lands. -/
theorem imsz_implies_fulcrum_of_gadget
    (C : ℝ) (hCpos : 0 < C) (gadget : SiegelModulusUnbounded)
    (h : Salt.TwinBar.InfinitelyManySiegelZeros) : FulcrumQualityMin C := by
  intro Q
  obtain ⟨cQ, hcQpos, hmod⟩ := gadget Q
  set c : ℝ := min (1 / C) cQ with hcdef
  have hcpos : 0 < c := lt_min (by positivity) hcQpos
  obtain ⟨q, hq, χ, β, h1q, hprim, hsq, hne, hzero, hlow, hβ1⟩ := h c hcpos
  haveI := hq
  have hLq : (0 : ℝ) < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast h1q)
  refine ⟨q, hq, χ, (β : ℂ), ?_, hprim, hsq, hne, hzero, ?_⟩
  · have hdiv : c / Real.log q ≤ cQ / Real.log q := by
      rw [div_le_div_iff₀ hLq hLq]
      exact mul_le_mul_of_nonneg_right (min_le_right _ _) hLq.le
    have hlowQ : 1 - cQ / Real.log q < β := by linarith [hlow, hdiv]
    exact hmod q χ β h1q hprim hsq hne hzero hlowQ hβ1
  · have hnorm : ‖(1 : ℂ) - (β : ℂ)‖ = 1 - β := by
      rw [show (1 : ℂ) - (β : ℂ) = ((1 - β : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - β)]
    rw [hnorm]
    have h1mβ : 1 - β < c / Real.log q := by linarith [hlow]
    have hstep1 : (1 - β) * Real.log q < c := (lt_div_iff₀ hLq).mp h1mβ
    have hstep2 : (1 - β) * Real.log q < 1 / C :=
      lt_of_lt_of_le hstep1 (min_le_left _ _)
    have hstep3 : (1 - β) * Real.log q * C < 1 := (lt_div_iff₀ hCpos).mp hstep2
    have hfin : (1 - β) * (C * Real.log q) < 1 := by
      calc (1 - β) * (C * Real.log q) = (1 - β) * Real.log q * C := by ring
        _ < 1 := hstep3
    linarith [hfin]

end Salt.Fulcrum
