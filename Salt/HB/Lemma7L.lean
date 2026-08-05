/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.HB.TwistedMertens
import Salt.SW.BCSup

/-!
# HB 1983, (2.4) — `L′/L(1,χ)` at the exceptional zero (node N4b, wave W1: the `(L1)` slot)

Heath-Brown's p.199 line for (2.4) is *"(2.4) falls out of the same analysis run at `s = 1` in
place of `s = 1 + L^{−1}`, same `a = (log η)^{1/2}`"*.  This file runs it.

With `m := zeroMult χ β₀`, `η := ((1−β₀)·log q)^{−1}` and `L := log q`, the target is

    (L1)    |L′/L(1,χ) − m·ηL|  ≤  K₁·L·(log η)^{−1/2}.

**One-sided (design v3, D7).**  The landed differencing engine yields the *upper* side only —
`Re(−L′/L(1,χ)) ≤ −m·ηL + rate`, equivalently `m·ηL − Re(L′/L(1,χ)) ≤ rate` — which is all
HB's p.200 consumer uses.  The lower side is a separate stone (`∑ m_ρ(1−Re ρ)/|1−ρ|²` off the
Deuring–Heilbronn floor) and is **not** proved here.

## The route (three lines of machinery, no new analysis)

1. `Salt.SW.LFunction_partialFraction_remainder_diff` exports the `t₀ = 0` zero set `Z` with
   multiplicities `m`, the converse membership (`hβZ`, `hmβ`), `m = zeroMult` on `Z`, and the
   remainder difference at the Lipschitz rate `1600·log(80√f(1+log f))·|σ−σ′|` for
   `1 ≤ σ, σ′ ≤ 2` — the σ-range that **admits the left endpoint `σ = 1`**.
2. `neg_re_logDeriv_differenced_mult` (the N4b W0-iv stone) is the differencing with `1 ≤ σ`
   (not `1 < σ`) and the exceptional residue kept at **full multiplicity**.  Fired at
   `σ = 1`, `σ′ = 1 + √ℓ/Lp` — HB's own optimum `a = (log η)^{1/2}` at the campaign's
   `Lp := 2·log q` (design v3 item 7) — it gives

       Re(−L′/L(1,χ)) ≤ −m/(1−β₀) + [1/(σ′−1) + 1] + m/(σ′−β₀)
                          + 4(σ′−1)·Sinv + Rrem.

3. `l1_error_collapse` (§1) collapses the four error terms onto the single
   `Lp·(log η)^{−1/2}` shape, exactly as `hbCoreRate_at_hb_optimum_absorbed` does for
   Lemma 3 — **including** the partial-fraction remainder `Rrem`, so that

       K₁ = 802 + m + 4·Cs   at the `Lp`-grade rate  (Lemma 3's `K = 802 + 4Cs`, plus the
                                                      `m/(σ′−β₀)` residue's own `m`).

   No free-standing additive remainder reaches a consumer.

## What rides (the named binders)

`hell`/`hellL` (`1 ≤ log η ≤ Lp`, i.e. the design's `hηq` at `Lp = 2L`), `hCs`/`hSinvC` (the
F-side repulsion pricing `Sinv ≤ Cs·Lp²/log η` that `invSq_sum_split_le` supplies), `hCR` (the
`L`-vs-`f` convention), the Deuring–Heilbronn floor data `r0`/`hσ'r`, and `hβlo`/`hβ1`/`hβ0`
(the Siegel zero itself).  **No window binder, no `x`** — `(L1)` is `x`-free, as designed.
-/

namespace Salt.HB

open Complex Metric DirichletCharacter Set

/-! ## §1 — the error collapse at `σ = 1`, `σ′ = 1 + √ℓ/Lp` -/

/-- **The four differenced error terms, collapsed onto one rate.**  At the left endpoint
`σ = 1` and HB's optimum `σ′ = 1 + √ℓ/Lp`, the differencing's error budget

    [1/(σ′−1) + 1]  +  m/(σ′−β₀)  +  4(σ′−1)·Sinv  +  CR·(σ′−1)

is at most `(802 + m + 4Cs)·Lp/√ℓ`, on the two campaign conventions `Sinv ≤ Cs·Lp²/ℓ` and
`CR ≤ 800·Lp`, given `1 ≤ ℓ ≤ Lp`.  The four contributions are `Lp/√ℓ` (the `σ′`-pole),
`1 ≤ Lp/√ℓ`, `m·Lp/√ℓ` (the exceptional residue at `σ′`, using `σ′−β₀ ≥ σ′−1`),
`4Cs·Lp/√ℓ` (the repulsion sum, using `√ℓ·Lp/ℓ = Lp/√ℓ`) and `800·Lp/√ℓ` (the remainder,
using `√ℓ ≤ Lp/√ℓ`) — total `1 + 1 + m + 4Cs + 800`.

This is `hbCoreRate_at_hb_optimum_absorbed`'s arithmetic with the `m/(σ′−β₀)` term added and
the `σ = 1` endpoint in place of `σ = 1 + 1/Lp`. -/
theorem l1_error_collapse {Lp ell Sinv Cs CR mβ β₀ : ℝ}
    (hell : 1 ≤ ell) (hellL : ell ≤ Lp) (hCs : 0 ≤ Cs) (hm : 0 ≤ mβ) (hβ1 : β₀ < 1)
    (hSinvC : Sinv ≤ Cs * (Lp ^ 2 / ell)) (hCR : CR ≤ 800 * Lp) :
    (1 / ((1 + Real.sqrt ell / Lp) - 1) + 1)
        + mβ / ((1 + Real.sqrt ell / Lp) - β₀)
        + 4 * ((1 + Real.sqrt ell / Lp) - 1) * Sinv
        + CR * ((1 + Real.sqrt ell / Lp) - 1)
      ≤ (802 + mβ + 4 * Cs) * (Lp / Real.sqrt ell) := by
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hell
  have hL : (0 : ℝ) < Lp := lt_of_lt_of_le hell0 hellL
  have hs : (0 : ℝ) < Real.sqrt ell := Real.sqrt_pos.mpr hell0
  have hs1 : (1 : ℝ) ≤ Real.sqrt ell := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt ell * Real.sqrt ell = ell := Real.mul_self_sqrt hell0.le
  have hR : Real.sqrt ell ≤ Lp / Real.sqrt ell := by
    have hd : Lp / Real.sqrt ell - Real.sqrt ell = (Lp - ell) / Real.sqrt ell := by
      field_simp
      nlinarith [hmul]
    have hpos : (0 : ℝ) ≤ (Lp - ell) / Real.sqrt ell := div_nonneg (by linarith) hs.le
    linarith
  have hR1 : (1 : ℝ) ≤ Lp / Real.sqrt ell := le_trans hs1 hR
  have hstep : (1 + Real.sqrt ell / Lp) - 1 = Real.sqrt ell / Lp := by ring
  have hd0 : (0 : ℝ) < Real.sqrt ell / Lp := div_pos hs hL
  -- (a) the `σ′`-pole
  have ht1 : 1 / ((1 + Real.sqrt ell / Lp) - 1) = Lp / Real.sqrt ell := by
    rw [hstep, one_div_div]
  -- (b) the exceptional residue at `σ′`, paid at `σ′ − β₀ ≥ σ′ − 1`
  have hD : (0 : ℝ) < (1 + Real.sqrt ell / Lp) - β₀ := by linarith
  have hge : Real.sqrt ell / Lp ≤ (1 + Real.sqrt ell / Lp) - β₀ := by linarith
  have ht2 : mβ / ((1 + Real.sqrt ell / Lp) - β₀) ≤ mβ * (Lp / Real.sqrt ell) := by
    rw [div_le_iff₀ hD]
    have hQ : (0 : ℝ) ≤ mβ * (Lp / Real.sqrt ell) := mul_nonneg hm (by positivity)
    have hchain := mul_le_mul_of_nonneg_left hge hQ
    have heq : mβ * (Lp / Real.sqrt ell) * (Real.sqrt ell / Lp) = mβ := by
      field_simp
    linarith
  -- (c) the repulsion sum
  have ht3 : 4 * ((1 + Real.sqrt ell / Lp) - 1) * Sinv ≤ 4 * Cs * (Lp / Real.sqrt ell) := by
    rw [hstep]
    have hpre : (0 : ℝ) ≤ 4 * (Real.sqrt ell / Lp) := by positivity
    have h1 : 4 * (Real.sqrt ell / Lp) * Sinv
        ≤ 4 * (Real.sqrt ell / Lp) * (Cs * (Lp ^ 2 / ell)) :=
      mul_le_mul_of_nonneg_left hSinvC hpre
    have h2 : 4 * (Real.sqrt ell / Lp) * (Cs * (Lp ^ 2 / ell))
        = 4 * Cs * (Lp / Real.sqrt ell) := by
      field_simp
      nlinarith [hmul]
    linarith
  -- (d) the partial-fraction remainder
  have ht4 : CR * ((1 + Real.sqrt ell / Lp) - 1) ≤ 800 * (Lp / Real.sqrt ell) := by
    rw [hstep]
    have h1 : CR * (Real.sqrt ell / Lp) ≤ 800 * Lp * (Real.sqrt ell / Lp) :=
      mul_le_mul_of_nonneg_right hCR hd0.le
    have h2 : 800 * Lp * (Real.sqrt ell / Lp) = 800 * Real.sqrt ell := by
      field_simp
    linarith
  rw [ht1]
  nlinarith [ht2, ht3, ht4, hR1]

/-! ## §2 — `(L1)`, one-sided, at `s = 1` -/

/-- **HB (2.4), ONE-SIDED, WITH THE MULTIPLICITY EXPLICIT (node N4b, W1).**  The `s = 1`
evaluation of the log-derivative at a Siegel zero `β₀`, with the exceptional residue extracted
at full multiplicity `m = zeroMult χ β₀` and a **single** rate constant:

    Re(−L′/L(1,χ))  ≤  −m/(1−β₀)  +  (802 + m + 4Cs)·Lp·(log η)^{−1/2},

i.e. `m·ηL − Re(L′/L(1,χ)) ≤ K₁·Lp·(log η)^{−1/2}` with `K₁ = 802 + m + 4Cs`, since
`ηL = (1−β₀)^{−1}`.  (The `η`-shaped restatement is `hb_L1_one_sided` below.)

The exported package mirrors `pretenseSum_unconditional_absorbed`: the zero set `Z` with its
multiplicities, `β₀ ∈ Z`, `m β₀ ≥ 1`, every `ρ ∈ Z` a zero, `m ≤ zeroMult` on `Z` (so the
F-side artillery `invSq_sum_split_le` plugs in verbatim), and the conclusion behind the two
Deuring–Heilbronn items `hfloor`/`hSinv`.  **No analytic input is carried**: `hrem` is
discharged internally by `LFunction_partialFraction_remainder_diff`, and the `σ′`-side input
by `neg_re_logDeriv_LFunction_le`.

The left operating point is genuinely **on** the line `σ = 1` — that is the whole content of
the W0-iv relaxation, and it is why `(1−β₀)^{-1}` (not `L`) appears in the main term. -/
theorem neg_re_logDeriv_one_le_mult {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f)
    {β₀ r0 Sinv Cs Lp ell : ℝ}
    (hell : 1 ≤ ell) (hellL : ell ≤ Lp) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * (Lp ^ 2 / ell))
    (hCR : 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ 800 * Lp)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hr0 : 0 < r0) (hσ'r : Real.sqrt ell / Lp ≤ r0 / 2) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖) →
        (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        (-logDeriv (DirichletCharacter.LFunction χ) (1 : ℂ)).re
          ≤ -((Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) / (1 - β₀))
            + (802 + (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) + 4 * Cs)
                * (Lp / Real.sqrt ell)) := by
  classical
  have hell0 : (0 : ℝ) < ell := lt_of_lt_of_le zero_lt_one hell
  have hL : (0 : ℝ) < Lp := lt_of_lt_of_le hell0 hellL
  have hs : (0 : ℝ) < Real.sqrt ell := Real.sqrt_pos.mpr hell0
  have hs1 : (1 : ℝ) ≤ Real.sqrt ell := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hell
  have hmul : Real.sqrt ell * Real.sqrt ell = ell := Real.mul_self_sqrt hell0.le
  have hsle : Real.sqrt ell ≤ Lp := le_trans (by nlinarith [hmul]) hellL
  have hd0 : (0 : ℝ) < Real.sqrt ell / Lp := div_pos hs hL
  have hσ'1 : (1 : ℝ) < 1 + Real.sqrt ell / Lp := by linarith
  have hσ'2 : 1 + Real.sqrt ell / Lp ≤ 2 := by
    have := (div_le_one hL).mpr hsle
    linarith
  obtain ⟨Z, m, hmemZ, hconv, hmult, hdiff⟩ :=
    Salt.SW.LFunction_partialFraction_remainder_diff χ hχ hf
  have hβball : ((β₀ : ℝ) : ℂ) ∈ ball (2 : ℂ) (3 / 2) := by
    rw [mem_ball, dist_eq_norm]
    have hcast : (((β₀ : ℝ) : ℂ) - 2) = ((β₀ - 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith
  obtain ⟨hβZ, hmβ⟩ := hconv ((β₀ : ℝ) : ℂ) hβball hβ0
  refine ⟨Z, m, hβZ, hmβ, fun ρ hρ => (hmemZ ρ hρ).2, fun ρ hρ => le_of_eq ?_, ?_⟩
  · exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (hmult ρ hρ)
  · intro hfloor hSinv
    -- the remainder difference at the pair `(1, 1 + √ℓ/Lp)` — the `σ = 1` endpoint is admitted
    have hrem := hdiff 1 (1 + Real.sqrt ell / Lp) le_rfl (by norm_num) hσ'1.le hσ'2
    have habs : |(1 : ℝ) - (1 + Real.sqrt ell / Lp)| = (1 + Real.sqrt ell / Lp) - 1 := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [habs] at hrem
    -- the `σ′`-side input
    have hs'top := neg_re_logDeriv_LFunction_le χ hσ'1 hσ'2
    -- the differencing, at `σ = 1`, multiplicity retained
    have hmain := neg_re_logDeriv_differenced_mult
      (Lf := DirichletCharacter.LFunction χ) (Z := Z) (m := m)
      (σ := 1) (σ' := 1 + Real.sqrt ell / Lp) (β₀ := β₀) (r0 := r0) (Sinv := Sinv)
      le_rfl (by linarith) hβ1 hβZ hr0 (by linarith) (by linarith) hfloor hSinv hrem hs'top
    have hone : ((1 : ℝ) : ℂ) = (1 : ℂ) := Complex.ofReal_one
    rw [hone] at hmain
    -- `m β₀ = zeroMult χ β₀`
    have hmz : (m (β₀ : ℂ) : ℝ) = (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (hmult _ hβZ)
    rw [hmz] at hmain
    -- the collapse
    have hcol := l1_error_collapse (Lp := Lp) (ell := ell) (Sinv := Sinv) (Cs := Cs)
      (CR := 1600 * Real.log (80 * Real.sqrt f * (1 + Real.log f)))
      (mβ := (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ)) (β₀ := β₀)
      hell hellL hCs (by positivity) hβ1 hSinvC hCR
    linarith

/-- **`(L1)` in the design's `η` currency.**  Written against `η := ((1−β₀)·L)^{−1}`,
`L := log q` and the campaign's `Lp := 2L` (design v3 item 7), the main term is HB's `m·ηL`
and the rate is his `L·(log η)^{−1/2}`:

    Re(−L′/L(1,χ))  ≤  −m·ηL  +  K₁·L·(log η)^{−1/2},    K₁ = 1604 + 2m + 8Cs,

one-sided per D7.  The `2` in `K₁` is the `Lp = 2L` convention, nothing else; `hηq` enters
exactly once, in the design's single spelling `log η ≤ L`. -/
theorem hb_L1_one_sided {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f)
    {β₀ r0 Sinv Cs L η : ℝ}
    (hLpos : 0 < L) (hη : η = 1 / ((1 - β₀) * L))
    (hell : 1 ≤ Real.log η) (hηq : Real.log η ≤ L) (hCs : 0 ≤ Cs)
    (hSinvC : Sinv ≤ Cs * ((2 * L) ^ 2 / Real.log η))
    (hCR : Real.log (80 * Real.sqrt f * (1 + Real.log f)) ≤ L)
    (hβlo : 1 / 2 < β₀) (hβ1 : β₀ < 1)
    (hβ0 : DirichletCharacter.LFunction χ (β₀ : ℂ) = 0)
    (hr0 : 0 < r0) (hσ'r : Real.sqrt (Real.log η) / (2 * L) ≤ r0 / 2) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (β₀ : ℂ) ∈ Z ∧ 1 ≤ m (β₀ : ℂ) ∧
      (∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ Z, (m ρ : ℝ) ≤ (Salt.SW.zeroMult χ ρ : ℝ)) ∧
      ((∀ ρ ∈ Z.erase ((β₀ : ℂ)), r0 ≤ ‖ρ - 1‖) →
        (∑ ρ ∈ Z.erase ((β₀ : ℂ)), (m ρ : ℝ) / ‖ρ - 1‖ ^ 2 ≤ Sinv) →
        (-logDeriv (DirichletCharacter.LFunction χ) (1 : ℂ)).re
          ≤ -((Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) * (η * L))
            + (1604 + 2 * (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) + 8 * Cs)
                * (L / Real.sqrt (Real.log η))) := by
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hβ0' : (0 : ℝ) < 1 - β₀ := by linarith
  have hβne : (1 : ℝ) - β₀ ≠ 0 := ne_of_gt hβ0'
  obtain ⟨Z, m, hβZ, hmβ, hzero, hmz, hbody⟩ :=
    neg_re_logDeriv_one_le_mult χ hχ hf (Lp := 2 * L) (ell := Real.log η)
      (β₀ := β₀) (r0 := r0) (Sinv := Sinv) (Cs := Cs)
      hell (by linarith) hCs hSinvC (by linarith) hβlo hβ1 hβ0 hr0 hσ'r
  refine ⟨Z, m, hβZ, hmβ, hzero, hmz, ?_⟩
  intro hfloor hSinv
  have hbd := hbody hfloor hSinv
  -- `η·L = (1−β₀)^{−1}`
  have hηL : η * L = 1 / (1 - β₀) := by
    rw [hη]; field_simp
  have hmain : (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) / (1 - β₀)
      = (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) * (η * L) := by
    rw [hηL]; ring
  -- the rate, at `Lp = 2L`
  have hrate : (802 + (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) + 4 * Cs)
        * (2 * L / Real.sqrt (Real.log η))
      = (1604 + 2 * (Salt.SW.zeroMult χ (β₀ : ℂ) : ℝ) + 8 * Cs)
        * (L / Real.sqrt (Real.log η)) := by
    ring
  rw [hmain, hrate] at hbd
  exact hbd

end Salt.HB
