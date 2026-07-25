/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.BallSup

/-!
# CENTRE-CORE — the M-shaped Halász core at the row's free centre (A-2 / A-3 / A-10)

The HCENTER ladder's centre clones (`docs/exploration/hsup-design.md`, ⟦THE HCENTER FREEZE⟧ +
⟦HCENTER AMENDMENT V2⟧ + ⟦THE TWO-M READING RATIFIED⟧), nodes **A-2**, **A-3**, **A-10**.

## ⟦THE TWO-M DISCIPLINE — LAW FOR THIS FILE⟧

From ⟦THE TWO-M READING RATIFIED⟧ (JYH, 2026-07-25 12:02 PDT), verbatim:

> Ball leg = the global M via the minimizer (M-shaped statements; the frozen terminal's own
> `exp(−M(f;X)/2)`); far/annulus legs = `M_range` (J0 intact on its domain); J0 refined, not
> reversed (its target was the seam-`t₀` drift, not the minimizer).

and ⟦AMENDMENT V2⟧ repair #4 (**THE M-SHAPE (R-1e, the kill)**), verbatim:

> the supplier is M-SHAPED, no numeral — `≤ (C·exp(−(1/(2e))·pretDistSq (seamCoeff (ellLin g)
> (fun _ => 1) t₀) (costwist t₁) X) + C·loglog X·(logX)^{−1/2})·k`; numeric exponents ONLY at
> consumers where `hfloor` lives.  The μ²-refutation (`g ≡ 1`: `S₀ ≈ 0.608`) kills any
> bare-power supplier.

Accordingly **every exit in this file carries the explicit
`pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X` in its exponent**: no
`M_range`, no numeral, no `hfloor`.  The floor is the consumer's business.

## The clones

`HalaszDirect` proves the same three shapes on the `M_range` *window*
(`window_sup_decay_gen` :171, `halasz_direct_ball` :385, `halasz_direct_gen` :325).  Here the
window-membership hypothesis
`hmem : (logX)^{1/15} ≤ |t| ∧ |t| ≤ T + (logX)^{1/16} ∧ |t| ≤ X`
is replaced by the plain cap `hcap : |t| ≤ X`, and the `M_range` floor
(`SupF.scale_floor_Mrange_seam`) by the **general-`f` floor** `SupF.scale_floor` (:869):

  `𝔻²(f, g; X) − 2·log(σ·logX) − 48 ≤ 𝔻²(f, g; e^{1/σ})`   (`f`, `g` 1-bounded, `e^{1/σ} ≤ X`).

**THE WEAKEN-BEFORE-FLOOR ORDER TRAP (HalaszDirect's banked page, restated).**  The `c`-downgrade
`exp(−(1/e)𝔻²) ≤ exp(−c𝔻²)` (legal by `pretDistSq_nonneg`) is applied FIRST, the floor SECOND.
Applying the floor first would need `𝔻²(X) − 2log(σL) − 48 ≥ 0`, which is false near the top of
the σ-range.

## ⟦THE S-3 / LIVE CITATION GUARD — LAW FOR THIS FILE⟧

From ⟦THE H-BLOCK FREEZE v2⟧, verbatim, as extended by ⟦AMENDMENT V2⟧ repair #5:

> **THE LIVE GUARD (replaces the tripwire)**: L3's arm cites
> `sigma_cutoff_pretentious_of_gen` (c = 1/e); the ball's arm cites `_half`
> (c = 1/(2e)); **a citation of `_half` in any §8.3 consumer is a STOP** — both instances
> landed side-by-side, discipline is the only requirement.

> **The LIVE GUARD extended**: a §8.3 consumer citing `_half` OR the ball-graded head of
> `center_halasz_supply` is a STOP.

The two faces below keep the arms separate by construction:

* `halasz_direct_center` — the **ball arm**, `c = 1/(2e)`, citing
  `SeamBallWeighted.sigma_cutoff_pretentious_half` (:392).
* `halasz_direct_center_gen` — the **§8.3/L3 arm**, `c = 1/e`, citing
  `SeamBallWeighted.sigma_cutoff_pretentious_of_gen` (:416).

## ⟦THE POSITIVITY TRAP, SHARPENED (new, this file)⟧

`HalaszDirect` records: `X > 0` is NOT assumed there — it is *derived* from the window
membership (`1 ≤ (logX)^{1/15} ≤ |t| ≤ X`), because mathlib's `Real.log` is even and `3 ≤ log X`
alone admits `X = −e³`.  **The plain cap `|t| ≤ X` supplies no such positivity** (it is vacuously
compatible with `X < 0` only when `t = 0`… and in any case gives only `0 ≤ X` when `t` is real,
never `0 < X`).  The σ-integrated faces therefore carry an explicit `hX : 0 < X`; the pointwise
face `window_sup_decay_center` does not need it (`hYX : e^{1/σ} ≤ X` already forces `X ≥ 2`).

## A-10 — the ball-centre dichotomy, and the half-open correction

⟦AMENDMENT V2⟧ repair #4 adds A-10: *`|t₁| ≤ seamT0 − seamRad ⟹ Ann ∩ ball = ∅`*.  **As stated
with the non-strict cut this is FALSE**, by one touching point: `seamAnn X T` is the CLOSED
condition `seamT0 X ≤ |t|`, so `t₁ = seamT0 X − seamRad X`, `t = seamT0 X` lies in both sets.
Both honest forms land here:

* `seamAnn_inter_seamBall_eq_empty` — the STRICT cut `|t₁| < seamT0 X − seamRad X` gives the
  genuine `= ∅`;
* `seamAnn_inter_seamBall_subset_pair` — the non-strict cut gives
  `Ann ∩ ball ⊆ {−seamT0 X, seamT0 X}`, a null set, so the ball leg's integral is still `0`
  (`ball_leg_empty_of_le`).  The freeze's intended consequence survives verbatim at the
  integral level; only the set-level `= ∅` needed the strict cut.

`ball_center_dichotomy` is the case split A-9 consumes; its live branch hypothesis is
`seamT0 X − seamRad X ≤ |t₁|` and **no floor is asserted here** (M-shaped discipline: the floor
supply in the live branch is the consumer's business).
-/

noncomputable section

namespace Salt.MR

open MeasureTheory

/-! ## §0 — the twist-algebra copy (the THIRD copy)

`GrandComp.dist_triv_left_eq` (:277) is `private` to its file, and so is
`HalaszDirect.dist_triv_left_eq_local` (:142) — itself the second copy.  The identity is
re-derived here byte-for-byte (no statement change, Iron rule 1), exactly as `SupF` re-derives
the `HalaszHead` twist lemmas it cannot reach (`costwist_conj_local` :1111,
`seamCoeff_trivial_dist_eq_local` :1125).  **Precedent noted: this is the third such copy.** -/

/-- Local copy of `GrandComp.dist_triv_left_eq` (`private` there; and of
`HalaszDirect.dist_triv_left_eq_local`, `private` there): the trivial-left-datum distance
`𝔻²(1, f·costwist(−t); X)` equals `𝔻²(f, costwist t; X)`. -/
private lemma dist_triv_left_eq_local (f : ℕ → ℂ) (t X : ℝ) :
    pretDistSq (fun _ => 1) (fun n => f n * costwist (-t) n) X
      = pretDistSq f (costwist t) X := by
  unfold pretDistSq
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hre : ((fun _ => (1 : ℂ)) p
        * (starRingEnd ℂ) ((fun n => f n * costwist (-t) n) p)).re
      = (f p * (starRingEnd ℂ) (costwist t p)).re := by
    simp only [one_mul, Complex.conj_re, costwist_conj]
  rw [hre]

/-! ## §1 (A-2) — the M-shaped pointwise decay at the centre

The byte-clone of `HalaszDirect.window_sup_decay_gen` (:171) with `hmem` replaced by the cap
and the `M_range` floor replaced by the general-`f` `SupF.scale_floor` (:869).  The exponent is
M-SHAPED: the explicit `pretDistSq` at the seam datum against `costwist t`, at scale `X`. -/

/-- **A-2 — the general-`c` M-shaped centre decay** (`window_sup_decay_center`).  For a globally
1-bounded (at primes) `g`, an exponent `0 < c ≤ 1/e`, `σ ∈ (0,1]` with `e^{1/σ} ≤ X`, and ANY
frequency `t` under the plain cap `|t| ≤ X`,

  `‖F_seam(1+σ+it)‖ ≤ C_F·(1/σ)·exp(−c·(𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t; X)
      − 2·log(σ·logX) − 48))`,  `C_F = exp(cpeel + (log 4 + cpeel))`.

**M-SHAPED** (⟦AMENDMENT V2⟧ #4): the exponent carries the explicit `pretDistSq` term at `t`,
NOT `M_range`, and no numeral.  Proof: `head_sigma_bound` at the seam datum, its distance
rewritten by `dist_triv_left_eq_local` ONLY (the `seamCoeff_trivial_dist_eq` transport to the
bare `ℓ`-datum is deliberately NOT taken — that is what would re-introduce the `t₀`-shifted
window datum), then the exponent chain `c·(𝔻²(X) − 2log(σL) − 48) ≤ c·𝔻²(e^{1/σ}) ≤
(1/e)·𝔻²(e^{1/σ})` — first step by `SupF.scale_floor` (`c > 0`), second by `𝔻² ≥ 0`, `c ≤ 1/e`.
**The order is load-bearing** (the weaken-before-floor trap; see the file header).

`_hcap` is carried for the consumer's shape only: the floor's scale condition is `hYX`, which
already forces `X ≥ 2`. -/
theorem window_sup_decay_center {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀ t X σ : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (_hcap : |t| ≤ X) :
    ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
        (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
        * Real.exp (-c * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
            - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  have hTwistOne : ∀ n : ℕ, ‖costwist t n‖ ≤ 1 := fun n => le_of_eq (costwist_norm t n)
  have hHead := head_sigma_bound (g := seamCoeff (ellLin g) (fun _ => 1) t₀) hSeamOne hσ0 hσ1 t
  have hdist_eq :
      pretDistSq (fun _ => 1)
          (fun n => seamCoeff (ellLin g) (fun _ => 1) t₀ n * costwist (-t) n) (Real.exp (1 / σ))
        = pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) (Real.exp (1 / σ)) :=
    dist_triv_left_eq_local (seamCoeff (ellLin g) (fun _ => 1) t₀) t (Real.exp (1 / σ))
  rw [hdist_eq] at hHead
  refine hHead.trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Real.exp_nonneg _) (div_nonneg zero_le_one hσ0.le))
  apply Real.exp_le_exp.mpr
  -- THE GENERAL-`f` FLOOR (`SupF.scale_floor`), applied AFTER the `c`-downgrade
  have hd := scale_floor (f := seamCoeff (ellLin g) (fun _ => 1) t₀) (g := costwist t)
    hSeamOne hTwistOne hσ0 hσ1 hYX
  have hnn : 0 ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t)
      (Real.exp (1 / σ)) :=
    pretDistSq_nonneg _ _ _ hSeamOne hTwistOne
  have h1 : c * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
        - 2 * Real.log (σ * Real.log X) - 48)
      ≤ c * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t)
          (Real.exp (1 / σ)) :=
    mul_le_mul_of_nonneg_left hd hc0.le
  have h2 : c * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t)
        (Real.exp (1 / σ))
      ≤ (1 / Real.exp 1) * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t)
          (Real.exp (1 / σ)) :=
    mul_le_mul_of_nonneg_right hce hnn
  linarith

/-! ## §2 — the majorant's interval integrability

`HalaszDirect.sigma_core_intervalIntegrable` (:216) is `private` to its file; the statement is
re-derived here byte-for-byte (Iron rule 1, the private-lemma restatement law). -/

/-- Local copy of `HalaszDirect.sigma_core_intervalIntegrable` (`private` there).  The σ-cutoff
integrand `σ ↦ σ^{−2}·exp(−c(M − 2log(σL) − 48))` is interval-integrable on `[1/L, b]`
(continuity: `σ ≥ 1/L > 0` on the range, so neither `σ^2` nor `σ·L` vanishes). -/
private lemma sigma_core_intervalIntegrable {c L M b : ℝ} (hL : 0 < L) (hb : 1 / L ≤ b) :
    IntervalIntegrable
      (fun σ : ℝ => (1 / σ ^ 2) * Real.exp (-c * (M - 2 * Real.log (σ * L) - 48)))
      volume (1 / L) b := by
  have hLinv0 : (0 : ℝ) < 1 / L := by positivity
  have hpos : ∀ σ ∈ Set.uIcc (1 / L) b, (0 : ℝ) < σ := by
    intro σ hσ
    rw [Set.uIcc_of_le hb, Set.mem_Icc] at hσ
    exact lt_of_lt_of_le hLinv0 hσ.1
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.mul ?_ ?_
  · exact continuousOn_const.div (continuousOn_pow 2) (fun σ hσ => pow_ne_zero 2 (hpos σ hσ).ne')
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub continuousOn_const ?_)
      continuousOn_const)
    exact continuousOn_const.mul (ContinuousOn.log
      ((continuous_id.mul continuous_const).continuousOn)
      (fun σ hσ => (mul_pos (hpos σ hσ) hL).ne'))

/-! ## §3 — the shared reduction (M-shaped)

The M-shaped analogue of `HalaszDirect.halasz_direct_reduce` (:245, `private` there): the true
integrand `‖F(1+σ+it)‖/σ` is dominated on `[1/logX, b]` by `C_F ×` the σ-cutoff's integrand at
exponent `c`, with the explicit `pretDistSq` in place of `M_range`.  Each face then finishes by
citing ITS OWN σ-cutoff instance (the S-3 guard). -/

/-- The `c`-generic M-shaped reduction.  `X > 0` is an explicit hypothesis here (see the
positivity trap in the file header: the window supplied it for free, the plain cap does not). -/
private lemma halasz_direct_center_reduce {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀ t X b : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hL : 3 ≤ Real.log X) (hX : 0 < X) (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1)
    (hcap : |t| ≤ X)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      volume (1 / Real.log X) b) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
        * ∫ σ in (1 / Real.log X)..b,
            (1 / σ ^ 2) * Real.exp (-c
              * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
                - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hLinv0 : (0 : ℝ) < 1 / Real.log X := by positivity
  have hexplog : Real.exp (Real.log X) = X := Real.exp_log hX
  have hpoint : ∀ σ ∈ Set.Icc (1 / Real.log X) b,
      ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ
        ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((1 / σ ^ 2) * Real.exp (-c
              * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
                - 2 * Real.log (σ * Real.log X) - 48))) := by
    intro σ hσ
    have hσ0 : (0 : ℝ) < σ := lt_of_lt_of_le hLinv0 hσ.1
    have hσ1 : σ ≤ 1 := le_trans hσ.2 hb1
    have hinvσ : 1 / σ ≤ Real.log X := by
      have h := one_div_le_one_div_of_le hLinv0 hσ.1
      rwa [one_div_one_div] at h
    have hYX : Real.exp (1 / σ) ≤ X := by
      calc Real.exp (1 / σ) ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hinvσ
        _ = X := hexplog
    have hkey := window_sup_decay_center (t₀ := t₀) hg hc0 hce hσ0 hσ1 hYX hcap
    rw [div_le_iff₀ hσ0]
    have hid : Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((1 / σ ^ 2) * Real.exp (-c
              * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
                - 2 * Real.log (σ * Real.log X) - 48))) * σ
        = Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
          * Real.exp (-c * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
              - 2 * Real.log (σ * Real.log X) - 48)) := by
      field_simp
    rw [hid]
    exact hkey
  have hmaj := (sigma_core_intervalIntegrable
    (c := c) (L := Real.log X)
    (M := pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X) (b := b)
    hLpos hb).const_mul (Real.exp (cpeel + (Real.log 4 + cpeel)))
  have hmono := intervalIntegral.integral_mono_on hb hint hmaj hpoint
  rwa [intervalIntegral.integral_const_mul] at hmono

/-! ## §4 (A-3) — THE TWO M-SHAPED FACES

Each arm cites its own σ-cutoff instance.  **The LIVE GUARD is law: `_half` may not appear in a
§8.3 consumer.**  Note that no `hM0` hypothesis is needed on either face: the M-shaped exponent
is a `pretDistSq`, whose nonnegativity is free (`pretDistSq_nonneg`). -/

/-- **A-3/BALL ARM — the M-shaped direct-form Halász core at `c = 1/(2e)`**
(`halasz_direct_center`).  For `g` 1-bounded at primes, `logX ≥ 3`, `X > 0`, `1/logX ≤ b ≤ 1`,
ANY frequency `t` under the plain cap `|t| ≤ X`, and the socketed integrability,

  `∫_{1/logX}^{b} ‖F_seam(1+σ+it)‖/σ dσ
     ≤ C_F·(e^{48/(2e)}/(1−1/e))·exp(−(1/(2e))·𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t; X))·logX`.

**M-SHAPED** (⟦AMENDMENT V2⟧ #4): the exponent is the explicit `pretDistSq` at `t`, not
`M_range`, and there is no numeral — numeric exponents live ONLY at consumers where `hfloor`
lives.

**THE LIVE GUARD (freeze v2 + ⟦AMENDMENT V2⟧ #5, verbatim): "L3's arm cites
`sigma_cutoff_pretentious_of_gen` (c = 1/e); the ball's arm cites `_half` (c = 1/(2e)); a
citation of `_half` in any §8.3 consumer is a STOP."  "The LIVE GUARD extended: a §8.3 consumer
citing `_half` OR the ball-graded head of `center_halasz_supply` is a STOP."**  THIS face cites
`sigma_cutoff_pretentious_half` (`SeamBallWeighted` :392) and is the BALL arm's supply ONLY — a
§8.3/L3 consumer of this statement is a STOP; use `halasz_direct_center_gen`. -/
theorem halasz_direct_center {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X b : ℝ} (hL : 3 ≤ Real.log X) (hX : 0 < X)
    (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1) (hcap : |t| ≤ X)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      volume (1 / Real.log X) b) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          * Real.log X := by
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE2 : (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
  have hce : 1 / (2 * Real.exp 1) ≤ 1 / Real.exp 1 := by
    rw [div_le_div_iff₀ (by positivity) hEpos]
    nlinarith
  have hCFnn : (0 : ℝ) ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) := Real.exp_nonneg _
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  -- `hM0` is FREE on the M-shaped exponent
  have hM0 : 0 ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X :=
    pretDistSq_nonneg _ _ _ hSeamOne (fun n => le_of_eq (costwist_norm t n))
  refine (halasz_direct_center_reduce (c := 1 / (2 * Real.exp 1)) hg hc0 hce hL hX hb hb1
    hcap hint).trans ?_
  -- THE BALL CITATION: the halved instance (a §8.3 consumer of this line is a STOP)
  have hsc := sigma_cutoff_pretentious_half (L := Real.log X)
      (M := pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X) (C := 48) (b := b)
      hL hM0 (by norm_num) hb
  have hconv : -(pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
        / (2 * Real.exp 1))
      = -(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X := by ring
  rw [hconv] at hsc
  calc Real.exp (cpeel + (Real.log 4 + cpeel))
        * (∫ σ in (1 / Real.log X)..b,
            (1 / σ ^ 2) * Real.exp (-(1 / (2 * Real.exp 1))
              * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
                - 2 * Real.log (σ * Real.log X) - 48)))
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
              * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
              * Real.log X) := mul_le_mul_of_nonneg_left hsc hCFnn
    _ = Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          * Real.log X := by ring

/-- **A-3/§8.3-L3 ARM — the M-shaped direct-form Halász core at `c = 1/e`**
(`halasz_direct_center_gen`).  The same σ-integral at the un-halved exponent:

  `∫_{1/logX}^{b} ‖F_seam(1+σ+it)‖/σ dσ
     ≤ C_F·(e^{48/e}/(1−2/e))·exp(−(1/e)·𝔻²(seamCoeff (ellLin g) 1 t₀, costwist t; X))·logX`.

**M-SHAPED** (⟦AMENDMENT V2⟧ #4), as above.

**THE LIVE GUARD (freeze v2 + ⟦AMENDMENT V2⟧ #5, verbatim): "L3's arm cites
`sigma_cutoff_pretentious_of_gen` (c = 1/e); the ball's arm cites `_half` (c = 1/(2e)); a
citation of `_half` in any §8.3 consumer is a STOP."  "The LIVE GUARD extended: a §8.3 consumer
citing `_half` OR the ball-graded head of `center_halasz_supply` is a STOP."**  THIS is the
§8.3/L3 arm's face — the un-halved ledger; it cites `sigma_cutoff_pretentious_of_gen`
(`SeamBallWeighted` :416) and nothing halved. -/
theorem halasz_direct_center_gen {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X b : ℝ} (hL : 3 ≤ Real.log X) (hX : 0 < X)
    (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1) (hcap : |t| ≤ X)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      volume (1 / Real.log X) b) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1)
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          * Real.log X := by
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hCFnn : (0 : ℝ) ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) := Real.exp_nonneg _
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  have hM0 : 0 ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X :=
    pretDistSq_nonneg _ _ _ hSeamOne (fun n => le_of_eq (costwist_norm t n))
  refine (halasz_direct_center_reduce (c := 1 / Real.exp 1) hg hc0 le_rfl hL hX hb hb1
    hcap hint).trans ?_
  -- THE §8.3/L3 CITATION: the `c = 1/e` instance
  have hsc := sigma_cutoff_pretentious_of_gen (L := Real.log X)
      (M := pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X) (C := 48) (b := b)
      hL hM0 (by norm_num) hb
  have hconv : -(pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
        / Real.exp 1)
      = -(1 / Real.exp 1)
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X := by ring
  rw [hconv] at hsc
  calc Real.exp (cpeel + (Real.log 4 + cpeel))
        * (∫ σ in (1 / Real.log X)..b,
            (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1)
              * (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X
                - 2 * Real.log (σ * Real.log X) - 48)))
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
              * Real.exp (-(1 / Real.exp 1)
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
              * Real.log X) := mul_le_mul_of_nonneg_left hsc hCFnn
    _ = Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1)
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          * Real.log X := by ring

/-! ## §5 — the hint-free faces

`BallSup.intervalIntegrable_seam_lseries_div` (:611) discharges the socketed integrability
hypothesis; it needs only `0 < logX` and `1/logX ≤ b` (checked against its statement — it does
NOT need `b ≤ 1`, `X > 0`, or any window). -/

/-- **The ball arm's M-shaped centre core, HINT-FREE.**  `halasz_direct_center` with its
socketed integrability discharged by `BallSup.intervalIntegrable_seam_lseries_div`.

**BALL ARM ONLY** — the LIVE GUARD, verbatim: *"L3's arm cites
`sigma_cutoff_pretentious_of_gen` (c = 1/e); the ball's arm cites `_half` (c = 1/(2e)); a
citation of `_half` in any §8.3 consumer is a STOP."*  A §8.3/L3 consumer of THIS statement is
a STOP — use `halasz_direct_center_gen_free`. -/
theorem halasz_direct_center_free {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X b : ℝ} (hL : 3 ≤ Real.log X) (hX : 0 < X)
    (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1) (hcap : |t| ≤ X) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
          * Real.exp (-(1 / (2 * Real.exp 1))
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          * Real.log X :=
  halasz_direct_center hg hL hX hb hb1 hcap
    (intervalIntegrable_seam_lseries_div hg (by linarith) hb)

/-- **The §8.3/L3 arm's M-shaped centre core, HINT-FREE.**  `halasz_direct_center_gen` with its
socketed integrability discharged by `BallSup.intervalIntegrable_seam_lseries_div`.

**THE LIVE GUARD**, verbatim: *"L3's arm cites `sigma_cutoff_pretentious_of_gen` (c = 1/e); the
ball's arm cites `_half` (c = 1/(2e)); a citation of `_half` in any §8.3 consumer is a STOP."*
THIS is the §8.3/L3 face — it cites nothing halved. -/
theorem halasz_direct_center_gen_free {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X b : ℝ} (hL : 3 ≤ Real.log X) (hX : 0 < X)
    (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1) (hcap : |t| ≤ X) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1)
              * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t) X)
          * Real.log X :=
  halasz_direct_center_gen hg hL hX hb hb1 hcap
    (intervalIntegrable_seam_lseries_div hg (by linarith) hb)

/-! ## §6 (A-10) — the ball-centre dichotomy

⟦AMENDMENT V2⟧ repair #4's stone.  Pure geometry: `seamT0 X = (logX)^{1/15}`,
`seamRad X = (logX)^{1/16}` (`SeamSplit` :92/:96), `seamAnn X T = {t | seamT0 X ≤ |t| ∧ |t| ≤ T}`
(:100), `seamBall X t₁ = {t | |t − t₁| ≤ seamRad X}` (:103).  **No floor is asserted here** —
the floor supply in the live branch is the consumer's business (M-shaped discipline). -/

/-- The radius is smaller than the inner cut as soon as `logX > 1`: for a base `b > 1`,
`b^{1/16} < b^{1/15}` because the EXPONENT is smaller (`Real.rpow_lt_rpow_left_iff`).  This is
what makes the small-centre branch of the dichotomy non-vacuous. -/
lemma seamRad_lt_seamT0 {X : ℝ} (hL : 1 < Real.log X) : seamRad X < seamT0 X :=
  (Real.rpow_lt_rpow_left_iff hL).mpr (by norm_num)

/-- The small-centre branch, STRICT cut: if `|t₁| < seamT0 X − seamRad X` then the ball misses
the annulus entirely.  Geometry: every `t` in the ball has
`|t| ≤ |t₁| + |t − t₁| < (seamT0 X − seamRad X) + seamRad X = seamT0 X`, strictly below the
annulus's lower cut `seamT0 X ≤ |t|`.

**The cut must be STRICT** (the half-open correction; see the file header): `seamAnn` closes at
`seamT0 X ≤ |t|`, so at the non-strict cut `t₁ = seamT0 X − seamRad X`, `t = seamT0 X` lies in
BOTH sets and the intersection is `{seamT0 X}`, not `∅`.  The non-strict form survives at the
integral level — `seamAnn_inter_seamBall_subset_pair` / `ball_leg_empty_of_le`. -/
lemma seamAnn_inter_seamBall_eq_empty {X T t₁ : ℝ}
    (hsmall : |t₁| < seamT0 X - seamRad X) :
    seamAnn X T ∩ seamBall X t₁ = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  have h1 : seamT0 X ≤ |t| := ht.1.1
  have h2 : |t - t₁| ≤ seamRad X := ht.2
  have h3 : |t| - |t₁| ≤ |t - t₁| := abs_sub_abs_le_abs_sub t t₁
  linarith

/-- The small-centre branch, NON-STRICT cut: at `|t₁| ≤ seamT0 X − seamRad X` the intersection
is contained in the two touching points `{−seamT0 X, seamT0 X}` — a null set.  (It is genuinely
nonempty there: `t₁ = seamT0 X − seamRad X`, `t = seamT0 X`.) -/
lemma seamAnn_inter_seamBall_subset_pair {X T t₁ : ℝ}
    (hle : |t₁| ≤ seamT0 X - seamRad X) :
    seamAnn X T ∩ seamBall X t₁ ⊆ {-seamT0 X, seamT0 X} := by
  intro t ht
  have h1 : seamT0 X ≤ |t| := ht.1.1
  have h2 : |t - t₁| ≤ seamRad X := ht.2
  have h3 : |t| - |t₁| ≤ |t - t₁| := abs_sub_abs_le_abs_sub t t₁
  have habs : |t| = seamT0 X := le_antisymm (by linarith) h1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases abs_choice t with h | h
  · exact Or.inr (h.symm.trans habs)
  · refine Or.inl ?_
    have hneg : -t = seamT0 X := h.symm.trans habs
    linarith

/-- **A-10 — THE BALL-CENTRE DICHOTOMY** (`ball_center_dichotomy`).  For ANY centre `t₁` (the
row's free centre) and any `X`, `T`: EITHER the ball leg's integration domain is empty, OR the
centre is at least `seamT0 X − seamRad X` away from the origin (the BALL-LIVE branch).

  `seamAnn X T ∩ seamBall X t₁ = ∅  ∨  seamT0 X − seamRad X ≤ |t₁|`

This is the case split A-9 consumes.  In the first branch the ball leg's integral is `0`
(`ball_leg_empty`, and `ball_leg_of_center_small` in `ball_leg_of_sup_weighted`'s exact
conclusion shape).  In the second, **no floor is asserted here**: supplying the floor at `t₁` on
the enlarged window is the consumer's business (the M-shaped discipline, ⟦AMENDMENT V2⟧ #4).

The dichotomy needs NO hypotheses at all.  `seamRad_lt_seamT0` (at `logX > 1`) is what makes the
first branch non-vacuous. -/
theorem ball_center_dichotomy (X T t₁ : ℝ) :
    seamAnn X T ∩ seamBall X t₁ = ∅ ∨ seamT0 X - seamRad X ≤ |t₁| := by
  by_cases h : seamT0 X - seamRad X ≤ |t₁|
  · exact Or.inr h
  · exact Or.inl (seamAnn_inter_seamBall_eq_empty (not_le.mp h))

/-- The empty branch at the INTEGRAL level (strict cut): the ball leg vanishes identically, for
any integrand. -/
theorem ball_leg_empty {X T t₁ : ℝ} (F : ℝ → ℝ)
    (hsmall : |t₁| < seamT0 X - seamRad X) :
    (∫ t in seamAnn X T ∩ seamBall X t₁, F t) = 0 := by
  rw [seamAnn_inter_seamBall_eq_empty hsmall, setIntegral_empty]

/-- The empty branch at the INTEGRAL level, NON-STRICT cut — the freeze's literal statement,
recovered: at `|t₁| ≤ seamT0 X − seamRad X` the ball leg still vanishes, because the residual
intersection is the null set `{−seamT0 X, seamT0 X}`. -/
theorem ball_leg_empty_of_le {X T t₁ : ℝ} (F : ℝ → ℝ)
    (hle : |t₁| ≤ seamT0 X - seamRad X) :
    (∫ t in seamAnn X T ∩ seamBall X t₁, F t) = 0 := by
  refine setIntegral_measure_zero F ?_
  refine measure_mono_null (seamAnn_inter_seamBall_subset_pair hle) ?_
  exact Set.Finite.measure_zero (Set.toFinite _) volume

/-- The empty branch in `SeamBallWeighted.ball_leg_of_sup_weighted`'s EXACT conclusion shape
(:162–168), discharged with NO `hSup` binder and no arithmetic hypotheses whatsoever: when the
centre is small the ball leg is `0 ≤ 8·S²`. -/
theorem ball_leg_of_center_small {N : ℕ} {a : ℕ → ℂ} {X T t₁ S : ℝ}
    (hle : |t₁| ≤ seamT0 X - seamRad X) :
    (∫ t in seamAnn X T ∩ seamBall X t₁, ‖spoly N a t‖ ^ 2) ≤ 8 * S ^ 2 := by
  rw [ball_leg_empty_of_le _ hle]
  positivity

end Salt.MR
