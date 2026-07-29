/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.GrandComp
import Salt.MR.SeamBallWeighted

/-!
# HALÁSZ-DIRECT — the direct-form Halász core (H-6)

The H-block's σ-integral core (`docs/exploration/hsup-design.md`, ⟦THE H-BLOCK FREEZE v2⟧,
node **H-6**): the LANDED pointwise `L`-series decay at `1+σ` (`SupF.head_sigma_bound`,
σ-uniform by construction) integrated over `σ` — **without the max-modulus step**.

## The source page we replace (GHS, `docs/sources/1706.03749v1.pdf`, p.2 + p.13)

Granville–Harper–Soundararajan, *A new proof of Halász's theorem, and its consequences*:

* **Theorem 1.1 (Halász).**  For `f ∈ 𝒞(κ)`,
  `∑_{n≤x} f(n) ≪_κ (x/log x)·∫_{1/log x}^{1} (max_{|t|≤(log x)^κ} |F(1+σ+it)/(1+σ+it)|)·dσ/σ
     + (x/log x)(loglog x)^κ`.
* **Corollary 1.2.**  With `M = M(x)` defined by
  `max_{|t|≤(log x)^κ} |F(1+1/log x+it)/(1+1/log x+it)| =: e^{−M}(log x)^κ`,
  `∑_{n≤x} f(n) ≪_κ (1+M)·e^{−M}·x·(log x)^{κ−1} + (x/log x)(loglog x)^κ`.
* **Its proof (p.13) — the step we REPLACE.**  "We use the maximum modulus principle in the
  region `{u+iv : 1+1/log x ≤ u ≤ 2, |v| ≤ (log x)^κ}` to bound
  `max_{|t|≤(log x)^κ} |F(1+σ+it)/(1+σ+it)|`.  By the definition of `M = M(x)`, the maximum of
  this quantity along the vertical line segment `u = 1+1/log x` is `e^{−M}(log x)^κ` … on the
  horizontal segments `|v| = (log x)^κ`, `|F(u+iv)/(u+iv)|` may be bounded by
  `ζ(1+1/log x)^κ/(log x)^κ = O(1)`, and the same bound holds on the vertical line segment
  `u = 2`.  Thus `max_{|t|≤(log x)^κ}|F(1+σ+it)/(1+σ+it)| ≤ e^{−M}(log x)^κ + O_κ(1)
  ≪ e^{−M}(log x)^κ`."  Then the trivial bound `≤ (1/σ + O(1))^κ`, and the σ-integral is split
  at `σ = e^{M/κ}/log x` into `≪_κ e^{−M}(log x)^κ·M/κ + e^{−M}(log x)^κ` — **the two-regime
  split that BIRTHS the `(1+M)` factor** (our `HExit.sigma_cutoff` :1226 is that page, κ = 1).

## Why the corpus does not need the max-modulus step (the direct form)

`SupF.head_sigma_bound` (:818) is *already* the σ-uniform bound the max-modulus argument is
used to manufacture — and it is **pointwise in `t`**, proved from the Euler product on the
line `Re s = 1+σ` (no analytic continuation into the box, no horizontal segments, no `ζ`
comparison on `u = 2`):

  `‖F(1+σ+it)‖ ≤ C_F·(1/σ)·exp(−(1/e)·𝔻²(1, g·p^{−it}; e^{1/σ}))`,  `C_F = e^{cpeel+(log4+cpeel)}`.

Two consequences, both strictly better than the source page:

1. **No max-modulus.**  The σ-uniformity is supplied by the proof, not recovered from a
   boundary principle.  The `t`-dependence stays honest: the decay is at the distance to the
   twist `p^{−it}` at that very `t`, floored on the `M_range` window by
   `SupF.scale_floor_Mrange_seam` (:1155).
2. **No `(1+M)` factor.**  The direct bound carries the *scale* of the distance, `e^{1/σ}`, so
   the floor costs `−2log(σ·logX) − 48` and the integrand is `K·σ^{2c−2}` — convergent at the
   top end for `2c < 1`.  The σ-integral therefore closes **flat**, with no two-regime split:
   the exits below are `C·e^{−c·M_range}·logX`, where GHS pay `(1+M)e^{−M}`.  The linear-in-`M`
   factor of Corollary 1.2 simply does not arise on this route.

## ⟦THE S-3 CITATION GUARD — LAW FOR THIS FILE⟧

From the freeze (⟦THE H-BLOCK FREEZE v2⟧, verbatim):

> **THE LIVE GUARD (replaces the tripwire)**: L3's arm cites
> `sigma_cutoff_pretentious_of_gen` (c = 1/e); the ball's arm cites `_half`
> (c = 1/(2e)); **a citation of `_half` in any §8.3 consumer is a STOP** — both instances
> landed side-by-side, discipline is the only requirement.

This file serves BOTH arms and keeps them separate by construction — two exits, each citing
its own σ-cutoff instance:

* `halasz_direct_gen` — the **§8.3/L3 arm's supply**, `c = 1/e`, citing
  `SeamBallWeighted.sigma_cutoff_pretentious_of_gen` (:416).  This is the un-halved ledger
  (ρ = 1/(32e)); §8.3 consumers take THIS one.
* `halasz_direct_ball` — the **ball arm's supply**, `c = 1/(2e)`, citing
  `SeamBallWeighted.sigma_cutoff_pretentious_half` (:392).  The ½ is the (A.11)/(A.13)/(A.14)
  𝒥-symmetrisation price, **paid downstream in the 𝒯₀/ball assembly, NOT in this integral**;
  it appears here only because the ball's consumer wants its supply already at the halved
  exponent.  A §8.3 consumer citing this exit is a STOP.

## WHERE THE `c` ACTUALLY ENTERS (the honest finding, H-6's charge)

**The `c` enters the SUPPLY, not the spend — and the halving is a free monotone weakening,
not a cost paid here.**

* The *spend* (`sigma_cutoff_pretentious_gen`, :325) is `c`-generic: it consumes any pointwise
  majorant of the shape `σ ↦ σ^{−2}·exp(−c(M − 2log(σL) − C))` with `0 < c`, `2c < 1`.  Nothing
  in the σ-integral prefers one `c`.
* The *supply* (`head_sigma_bound`) is hard-pinned at `c = 1/e`: the `1/e` is the termwise cut
  `p^{−σ} ≥ 1/e` for `p ≤ e^{1/σ}` inside `SupF.sigma_cut_lower` — i.e. the exponent is the
  price of truncating the prime sum at the scale `Y = e^{1/σ}`, not a choice.
* The halving is therefore NOT re-derived: `𝔻² ≥ 0` (`pretDistSq_nonneg`) makes
  `exp(−(1/e)𝔻²) ≤ exp(−c·𝔻²)` for every `0 < c ≤ 1/e`, and the `M_range` floor is applied
  AFTER the weakening (order matters: applying the floor first would need `M − 2log(σL) − 48 ≥ 0`,
  which is false near the top of the σ-range).  `window_sup_decay_gen` below is exactly that
  two-line page, and it is the only place any `c ≠ 1/e` appears in this file.

## What lands here

* `window_sup_decay_gen` [D1] — the general-`c` window pointwise decay (`0 < c ≤ 1/e`), the
  `c`-freed clone of `GrandComp.window_sup_decay` (:299).  Both arms are fed by this ONE
  pointwise bound.
* `halasz_direct_gen` [D2, `c = 1/e`] and `halasz_direct_ball` [D2, `c = 1/(2e)`] — the two
  exits: the σ′-integrated bound `∫_{1/logX}^{b} ‖F_seam(1+σ′+it)‖/σ′ dσ′ ≤ C·e^{−c·M_range}·logX`
  at a window frequency `t`, for any upper limit `b ∈ [1/logX, 1]` (the `2η`/`2/log y`-grade
  cutoffs are instances: the flat bound holds regardless of the top).
* `halasz_direct_ball_window` [D3] — the ball-restricted corollary: for `t` in
  `seamAnn X T ∩ seamBall X t₁`, the window membership is FREE (H-0's window-legality win:
  `seamT0 X = (logX)^{1/45}` is `M_range`'s floor byte-for-byte, `|t| ≤ T ≤ T + (logX)^{1/46}`,
  and `|t| ≤ T ≤ X`).  The shape H-7 consumes.

## Honest hypotheses (nothing hidden)

* `hint` — interval-integrability of the true integrand `σ ↦ ‖F(1+σ+it)‖/σ` is SOCKETED, per
  the corpus idiom (`HExit.sigma_cutoff` :1228, `JointHead.sigma_wiring` :274).  It is a
  property of the `L`-series along a horizontal segment inside `Re s > 1` (continuity from
  `LSeries` differentiability), not of the estimate; this file does not claim it.
* `b ≤ 1` is the honest top of `head_sigma_bound`'s `σ ∈ (0,1]` window; `1/logX ≤ σ` is what
  makes `e^{1/σ} ≤ X` (the floor's scale condition) automatic on the whole range.
* `hM0 : 0 ≤ M_range …` is `sigma_cutoff_pretentious_gen`'s own hypothesis (nonneg `M`), and
  is free from `pretDistSq_nonneg` at any consumer that has the window nonempty.
* `X > 0` is NOT assumed: it is derived from the window membership (`|t| ≤ X` with
  `|t| ≥ (logX)^{1/45} ≥ 1`) — mathlib's `Real.log` is even, so `3 ≤ log X` alone does not
  give it (a banked trap).

Source pins: GHS `1706.03749v1` Thm 1.1 / Cor 1.2 (p.2) + proof (p.13); MRT v3 Appendix
A.6/A.13/A.14 for the ball arm's ½.
-/

noncomputable section

namespace Salt.MR

open MeasureTheory

/-! ## §0 — the twist-algebra copy

`GrandComp.dist_triv_left_eq` (:277) is `private` to its file; the identity is re-derived here
byte-for-byte (no statement change, Iron rule 1), exactly as `SupF` re-derives the `HalaszHead`
twist lemmas it cannot reach. -/

/-- Local copy of `GrandComp.dist_triv_left_eq` (`private` there): the trivial-left-datum
distance `𝔻²(1, f·costwist(−t); X)` equals `𝔻²(f, costwist t; X)`. -/
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

/-! ## §1 (D1) — the general-`c` pointwise window decay

The ONE pointwise supply both arms consume.  `head_sigma_bound`'s `1/e` is weakened to any
`0 < c ≤ 1/e` BEFORE the `M_range` floor is applied — the order is load-bearing (see the
"where the `c` enters" note in the file header). -/

/-- **D1 — the general-`c` window head decay** (`window_sup_decay_gen`).  For a globally
1-bounded (at primes) `g`, an exponent `0 < c ≤ 1/e`, `σ ∈ (0,1]` with `e^{1/σ} ≤ X`, and a
frequency `t` in the `M_range` window,

  `‖F_seam(1+σ+it)‖ ≤ C_F·(1/σ)·exp(−c·(M_range(seamCoeff (ellLin g) 1 t₀; X,T)
      − 2·log(σ·logX) − 48))`,  `C_F = exp(cpeel + (log 4 + cpeel))`.

The `c`-freed clone of `GrandComp.window_sup_decay` (:299).  Proof: `head_sigma_bound` at the
seam datum, its distance rewritten to the bare `ℓ`-datum shifted-center form
(`dist_triv_left_eq_local` + `seamCoeff_trivial_dist_eq`), then the exponent chain
`c·(M − 2log(σL) − 48) ≤ c·𝔻² ≤ (1/e)·𝔻²` — the first step by the floor
(`scale_floor_Mrange_seam`, `c > 0`), the second by `𝔻² ≥ 0` and `c ≤ 1/e`. -/
theorem window_sup_decay_gen {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀ t X T σ : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hYX : Real.exp (1 / σ) ≤ X)
    (hmem : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X) :
    ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
        (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
        * Real.exp (-c * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
            - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hEllOne : ∀ n : ℕ, ‖ellLin g n‖ ≤ 1 := fun n => ellLin_norm_le_one g hg n
  have hSeamOne : ∀ n : ℕ, ‖seamCoeff (ellLin g) (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hEllOne (fun _ => le_of_eq norm_one) t₀ n
  have hHead := head_sigma_bound (g := seamCoeff (ellLin g) (fun _ => 1) t₀) hSeamOne hσ0 hσ1 t
  have hdist_eq :
      pretDistSq (fun _ => 1)
          (fun n => seamCoeff (ellLin g) (fun _ => 1) t₀ n * costwist (-t) n) (Real.exp (1 / σ))
        = pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ)) :=
    (dist_triv_left_eq_local (seamCoeff (ellLin g) (fun _ => 1) t₀) t (Real.exp (1 / σ))).trans
      (seamCoeff_trivial_dist_eq t₀ t (Real.exp (1 / σ)))
  rw [hdist_eq] at hHead
  refine hHead.trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Real.exp_nonneg _) (div_nonneg zero_le_one hσ0.le))
  apply Real.exp_le_exp.mpr
  have hd := scale_floor_Mrange_seam (t₀ := t₀) hg hσ0 hσ1 hYX hmem
  have hnn : 0 ≤ pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ)) :=
    pretDistSq_nonneg _ _ _ hEllOne (fun n => le_of_eq (costwist_norm (t + t₀) n))
  have h1 : c * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
        - 2 * Real.log (σ * Real.log X) - 48)
      ≤ c * pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ)) :=
    mul_le_mul_of_nonneg_left hd hc0.le
  have h2 : c * pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ))
      ≤ (1 / Real.exp 1) * pretDistSq (ellLin g) (costwist (t + t₀)) (Real.exp (1 / σ)) :=
    mul_le_mul_of_nonneg_right hce hnn
  linarith

/-! ## §2 — the majorant's interval integrability

The σ-cutoff stones compute the majorant's integral in closed form, but
`intervalIntegral.integral_mono_on` needs its integrability separately: the integrand is
continuous on `[1/L, b]` because the whole range is bounded away from `0`. -/

/-- The σ-cutoff integrand `σ ↦ σ^{−2}·exp(−c(M − 2log(σL) − 48))` is interval-integrable on
`[1/L, b]` (continuity: `σ ≥ 1/L > 0` on the range, so neither `σ^2` nor `σ·L` vanishes). -/
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

/-! ## §3 — the shared reduction (pointwise decay → the σ-cutoff's integrand)

The half of the exits that is `c`-generic: the true integrand `‖F(1+σ+it)‖/σ` is dominated on
`[1/logX, b]` by `C_F ×` the σ-cutoff's integrand at exponent `c`.  Each exit then finishes by
citing ITS OWN σ-cutoff instance (the S-3 guard). -/

/-- The `c`-generic reduction: `∫ ‖F_seam(1+σ+it)‖/σ ≤ C_F·∫ σ^{−2}exp(−c(M_range − 2log(σL) − 48))`
on `[1/logX, b]`, for `0 < c ≤ 1/e` and `b ≤ 1`.  The scale condition `e^{1/σ} ≤ X` of the floor
holds automatically: `σ ≥ 1/logX` gives `1/σ ≤ logX`, and `X > 0` comes from the window
membership (`1 ≤ (logX)^{1/45} ≤ |t| ≤ X`), NOT from `3 ≤ log X` (mathlib's `Real.log` is even). -/
private lemma halasz_direct_reduce {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {c t₀ t X T b : ℝ} (hc0 : 0 < c) (hce : c ≤ 1 / Real.exp 1)
    (hL : 3 ≤ Real.log X) (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1)
    (hmem : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      volume (1 / Real.log X) b) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
        * ∫ σ in (1 / Real.log X)..b,
            (1 / σ ^ 2) * Real.exp (-c * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
              - 2 * Real.log (σ * Real.log X) - 48)) := by
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hLinv0 : (0 : ℝ) < 1 / Real.log X := by positivity
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by linarith
  -- `X > 0` from the window membership (NOT from `3 ≤ log X`: `Real.log` is even)
  have hr15 : (1 : ℝ) ≤ (Real.log X) ^ (1 / 45 : ℝ) := Real.one_le_rpow hlogX1 (by norm_num)
  have hXpos : (0 : ℝ) < X := by
    have := hmem.1
    have := hmem.2.2
    linarith
  have hexplog : Real.exp (Real.log X) = X := Real.exp_log hXpos
  -- the pointwise domination on the σ-range
  have hpoint : ∀ σ ∈ Set.Icc (1 / Real.log X) b,
      ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ
        ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((1 / σ ^ 2) * Real.exp (-c * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
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
    have hkey := window_sup_decay_gen (t₀ := t₀) hg hc0 hce hσ0 hσ1 hYX hmem
    rw [div_le_iff₀ hσ0]
    have hid : Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((1 / σ ^ 2) * Real.exp (-c * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
              - 2 * Real.log (σ * Real.log X) - 48))) * σ
        = Real.exp (cpeel + (Real.log 4 + cpeel)) * (1 / σ)
          * Real.exp (-c * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
              - 2 * Real.log (σ * Real.log X) - 48)) := by
      field_simp
    rw [hid]
    exact hkey
  have hmaj := (sigma_core_intervalIntegrable
    (c := c) (L := Real.log X)
    (M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) (b := b) hLpos hb).const_mul
    (Real.exp (cpeel + (Real.log 4 + cpeel)))
  have hmono := intervalIntegral.integral_mono_on hb hint hmaj hpoint
  rwa [intervalIntegral.integral_const_mul] at hmono

/-! ## §4 (D2) — THE TWO EXITS

Each arm cites its own σ-cutoff instance.  **The S-3 guard is law: `_half` may not appear in a
§8.3 consumer.** -/

/-- **D2/§8.3-L3 ARM — the direct-form Halász core at `c = 1/e`** (`halasz_direct_gen`).
For `g` 1-bounded at primes, `logX ≥ 3`, `1/logX ≤ b ≤ 1`, `M_range ≥ 0`, a frequency `t` in
the `M_range` window, and the socketed integrability of the true integrand,

  `∫_{1/logX}^{b} ‖F_seam(1+σ+it)‖/σ dσ
     ≤ C_F·(e^{48/e}/(1−2/e))·exp(−(1/e)·M_range(seamCoeff (ellLin g) 1 t₀; X,T))·logX`,

with `C_F = exp(cpeel + (log 4 + cpeel))`.  This is GHS Corollary 1.2's σ-integral WITHOUT the
max-modulus step and WITHOUT the `(1+M)` factor (see the file header).

**THE CITATION GUARD (freeze v2, verbatim): "L3's arm cites `sigma_cutoff_pretentious_of_gen`
(c = 1/e); the ball's arm cites `_half` (c = 1/(2e)); a citation of `_half` in any §8.3
consumer is a STOP."**  THIS is the §8.3/L3 arm's supply — the un-halved ledger
(ρ = 1/(32e)); it cites `sigma_cutoff_pretentious_of_gen` (`SeamBallWeighted` :416) and nothing
halved. -/
theorem halasz_direct_gen {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X T b : ℝ} (hL : 3 ≤ Real.log X) (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1)
    (hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
    (hmem : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X)
    (hint : IntervalIntegrable
      (fun σ : ℝ => ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      volume (1 / Real.log X) b) :
    (∫ σ in (1 / Real.log X)..b,
        ‖LSeries (ellLin (seamCoeff (ellLin g) (fun _ => 1) t₀))
          (((1 + σ : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ / σ)
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hc0 : (0 : ℝ) < 1 / Real.exp 1 := by positivity
  have hCFnn : (0 : ℝ) ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) := Real.exp_nonneg _
  refine (halasz_direct_reduce (c := 1 / Real.exp 1) hg hc0 le_rfl hL hb hb1 hmem hint).trans ?_
  -- THE §8.3/L3 CITATION: the `c = 1/e` instance
  have hsc := sigma_cutoff_pretentious_of_gen (L := Real.log X)
      (M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) (C := 48) (b := b)
      hL hM0 (by norm_num) hb
  have hconv : -(M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T / Real.exp 1)
      = -(1 / Real.exp 1) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T := by ring
  rw [hconv] at hsc
  calc Real.exp (cpeel + (Real.log 4 + cpeel))
        * (∫ σ in (1 / Real.log X)..b,
            (1 / σ ^ 2) * Real.exp (-(1 / Real.exp 1)
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                - 2 * Real.log (σ * Real.log X) - 48)))
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
              * Real.exp (-(1 / Real.exp 1)
                  * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
              * Real.log X) := mul_le_mul_of_nonneg_left hsc hCFnn
    _ = Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / Real.exp 1) / (1 - 2 / Real.exp 1))
          * Real.exp (-(1 / Real.exp 1)
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by ring

/-- **D2/BALL ARM — the direct-form Halász core at `c = 1/(2e)`** (`halasz_direct_ball`).
The same σ-integral, graded at the HALVED exponent:

  `∫_{1/logX}^{b} ‖F_seam(1+σ+it)‖/σ dσ
     ≤ C_F·(e^{48/(2e)}/(1−1/e))·exp(−(1/(2e))·M_range(seamCoeff (ellLin g) 1 t₀; X,T))·logX`.

**Where the ½ comes from — and where it does NOT.**  It is the (A.11) 𝒥-symmetrisation square
root propagating through MRT (A.13)/(A.14), **paid downstream in the 𝒯₀/ball assembly, not in
this integral**: here it is a free monotone weakening of the SAME pointwise supply
(`window_sup_decay_gen` at `c = 1/(2e)`, legal because `𝔻² ≥ 0`), taken so the ball's consumer
receives its supply already at the exponent it will spend.

**THE CITATION GUARD (freeze v2, verbatim): "L3's arm cites `sigma_cutoff_pretentious_of_gen`
(c = 1/e); the ball's arm cites `_half` (c = 1/(2e)); a citation of `_half` in any §8.3
consumer is a STOP."**  THIS exit cites `sigma_cutoff_pretentious_half` (`SeamBallWeighted`
:392) and is the BALL arm's supply ONLY.  A §8.3/L3 consumer of this statement is a STOP —
use `halasz_direct_gen`. -/
theorem halasz_direct_ball {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t X T b : ℝ} (hL : 3 ≤ Real.log X) (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1)
    (hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
    (hmem : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 46 : ℝ) ∧ |t| ≤ X)
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
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by
  have hEpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hE2 : (2 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hc0 : (0 : ℝ) < 1 / (2 * Real.exp 1) := by positivity
  have hce : 1 / (2 * Real.exp 1) ≤ 1 / Real.exp 1 := by
    rw [div_le_div_iff₀ (by positivity) hEpos]
    nlinarith
  have hCFnn : (0 : ℝ) ≤ Real.exp (cpeel + (Real.log 4 + cpeel)) := Real.exp_nonneg _
  refine (halasz_direct_reduce (c := 1 / (2 * Real.exp 1)) hg hc0 hce hL hb hb1 hmem hint).trans ?_
  -- THE BALL CITATION: the halved instance (a §8.3 consumer of this line is a STOP)
  have hsc := sigma_cutoff_pretentious_half (L := Real.log X)
      (M := M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) (C := 48) (b := b)
      hL hM0 (by norm_num) hb
  have hconv : -(M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T / (2 * Real.exp 1))
      = -(1 / (2 * Real.exp 1)) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T := by ring
  rw [hconv] at hsc
  calc Real.exp (cpeel + (Real.log 4 + cpeel))
        * (∫ σ in (1 / Real.log X)..b,
            (1 / σ ^ 2) * Real.exp (-(1 / (2 * Real.exp 1))
              * (M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T
                - 2 * Real.log (σ * Real.log X) - 48)))
      ≤ Real.exp (cpeel + (Real.log 4 + cpeel))
          * ((Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
              * Real.exp (-(1 / (2 * Real.exp 1))
                  * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
              * Real.log X) := mul_le_mul_of_nonneg_left hsc hCFnn
    _ = Real.exp (cpeel + (Real.log 4 + cpeel))
          * (Real.exp (48 / (2 * Real.exp 1)) / (1 - 1 / Real.exp 1))
          * Real.exp (-(1 / (2 * Real.exp 1))
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by ring

/-! ## §5 (D3) — the ball-restricted corollary (the H-7 shape)

H-0's window-legality win, cashed: on the ball's own integration domain
`seamAnn X T ∩ seamBall X t₁` the `M_range` window membership is FREE.  `seamT0 X` is
`M_range`'s floor `(logX)^{1/45}` byte-for-byte; `|t| ≤ T ≤ T + (logX)^{1/46}` needs only
`logX ≥ 0`; `|t| ≤ X` needs only `T ≤ X`.  The ball hypothesis itself is carried for the
consumer's shape — the floor does not need it (that is exactly why H-0 was a free win). -/

/-- **D3 — the ball-restricted direct core** (`halasz_direct_ball_window`).  For `t` in the
seam annulus `Ann(T₀,T)` and the ball `B(t₁, seamRad X)` (the weighted ball leg's own
integration domain), with `T ≤ X`, the `c = 1/(2e)` exit holds with NO separate window
hypothesis:

  `∫_{1/logX}^{b} ‖F_seam(1+σ+it)‖/σ dσ
     ≤ C_F·(e^{48/(2e)}/(1−1/e))·exp(−(1/(2e))·M_range(…))·logX`.

This is the shape H-7 assembles into `ball_leg_of_sup_weighted`'s binder.  Ball arm only —
the S-3 guard (see `halasz_direct_ball`). -/
theorem halasz_direct_ball_window {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {t₀ t t₁ X T b : ℝ} (hL : 3 ≤ Real.log X) (hTX : T ≤ X)
    (hb : 1 / Real.log X ≤ b) (hb1 : b ≤ 1)
    (hM0 : 0 ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
    (hann : t ∈ seamAnn X T) (_hball : t ∈ seamBall X t₁)
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
              * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T)
          * Real.log X := by
  have hLnn : (0 : ℝ) ≤ Real.log X := by linarith
  have h16 : (0 : ℝ) ≤ (Real.log X) ^ (1 / 46 : ℝ) := Real.rpow_nonneg hLnn _
  have h1 : (Real.log X) ^ (1 / 45 : ℝ) ≤ |t| := hann.1
  have h2 : |t| ≤ T := hann.2
  exact halasz_direct_ball hg hL hb hb1 hM0 ⟨h1, by linarith, le_trans h2 hTX⟩ hint

end Salt.MR
