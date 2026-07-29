/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.SupplyGeneric
import Salt.MR.SeamBallWeighted
import Salt.MR.SeamLemma14

/-!
# S8 ladder, node A2-3 — THE `T₀`-BAND SUPPLY (`T0Band`)

Freeze: `docs/exploration/s8-freeze-0727.md` row A2-3, **SETTLED AS OPTION W** by
⟦AMENDMENT A⟧ — *one FREE-CENTRE ball of radius `≥ seamT0` covering `[−T₀,T₀]`, through
`SupplyGeneric`'s centre-uniform chain*.  This file produces the `B₀` of
`ThmA2Spine.thm_a2_spine`'s binder

  `hT0band : ∫_{−T₀}^{T₀} ‖dpolyA a (seamS0 N X) t‖² dt ≤ B₀`,  `T₀ = seamT0 X = (log X)^{1/45}`.

## THE RADIUS-FREEDOM VERDICT (the node's design question, answered)

The kill-check asked whether the corpus's centre chain survives at the WIDER radius `T₀`
(`seamRad X = (log X)^{1/46} < (log X)^{1/45} = seamT0 X` — `CenterCore.seamRad_lt_seamT0`).
Reading the chain end to end:

* **`SupplyGeneric.center_halasz_supply_Y` (:257) mentions no radius at all.**  Its subject is
  the CENTRE partial sum `∑_{n≤k} f(n)·e^{−it₁ log n}`; `t₁` is a top-level `∀`-bound real and
  the four `Y`-gates, `hRHS` and the grade page are radius-blind.  So the chain is
  *centre-uniform AND radius-free*, exactly as the verdict said — nothing to repair.
* **`BallSup.budget_le_half` / `exp_budget_le` (:141–193) are radius-free by construction**
  (the KC-A23B finding, confirmed here): their only datum is `u = f·n^{−it₁}`, the CENTRE
  twist.  The `7/8`-page analogue (here the honest `1/2`-cut) never sees `|t − t₁|`.
* **The radius is pinned in exactly ONE place**: `BallSup.ball_sup_of_center` (:473) fixes
  `seamRad X` in its `hball` binder, and it enters the proof at exactly two monotone steps —
  `BallSup.ballErr_le`'s majorant (`r ≤ seamRad X` inside `ballLterm`) and the payment of the
  weight (`1 + |t − t₁| ≤ 1 + seamRad X`).  Both are monotone in the radius, so the twin at a
  FREE radius `R` (§2 below) is the landed page with `seamRad X` replaced by `R`, and
  `bandSupS X (seamRad X) = ballSupS X` holds by `rfl` (`bandSupS_seamRad`).

Consequently option W costs no new analysis: only the explicit `R`-dependence of the error
constant, priced in the grade note below.  **Iron rule 1 is respected literally**: no landed
statement is touched, no existing file is edited; every stone here is a new twin.

## THE CENTRE IS `0` BY CHOICE (Amendment A / Amendment B's ban)

A `t₁`-ball of radius `T₀` covers `[−T₀,T₀]` only at `t₁ = 0`, so the exit
(`t0_band_supply`) instantiates the free centre at `0`.  **`SupStation`'s internally
produced centre is never touched, and `FarArm` is never cited** — the ban of ⟦AMENDMENT B⟧,
honoured by construction: the free-centre chain is the only supplier in this file.

Note also U-3: the interior `|t| ≤ T₀` cannot be paid by `M_range` (its window floor
`|t| ≥ (log X)^{1/45}` is structural), so the band pays ENTIRELY on the ball side — which is
what this file does.

## The stones

* §1 `bandLterm` / `bandTail` / `bandSupS` and `ballErr_le_radius` — `BallSup`'s error page
  at a FREE radius; `bandSupS_seamRad` is the `rfl` cross-check against the landed constant.
* §2 `band_sup_of_center` [B-1] — `BallSup.ball_sup_of_center` at a free radius, with the two
  annulus binders DROPPED (they are unused in the landed proof — `intro t _hann0 _hann1`).
* §3 `band_sup_supplied_Y` [B-1′] — the crown: §2 fed by `SupplyGeneric`'s `y`-generic,
  centre-uniform chain.  Free `Y`, free centre, free radius, no annulus.
* §4 `band_integral_of_sup` [B-2] — the band integral from the weighted sup, through the
  landed `SeamSplit.spoly_abel_sup` and `SeamBallWeighted.integral_ballWeight_le`:
  `∫_{−R}^{R} ‖dpolyA a (seamS0 N X) t‖² ≤ 8·S²` — the measure × sup² device in its
  WEIGHTED form (the Cauchy weight kills the `2R` factor; see the grade note).
* §5 `t0BandS` / `t0BandB` / `t0_band_supply` [B-3] — THE EXIT, in `thm_a2_spine`'s binder
  shape, at centre `0` and radius `seamT0 X`.

## THE HONEST GRADE NOTE (no `o(1)`; every factor written out)

With `T₀ = (log X)^{1/45}`, `M = 𝔻²(f, n^{it₁}; X)` at `t₁ = 0`, and

  `S₀ = C₁·exp(−M/(2e)) + 4·(log X)^{−1/2+1/1000}`  (the centre bound's coefficient),
  `bandTail X T₀ = 4·ballSupC·(1 + log(3 + T₀·(1 + log(2X))))/√(log X)`,
  `S_band = bandSupS X T₀ S₀ = 2√2·S₀ + bandTail X T₀·(1 + T₀)`,

the exit is `B₀ = t0BandB X C₁ M = 8·S_band²`, i.e.

  `B₀ ≤ 128·S₀² + 16·(bandTail X T₀·(1 + T₀))²`.

* **The main term** is `8·(2√2·S₀)² = 64·S₀² ≈ 64·C₁²·exp(−M/e)` — byte-for-byte
  ⟦AMENDMENT A⟧'s pinned interface term (`8·(2√2·C₁′)² = 64C₁′²`, no `M`-shaped factor),
  and there is **no `T₀` factor on it**: the weight `1/(1+|t|)` survives inside the integral,
  so the Cauchy page `∫_ℝ (1+|u|)^{−2} du ≤ 2` pays the whole band.  (The crude alternative
  — throw the weight away and use `measure × sup²` — gives `2T₀·(2S)² = 8T₀·S²` instead, i.e.
  the same expression multiplied by `T₀ = (log X)^{1/45}`.  It is NOT taken; the weighted
  form is strictly stronger and is the shape ⟦AMENDMENT A⟧ priced.)
* **The error term** is the fourth summand of the pinned interface.  The exact log factor is
  `1 + log(3 + T₀·(1 + log(2X)))` — note `log(2X)`, the dyadic TOP, not `log X`; at
  `T₀ = (log X)^{1/45}` it is `(46/45)·loglog X · (1 + o(1))`, so

    `bandTail X T₀·(1 + T₀) ≍ 4·ballSupC·(46/45)·loglog X·(log X)^{1/45 − 1/2}
       = (log X)^{−43/90 + o(1)}`,

  and its square, the fourth summand, is `(log X)^{−43/45 + o(1)}`.
* **The margin.**  The interface's third summand is `(log X)^{−1/500}`, so the fourth summand
  sits under it with exponent margin `43/45 − 1/500 = 0.9536…` — a factor `477×` in the
  exponent.  The main term likewise dominates it: `exp(−M/e) ≥ (log X)^{−1/(16e)}` on the
  live band (`M < (1/16)·loglog X`) and `1/(16e) = 0.02299… ≪ 43/45`.
* **The cost of option W, exactly.**  At the landed radius `seamRad X` the same square is
  `(log X)^{−7/8+o(1)}` (⟦AMENDMENT A⟧'s number); at `T₀` it is `(log X)^{−43/45+o(1)}`.  The
  price of widening the recentring radius is therefore
  `2·(1/45 − 1/46) = 1/1035` of an exponent — `(log X)^{1/1035}`, against the `477×` margin.
  That is the whole cost of option W, and it is why the covering route (option C, with its
  `(log X)^{1/240}` balls and the `~29×` `M`-demand) is not needed.

## What is CARRIED (named, never hidden)

`hRHS` (the joint-head grade socket at the free `Y`) and `hMcap` (the A-10 ball-centre
dichotomy) are binders, exactly as in `CenterSupply.ball_sup_supplied` and
`SupplyGeneric.ball_sup_supplied_Y` upstream — this file transfers a supply across a radius,
it does not manufacture the centre's Halász bound.  At `t₁ = 0` both read at `costwist 0`.

**LIVE GUARD** (inherited verbatim from `CenterSupply`/`SupplyGeneric`): the exponent here is
the BALL arm's halved constant `c = 1/(2e)`; a §8.3 consumer citing this head is a STOP.
-/

noncomputable section

namespace Salt.MR

open Complex MeasureTheory
open scoped BigOperators

/-! ## §1 — `BallSup`'s error page at a FREE radius

`BallSup.ballLterm`/`ballTail`/`ballSupS` with `seamRad X` replaced by a free `R`.  The
landed constants are the `R := seamRad X` instances, definitionally (`bandSupS_seamRad`). -/

/-- The ball's log-factor at radius `R`: `1 + log(3 + R·(1 + log(2X)))` — `BallSup.ballLterm`
with the radius freed.  (The inner `log(2X)` is the dyadic top, as upstream.) -/
def bandLterm (X R : ℝ) : ℝ :=
  1 + Real.log (3 + R * (1 + Real.log (2 * X)))

/-- The tail coefficient at radius `R`, before the weight is paid — `BallSup.ballTail`
with the radius freed. -/
def bandTail (X R : ℝ) : ℝ :=
  4 * ballSupC * bandLterm X R / Real.sqrt (Real.log X)

/-- **The exit constant at radius `R`** — `BallSup.ballSupS` with the radius freed:
`S = 2√2·S₀ + bandTail X R·(1 + R)`. -/
def bandSupS (X R S₀ : ℝ) : ℝ :=
  2 * Real.sqrt 2 * S₀ + bandTail X R * (1 + R)

/-- **The cross-check**: at the landed radius the twin IS the landed constant, definitionally.
(The evidence that §1–§3 really are `BallSup`'s page with one slot freed.) -/
lemma bandSupS_seamRad (X S₀ : ℝ) : bandSupS X (seamRad X) S₀ = ballSupS X S₀ := rfl

lemma bandLterm_pos {X R : ℝ} (hX : 3 ≤ X) (hR : 0 ≤ R) : 0 < bandLterm X R := by
  have hlog : 0 ≤ Real.log (2 * X) := Real.log_nonneg (by linarith)
  have h3 : (1 : ℝ) ≤ 3 + R * (1 + Real.log (2 * X)) := by nlinarith
  have := Real.log_nonneg h3
  unfold bandLterm
  linarith

lemma bandTail_nonneg {X R : ℝ} (hX : 3 ≤ X) (hR : 0 ≤ R) : 0 ≤ bandTail X R := by
  have h1 := bandLterm_pos hX hR
  have h2 := ballSupC_pos
  unfold bandTail
  positivity

lemma bandSupS_nonneg {X R S₀ : ℝ} (hX : 3 ≤ X) (hR : 0 ≤ R) (hS₀ : 0 ≤ S₀) :
    0 ≤ bandSupS X R S₀ := by
  have h1 : 0 ≤ bandTail X R * (1 + R) := mul_nonneg (bandTail_nonneg hX hR) (by linarith)
  have h2 : 0 ≤ 2 * Real.sqrt 2 * S₀ := mul_nonneg (by positivity) hS₀
  unfold bandSupS
  linarith

/-- **The error majorant at a FREE radius** — `BallSup.ballErr_le` with `seamRad X` replaced
by `R`.  Both monotonicities are the landed ones: `x/√(log x)` increases and the log-factor
increases in both the radius and the scale. -/
lemma ballErr_le_radius {X x r R : ℝ} (hX : 3 ≤ X) (hx : X ≤ x) (hx2 : x ≤ 2 * X)
    (hr : 0 ≤ r) (hrad : r ≤ R) :
    ballErr x r ≤ bandTail X R * X / 2 := by
  have hR0 : (0 : ℝ) ≤ R := le_trans hr hrad
  have hX0 : (0 : ℝ) < X := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hE : Real.exp 1 ≤ X := by
    have := Real.exp_one_lt_d9
    linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hE
  have hlogx : Real.log X ≤ Real.log x := Real.log_le_log hX0 hx
  have hsX : 0 < Real.sqrt (Real.log X) := Real.sqrt_pos.mpr (by linarith)
  have hmono : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hlogx
  -- (i) the `x/√(log x)` factor
  have hxq : x / Real.sqrt (Real.log x) ≤ 2 * X / Real.sqrt (Real.log X) := by
    rw [div_le_div_iff₀ (lt_of_lt_of_le hsX hmono) hsX]
    have ha : x * Real.sqrt (Real.log X) ≤ 2 * X * Real.sqrt (Real.log X) :=
      mul_le_mul_of_nonneg_right hx2 hsX.le
    have hb : 2 * X * Real.sqrt (Real.log X) ≤ 2 * X * Real.sqrt (Real.log x) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    linarith
  -- (ii) the log-factor
  have hlog2X : Real.log x ≤ Real.log (2 * X) := Real.log_le_log hx0 (by linarith)
  have hlogx0 : (0 : ℝ) ≤ Real.log x := by linarith
  have hinner : 3 + r * (1 + Real.log x) ≤ 3 + R * (1 + Real.log (2 * X)) := by
    have : r * (1 + Real.log x) ≤ R * (1 + Real.log (2 * X)) :=
      mul_le_mul hrad (by linarith) (by linarith) hR0
    linarith
  have hpos : (0 : ℝ) < 3 + r * (1 + Real.log x) := by nlinarith
  have hLog : 1 + Real.log (3 + r * (1 + Real.log x)) ≤ bandLterm X R := by
    unfold bandLterm
    have := Real.log_le_log hpos hinner
    linarith
  -- assemble
  have hC := ballSupC_pos
  have hLt := bandLterm_pos hX hR0
  have hq0 : (0 : ℝ) ≤ x / Real.sqrt (Real.log x) := by positivity
  have hlogpos : (0 : ℝ) ≤ 1 + Real.log (3 + r * (1 + Real.log x)) := by
    have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 3 + r * (1 + Real.log x))
    linarith
  calc ballErr x r
      = ballSupC * (x / Real.sqrt (Real.log x))
          * (1 + Real.log (3 + r * (1 + Real.log x))) := rfl
    _ ≤ ballSupC * (2 * X / Real.sqrt (Real.log X)) * bandLterm X R := by
        gcongr
    _ = bandTail X R * X / 2 := by
        unfold bandTail
        ring

/-! ## §2 (B-1) — the centre-to-ball transfer at a FREE radius -/

/-- **B-1 — `band_sup_of_center`: `BallSup.ball_sup_of_center` at a FREE radius.**

  `(∀ k ∈ [⌊X⌋₊, N], ‖∑_{n≤k} f(n)n^{−it₁}‖ ≤ S₀·k)  ⟹
     ∀ t with |t − t₁| ≤ R, ∀ m ≤ N, ‖A_t(m)‖ ≤ bandSupS X R S₀ · m/(1+|t−t₁|)`.

Two differences from the landed page, both recorded in the module header:

* the radius is the free `R`, not `seamRad X` (the whole point of option W);
* the two ANNULUS binders (`seamT0 X ≤ |t|`, `|t| ≤ T`) are DROPPED.  They are unused in the
  landed proof (`intro t _hann0 _hann1 hball m hm`) and they are exactly the binders a
  `T₀`-band consumer cannot supply — the band is the region they exclude.

Everything else is `ball_sup_of_center`'s page verbatim: `hDatum`+`hsupp` give
`A_t(m) = F_t(m) − F_t(⌊X⌋₊)` (`spolyA_datum_split`), each full partial sum is transferred to
the centre by `transfer_at_scale`, `hCenter` bounds the two centre sums, the two errors are
majorised by `ballErr_le_radius`, and the weight is paid at `1+|t−t₁| ≤ 1+R`. -/
theorem band_sup_of_center {N : ℕ} {a f : ℕ → ℂ} {X R t₁ S₀ : ℝ}
    (hX : 3 ≤ X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hR : 0 ≤ R)
    (hf1 : f 1 = 1) (hfmul : ∀ p q : ℕ, Nat.Coprime p q → f (p * q) = f p * f q)
    (hfle : ∀ n, ‖f n‖ ≤ 1) (hS₀ : 0 ≤ S₀)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hDatum : ∀ n : ℕ, X < (n : ℝ) → a n = f n)
    (hCenter : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖∑ n ∈ Finset.Icc 1 k, f n * eIu (-t₁) n‖ ≤ S₀ * k)
    (hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => f n * eIu (-t₁) n) (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8) :
    ∀ t : ℝ, |t - t₁| ≤ R →
      ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ bandSupS X R S₀ * m / (1 + |t - t₁|) := by
  intro t hball m hm
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hd : (0 : ℝ) < 1 + |t - t₁| := by positivity
  have hSnn : 0 ≤ bandSupS X R S₀ := bandSupS_nonneg hX hR hS₀
  rw [le_div_iff₀ hd]
  rcases le_or_gt m ⌊X⌋₊ with hcase | hcase
  · -- below the dyadic window the polynomial is empty
    have hz : spolyA a t m = 0 := by
      unfold spolyA
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnm : n ≤ m := (Finset.mem_Icc.mp hn).2
      have hle : (n : ℝ) ≤ X :=
        le_trans (Nat.cast_le.mpr (le_trans hnm hcase)) (Nat.floor_le hX0)
      rw [hsupp n hle, zero_div]
    rw [hz, norm_zero, zero_mul]
    positivity
  · -- the live range `⌊X⌋₊ < m ≤ N ≤ 2X`
    have hkm : ⌊X⌋₊ ≤ m := le_of_lt hcase
    have hXm : X < (m : ℝ) := (Nat.floor_lt hX0).mp hcase
    have hmN : (m : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hm
    have hm2X : (m : ℝ) ≤ 2 * X := le_trans hmN hN2
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := le_trans hX hXm.le
    have hkN : ⌊X⌋₊ ≤ N := Nat.cast_le.mp (le_trans (Nat.floor_le hX0) hXN)
    have hkle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hkm
    -- the datum split
    have hsplit := spolyA_datum_split hX0 hsupp hDatum t hkm
    -- the transfer at scale `m`
    have hAm : ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ)) + ballErr (m : ℝ) |t - t₁| := by
      have h := transfer_at_scale hf1 hfmul hfle (t := t) (t₁ := t₁) (x := (m : ℝ)) hm3
        (hMball (m : ℝ) hXm.le hm2X)
      rw [Nat.floor_natCast] at h
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁|) := by positivity
      have := mul_le_mul_of_nonneg_left (hCenter m hkm hm) hq
      linarith
    -- the transfer at scale `X`
    have hAX : ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n‖
        ≤ Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ)) + ballErr X |t - t₁| := by
      have h := transfer_at_scale hf1 hfmul hfle (t := t) (t₁ := t₁) (x := X) hX
        (hMball X le_rfl (by linarith))
      refine h.trans ?_
      have hq : (0 : ℝ) ≤ Real.sqrt 2 / (1 + |t - t₁|) := by positivity
      have hc := hCenter ⌊X⌋₊ le_rfl hkN
      have hmono : S₀ * ((⌊X⌋₊ : ℕ) : ℝ) ≤ S₀ * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hkle hS₀
      have := mul_le_mul_of_nonneg_left (le_trans hc hmono) hq
      linarith
    -- the two errors, at the free radius
    have hTX0 : (0 : ℝ) ≤ bandTail X R := bandTail_nonneg hX hR
    have hEm : ballErr (m : ℝ) |t - t₁| ≤ bandTail X R * (m : ℝ) / 2 := by
      refine (ballErr_le_radius hX hXm.le hm2X (abs_nonneg _) hball).trans ?_
      have : bandTail X R * X ≤ bandTail X R * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hXm.le hTX0
      linarith
    have hEX : ballErr X |t - t₁| ≤ bandTail X R * (m : ℝ) / 2 := by
      refine (ballErr_le_radius hX le_rfl (by linarith) (abs_nonneg _) hball).trans ?_
      have : bandTail X R * X ≤ bandTail X R * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hXm.le hTX0
      linarith
    -- assemble the pointwise bound
    have hnorm : ‖spolyA a t m‖
        ≤ ‖∑ n ∈ Finset.Icc 1 m, f n * eIu (-t) n‖
          + ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n * eIu (-t) n‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    have hmain : ‖spolyA a t m‖
        ≤ 2 * (Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ))) + bandTail X R * (m : ℝ) := by
      linarith
    -- pay the weight
    have hQd : Real.sqrt 2 / (1 + |t - t₁|) * (1 + |t - t₁|) = Real.sqrt 2 :=
      div_mul_cancel₀ _ (ne_of_gt hd)
    have hTm : (0 : ℝ) ≤ bandTail X R * (m : ℝ) := by positivity
    calc ‖spolyA a t m‖ * (1 + |t - t₁|)
        ≤ (2 * (Real.sqrt 2 / (1 + |t - t₁|) * (S₀ * (m : ℝ)))
            + bandTail X R * (m : ℝ)) * (1 + |t - t₁|) :=
          mul_le_mul_of_nonneg_right hmain hd.le
      _ = 2 * (Real.sqrt 2 / (1 + |t - t₁|) * (1 + |t - t₁|)) * (S₀ * (m : ℝ))
            + bandTail X R * (m : ℝ) * (1 + |t - t₁|) := by ring
      _ = 2 * Real.sqrt 2 * (S₀ * (m : ℝ)) + bandTail X R * (m : ℝ) * (1 + |t - t₁|) := by
          rw [hQd]
      _ ≤ 2 * Real.sqrt 2 * (S₀ * (m : ℝ)) + bandTail X R * (m : ℝ) * (1 + R) := by
          have := mul_le_mul_of_nonneg_left (by linarith : 1 + |t - t₁| ≤ 1 + R) hTm
          linarith
      _ = bandSupS X R S₀ * (m : ℝ) := by
          unfold bandSupS
          ring

/-! ## §3 (B-1′) — the crown: the free-centre, free-radius, `y`-generic supply -/

/-- **B-1′ — `band_sup_supplied_Y`.**  `SupplyGeneric.ball_sup_supplied_Y` (:409) with the
radius FREED and the annulus binders dropped: §2 fed by the `y`-generic, centre-uniform
centre supply `SupplyGeneric.center_halasz_supply_Y`.

  `∀ t with |t − t₁| ≤ R, ∀ m ≤ N,
     ‖spolyA a t m‖ ≤ bandSupS X R S₀ · m/(1+|t−t₁|)`,
  `S₀ = C₁·exp(−(1/(2e))·𝔻²(f, p^{it₁}; X)) + 4·(log X)^{−1/2+1/1000}`.

Nothing in the chain below it sees the radius (the verdict in the module header), so this is
the landed crown with one slot opened.  The carried binders are upstream's own: `hsupp`,
`hDatum`, the four `Y`-gates, `hRHS` (the joint-head grade socket) and `hMcap` (the A-10
ball-centre dichotomy).  **LIVE GUARD**: `c = 1/(2e)`, the BALL arm. -/
theorem band_sup_supplied_Y {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ t₁ : ℝ)
    (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (R C₁ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ R → 0 ≤ C₁ →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
            pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) x
              ≤ (1 / 16) * Real.log (Real.log X)) →
      ∀ t : ℝ, |t - t₁| ≤ R →
        ∀ m : ℕ, m ≤ N →
          ‖spolyA a t m‖
            ≤ bandSupS X R (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
                + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000)) * m / (1 + |t - t₁|) := by
  obtain ⟨X₁, hX₁0, hsupply⟩ := center_halasz_supply_Y hg t₀ Y
  refine ⟨max X₁ ballMertensThreshold, lt_of_lt_of_le hX₁0 (le_max_left _ _), ?_⟩
  intro X N R C₁ a hXlb hXN hN2 hR hC₁0 hsupp hDatum hY10 hYsq hYlow hYlog hRHS hMcap
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hXlb
  have hXth : ballMertensThreshold ≤ X := le_trans (le_max_right _ _) hXlb
  have hX3 : (3 : ℝ) ≤ X := le_trans three_le_ballMertensThreshold hXth
  have hlogX0 : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hB0 : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
      * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) :=
    mul_nonneg hC₁0 (Real.exp_nonneg _)
  have hS₀ : (0 : ℝ) ≤ C₁ * Real.exp (-(1 / (2 * Real.exp 1))
        * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := by
    have h2 : (0 : ℝ) ≤ Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000) := Real.rpow_nonneg hlogX0 _
    linarith
  -- the grade factor, in the supply's `B·k` shape
  have hRHS' : ∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
      ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + t₁ : ℝ) : ℂ) * I)) (t₀ + t₁)
          (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
          (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
        ≤ (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X))
          * (k : ℝ) := by
    intro k h1 h2
    have h := hRHS k h1 h2
    have hring : (C₁ * Real.exp (-(1 / (2 * Real.exp 1))
          * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X)) * (k : ℝ)
        = C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
            * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X) := by ring
    rw [hring]
    exact h
  have hMball : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (fun n => seamCoeff (ellLin g) (fun _ => 1) t₀ n * eIu (-t₁) n)
          (fun _ => 1) x
        ≤ Salt.Mertens.SPartial x / 8 := by
    refine hMball_of_A4_cap hXth ?_
    intro x h1 h2
    rw [← pretDistSq_twist_slot]
    exact hMcap x h1 h2
  exact band_sup_of_center hX3 hXN hN2 hR (seamCoeff_ellLin_one g t₀)
    (seamCoeff_ellLin_mul_coprime g t₀)
    (fun n => norm_seamCoeff_le (fun m => ellLin_norm_le_one g hg m) (fun _ => by simp) t₀ n)
    hS₀ hsupp hDatum
    (hsupply t₁ X N _ hX1 hXN hN2 hB0 hY10 hYsq hYlow hYlog hRHS') hMball

/-! ## §4 (B-2) — the band integral from the weighted sup -/

/-- **B-2 — `band_integral_of_sup`: the band integral, weighted.**  From the CENTRED
(`t₁ = 0`) weighted sup binder at radius `R`,

  `∫_{−R}^{R} ‖dpolyA a (seamS0 N X) t‖² dt ≤ 8·S²`.

The page is `SeamBallWeighted.ball_leg_of_sup_weighted`'s, transplanted to the interval
`[−R,R]` (a proper interval integral, which is the shape `ThmA2Spine.thm_a2_spine` demands):

* `SeamLemma14.spoly_eq_dpolyA_filter` identifies the integrand with `‖spoly N a t‖²`;
* the landed per-`t` Abel inequality `SeamSplit.spoly_abel_sup`, instantiated at
  `S_t := S/(1+|t|)`, gives `‖spoly N a t‖ ≤ 2S/(1+|t|)`;
* `SeamBallWeighted.integral_ballWeight_le` — `∫_{−R}^{R}(1+|u|)^{−2}du ≤ 2`, uniformly in
  `R` — pays the whole band, so **no `2R` measure factor appears**.

The crude alternative (drop the weight, use `measure × sup²`) would give `8R·S²` instead;
at `R = seamT0 X` that is a `(log X)^{1/45}` inflation of the main term.  See the module's
grade note. -/
theorem band_integral_of_sup {N : ℕ} {a : ℕ → ℂ} {X R S : ℝ}
    (hX : 0 < X) (hXN : X ≤ (N : ℝ)) (hN2 : (N : ℝ) ≤ 2 * X) (hR : 0 ≤ R)
    (hsupp : ∀ n : ℕ, (n : ℝ) ≤ X → a n = 0)
    (hSup : ∀ t : ℝ, |t| ≤ R → ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ S * m / (1 + |t|)) :
    (∫ t in (-R)..R, ‖dpolyA a (seamS0 N X) t‖ ^ 2) ≤ 8 * S ^ 2 := by
  have hcong : ∀ t : ℝ, ‖dpolyA a (seamS0 N X) t‖ ^ 2 = ‖spoly N a t‖ ^ 2 := by
    intro t
    rw [spoly_eq_dpolyA_filter hsupp t]
  have hcont : Continuous fun t : ℝ => ‖dpolyA a (seamS0 N X) t‖ ^ 2 :=
    dpolyA_seamS0_normSq_continuous hX.le
  have hgcont : Continuous fun t : ℝ => (2 * S) ^ 2 * (1 / (1 + |t|) ^ 2) := by
    refine continuous_const.mul (continuous_const.div ?_ fun _ => by positivity)
    exact (continuous_const.add continuous_abs).pow 2
  have hdom : ∀ t ∈ Set.Icc (-R) R,
      ‖dpolyA a (seamS0 N X) t‖ ^ 2 ≤ (2 * S) ^ 2 * (1 / (1 + |t|) ^ 2) := by
    intro t ht
    have habs : |t| ≤ R := abs_le.mpr ⟨(Set.mem_Icc.mp ht).1, (Set.mem_Icc.mp ht).2⟩
    have hd : (0 : ℝ) < 1 + |t| := by positivity
    have hA : ∀ m : ℕ, m ≤ N → ‖spolyA a t m‖ ≤ (S / (1 + |t|)) * m := by
      intro m hm
      have h := hSup t habs m hm
      rwa [div_mul_eq_mul_div]
    have hpt : ‖spoly N a t‖ ≤ 2 * (S / (1 + |t|)) := spoly_abel_sup hX hXN hN2 hsupp hA
    rw [hcong t]
    calc ‖spoly N a t‖ ^ 2 ≤ (2 * (S / (1 + |t|))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hpt 2
      _ = (2 * S) ^ 2 * (1 / (1 + |t|) ^ 2) := by field_simp
  calc (∫ t in (-R)..R, ‖dpolyA a (seamS0 N X) t‖ ^ 2)
      ≤ ∫ t in (-R)..R, (2 * S) ^ 2 * (1 / (1 + |t|) ^ 2) :=
        intervalIntegral.integral_mono_on (by linarith)
          (hcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _) hdom
    _ = (2 * S) ^ 2 * ∫ t in (-R)..R, 1 / (1 + |t|) ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (2 * S) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (integral_ballWeight_le hR) (sq_nonneg _)
    _ = 8 * S ^ 2 := by ring

/-! ## §5 (B-3) — THE EXIT: `thm_a2_spine`'s `B₀` -/

/-- The band's sup constant: `bandSupS` at the `T₀`-radius and the centre bound's own
coefficient.  `M` is the centre's pretentious distance `𝔻²(f, n^{it₁}; X)` at `t₁ = 0`. -/
def t0BandS (X C₁ M : ℝ) : ℝ :=
  bandSupS X (seamT0 X)
    (C₁ * Real.exp (-(1 / (2 * Real.exp 1)) * M)
      + 4 * Real.log X ^ (-(1 : ℝ) / 2 + 1 / 1000))

/-- **`B₀` — the `T₀`-band bound** `8·S_band²`, the quantity `ThmA2Spine.thm_a2_spine`'s
`hT0band` binder consumes.  Fully explicit: unfolding gives

  `8·(2√2·(C₁·e^{−M/(2e)} + 4(log X)^{−1/2+1/1000})
        + (4·ballSupC·(1 + log(3 + T₀(1+log 2X)))/√(log X))·(1 + T₀))²`,
  `T₀ = seamT0 X = (log X)^{1/45}`.

Main term `64·(C₁·e^{−M/(2e)} + …)²` — no `T₀` factor, no `M`-shaped factor; fourth-summand
residue `(log X)^{−43/45+o(1)}`.  See the module's grade note for the margin. -/
def t0BandB (X C₁ M : ℝ) : ℝ := 8 * t0BandS X C₁ M ^ 2

/-- **B-3 — THE `T₀`-BAND SUPPLY (`t0_band_supply`).**  Option W, executed: ONE free-centre
ball, centre `t₁ = 0` BY CHOICE, radius `seamT0 X = (log X)^{1/45}` — which covers
`[−T₀,T₀]` exactly — fed by `SupplyGeneric`'s centre-uniform `y`-generic chain, and turned
into the band integral by the weighted Cauchy page.  The exit is literally
`ThmA2Spine.thm_a2_spine`'s `hT0band` binder:

  `∫_{−T₀}^{T₀} ‖dpolyA a (seamS0 N X) t‖² dt ≤ t0BandB X C₁ M`,
  `M = 𝔻²(seamCoeff(ℓ(g),1,t₀), n^{i·0}; X)`.

**`SupStation`'s produced centre and `FarArm` are never touched** (⟦AMENDMENT B⟧'s ban): the
centre is the free `0`, and the only chain cited is `center_halasz_supply_Y`.

The carried binders are upstream's, at `t₁ = 0`: the four `Y`-gates (any split point `Y`
meeting them — e.g. `ypin2 ∘ log`, whose gates `SupplyGeneric.ball_sup_closed_star2`
discharges from the single family gate `pin2Gate ≤ k`), `hRHS` (the joint-head grade socket)
and `hMcap` (the A-10 ball-centre cap at the centre `0`).  Nothing else. -/
theorem t0_band_supply {g : ℕ → ℂ} (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (t₀ : ℝ) (Y : ℝ → ℝ) :
    ∃ X₀ : ℝ, 0 < X₀ ∧
      ∀ (X : ℝ) (N : ℕ) (C₁ : ℝ) (a : ℕ → ℂ),
        X₀ ≤ X → X ≤ (N : ℝ) → (N : ℝ) ≤ 2 * X → 0 ≤ C₁ →
        (∀ n : ℕ, (n : ℝ) ≤ X → a n = 0) →
        (∀ n : ℕ, X < (n : ℝ) → a n = seamCoeff (ellLin g) (fun _ => 1) t₀ n) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → 10 ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Y (k : ℝ) ≤ Real.sqrt (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N → Real.sqrt (Real.log (k : ℝ)) ≤ Y (k : ℝ)) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            Real.log (Y (k : ℝ)) ≤ Real.sqrt (Real.log (k : ℝ))) →
        (∀ k : ℕ, ⌊X⌋₊ ≤ k → k ≤ N →
            ‖prop21RHS (fun p => g p * (p : ℂ) ^ (-((t₀ + 0 : ℝ) : ℂ) * I)) (t₀ + 0)
                (k : ℝ) ((k : ℝ) / Real.sqrt (Real.log (k : ℝ))) (1 + 1 / Real.log (k : ℝ))
                (Y (k : ℝ)) (1 / Real.log (Y (k : ℝ)))‖
              ≤ C₁ * (k : ℝ) * Real.exp (-(1 / (2 * Real.exp 1))
                  * pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist 0) X)) →
        (∀ x : ℝ, X ≤ x → x ≤ 2 * X →
            pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist 0) x
              ≤ (1 / 16) * Real.log (Real.log X)) →
        (∫ t in (-(seamT0 X))..(seamT0 X), ‖dpolyA a (seamS0 N X) t‖ ^ 2)
          ≤ t0BandB X C₁
              (pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist 0) X) := by
  obtain ⟨X₀, hX₀0, H⟩ := band_sup_supplied_Y hg t₀ 0 Y
  refine ⟨max X₀ 3, lt_of_lt_of_le hX₀0 (le_max_left _ _), ?_⟩
  intro X N C₁ a hXlb hXN hN2 hC₁0 hsupp hDatum hY10 hYsq hYlow hYlog hRHS hMcap
  have hX0' : X₀ ≤ X := le_trans (le_max_left _ _) hXlb
  have hX3 : (3 : ℝ) ≤ X := le_trans (le_max_right _ _) hXlb
  have hX0 : (0 : ℝ) < X := by linarith
  have hT0 : (0 : ℝ) ≤ seamT0 X := seamT0_nonneg (Real.log_nonneg (by linarith))
  have hband := H X N (seamT0 X) C₁ a hX0' hXN hN2 hT0 hC₁0 hsupp hDatum
    hY10 hYsq hYlow hYlog hRHS hMcap
  simp only [sub_zero] at hband
  have hfinal := band_integral_of_sup (N := N) (a := a) (X := X) (R := seamT0 X)
    hX0 hXN hN2 hT0 hsupp hband
  simpa only [t0BandB, t0BandS] using hfinal

end Salt.MR
