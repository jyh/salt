/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.MWindowBridge
import Salt.MR.FarStar

/-!
# THE D10-AT-CENTRE REPAIR — the M-window bridge at the station's OWN reach

`MWindowBridge.M_window_bridge_seam` (:323) supplies the station's distance floor on
MRT's box `|v| ≤ X`.  The station does not consume it there.  **The consumption site,
read:** `SPartStation.dilated_scale_grade` (:540–558) uses `hM₀` at the frequency
`v = t − t₀` for every `t` in the dilated scale's recentring window
`|t − (t₀+t₁)| ≤ T*(k, log k)`, so the frequencies actually touched are

  `|v| ≤ |t₁| + T*(k, log k)`,  `k ≤ 2X`,  i.e.  `|v| ≤ |t₁| + T*(2X, log 2X) ≤ Rad`,

and `Rad` enters `seam_ball_leg_station_M_gen` (:886–888) ONLY through that gate and that
binder.  The corpus's own radius is `FarStar.seamGateRstar X T = T + seamRad X +
T*(2X, log 2X) + 1` (`seam_gate_star_of_nonempty` supplies the gate there), which at the
row's `T := X` is `X + (log X)^{1/46} + T*(2X, log 2X) + 1` — **genuinely larger than `X`**.
So the landed bridge cannot serve a box centre as stated: finding 3 of the summit freeze
(⟦AMENDMENT I⟧) is real, and this file repairs it.

## The repair, and why it costs nothing

The far leg of the bridge is `dist_one_floor_pow`-driven, and that stone is valid at EVERY
separation `|b| ≥ 1` — the `2X` in `MWindowBridge.dist_floor_far_sep` is not a domain, it is
the single height at which the (antitone) floor shape is evaluated.  Promoting that height to
a parameter therefore extends the bridge to an ARBITRARY reach `R`, with the shape read at
the honest triangle bound `R + W` (reach + window).  Nothing landed is widened: every
statement here is a new additive twin (the measure-cage discipline), and at `R := X`,
`W := X` the height `R + W` is the landed `2X` on the nose.

## The stones

* **§1 `dist_floor_far_sep_at`** — `MWindowBridge.dist_floor_far_sep` with the evaluation
  height a parameter `B`.
* **§2 `dist_floor_far_reach`** — the window form at reach `R`: reference in `|t'| ≤ Wref`,
  target past the unit collar and inside `|t| ≤ R`, shape at any `B ≥ R + Wref`.
* **§3 `M_window_bridge_reach`** — the assembled `min`, unconditional, at the interface
  object `M_win`, for every `|v| ≤ R`; height `R + W`.
* **§4 `M_window_bridge_seam_reach`** (X-3) — the same at the station's seam datum, at an
  ARBITRARY reach.  This is the general-`Rad` repair: no `2X` is privileged.
* **§5 `M_window_bridge_seam_2X`** (X-1) — the `R := 2X` instance (height `2X + W`), plus
  `M_window_bridge_seam_3X`, its `W ≤ X` reading at the height `3X` the summit named.
* **§6 `hM0_at_centre`** (X-2) — the composition: BOTH members of the station's item (5) at
  one centre — the recentring gate `|t₁| + T*(2X, log 2X) ≤ seamGateRstar X T` and the `hM₀`
  binder on `|v| ≤ seamGateRstar X T`, at
  `M₀ := min (M_win datum X W) ((1/2)(pretFloorShape X (seamGateRstar X T + W) − C)
  − M_win datum X (W−1))`.
* **§7 `pretFloorShape_quarter_at_pow`** — the honest price of the reach: if the height `b`
  obeys `b + 16 ≤ X^A` then `pretFloorShape X b ≥ (1/4)loglog X − (3/4)log A
  − 5 log(1+log A) − 5 logloglog X`.  The reach is paid in ABSOLUTE constants only; the
  `1/4` grade is untouched.  `pretFloorShape_quarter_sq` is the `A = 2` reading with the
  price bounded by the numeral `4`.
* **§8 `Tstar_two_mul_le_quarter` + `seamGateRstar_le_two_mul`** — the verdict made
  concrete: at the station's own scale `X ≥ e^{8192}` the reach exceeds `X` but sits inside
  `2X`, so §5's stone is the operative one and §7 runs at `A = 2`.

## Traps carried

`Real.log` is EVEN, so every positivity step is explicit (never read off a sign); the
`1 ≤ |b|` gate of `dist_one_floor_pow` is structural and is paid by the unit collar exactly
as in the landed file (`Wref + 1 ≤ |t|`, so `|t − t'| ≥ 1` by the triangle inequality alone);
the far slot carries `M_win f X (W − 1) ≥ M_win f X W` (`M_win_anti`) — the safe direction,
and it may NOT be replaced by `M_win f X W`; `min` is consumed through
`min_le_of_left_le`/`min_le_of_right_le` only.
-/

namespace Salt.MR

/-! ## §1 — the far floor with the evaluation height as a parameter -/

/-- **§1 — `dist_floor_far_sep_at`.**  `MWindowBridge.dist_floor_far_sep` with `2X` promoted
to a parameter `B`.  For 1-bounded `f`, `X ≥ e`, and frequencies separated by at least `1`
and at most `B`,

  `(1/2)·(pretFloorShape X B − C) − 𝔻²(f, n^{it'}; X) ≤ 𝔻²(f, n^{it}; X)`.

Same two-step engine (`dist_mul_half` at the triple `(n^{it'}, f, n^{it})`, then the
character shift into `dist_one_floor_pow`); the ONLY change is that the height at which the
antitone shape is read is no longer tied to MRT's box.  `B := 2X` gives the landed stone
back verbatim. -/
theorem dist_floor_far_sep_at :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X B t t' : ℝ),
      Real.exp 1 ≤ X → 1 ≤ |t - t'| → |t - t'| ≤ B →
      (1 / 2) * (pretFloorShape X B - C) - pretDistSq f (costwist t') X
        ≤ pretDistSq f (costwist t) X := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun f hf X B t t' hX hsep1 hsep2 => ?_⟩
  -- the `f = 1` floor at the shifted frequency
  have hfl := hC X (t - t') hX hsep1
  have hshape : pretFloorShape X |t - t'| - C
      ≤ pretDistSq (fun _ => 1) (costwist (t - t')) X := by
    rw [pretFloorShape_def]; exact hfl
  have hmono := pretFloorShape_le_of_le X hsep1 hsep2
  -- the halving, at the triple `(n^{it'}, f, n^{it})`
  have hhalf := dist_mul_half (f := costwist t') (g := f) (h := costwist t) X
    (norm_costwist_le t') hf (norm_costwist_le t)
  rw [pretDistSq_costwist_shift, pretDistSq_comm (costwist t') f] at hhalf
  linarith

/-! ## §2 — the far floor at an arbitrary reach -/

/-- **§2 — `dist_floor_far_reach`.**  `MWindowBridge.dist_floor_far_range` with MRT's box
`|t| ≤ X` replaced by an arbitrary reach `|t| ≤ R` and the height a parameter `B ≥ R + Wref`:

  `(1/2)·(pretFloorShape X B − C) − S ≤ 𝔻²(f, n^{it}; X)`.

The two structural gates are met exactly as in the landed proof, and neither one knows about
`X`: the collar `Wref + 1 ≤ |t|` gives `|t − t'| ≥ |t| − |t'| ≥ 1`, and the triangle
inequality gives `|t − t'| ≤ |t| + |t'| ≤ R + Wref ≤ B`.  At `R := X`, `B := 2X` (where
`Wref ≤ |t| − 1 ≤ X` forces `R + Wref ≤ 2X`) this is `dist_floor_far_range`. -/
theorem dist_floor_far_reach :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X Wref R B t t' S : ℝ),
      Real.exp 1 ≤ X → |t'| ≤ Wref → Wref + 1 ≤ |t| → |t| ≤ R → R + Wref ≤ B →
      pretDistSq f (costwist t') X ≤ S →
      (1 / 2) * (pretFloorShape X B - C) - S ≤ pretDistSq f (costwist t) X := by
  obtain ⟨C, hC⟩ := dist_floor_far_sep_at
  refine ⟨C, fun f hf X Wref R B t t' S hX ht' hcollar hreach hB hcap => ?_⟩
  have hlow : |t| - |t'| ≤ |t - t'| := abs_sub_abs_le_abs_sub t t'
  have hhigh : |t - t'| ≤ |t| + |t'| := by
    rw [sub_eq_add_neg, ← abs_neg t']
    exact abs_add_le _ _
  have habs' : (0 : ℝ) ≤ |t'| := abs_nonneg t'
  have hsep1 : (1 : ℝ) ≤ |t - t'| := by linarith
  have hsep2 : |t - t'| ≤ B := by linarith
  have h := hC f hf X B t t' hX hsep1 hsep2
  linarith

/-! ## §3 — the bridge at an arbitrary reach -/

/-- **§3 — `M_window_bridge_reach`, UNCONDITIONAL.**  `MWindowBridge.M_window_bridge_inf`
with the exit's domain `|v| ≤ X` promoted to `|v| ≤ R`:

  `min (M_win f X W) ((1/2)·(pretFloorShape X (R+W) − C) − M_win f X (W−1))
      ≤ 𝔻²(f, n^{iv}; X)`   for every `|v| ≤ R`.

No relation between `R` and `X`, and no relation between `R` and `W`, is needed: the near
band `|v| ≤ W` is closed by the infimum's own defining property, and on the far band
`W < |v| ≤ R` the height bound is `|v − t'| ≤ R + (W−1) ≤ R + W`.  The reference is supplied
by `M_win_approx` and the `ε` passed to the limit, exactly as in the landed proof — no
minimiser, no compactness, no continuity of `t ↦ 𝔻²`. -/
theorem M_window_bridge_reach :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X W R : ℝ),
      Real.exp 1 ≤ X → 1 ≤ W →
      ∀ v : ℝ, |v| ≤ R →
        min (M_win f X W) ((1 / 2) * (pretFloorShape X (R + W) - C) - M_win f X (W - 1))
          ≤ pretDistSq f (costwist v) X := by
  obtain ⟨C, hC⟩ := dist_floor_far_reach
  refine ⟨C, fun f hf X W R hX hW v hv => ?_⟩
  by_cases hband : |v| ≤ W
  · exact min_le_of_left_le (M_win_le hf X hband)
  · push Not at hband
    refine min_le_of_right_le ?_
    -- the `ε`-form, then the limit
    have hkey : ∀ ε : ℝ, 0 < ε →
        (1 / 2) * (pretFloorShape X (R + W) - C) - M_win f X (W - 1)
          ≤ pretDistSq f (costwist v) X + ε := by
      intro ε hε
      obtain ⟨t', ht', hlt⟩ := M_win_approx f X (by linarith : (0 : ℝ) ≤ W - 1) hε
      have h := hC f hf X (W - 1) R (R + W) v t' (M_win f X (W - 1) + ε) hX ht'
        (by linarith) hv (by linarith) (le_of_lt hlt)
      linarith
    by_contra hcon
    push Not at hcon
    have h := hkey (((1 / 2) * (pretFloorShape X (R + W) - C) - M_win f X (W - 1)
      - pretDistSq f (costwist v) X) / 2) (by linarith)
    linarith

/-! ## §4 — X-3: the general-reach bridge at the station's datum -/

/-- **X-3 — `M_window_bridge_seam_reach`.**  §3 at the station's datum
`seamCoeff (ellLin g) 1 t₀` (1-bounded by `ellLin_norm_le_one` ∘ `norm_seamCoeff_le` from the
corpus-standard PRIME bound on `g`), at an ARBITRARY reach `R`.

This is the D10-at-centre repair in its general form: the station's `hM₀` binder is available
at ANY radius `Rad := R`, with the floor's evaluation height `R + W` printed in the statement.
The consumer instantiates `R` at whatever the recentring gate forces — `2X`, `seamGateRstar
X T`, or anything else — and pays only §7's absolute constant. -/
theorem M_window_bridge_seam_reach :
    ∃ C : ℝ, ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ X W R : ℝ),
      Real.exp 1 ≤ X → 1 ≤ W →
      ∀ v : ℝ, |v| ≤ R →
        min (M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X W)
            ((1 / 2) * (pretFloorShape X (R + W) - C)
              - M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X (W - 1))
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X := by
  obtain ⟨C, hC⟩ := M_window_bridge_reach
  refine ⟨C, fun g hg t₀ X W R hX hW v hv => ?_⟩
  exact hC (seamCoeff (ellLin g) (fun _ => 1) t₀)
    (fun n => norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ n)
    X W R hX hW v hv

/-! ## §5 — X-1: the bridge at the doubled box -/

/-- **X-1 — `M_window_bridge_seam_2X`.**  §4 at `R := 2X`: the station's floor binder on the
DOUBLED box `|v| ≤ 2X`, with the shape read at the honest triangle height `2X + W`
(`|t − t'| ≤ |t| + |t'| ≤ 2X + (W−1)`).  Everything larger than `X` that the recentring gate
can reach — `|t₁| ≤ X + seamRad X` at a box centre, plus the sub-polynomial `T*(2X, log 2X)`
— is inside this box at the station's own scale (§8). -/
theorem M_window_bridge_seam_2X :
    ∃ C : ℝ, ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ X W : ℝ),
      Real.exp 1 ≤ X → 1 ≤ W →
      ∀ v : ℝ, |v| ≤ 2 * X →
        min (M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X W)
            ((1 / 2) * (pretFloorShape X (2 * X + W) - C)
              - M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X (W - 1))
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X := by
  obtain ⟨C, hC⟩ := M_window_bridge_seam_reach
  exact ⟨C, fun g hg t₀ X W hX hW v hv => hC g hg t₀ X W (2 * X) hX hW v hv⟩

/-- **X-1′ — `M_window_bridge_seam_3X`.**  X-1 read at the summit's own height: when the
sieve window sits inside the box (`W ≤ X`), `2X + W ≤ 3X` and the shape may be evaluated at
`3X` instead — a WEAKER floor (`pretFloorShape_le_of_le`), stated only because `3X` is the
height the freeze's finding 3 names.  The `1 ≤ X` gate is what puts the height above the
shape's own monotonicity gate. -/
theorem M_window_bridge_seam_3X :
    ∃ C : ℝ, ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ X W : ℝ),
      Real.exp 1 ≤ X → 1 ≤ W → W ≤ X →
      ∀ v : ℝ, |v| ≤ 2 * X →
        min (M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X W)
            ((1 / 2) * (pretFloorShape X (3 * X) - C)
              - M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X (W - 1))
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X := by
  obtain ⟨C, hC⟩ := M_window_bridge_seam_2X
  refine ⟨C, fun g hg t₀ X W hX hW hWX v hv => ?_⟩
  have hXe : (1 : ℝ) ≤ X := le_trans (by linarith [Real.exp_one_gt_d9]) hX
  have hmono : pretFloorShape X (3 * X) ≤ pretFloorShape X (2 * X + W) :=
    pretFloorShape_le_of_le X (by linarith) (by linarith)
  exact le_trans (min_le_min (le_refl _) (by linarith)) (hC g hg t₀ X W hX hW v hv)

/-! ## §6 — X-2: the station's item (5), BOTH members, at one centre -/

/-- **X-2 — `hM0_at_centre`.**  The composition the finding asks for.  For a centre `t₁`
whose ball meets the annulus (the ball leg's own domain — `seamAnn X T ∩ seamBall X t₁`
nonempty, which is what `FarStar.seam_gate_star_of_nonempty` consumes), BOTH members of
`SPartStation.seam_ball_leg_station_M_gen`'s item (5) hold at `Rad := seamGateRstar X T`:

* the recentring gate `|t₁| + T*(2X, log 2X) ≤ Rad`, and
* the distance floor `∀ v, |v| ≤ Rad → M₀ ≤ 𝔻²(seamCoeff (ellLin F) 1 t₀, n^{iv}; X)` at

  `M₀ = min (M_win datum X W)
            ((1/2)·(pretFloorShape X (seamGateRstar X T + W) − C) − M_win datum X (W−1))`.

The floor's range is `|v| ≤ seamGateRstar X T`, which EXCEEDS `X` — that is the defect, and
§4 is what dissolves it: the reach is a parameter, so the radius the gate forces is exactly
the radius the floor is proved on.  The scale gate is `e^e ≤ X` (needed only to put `2X`
above `Tstar_mono`'s own `e^e`); the station runs at `X ≥ e^{8192}`.

CONSUMER-CHECKED against `SPartStation.seam_ball_leg_station_M_gen` (:879): the pair below
discharges that stone's `hRad`/`hM₀` slots at `Rad := seamGateRstar X T` and `M₀ :=` the
`min`, leaving its other binders untouched.  The check is not carried here — importing the
station would drag `SPartStation` into this file's surface, which is `MWindowBridge`
(the `M_win`/shape machinery) and `FarStar` (`Tstar`, `seamGateRstar`) only. -/
theorem hM0_at_centre :
    ∃ C : ℝ, ∀ (F : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖F p‖ ≤ 1) → ∀ (t₀ t₁ X W T : ℝ),
      Real.exp (Real.exp 1) ≤ X → 1 ≤ W →
      (seamAnn X T ∩ seamBall X t₁).Nonempty →
      |t₁| + Tstar (2 * X) (Real.log (2 * X)) ≤ seamGateRstar X T
        ∧ ∀ v : ℝ, |v| ≤ seamGateRstar X T →
            min (M_win (seamCoeff (ellLin F) (fun _ => 1) t₀) X W)
                ((1 / 2) * (pretFloorShape X (seamGateRstar X T + W) - C)
                  - M_win (seamCoeff (ellLin F) (fun _ => 1) t₀) X (W - 1))
              ≤ pretDistSq (seamCoeff (ellLin F) (fun _ => 1) t₀) (costwist v) X := by
  obtain ⟨C, hC⟩ := M_window_bridge_seam_reach
  refine ⟨C, fun F hF t₀ t₁ X W T hX hW hne => ⟨?_, ?_⟩⟩
  · have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
    have hk : Real.exp (Real.exp 1) ≤ 2 * X := by linarith
    exact seam_gate_star_of_nonempty hk (le_refl (2 * X)) hne
  · have hXe : Real.exp 1 ≤ X :=
      le_trans (Real.exp_le_exp.mpr (by linarith [Real.exp_one_gt_d9])) hX
    exact fun v hv => hC F hF t₀ X W (seamGateRstar X T) hXe hW v hv

/-! ## §7 — the honest price of the reach

The floor shape at height `b` is `loglog X − (3/4)loglog(b+3) − 5·logloglog(b+16)`.  A reach
`b` polynomial in `X` costs an ABSOLUTE constant and nothing else — the `1/4` grade of
`Mrange_one_floor` survives verbatim.  This is what licenses the `2X`, `3X` or
`seamGateRstar X T + W` heights above. -/

/-- **§7 — `pretFloorShape_quarter_at_pow`.**  For `X ≥ e^e`, `b ≥ 1`, `A ≥ 1` and
`b + 16 ≤ X^A`,

  `(1/4)·loglog X − (3/4)·log A − 5·log(1+log A) − 5·logloglog X ≤ pretFloorShape X b`.

Both corrections are read through `log(b+16) ≤ A·log X`: the first gives
`loglog(b+3) ≤ log A + loglog X`, whose `−3/4` eats three quarters of the leading term and
leaves `(1/4)loglog X`; the second gives `logloglog(b+16) ≤ log(log A + loglog X)
≤ log(1+log A) + logloglog X`, using `log A + loglog X ≤ (1+log A)·loglog X` (valid because
`loglog X ≥ 1`, which is exactly what the `e^e` gate buys).  Every outer logarithm is applied
only after its argument's positivity is established — `Real.log` is even, so no sign is ever
read off an expression. -/
theorem pretFloorShape_quarter_at_pow {X b A : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) (hb : 1 ≤ b) (hA : 1 ≤ A) (hbA : b + 16 ≤ X ^ A) :
    (1 / 4) * Real.log (Real.log X) - (3 / 4) * Real.log A
        - 5 * Real.log (1 + Real.log A) - 5 * Real.log (Real.log (Real.log X))
      ≤ pretFloorShape X b := by
  have h1e : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  -- the two scale facts the `e^e` gate buys
  have hLX : Real.exp 1 ≤ Real.log X := by
    rw [← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hX
  have hLXpos : (0 : ℝ) < Real.log X := lt_of_lt_of_le (Real.exp_pos 1) hLX
  have hL2 : (1 : ℝ) ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hLX
  have hL2pos : (0 : ℝ) < Real.log (Real.log X) := by linarith
  have hLA : (0 : ℝ) ≤ Real.log A := Real.log_nonneg hA
  -- the height, through `log (X^A) = A log X`
  have hpow : Real.log (X ^ A) = A * Real.log X := Real.log_rpow hXpos A
  have h16 : Real.log (b + 16) ≤ A * Real.log X := by
    rw [← hpow]; exact Real.log_le_log (by linarith) hbA
  have h3 : Real.log (b + 3) ≤ A * Real.log X :=
    le_trans (Real.log_le_log (by linarith) (by linarith)) h16
  -- `log (A log X) = log A + loglog X`
  have hprod : Real.log (A * Real.log X) = Real.log A + Real.log (Real.log X) :=
    Real.log_mul (by linarith) (by linarith)
  -- the `−(3/4)loglog(b+3)` correction
  have h3pos : (0 : ℝ) < Real.log (b + 3) := Real.log_pos (by linarith)
  have hc1 : Real.log (Real.log (b + 3)) ≤ Real.log A + Real.log (Real.log X) := by
    rw [← hprod]; exact Real.log_le_log h3pos h3
  -- the `−5·logloglog(b+16)` correction
  have hexp1lt17 : Real.exp 1 < 17 := by have := Real.exp_one_lt_d9; linarith
  have hlog17gt1 : (1 : ℝ) < Real.log 17 := by
    have h := Real.log_lt_log (Real.exp_pos 1) hexp1lt17; rwa [Real.log_exp] at h
  have h16gt1 : (1 : ℝ) < Real.log (b + 16) :=
    lt_of_lt_of_le hlog17gt1 (Real.log_le_log (by norm_num) (by linarith))
  have h16pos : (0 : ℝ) < Real.log (Real.log (b + 16)) := Real.log_pos h16gt1
  have hc2a : Real.log (Real.log (b + 16)) ≤ Real.log A + Real.log (Real.log X) := by
    rw [← hprod]; exact Real.log_le_log (by linarith) h16
  have hsplit : Real.log A + Real.log (Real.log X)
      ≤ (1 + Real.log A) * Real.log (Real.log X) := by nlinarith
  have hc2 : Real.log (Real.log (Real.log (b + 16)))
      ≤ Real.log (1 + Real.log A) + Real.log (Real.log (Real.log X)) := by
    have hstep : Real.log (Real.log (Real.log (b + 16)))
        ≤ Real.log ((1 + Real.log A) * Real.log (Real.log X)) :=
      Real.log_le_log h16pos (le_trans hc2a hsplit)
    rwa [Real.log_mul (by linarith) (by linarith)] at hstep
  rw [pretFloorShape_def]
  linarith

/-- **§7′ — `pretFloorShape_quarter_sq`.**  The `A = 2` reading, with the price collapsed to a
numeral: for `X ≥ e^e`, `b ≥ 1` and `b + 16 ≤ X²`,

  `(1/4)·loglog X − 5·logloglog X − 4 ≤ pretFloorShape X b`.

The price is `(3/4)log 2 + 5·log(1+log 2) ≤ (3/4)log 2 + 5·log 2 = 5.75·log 2 < 4`
(`1 + log 2 ≤ 2` since `log 2 ≤ 1`).  So the D10 reach costs FOUR — nothing in the `1/4`
grade, nothing in `loglog X`. -/
theorem pretFloorShape_quarter_sq {X b : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X) (hb : 1 ≤ b) (hbX : b + 16 ≤ X ^ (2 : ℝ)) :
    (1 / 4) * Real.log (Real.log X) - 5 * Real.log (Real.log (Real.log X)) - 4
      ≤ pretFloorShape X b := by
  have hmain := pretFloorShape_quarter_at_pow hX hb (by norm_num : (1 : ℝ) ≤ 2) hbX
  have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsub : Real.log (1 + Real.log 2) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-! ## §8 — the reach, bounded: `seamGateRstar X T ≤ 2X` at the station's scale -/

/-- **§8a — `Tstar_two_mul_le_quarter`.**  `T*(2X, log 2X) ≤ X/4` for `X ≥ e^{8192}`.
`T*(k, L) = L⁴·k^{1/(4 log L)}`, so at `k = 2X`, `u = log 2X`, `m = log u`,

  `T*(2X, log 2X) = exp(4m + u/(4m))`,

and the claim is `4m + u/(4m) ≤ log(X/4) = u − log 8`.  The two crude gates suffice:
`m ≥ 8` (from `e⁸ < 8192 ≤ u`) makes `u/(4m) ≤ u/32`, and `m = log u ≤ 2(√u − 1)` makes
`4m ≤ 8√u`; at `u ≥ 8192` (i.e. `√u ≥ 90`) the quadratic `8s + log 8 ≤ (31/32)s²` closes with
room.  SUB-POLYNOMIAL, as `FarStar`'s `⟦V3e⟧` note says — here with the constant pinned. -/
theorem Tstar_two_mul_le_quarter {X : ℝ} (hX : Real.exp 8192 ≤ X) :
    Tstar (2 * X) (Real.log (2 * X)) ≤ X / 4 := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have h2Xpos : (0 : ℝ) < 2 * X := by linarith
  have hlogX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hX
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hu : Real.log (2 * X) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) (by linarith)
  set u : ℝ := Real.log (2 * X) with hudef
  have hu8192 : (8192 : ℝ) ≤ u := by rw [hu]; linarith
  have hupos : (0 : ℝ) < u := by linarith
  set m : ℝ := Real.log u with hmdef
  -- `m ≥ 8`, from `e⁸ < 8192`
  have hexp8 : Real.exp 8 < 8192 := by
    have h1 : Real.exp 8 = Real.exp 1 ^ (8 : ℕ) := by
      rw [Real.exp_one_pow]; norm_num
    rw [h1]
    calc Real.exp 1 ^ (8 : ℕ) < (2.7182818286 : ℝ) ^ (8 : ℕ) :=
          pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg 1) (by norm_num)
      _ < 8192 := by norm_num
  have hm8 : (8 : ℝ) ≤ m := by
    rw [hmdef, ← Real.log_exp 8]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hmpos : (0 : ℝ) < m := by linarith
  -- `m ≤ 2(√u − 1)` and `√u ≥ 90`
  have hs0 : (0 : ℝ) < Real.sqrt u := Real.sqrt_pos.mpr hupos
  have hssq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hupos.le
  have hs90 : (90 : ℝ) ≤ Real.sqrt u := by
    have h1 : Real.sqrt 8100 ≤ Real.sqrt u := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt 8100 = 90 := by
      rw [show (8100 : ℝ) = 90 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 90)]
    linarith
  have hmsq : m ≤ 2 * (Real.sqrt u - 1) := by
    have h1 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt u) = Real.log u / 2 := Real.log_sqrt hupos.le
    rw [hmdef]; linarith [h1, h2]
  -- the arithmetic core
  have hdiv : u / (4 * m) ≤ u / 32 :=
    div_le_div_of_nonneg_left hupos.le (by norm_num) (by linarith)
  have hcore : 4 * m + u / (4 * m) ≤ u - 3 * Real.log 2 := by
    have hquad : 8 * Real.sqrt u + 3 * 0.6931471808 ≤ (31 / 32) * u := by
      nlinarith [hs90, hssq, sq_nonneg (Real.sqrt u - 90)]
    linarith
  -- the exponential form of `T*`
  have hu4 : u ^ 4 = Real.exp (4 * m) := by
    have hlogu4 : Real.log (u ^ 4) = 4 * m := by
      rw [Real.log_pow, hmdef]; push_cast; ring
    rw [← hlogu4, Real.exp_log (by positivity)]
  have hrp : (2 * X) ^ (1 / (4 * m)) = Real.exp (u * (1 / (4 * m))) := by
    rw [Real.rpow_def_of_pos h2Xpos, ← hudef]
  have hTs : Tstar (2 * X) u = Real.exp (4 * m + u / (4 * m)) := by
    unfold Tstar
    rw [← hmdef, hu4, hrp, ← Real.exp_add, mul_one_div]
  rw [hTs]
  have hXq : X / 4 = Real.exp (u - 3 * Real.log 2) := by
    have hlog4 : Real.log (X / 4) = u - 3 * Real.log 2 := by
      rw [Real.log_div (by linarith) (by norm_num), hu,
        show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    rw [← hlog4, Real.exp_log (by linarith)]
  rw [hXq]
  exact Real.exp_le_exp.mpr hcore

/-- **§8b — `seamGateRstar_le_two_mul`.**  THE VERDICT, concretely: at the station's own scale
`X ≥ e^{8192}` and for a truncation height inside the box (`T ≤ X`),

  `seamGateRstar X T = T + seamRad X + T*(2X, log 2X) + 1 ≤ 2X`.

So the reach the recentring gate forces EXCEEDS `X` (that is finding 3) but never leaves the
DOUBLED box — X-1 is the operative stone, and §7 runs at `A = 2` (`2X + W + 16 ≤ X²` for any
`W ≤ X` once `X ≥ 20`).  The collar `seamRad X = (log X)^{1/46} ≤ log X ≤ 2√X` is what makes
the remainder fit. -/
theorem seamGateRstar_le_two_mul {X T : ℝ} (hX : Real.exp 8192 ≤ X) (hT : T ≤ X) :
    seamGateRstar X T ≤ 2 * X := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX : (8192 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 8192]; exact Real.log_le_log (Real.exp_pos _) hX
  have hLpos : (0 : ℝ) < Real.log X := by linarith
  have hXbig : (8100 : ℝ) ≤ X := by linarith [Real.add_one_le_exp (8192 : ℝ)]
  -- the collar: `(log X)^{1/46} ≤ log X ≤ 2(√X − 1)`
  have hrad : seamRad X ≤ Real.log X := by
    unfold seamRad
    calc (Real.log X) ^ (1 / 46 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = Real.log X := Real.rpow_one _
  have hs0 : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  have hssq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXpos.le
  have hs90 : (90 : ℝ) ≤ Real.sqrt X := by
    have h1 : Real.sqrt 8100 ≤ Real.sqrt X := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt 8100 = 90 := by
      rw [show (8100 : ℝ) = 90 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 90)]
    linarith
  have hlogsq : Real.log X ≤ 2 * (Real.sqrt X - 1) := by
    have h1 : Real.log (Real.sqrt X) ≤ Real.sqrt X - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hXpos.le
    linarith
  have hsmall : Real.log X + 1 ≤ X / 4 := by nlinarith [hs90, hssq, hs0]
  have hTs := Tstar_two_mul_le_quarter hX
  unfold seamGateRstar
  linarith

end Salt.MR
