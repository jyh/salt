/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DistSplit
import Salt.MR.DistHalasz

/-!
# A2-4 — THE M-WINDOW BRIDGE (`docs/exploration/s8-freeze-0727.md`, ladder row A2-4)

The interface `thm_A2′` offers its quality at the SIEVE parameter:
`M(f; X, W) = inf_{|t| ≤ W} 𝔻²(f, n^{it}; X)` at `W = (log H)^{12}`.  The landed
station consumes a floor on MRT's OWN window `|v| ≤ X`
(`SupStation.seam_ball_leg_station_M:723–724`,
`hM₀ : ∀ v, |v| ≤ X → M₀ ≤ 𝔻²(datum, n^{iv}; X)`).  This file bridges the two:
the far band `W ≲ |v| ≤ X` is paid by the `f = 1` distance floor
(`DistHalasz.dist_one_floor_pow`) recentred at a window point through the
pretentious triangle (`PretentiousTriangle.dist_mul_half`), and the two bands are
joined by a `min`.

## The three stones

* **B-1 `dist_floor_far_range`** (§2) — the far floor.  For a reference `t'` in the
  window and a target `|t| ≥ Wref + 1` with `|t| ≤ X`,
  `𝔻²(f, n^{it}; X) ≥ (1/2)·(pretFloorShape X (2X) − C) − 𝔻²(f, n^{it'}; X)`.
* **B-2 `M_window_bridge` / `M_window_bridge_inf` / `M_window_bridge_seam`** (§4) —
  the assembled `min`, in the hypothesis form, in the infimum form (unconditional,
  stated at the interface object `M_win`), and at the station's own seam datum.
* **B-3 `M_rangeCap` + `Mrange_cap_one_floor` + `contour_height_le_two_mul`** (§5) —
  the D10 repair: `M_range`'s domain caps at `|t| ≤ X` (`DistHalasz:262–265`) while
  MRT p. 25's contour reaches `|t'| ≤ X + (log X)²`.  The capped twin `M_rangeCap`
  carries the height cap as a parameter, its floor is the same `1/4 − o(1)` grade,
  and `contour_height_le_two_mul` puts the contour reach inside the doubled cap.

## THE BOUNDARY BAND — the honest design (read before instantiating)

`dist_one_floor_pow` is gated at `1 ≤ |b|`: below that the floor is FALSE, not merely
unavailable (`𝔻²(1, n^{i·0}; X) = 0` while the shape is `≍ loglog X`).  The gate is
structural, so the far floor can never be run at a separation `|t − t'| < 1`.  With a
reference `t'` anywhere in `|t'| ≤ W` and a target just past the window, `|t − t'|` can
be `0`; the region `W < |t| < W + 1` is therefore NOT reachable from the window's own
reference.  **The design chosen: a unit collar.**  The near band is `|v| ≤ Wnear`, the
reference is drawn from `|t'| ≤ Wref` with `Wref + 1 ≤ Wnear`, and the far band
`|v| > Wnear` then has `|v − t'| ≥ 1` by the triangle inequality alone.  The infimum
form takes `Wnear := W` and `Wref := W − 1`, so the headline term is the interface's
`M(f; X, W)` EXACTLY and the collar is paid in the far slot, which reads
`M(f; X, W − 1) ≥ M(f; X, W)` (`M_win_anti`) — the safe direction: the far floor is
stated smaller than the `W`-window value would make it, never larger.  At
`W = (log H)^{12}` the collar is invisible to the consumer.

Three alternatives, and why they were not taken:

1. *Reference `t' := 0`.*  The gate is then free (`|v − 0| = |v| ≥ W ≥ 1`), but the
   far floor subtracts `𝔻²(f, 1; X)`, for which a general 1-bounded `f` admits NO
   upper bound (it can be `≍ loglog X`); the floor is vacuous.
2. *Reference `t' := v − sign v` (separation exactly `1`).*  The gate is met for every
   `v` past the window, but the cap is then demanded at an ARBITRARY window point,
   i.e. a uniform `sup` bound over the window — not an object anyone owns.
3. *Restating at `M(f; X, 2W)` (the brief's fallback).*  Sound, and strictly WEAKER
   than the collar: a near hypothesis on `|t| ≤ 2W` is a stronger demand than on
   `|t| ≤ W`.  It is the `Wnear := 2W, Wref := W` instance of the same B-1/B-2 pair
   (any `Wref + 1 ≤ Wnear` is admissible), so nothing is lost by taking the collar.

## The grade

`pretFloorShape X (2X) = loglog X − (3/4)loglog(2X+3) − 5·logloglog(2X+16)` is the
`(1/4 − o(1))·loglog X` shape of `Mrange_one_floor`, evaluated at the DOUBLED height
(the `2X` is what the far band's own triangle inequality forces: `|t − t'| ≤ |t| + |t'|
≤ X + Wref ≤ 2X`).  So at the corpus's own cap `S = (1/16)·loglog X` the far floor is
`(1/2)·(1/4)loglog X − (1/16)loglog X = (1/16)·loglog X + o(loglog X)` — the same grade
the landed pointwise rows carry, with the constant fit explicit.

## Traps carried

`Real.log` is EVEN (`Real.log (-x) = Real.log x`), so every positivity step here is
explicit and never read off the argument's sign; the `1 ≤ |b|` gate above; `min` is
consumed through `min_le_of_left_le`/`min_le_of_right_le` only (never `le_min`); and
nothing landed is edited — every statement in this file is new (Iron rule 5).
-/

namespace Salt.MR

open scoped BigOperators

/-! ## §1 — the floor shape and its monotonicity -/

/-- **The `dist_one_floor_pow` floor shape.**
`pretFloorShape x b = loglog x − (3/4)·loglog(b+3) − 5·logloglog(b+16)` — the right-hand
side of `DistHalasz.dist_one_floor_pow` (`:179`) with the additive constant stripped,
read as a function of the frequency height `b = |t|`.  Every floor produced below is
`pretFloorShape X · − C` at the SAME `C` the landed stone produces. -/
noncomputable def pretFloorShape (x b : ℝ) : ℝ :=
  Real.log (Real.log x) - (3 / 4) * Real.log (Real.log (b + 3))
    - 5 * Real.log (Real.log (Real.log (b + 16)))

lemma pretFloorShape_def (x b : ℝ) :
    pretFloorShape x b = Real.log (Real.log x) - (3 / 4) * Real.log (Real.log (b + 3))
      - 5 * Real.log (Real.log (Real.log (b + 16))) := rfl

/-- **The shape is antitone in the height.**  For `1 ≤ b₁ ≤ b₂`,
`pretFloorShape x b₂ ≤ pretFloorShape x b₁`: both corrections `loglog(·+3)` and
`logloglog(·+16)` are monotone in the height, and both inner logarithms are positive on
`b ≥ 1` (`b + 3 ≥ 4 > 1` and `b + 16 ≥ 17 > e`), which is what licenses the outer
`Real.log_le_log` steps.  This is the step that lets the far band be priced once, at the
worst height `2X`, instead of per-frequency. -/
lemma pretFloorShape_le_of_le (x : ℝ) {b₁ b₂ : ℝ} (hb1 : 1 ≤ b₁) (hb12 : b₁ ≤ b₂) :
    pretFloorShape x b₂ ≤ pretFloorShape x b₁ := by
  have hexp1lt17 : Real.exp 1 < 17 := by have := Real.exp_one_lt_d9; linarith
  have hlog17gt1 : (1 : ℝ) < Real.log 17 := by
    have h := Real.log_lt_log (Real.exp_pos 1) hexp1lt17; rwa [Real.log_exp] at h
  -- the `loglog(·+3)` correction
  have hlog3pos : (0 : ℝ) < Real.log (b₁ + 3) :=
    Real.log_pos (by linarith)
  have hm1 : Real.log (Real.log (b₁ + 3)) ≤ Real.log (Real.log (b₂ + 3)) :=
    Real.log_le_log hlog3pos (Real.log_le_log (by linarith) (by linarith))
  -- the `logloglog(·+16)` correction
  have hlog16 : (1 : ℝ) < Real.log (b₁ + 16) :=
    lt_of_lt_of_le hlog17gt1 (Real.log_le_log (by norm_num) (by linarith))
  have hℓ16pos : (0 : ℝ) < Real.log (Real.log (b₁ + 16)) := Real.log_pos hlog16
  have hm2 : Real.log (Real.log (Real.log (b₁ + 16)))
      ≤ Real.log (Real.log (Real.log (b₂ + 16))) :=
    Real.log_le_log hℓ16pos
      (Real.log_le_log (by linarith) (Real.log_le_log (by linarith) (by linarith)))
  rw [pretFloorShape_def, pretFloorShape_def]
  linarith

/-! ## §2 — B-1: the far-range floor

The two-step engine.  `dist_mul_half` (`PretentiousTriangle:213`) at the triple
`(n^{it'}, f, n^{it})` gives `𝔻²(f, n^{it}) ≥ (1/2)·𝔻²(n^{it'}, n^{it}) − 𝔻²(f, n^{it'})`;
the character shift (`DistSplit.pretDistSq_costwist_shift`, the corpus's own recentring
device) turns the first term into `𝔻²(1, n^{i(t−t')})`, where `dist_one_floor_pow` applies
— PROVIDED the separation clears the structural gate `1 ≤ |t − t'|`. -/

/-- **B-1a — the far floor, separation form (`dist_floor_far_sep`).**  For 1-bounded `f`,
`X ≥ e` and a pair of frequencies separated by at least `1` and at most `2X`,

  `(1/2)·(pretFloorShape X (2X) − C) − 𝔻²(f, n^{it'}; X) ≤ 𝔻²(f, n^{it}; X)`.

The separation hypotheses are exactly the two structural gates: `1 ≤ |t − t'|` is
`dist_one_floor_pow`'s own (below it the floor is false, not merely unavailable), and
`|t − t'| ≤ 2X` is what lets the shape be evaluated once at the worst height. -/
theorem dist_floor_far_sep :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X t t' : ℝ),
      Real.exp 1 ≤ X → 1 ≤ |t - t'| → |t - t'| ≤ 2 * X →
      (1 / 2) * (pretFloorShape X (2 * X) - C) - pretDistSq f (costwist t') X
        ≤ pretDistSq f (costwist t) X := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun f hf X t t' hX hsep1 hsep2 => ?_⟩
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

/-- **B-1 — the far floor, window form (`dist_floor_far_range`).**  For 1-bounded `f`,
`X ≥ e`, a reference `t'` inside the window `|t'| ≤ Wref` and a target `t` past the
collar (`Wref + 1 ≤ |t|`) but inside MRT's box (`|t| ≤ X`), any cap `S` at the reference
gives

  `(1/2)·(pretFloorShape X (2X) − C) − S ≤ 𝔻²(f, n^{it}; X)`.

The collar `Wref + 1 ≤ |t|` is the ONLY place the boundary band is paid: it produces
`|t − t'| ≥ |t| − |t'| ≥ 1` from the triangle inequality alone, uniformly in the
reference.  The upper separation is free: `|t − t'| ≤ |t| + |t'| ≤ X + Wref ≤ 2X`,
since `Wref ≤ |t| − 1 ≤ X`. -/
theorem dist_floor_far_range :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X Wref t t' S : ℝ),
      Real.exp 1 ≤ X → |t'| ≤ Wref → Wref + 1 ≤ |t| → |t| ≤ X →
      pretDistSq f (costwist t') X ≤ S →
      (1 / 2) * (pretFloorShape X (2 * X) - C) - S ≤ pretDistSq f (costwist t) X := by
  obtain ⟨C, hC⟩ := dist_floor_far_sep
  refine ⟨C, fun f hf X Wref t t' S hX ht' hcollar hbox hcap => ?_⟩
  have hlow : |t| - |t'| ≤ |t - t'| := abs_sub_abs_le_abs_sub t t'
  have hhigh : |t - t'| ≤ |t| + |t'| := by
    rw [sub_eq_add_neg, ← abs_neg t']
    exact abs_add_le _ _
  have habs' : (0 : ℝ) ≤ |t'| := abs_nonneg t'
  have hsep1 : (1 : ℝ) ≤ |t - t'| := by linarith
  have hsep2 : |t - t'| ≤ 2 * X := by linarith
  have h := hC f hf X t t' hX hsep1 hsep2
  linarith

/-! ## §3 — the M-window object

`M_win f X W` is the interface's `M(f; X, W)`: the infimum of `𝔻²(f, n^{it}; X)` over the
sieve window `|t| ≤ W`.  It is bounded below by `0` (`pretDistSq_nonneg`) and its window
is nonempty (`t = 0`), so the two conditionally-complete facts below are unconditional
once `0 ≤ W`. -/

/-- **The M-window infimum (the interface object).**
`M_win f X W = inf_{|t| ≤ W} 𝔻²(f, n^{it}; X)`. -/
noncomputable def M_win (f : ℕ → ℂ) (X W : ℝ) : ℝ :=
  sInf ((fun t : ℝ => pretDistSq f (costwist t) X) '' {t : ℝ | |t| ≤ W})

lemma M_win_bddBelow {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (X W : ℝ) :
    BddBelow ((fun t : ℝ => pretDistSq f (costwist t) X) '' {t : ℝ | |t| ≤ W}) := by
  refine ⟨0, ?_⟩
  rintro v ⟨t, _, rfl⟩
  exact pretDistSq_nonneg f (costwist t) X hf (norm_costwist_le t)

lemma M_win_window_nonempty {W : ℝ} (hW : 0 ≤ W) : ({t : ℝ | |t| ≤ W}).Nonempty :=
  ⟨0, by simpa using hW⟩

/-- **The infimum property.**  Every frequency of the window dominates `M_win`. -/
lemma M_win_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (X : ℝ) {W t : ℝ} (ht : |t| ≤ W) :
    M_win f X W ≤ pretDistSq f (costwist t) X :=
  csInf_le (M_win_bddBelow hf X W) ⟨t, ht, rfl⟩

/-- **The approximation property.**  `M_win` is approached inside the window: for every
`ε > 0` there is a window frequency whose distance is `< M_win + ε`.  This is what
supplies B-2's reference point WITHOUT constructing a minimiser (no compactness, no
continuity of `t ↦ 𝔻²`). -/
lemma M_win_approx (f : ℕ → ℂ) (X : ℝ) {W ε : ℝ} (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ t' : ℝ, |t'| ≤ W ∧ pretDistSq f (costwist t') X < M_win f X W + ε := by
  have hne : ((fun t : ℝ => pretDistSq f (costwist t) X) '' {t : ℝ | |t| ≤ W}).Nonempty :=
    (M_win_window_nonempty hW).image _
  obtain ⟨v, ⟨t', ht', rfl⟩, hv⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (M_win f X W) hε)
  exact ⟨t', ht', hv⟩

/-- **The window infimum is antitone in the radius.**  `W₁ ≤ W₂ → M_win f X W₂ ≤
M_win f X W₁`: a wider window infimises over more.  This pins the DIRECTION of the
collar: the far slot of `M_window_bridge_inf` carries `M_win f X (W − 1)`, which is
`≥ M_win f X W`, so subtracting it is the safe (smaller-floor) reading — it may NOT be
replaced by `M_win f X W`. -/
lemma M_win_anti {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (X : ℝ) {W₁ W₂ : ℝ} (hW₁ : 0 ≤ W₁)
    (h : W₁ ≤ W₂) : M_win f X W₂ ≤ M_win f X W₁ :=
  csInf_le_csInf (M_win_bddBelow hf X W₂) ((M_win_window_nonempty hW₁).image _)
    (Set.image_mono (fun _ ht => le_trans ht h))

/-! ## §4 — B-2: the assembled bridge -/

/-- **B-2 — THE M-WINDOW BRIDGE (`M_window_bridge`).**  The `min` that turns a
window-`W` quality into the station's `|v| ≤ X` binder.  Given

* a near floor `M` valid on `|t| ≤ Wnear`,
* a reference `t'` with `|t'| ≤ Wref` and `Wref + 1 ≤ Wnear` (the unit collar),
* a cap `𝔻²(f, n^{it'}; X) ≤ S` at that reference,

every frequency of MRT's box obeys

  `min M ((1/2)·(pretFloorShape X (2X) − C) − S) ≤ 𝔻²(f, n^{iv}; X)`   for `|v| ≤ X`.

The `by_cases` is on `|v| ≤ Wnear`: inside, the near floor; outside, B-1 (whose collar
gate `Wref + 1 ≤ |v|` follows from `Wref + 1 ≤ Wnear < |v|`).  The exit is EXACTLY
`SupStation.seam_ball_leg_station_M`'s `hM₀` binder shape at `M₀ := min …`.

NON-VACUITY (the house creed).  No hypothesis here is a hole: the cap slot is always
inhabited at `S := 𝔻²(f, n^{it'}; X)` (`le_refl`), the collar is satisfiable at any
`Wnear := Wref + 1`, and `M_window_bridge_inf` below discharges BOTH the reference and
the cap outright, so the bridge has an unconditional instance. -/
theorem M_window_bridge :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X Wref Wnear M S t' : ℝ),
      Real.exp 1 ≤ X → Wref + 1 ≤ Wnear → |t'| ≤ Wref →
      (∀ t : ℝ, |t| ≤ Wnear → M ≤ pretDistSq f (costwist t) X) →
      pretDistSq f (costwist t') X ≤ S →
      ∀ v : ℝ, |v| ≤ X →
        min M ((1 / 2) * (pretFloorShape X (2 * X) - C) - S)
          ≤ pretDistSq f (costwist v) X := by
  obtain ⟨C, hC⟩ := dist_floor_far_range
  refine ⟨C, fun f hf X Wref Wnear M S t' hX hcollar ht' hnear hcap v hv => ?_⟩
  by_cases hband : |v| ≤ Wnear
  · exact min_le_of_left_le (hnear v hband)
  · push Not at hband
    exact min_le_of_right_le
      (hC f hf X Wref v t' S hX ht' (by linarith) hv hcap)

/-- **B-2′ — THE BRIDGE AT THE INTERFACE OBJECT (`M_window_bridge_inf`), UNCONDITIONAL.**
No cap is assumed: the reference is supplied by the infimum's own approximation property
and the `ε` is passed to the limit.  For 1-bounded `f`, `X ≥ e` and `W ≥ 1`,

  `min (M_win f X W) ((1/2)·(pretFloorShape X (2X) − C) − M_win f X (W−1))
      ≤ 𝔻²(f, n^{iv}; X)`   for every `|v| ≤ X`.

The headline slot is the interface's `M(f; X, W)` EXACTLY; the collar is paid in the far
slot, at the shrunk window's infimum `M_win f X (W−1) ≥ M_win f X W` (`M_win_anti`) — the
honest direction.  At `W = (log H)^{12}` the shrink is invisible; at the corpus's own
`(1/16)·loglog X` cap the far slot is `(1/16)·loglog X + o(loglog X)`. -/
theorem M_window_bridge_inf :
    ∃ C : ℝ, ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (X W : ℝ),
      Real.exp 1 ≤ X → 1 ≤ W →
      ∀ v : ℝ, |v| ≤ X →
        min (M_win f X W) ((1 / 2) * (pretFloorShape X (2 * X) - C) - M_win f X (W - 1))
          ≤ pretDistSq f (costwist v) X := by
  obtain ⟨C, hC⟩ := dist_floor_far_range
  refine ⟨C, fun f hf X W hX hW v hv => ?_⟩
  by_cases hband : |v| ≤ W
  · exact min_le_of_left_le (M_win_le hf X hband)
  · push Not at hband
    refine min_le_of_right_le ?_
    -- the `ε`-form, then the limit
    have hkey : ∀ ε : ℝ, 0 < ε →
        (1 / 2) * (pretFloorShape X (2 * X) - C) - M_win f X (W - 1)
          ≤ pretDistSq f (costwist v) X + ε := by
      intro ε hε
      obtain ⟨t', ht', hlt⟩ := M_win_approx f X (by linarith : (0 : ℝ) ≤ W - 1) hε
      have h := hC f hf X (W - 1) v t' (M_win f X (W - 1) + ε) hX ht'
        (by linarith) hv (le_of_lt hlt)
      linarith
    by_contra hcon
    push Not at hcon
    have h := hkey (((1 / 2) * (pretFloorShape X (2 * X) - C) - M_win f X (W - 1)
      - pretDistSq f (costwist v) X) / 2) (by linarith)
    linarith

/-- **B-2″ — THE BRIDGE AT THE STATION'S DATUM (`M_window_bridge_seam`).**
`M_window_bridge_inf` at `f := seamCoeff (ellLin g) 1 t₀`, the datum
`SupStation.seam_ball_leg_station_M` carries, from the corpus-standard PRIME bound on
`g` (`ellLin_norm_le_one` ∘ `norm_seamCoeff_le`).  The conclusion is that station's
`hM₀` hypothesis VERBATIM, at

  `M₀ := min (M_win datum X W) ((1/2)·(pretFloorShape X (2X) − C) − M_win datum X (W−1))`,

so the station's ball leg can be run off a window-`W` quality with no further adapter. -/
theorem M_window_bridge_seam :
    ∃ C : ℝ, ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ X W : ℝ),
      Real.exp 1 ≤ X → 1 ≤ W →
      ∀ v : ℝ, |v| ≤ X →
        min (M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X W)
            ((1 / 2) * (pretFloorShape X (2 * X) - C)
              - M_win (seamCoeff (ellLin g) (fun _ => 1) t₀) X (W - 1))
          ≤ pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist v) X := by
  obtain ⟨C, hC⟩ := M_window_bridge_inf
  refine ⟨C, fun g hg t₀ X W hX hW v hv => ?_⟩
  exact hC (seamCoeff (ellLin g) (fun _ => 1) t₀)
    (fun n => norm_seamCoeff_le (ellLin_norm_le_one g hg) (fun _ => le_of_eq norm_one) t₀ n)
    X W hX hW v hv

/-! ## §5 — B-3: the D10 repair (the max-modulus reach)

`M_range` (`DistHalasz:262–265`) caps its window at `|t| ≤ X`, while MRT p. 25's contour
reaches `|t'| ≤ X + (log X)²` (the THIRD object wearing the `T₀` glyph — not `seamT0`,
not MRT's set `𝒯₀`).  The repair is ADDITIVE: a capped twin `M_rangeCap` carrying the
height as a parameter, with the same `1/4 − o(1)` floor.  Nothing landed is edited, and
the twin feeds the landed consumers in the SAFE direction — see
`M_rangeCap_le_M_range`. -/

/-- **The height-capped range minimum (`M_rangeCap`).**  `M_range` with its `|t| ≤ X` cap
promoted to a parameter `K`: the infimum of `𝔻²(f, n^{it}; X)` over
`(logX)^{1/15} ≤ |t| ≤ T + (logX)^{1/16}` intersected with `|t| ≤ K`.  `K := X` is
`M_range` on the nose (`M_rangeCap_at_self`); `K := 2X` covers the contour reach. -/
noncomputable def M_rangeCap (f : ℕ → ℂ) (X T K : ℝ) : ℝ :=
  sInf ((fun t : ℝ => pretDistSq f (costwist t) X) ''
    {t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ K})

/-- At `K = X` the capped twin IS the landed `M_range` (definitional). -/
lemma M_rangeCap_at_self (f : ℕ → ℂ) (X T : ℝ) : M_rangeCap f X T X = M_range f X T := rfl

/-- The window of the capped twin, packaged (the nonemptiness witness is
`Mrange_one_floor`'s own, `t = (logX)^{1/15}`). -/
lemma M_rangeCap_window_nonempty {X T K : ℝ} (hX : Real.exp 1 ≤ X)
    (hT : (Real.log X) ^ (1 / 15 : ℝ) ≤ T) (hXK : X ≤ K) :
    ({t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ K}).Nonempty := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hr15X : (Real.log X) ^ (1 / 15 : ℝ) ≤ X := by
    calc (Real.log X) ^ (1 / 15 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogX1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
      _ ≤ X := by linarith [Real.log_le_sub_one_of_pos hXpos]
  refine ⟨(Real.log X) ^ (1 / 15 : ℝ), ?_⟩
  have habs : |(Real.log X) ^ (1 / 15 : ℝ)| = (Real.log X) ^ (1 / 15 : ℝ) :=
    abs_of_nonneg (Real.rpow_nonneg hLXpos.le _)
  have h16nn : (0 : ℝ) ≤ (Real.log X) ^ (1 / 16 : ℝ) := Real.rpow_nonneg hLXpos.le _
  rw [Set.mem_setOf_eq, habs]
  exact ⟨le_refl _, by linarith, le_trans hr15X hXK⟩

/-- **The widened cap only lowers the infimum (`M_rangeCap_le_M_range`).**  For `X ≤ K`,
`M_rangeCap f X T K ≤ M_range f X T`.  THIS is why the D10 repair disturbs no landed
consumer: every landed row reads `M_range` through a FLOOR hypothesis
(`hfloor : (1/32)·loglog X ≤ M_range …`, e.g. `AnnHead:307/344/402`, `HExit`,
`Prop1Assembly`), and a floor proven for the wider-cap infimum implies the same floor for
`M_range` by this inequality.  The traffic runs one way only: the wider object is the
weaker (smaller) one, so it is also the SAFE one to place under `exp(−M/e)`. -/
lemma M_rangeCap_le_M_range {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X T K : ℝ}
    (hX : Real.exp 1 ≤ X) (hT : (Real.log X) ^ (1 / 15 : ℝ) ≤ T) (hXK : X ≤ K) :
    M_rangeCap f X T K ≤ M_range f X T := by
  refine csInf_le_csInf ⟨0, ?_⟩ ((M_rangeCap_window_nonempty hX hT (le_refl X)).image _) ?_
  · rintro v ⟨t, _, rfl⟩
    exact pretDistSq_nonneg f (costwist t) X hf (norm_costwist_le t)
  · exact Set.image_mono (fun t ht => ⟨ht.1, ht.2.1, le_trans ht.2.2 hXK⟩)

/-- **B-3 — THE CAPPED `M_range` FLOOR (`Mrange_cap_one_floor`).**  For `X ≥ e`,
`(logX)^{1/15} ≤ T` and any height cap `K ≥ X`,

  `pretFloorShape X K − C ≤ M_rangeCap (1; X, T, K)`,

i.e. `loglog X − (3/4)·loglog(K+3) − 5·logloglog(K+16) − C`.  At `K = X` this is
`Mrange_one_floor` (`DistHalasz:276`) re-derived; at `K = 2X` it is the same
`(1/4 − o(1))·loglog X` grade with the correction read at the doubled height — the floor
is `dist_one_floor_pow`-driven and that stone holds at EVERY `|b| ≥ 1`, so widening the
cap costs only the shape's own monotonicity (`pretFloorShape_le_of_le`). -/
theorem Mrange_cap_one_floor :
    ∃ C : ℝ, ∀ X T K : ℝ, Real.exp 1 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T → X ≤ K →
      pretFloorShape X K - C ≤ M_rangeCap (fun _ => 1) X T K := by
  obtain ⟨C, hC⟩ := dist_one_floor_pow
  refine ⟨C, fun X T K hX hT hXK => ?_⟩
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hr15_1 : (1 : ℝ) ≤ (Real.log X) ^ (1 / 15 : ℝ) := Real.one_le_rpow hlogX1 (by norm_num)
  have hfloor : ∀ t : ℝ,
      (Real.log X) ^ (1 / 15 : ℝ) ≤ |t| ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ K →
      pretFloorShape X K - C ≤ pretDistSq (fun _ => 1) (costwist t) X := by
    rintro t ⟨htlo, _, htK⟩
    have ht1 : (1 : ℝ) ≤ |t| := le_trans hr15_1 htlo
    have hd := hC X t hX ht1
    have hshape : pretFloorShape X |t| - C ≤ pretDistSq (fun _ => 1) (costwist t) X := by
      rw [pretFloorShape_def]; exact hd
    have hmono := pretFloorShape_le_of_le X ht1 htK
    linarith
  refine le_csInf ((M_rangeCap_window_nonempty hX hT hXK).image _) ?_
  rintro v ⟨t, ht, rfl⟩
  exact hfloor t ht

/-- **B-3′ — the doubled-cap instance (`Mrange_one_floor_2X`).**  `Mrange_cap_one_floor`
at `K = 2X`: the `1/4 − o(1)` floor on the infimum taken over the DOUBLED height box,
which is the object the max-modulus contour actually needs. -/
theorem Mrange_one_floor_2X :
    ∃ C : ℝ, ∀ X T : ℝ, Real.exp 1 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T →
      pretFloorShape X (2 * X) - C ≤ M_rangeCap (fun _ => 1) X T (2 * X) := by
  obtain ⟨C, hC⟩ := Mrange_cap_one_floor
  refine ⟨C, fun X T hX hT => ?_⟩
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  exact hC X T (2 * X) hX hT (by linarith)

/-- **`(log X)² ≤ X` for `X ≥ 256` (`log_sq_le_self`).**  The fourth-root route:
`log X = 4·log(X^{1/4}) ≤ 4·(X^{1/4} − 1) ≤ 4·X^{1/4}`, so `(log X)² ≤ 16·√X ≤ X` once
`√X ≥ 16`.  (The square-root route `log X ≤ 2√X − 2` is NOT enough — it gives `4X`.) -/
theorem log_sq_le_self {X : ℝ} (hX : 256 ≤ X) : Real.log X ^ 2 ≤ X := by
  have hXpos : (0 : ℝ) < X := by linarith
  set s : ℝ := X ^ ((1 : ℝ) / 4) with hsdef
  have hspos : (0 : ℝ) < s := Real.rpow_pos_of_pos hXpos _
  have hlogs : Real.log s = (1 / 4) * Real.log X := by
    rw [hsdef, Real.log_rpow hXpos]
  have hlogsle : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  have hlogX4 : Real.log X ≤ 4 * s := by
    rw [hlogs] at hlogsle; linarith
  have hlogXnn : (0 : ℝ) ≤ Real.log X := Real.log_nonneg (by linarith)
  have hs2 : s ^ 2 = Real.sqrt X := by
    rw [hsdef, ← Real.rpow_natCast (X ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul hXpos.le,
      Real.sqrt_eq_rpow]
    norm_num
  have hsqrt16 : (16 : ℝ) ≤ Real.sqrt X := by
    have h256 : Real.sqrt 256 ≤ Real.sqrt X := Real.sqrt_le_sqrt hX
    have : Real.sqrt 256 = 16 := by
      rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 16)]
    linarith [h256, this.symm.le, this.le]
  have hsqrtsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXpos.le
  have h16 : 16 * Real.sqrt X ≤ X := by nlinarith [hsqrt16, hsqrtsq]
  nlinarith [hlogX4, hlogXnn, hs2, h16, hspos]

/-- **THE CONTOUR REACH SITS INSIDE THE DOUBLED CAP (`contour_height_le_two_mul`).**
For `X ≥ 256`, `X + (log X)² ≤ 2X`: MRT p. 25's max-modulus height `|t'| ≤ X + (log X)²`
is covered by `M_rangeCap`'s `K = 2X` window (`Mrange_one_floor_2X`).  This is the D10
defect discharged: the reach is bounded, not the statement widened. -/
theorem contour_height_le_two_mul {X : ℝ} (hX : 256 ≤ X) : X + Real.log X ^ 2 ≤ 2 * X := by
  linarith [log_sq_le_self hX]

end Salt.MR
