/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.FarArm
import Salt.MR.HExit

/-!
# FLOOR-PROVENANCE — the honest supply of the prop-A3 column's `hfloor` (`FloorProvenance`)

**The repair of `flags.md`'s "hfloor's seam-datum provenance" entry (2026-07-25,
GRADE-REF UNASSIGNED-2).**  The prop-A3 column's floor binder — byte-for-byte
`Prop1Assembly:406`, `HExit:1465`, `HalaszHead:455`, `AnnHead:306`… —

  `(1/32)·loglog X ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T`

is at the SEAM datum `ℓ(g)·n^{−it₀}`.  `DistHalasz.Mrange_one_floor` (the stone the
docstrings named as its supplier) is at the CONSTANT datum `fun _ => 1`.  This file
lands the chain that actually connects them, with every price in the open.

## The three findings (all arithmetic, all checked here)

1. **There is no additive comparison.**  `M_range(1) − (a loss) ≤ M_range(seam)` is not a
   shape the machinery produces and is not true with any `o(loglog X)` loss: take
   `g p = p^{iτ}` with `τ − t₀` INSIDE the window `[(logX)^{1/15}, T + (logX)^{1/16}]` — the
   seam datum's distance vanishes there, so `M_range(seam) = 0` while `M_range(1) ≍ loglog X`.
   The honest comparison is the RECENTRING `(√L − √S)²` of `DistSplit.dist_recenter_sq`:
   it needs a CENTRE `t₁` and a CAP `S` at that centre, and it costs a factor `4`
   (`L = (1/4)loglog X ↦ (1/16)loglog X`) plus the `o(loglog X)` height corrections — never a
   subtraction of a small loss.

2. **The frozen stone cannot supply the binder at face value.**
   `PropA3Core.dist_split_A4_frozen` concludes
   `(1/32)loglog X − 5·logloglog(2X+16) − C − W ≤ 𝔻²(fg_J, n^{it}; X)`, which is STRICTLY
   below the binder's `(1/32)loglog X` for every `X ≥ e` (both corrections are `≥ 0` there,
   `logloglog_two_X_nonneg`), and its `(1/16)` branch numeral is frozen, so it cannot be
   re-run with slack.  The gap is the HALVING: `dist_split_A4` pays a factor `2` to move a
   floor from `f` onto a windowed factor `fg_J`.  **On this column the window is the TRIVIAL
   indicator, so no halving is owed** — `seamCoeff_trivial_dist_eq` (`HalaszHead:375`) is an
   EXACT identity, not an inequality.  The repair therefore re-runs the frozen stone's own
   components (`dist_one_floor_pow` → `dist_recenter_sq` → `recenter_sq_floor`) one level
   down, where the recentring output `(1/16)loglog X − δ` has a full factor-2 of room above
   the binder's `(1/32)loglog X` — and that room is exactly what pays `δ`.

3. **The W-loss on this column is ZERO, as proven.**  `W` in the frozen stone is the MULT-SHIU
   window mass `𝔻²(f, fg_J; X)`; at the trivial indicator that datum IS the seam datum and the
   mass is `0`.  `W` survives here only as a NAMED SLACK SLOT (`hW : 0 ≤ W`) inside the gate,
   so a consumer who must pay a genuine loss (a damped window in place of `fun _ => 1`) can
   read off exactly how much the `(1/32)`-slack absorbs:
   `5·logloglog(2X+16) + C + W ≤ (1/32)·loglog X`.

## The chain

* **§0** the triple-log bookkeeping — `fp_expexp_le_two_X`, `fp_logloglog_two_X_nonneg`,
  `fp_logloglog_mono_of_le`: verbatim re-derivations of `PropA3Core`'s privates (unreachable
  across files; the statements are byte-identical).
* **§1** `dist_one_floor_uniform` — the constant-datum floor made `b`-UNIFORM on the capped
  height range `1 ≤ |b| ≤ X`:
  `(1/4)loglog X − 5·logloglog(2X+16) − C ≤ 𝔻²(1, n^{ib}; X)`.  The `(3/4)·loglog(|b|+3)`
  height correction is absorbed by `NonPret.loglog_height_le` at `Q = 1`, the triple log by
  §0's monotonicity; `C` is `∃`-bound and `≥ 0` (law #253: the `logloglog` stays visible).
* **§2 (F-1)** `seam_floor_of_cap_pointwise` — the per-`t` comparison: the A-10 ball cap at
  the centre `t₁` (in the SEAM frame, the shape `CenterSupply.ball_sup_supplied` /
  `FarStar.ball_sup_closed_star` hand over) gives, at every frequency separated from the
  centre by `1 ≤ |t − t₁| ≤ X`,
  `(1/16)loglog X − 5·logloglog(2X+16) − C ≤ 𝔻²(seamCoeff f 1 t₀, n^{it}; X)`.
  The `t₀`-shift is invisible: it cancels between the cap and the target
  (`(t + t₀) − (t₁ + t₀) = t − t₁`) — the seam frame and the bare frame differ by a rigid
  translation, which is the whole content of `seamCoeff_trivial_dist_eq`.
* **§3 (F-2)** `Mrange_seam_floor_of_cap` — the composed floor: the pointwise bound holds at
  every frequency the infimum sees, and the window is nonempty
  (`Mrange_one_floor`'s own witness `t = (logX)^{1/15}`, under its own gate
  `(logX)^{1/15} ≤ T`; `sInf ∅ = 0` in `ℝ`, so nonemptiness is load-bearing).  Two geometric
  gates make the height range hold uniformly on the window:
  `|t₁| + 1 ≤ (logX)^{1/15}` (separation) and `T + (logX)^{1/16} + |t₁| ≤ X` (the cap on the
  height, `M_range`'s own `|t| ≤ X` cap being too weak to survive the recentring shift).
* **§4 (F-3)** `Mrange_seam_floor_column` — the binder produced VERBATIM at the column's datum
  `seamCoeff (ellLin g) (fun _ => 1) t₀`; `T1_decay_column_cap_supplied` pins it into
  `HExit.T1_decay_conditional_final` (the column consumer) end-to-end, `hfloor` DISCHARGED.
* **§5** `Mrange_seam_floor_A10` — the A-10 tree closed: the cap is a free dichotomy.  Cap
  HOLDS ⟹ §3; cap FAILS ⟹ `FarArm.cap_fails_floor` + `FarArm.Mrange_floor_of_center_floor_radius`
  (the minimiser arm).  Either way the binder lands.

**Nothing existing is touched** (Iron rule 1/5): `dist_split_A4_frozen`, the column's
statements and every landed numeral are used only in the direction they were frozen for; the
frozen `(1/16)`/`(1/32)` numerals appear here unchanged.
-/

namespace Salt.MR

/-! ## §0 — the triple-log bookkeeping

Verbatim re-derivations of `PropA3Core`'s private helpers (`private` there, so unreachable
across files).  The statements are byte-identical to the originals. -/

/-- The numeric anchor `e^e ≤ 2X + 16` for `X ≥ e` (verbatim `PropA3Core.expexp_le_two_X`). -/
private lemma fp_expexp_le_two_X {X : ℝ} (hX : Real.exp 1 ≤ X) :
    Real.exp (Real.exp 1) ≤ 2 * X + 16 := by
  have he1u : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he1l : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hX' : (2.7182818283 : ℝ) < X := lt_of_lt_of_le he1l hX
  have hexp3eq : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]; ring
  have hexp3lt : Real.exp 3 < 2.7182818286 ^ 3 := by rw [hexp3eq]; gcongr
  have hee : Real.exp (Real.exp 1) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by linarith)
  have hpow : (2.7182818286 : ℝ) ^ 3 < 21 := by norm_num
  linarith [hee, hexp3lt, hpow, hX']

/-- `logloglog(2X+16) ≥ 0` for `X ≥ e` (verbatim `PropA3Core.logloglog_two_X_nonneg`) — what
makes the in-statement `−5·logloglog(2X+16)` a genuine downward correction. -/
private lemma fp_logloglog_two_X_nonneg {X : ℝ} (hX : Real.exp 1 ≤ X) :
    0 ≤ Real.log (Real.log (Real.log (2 * X + 16))) := by
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogpos : 0 < Real.log (2 * X + 16) := Real.log_pos (by linarith)
  have h1 : Real.exp 1 ≤ Real.log (2 * X + 16) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (fp_expexp_le_two_X hX)
  have h2 : (1 : ℝ) ≤ Real.log (Real.log (2 * X + 16)) :=
    (Real.le_log_iff_exp_le hlogpos).mpr h1
  exact Real.log_nonneg h2

/-- Monotonicity of the triple log on `0 ≤ b ≤ X` (verbatim
`PropA3Core.logloglog_mono_of_le`). -/
private lemma fp_logloglog_mono_of_le {b X : ℝ} (hb : 0 ≤ b) (hbX : b ≤ X) :
    Real.log (Real.log (Real.log (b + 16)))
      ≤ Real.log (Real.log (Real.log (2 * X + 16))) := by
  have hX0 : 0 ≤ X := le_trans hb hbX
  have hb16 : (0 : ℝ) < b + 16 := by linarith
  have h2X : b + 16 ≤ 2 * X + 16 := by linarith
  have hlog1 : Real.log (b + 16) ≤ Real.log (2 * X + 16) := Real.log_le_log hb16 h2X
  have hlogb_gt1 : (1 : ℝ) < Real.log (b + 16) := by
    have hexp : Real.exp 1 < b + 16 := by have := Real.exp_one_lt_d9; linarith
    exact (Real.lt_log_iff_exp_lt (by linarith)).mpr hexp
  have hll1 : Real.log (Real.log (b + 16)) ≤ Real.log (Real.log (2 * X + 16)) :=
    Real.log_le_log (by linarith) hlog1
  exact Real.log_le_log (Real.log_pos hlogb_gt1) hll1

/-! ## §1 — the constant-datum floor, made height-uniform -/

/-- **The uniform constant-datum floor (`dist_one_floor_uniform`).**  `dist_one_floor_pow`'s
floor `loglog X − (3/4)loglog(|b|+3) − 5·logloglog(|b|+16) − C_floor` depends on the height
`b`; on the CAPPED height range `1 ≤ |b| ≤ X` it flattens to a `b`-free floor

  `(1/4)·loglog X − 5·logloglog(2X+16) − C ≤ 𝔻(1, n^{ib}; X)²`.

The `(3/4)` height correction is what eats three quarters of the leading `loglog X`
(`NonPret.loglog_height_le` at `Q = 1`, the constant `κ = log(1 + log 4)` absorbed into `C`);
the triple log is monotone up to `2X+16` (§0).  `C = (3/4)·κ + max C_floor 0 ≥ 0` is `∃`-bound;
the `−5·logloglog(2X+16)` correction stays IN-STATEMENT (S5 law — never absorbed). -/
theorem dist_one_floor_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X b : ℝ, Real.exp 1 ≤ X → 1 ≤ |b| → |b| ≤ X →
      (1 / 4) * Real.log (Real.log X)
          - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C
        ≤ pretDistSq (fun _ => 1) (costwist b) X := by
  obtain ⟨Cfloor, hCfloor⟩ := dist_one_floor_pow
  have hκnn : 0 ≤ Real.log (1 + Real.log (1 + 3)) :=
    Real.log_nonneg (by nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + 3 by norm_num)])
  -- fold the closed `log`-of-arithmetic constant to a plain variable: `linarith` cannot
  -- scale it by a rational coefficient in place (`PropA3Core`'s frozen-proof idiom)
  set κ := Real.log (1 + Real.log (1 + 3)) with hκdef
  refine ⟨(3 / 4) * κ + max Cfloor 0, ?_, ?_⟩
  · linarith [le_max_right Cfloor 0, mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hκnn]
  · intro X b hX hb1 hbX
    have hd := hCfloor X b hX hb1
    have hκ := loglog_height_le (Q := 1) (by norm_num) hX
      (show |b| ≤ 1 * X by rw [one_mul]; exact hbX)
    rw [← hκdef] at hκ
    have hmono3 := fp_logloglog_mono_of_le (abs_nonneg b) hbX
    linarith [hd, hκ, hmono3, le_max_left Cfloor 0]

/-! ## §2 — F-1: the per-`t` seam floor from the ball cap

The recentring engine, run at the SEAM datum.  Everything below is stated in the seam frame
(the frame the column's cap suppliers live in); the `t₀`-shift cancels internally. -/

/-- **F-1 — THE PER-`t` SEAM FLOOR (`seam_floor_of_cap_pointwise`).**  With

* the A-10 ball cap at the centre, in the SEAM frame:
  `𝔻²(seamCoeff f 1 t₀, n^{it₁}; X) ≤ (1/16)·loglog X`,
* the height gates `1 ≤ |t − t₁| ≤ X` (the frequency is separated from the centre, and not
  above the `dist_one_floor_pow` cap),
* the slack gate `5·logloglog(2X+16) + C ≤ (3/16)·loglog X` (what makes the recentring regime
  `S ≤ L` hold — stated, never assumed),

the seam datum obeys, at that frequency,

  `𝔻²(seamCoeff f 1 t₀, n^{it}; X) ≥ (1/16)·loglog X − 5·logloglog(2X+16) − C`.

Route: `seamCoeff_trivial_dist_eq` moves both sides to the bare datum (cap at `t₁ + t₀`,
target at `t + t₀`, height `(t+t₀) − (t₁+t₀) = t − t₁` — the shift cancels EXACTLY, no loss);
`dist_one_floor_uniform` supplies `L`; `DistSplit.dist_recenter_sq` produces `(√L − √S)²`;
`PropA3Core.recenter_sq_floor` turns that into `(1/16)loglog X − δ` at `δ = 5·logloglog + C`.

**No halving.**  `dist_split_A4`'s factor `2` is owed only when a floor is transported from
`f` onto a DIFFERENT (windowed) datum; here the trivial indicator makes the two data equal,
`seamCoeff_trivial_dist_eq` is an identity, and the window loss `W` is `0`.  That is the whole
reason this stone reaches `(1/16)` where `dist_split_A4_frozen` reaches only `(1/32) − δ`. -/
theorem seam_floor_of_cap_pointwise :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (t₀ t t₁ X : ℝ),
      Real.exp 1 ≤ X → 1 ≤ |t - t₁| → |t - t₁| ≤ X →
      pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t₁) X
          ≤ (1 / 16) * Real.log (Real.log X) →
      5 * Real.log (Real.log (Real.log (2 * X + 16))) + C
          ≤ (3 / 16) * Real.log (Real.log X) →
      (1 / 16) * Real.log (Real.log X)
            - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C
          ≤ pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t) X := by
  obtain ⟨C, hC0, hone⟩ := dist_one_floor_uniform
  refine ⟨C, hC0, ?_⟩
  intro f hf t₀ t t₁ X hX hb1 hbX hcap hgate
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hℓnn : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX1
  have hL3nn : 0 ≤ Real.log (Real.log (Real.log (2 * X + 16))) := fp_logloglog_two_X_nonneg hX
  -- the height, in the bare frame: the `t₀`-shift cancels
  have hshift : t + t₀ - (t₁ + t₀) = t - t₁ := by ring
  have hfl : (1 / 4) * Real.log (Real.log X)
      - 5 * Real.log (Real.log (Real.log (2 * X + 16))) - C
      ≤ pretDistSq (fun _ => 1) (costwist (t + t₀ - (t₁ + t₀))) X := by
    rw [hshift]; exact hone X (t - t₁) hX hb1 hbX
  -- the cap, transported onto the bare datum at the shifted centre
  have hcap' : pretDistSq f (costwist (t₁ + t₀)) X ≤ (1 / 16) * Real.log (Real.log X) := by
    rw [← seamCoeff_trivial_dist_eq (f := f) t₀ t₁ X]; exact hcap
  set ℓ := Real.log (Real.log X) with hℓdef
  set L3 := Real.log (Real.log (Real.log (2 * X + 16))) with hL3def
  set L : ℝ := (1 / 4) * ℓ - 5 * L3 - C with hLdef
  have hSL : (1 / 16) * ℓ ≤ L := by rw [hLdef]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hrec := dist_recenter_sq (f := f) hf (t := t + t₀) (t₁ := t₁ + t₀) (x := X)
    (L := L) (S := (1 / 16) * ℓ) hfl hcap' hSL
  have hsqf := recenter_sq_floor (L := L) (S := (1 / 16) * ℓ) (ℓ := ℓ) (δ := 5 * L3 + C)
    hℓnn (by linarith) rfl hL0 (by rw [hLdef]; linarith)
  rw [seamCoeff_trivial_dist_eq (f := f) t₀ t X]
  linarith [hrec, hsqf]

/-! ## §3 — F-2: the composed `M_range` floor -/

/-- **F-2 — THE COMPOSED SEAM FLOOR (`Mrange_seam_floor_of_cap`).**  The A-10 ball cap at a
centre `t₁`, plus the ball/window geometry, supplies the column's floor OUTRIGHT:

  `(1/32)·loglog X ≤ M_range (seamCoeff f (fun _ => 1) t₀) X T`.

The gates, all in-statement (law #253):

* `Real.exp 1 ≤ X` — every `loglog` page's opening gate;
* `(logX)^{1/15} ≤ T` — `Mrange_one_floor`'s own gate; it is what makes the window NONEMPTY
  (witness `t = (logX)^{1/15}`).  `sInf ∅ = 0` in `ℝ`, so without it the claim is false, not
  merely unprovable;
* `|t₁| + 1 ≤ (logX)^{1/15}` — the SEPARATION gate: the centre sits inside the annulus's inner
  radius with `1` to spare, so every frequency the infimum sees is `≥ 1` away from it (the
  `dist_one_floor_pow` hypothesis `1 ≤ |b|`);
* `T + (logX)^{1/16} + |t₁| ≤ X` — the HEIGHT gate: `M_range`'s own cap `|t| ≤ X` does not
  survive the recentring translation `t ↦ t − t₁`, so the cap is restated on the translated
  height (`dist_one_floor_pow`'s `|b| ≤ X`, via `loglog_height_le` at `Q = 1`);
* `0 ≤ W` and `5·logloglog(2X+16) + C + W ≤ (1/32)·loglog X` — the SLACK page.  `W` is the
  frozen stone's window-loss slot; on this column the loss is `0` (the trivial indicator makes
  `seamCoeff_trivial_dist_eq` an identity), so `W` is pure headroom, and the gate says exactly
  how much loss the `(1/16) → (1/32)` gap can absorb.  Asymptotically the gate is free:
  `logloglog = o(loglog)`.

Proof: `seam_floor_of_cap_pointwise` at every frequency of the window (the two abs-triangle
steps `|t| − |t₁| ≤ |t − t₁| ≤ |t| + |t₁|` turn the window's own bounds into the height
gates), then `le_csInf` over the nonempty window. -/
theorem Mrange_seam_floor_of_cap :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (t₀ t₁ X T W : ℝ),
      Real.exp 1 ≤ X →
      (Real.log X) ^ (1 / 15 : ℝ) ≤ T →
      |t₁| + 1 ≤ (Real.log X) ^ (1 / 15 : ℝ) →
      T + (Real.log X) ^ (1 / 16 : ℝ) + |t₁| ≤ X →
      0 ≤ W →
      pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t₁) X
          ≤ (1 / 16) * Real.log (Real.log X) →
      5 * Real.log (Real.log (Real.log (2 * X + 16))) + C + W
          ≤ (1 / 32) * Real.log (Real.log X) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff f (fun _ => 1) t₀) X T := by
  obtain ⟨C, hC0, hpt⟩ := seam_floor_of_cap_pointwise
  refine ⟨C, hC0, ?_⟩
  intro f hf t₀ t₁ X T W hX hT15 hsep htop hW hcap hgate
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hLXpos : (0 : ℝ) < Real.log X := by linarith
  have hℓnn : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX1
  have hr15nn : (0 : ℝ) ≤ (Real.log X) ^ (1 / 15 : ℝ) := Real.rpow_nonneg hLXpos.le _
  have hr16nn : (0 : ℝ) ≤ (Real.log X) ^ (1 / 16 : ℝ) := Real.rpow_nonneg hLXpos.le _
  have hr15X : (Real.log X) ^ (1 / 15 : ℝ) ≤ X := by
    calc (Real.log X) ^ (1 / 15 : ℝ) ≤ (Real.log X) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogX1 (by norm_num)
      _ = Real.log X := Real.rpow_one _
      _ ≤ X := by linarith [Real.log_le_sub_one_of_pos hXpos]
  -- the pointwise floor, at every frequency the infimum sees
  have hfloor : ∀ t : ℝ,
      (Real.log X) ^ (1 / 15 : ℝ) ≤ |t| ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X →
      (1 / 32) * Real.log (Real.log X)
        ≤ pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t) X := by
    rintro t ⟨htlo, hthi, _⟩
    have hlow : |t| - |t₁| ≤ |t - t₁| := abs_sub_abs_le_abs_sub t t₁
    have hhigh : |t - t₁| ≤ |t| + |t₁| := by
      rw [sub_eq_add_neg, ← abs_neg t₁]
      exact abs_add_le _ _
    have h1 : (1 : ℝ) ≤ |t - t₁| := by linarith
    have h2 : |t - t₁| ≤ X := by linarith
    have hpt' := hpt f hf t₀ t t₁ X hX h1 h2 hcap (by linarith)
    linarith [hpt']
  -- the window is nonempty (`Mrange_one_floor`'s own witness)
  have hne : ({t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|
      ∧ |t| ≤ T + (Real.log X) ^ (1 / 16 : ℝ) ∧ |t| ≤ X}).Nonempty := by
    refine ⟨(Real.log X) ^ (1 / 15 : ℝ), ?_⟩
    have habs : |(Real.log X) ^ (1 / 15 : ℝ)| = (Real.log X) ^ (1 / 15 : ℝ) :=
      abs_of_nonneg hr15nn
    rw [Set.mem_setOf_eq, habs]
    exact ⟨le_refl _, by linarith, hr15X⟩
  unfold M_range
  refine le_csInf (hne.image _) ?_
  rintro v ⟨t, ht, rfl⟩
  exact hfloor t ht

/-- **Non-vacuity of the cap gate (`cap_gate_satisfiable`).**  The house creed (six vacuity
catches on this campaign): a hypothesis nobody can satisfy is not a gate, it is a hole.  The
A-10 ball cap of §3 IS satisfiable — at the trivial datum and the trivial centre the seam
distance is exactly `0`, so the cap holds with the whole `(1/16)·loglog X` to spare.  The
matching geometry is satisfiable at the same witness (`t₁ = 0`: separation reads
`1 ≤ (logX)^{1/15}`, true for `X ≥ e`; the height gate reads `T + (logX)^{1/16} ≤ X`, true at
`T = (logX)^{1/15}` for large `X`), and the slack gate is `logloglog = o(loglog)`.  So §3 has
a non-empty instance set; what it does NOT have is a landed asymptotic discharge of the slack
gate (an explicit `X₀` tower) — that is carried, not hidden. -/
theorem cap_gate_satisfiable {X : ℝ} (hX : Real.exp 1 ≤ X) :
    pretDistSq (seamCoeff (fun _ => 1) (fun _ => 1) 0) (costwist 0) X
      ≤ (1 / 16) * Real.log (Real.log X) := by
  have hlogX1 : (1 : ℝ) ≤ Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hX
  have hℓnn : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlogX1
  have hz : pretDistSq (seamCoeff (fun _ => (1 : ℂ)) (fun _ => 1) 0) (costwist 0) X = 0 := by
    unfold pretDistSq
    refine Finset.sum_eq_zero (fun p hp => ?_)
    obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
    have hsc : seamCoeff (fun _ => (1 : ℂ)) (fun _ => 1) 0 p = 1 := by
      unfold seamCoeff
      rw [if_neg hpp.pos.ne']
      simp
    have hcw : costwist 0 p = 1 := by unfold costwist; simp
    rw [hsc, hcw]
    simp
  rw [hz]
  linarith

/-! ## §4 — F-3: the binder, produced -/

/-- **F-3 — THE COLUMN'S BINDER (`Mrange_seam_floor_column`).**  `Mrange_seam_floor_of_cap` at
the column's datum `f = ellLin g` (1-bounded by `ellLin_norm_le_one` from the corpus-standard
PRIME bound on `g`).  The conclusion is the prop-A3 column's `hfloor` binder BYTE-FOR-BYTE
(`Prop1Assembly:406`, `HExit:1465`, `HalaszHead:455`, `AnnHead:306/343/401/…`):

  `(1 / 32) * Real.log (Real.log X) ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T`.

This is the stone the column's docstrings should name in place of `Mrange_one_floor`. -/
theorem Mrange_seam_floor_column :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) → ∀ (t₀ t₁ X T W : ℝ),
      Real.exp 1 ≤ X →
      (Real.log X) ^ (1 / 15 : ℝ) ≤ T →
      |t₁| + 1 ≤ (Real.log X) ^ (1 / 15 : ℝ) →
      T + (Real.log X) ^ (1 / 16 : ℝ) + |t₁| ≤ X →
      0 ≤ W →
      pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
          ≤ (1 / 16) * Real.log (Real.log X) →
      5 * Real.log (Real.log (Real.log (2 * X + 16))) + C + W
          ≤ (1 / 32) * Real.log (Real.log X) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T := by
  obtain ⟨C, hC0, h⟩ := Mrange_seam_floor_of_cap
  exact ⟨C, hC0, fun g hg => h (ellLin g) (ellLin_norm_le_one g hg)⟩

/-- **The pin (`T1_decay_column_cap_supplied`).**  The binder, consumed: `HExit`'s column exit
`T1_decay_conditional_final` with its `hfloor` slot DISCHARGED from the ball cap.  The seam
column's `U`-grade `(log X)^{−1/(32e)} + (log X)^{−1/2+ε}` now rests on the cap and the four
geometric/slack gates instead of on an unsupplied floor hypothesis — the provenance repair,
end to end.  (`T1_decay_conditional_final`'s frequency parameter `t` is VESTIGIAL — it occurs
in none of its hypotheses and not in its conclusion — so it is instantiated at `0` here rather
than carried as a binder this statement never mentions.) -/
theorem T1_decay_column_cap_supplied :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : ℕ → ℂ), (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      ∀ (t₀ t₁ T X ε U Uhead Utail C₁ C₂ W : ℝ),
        Real.exp 1 ≤ X → 0 ≤ ε → 0 ≤ C₁ → 0 ≤ C₂ →
        U = Uhead + Utail →
        Uhead ≤ C₁ * X
          * Real.exp (-(1 / Real.exp 1) * M_range (seamCoeff (ellLin g) (fun _ => 1) t₀) X T) →
        Utail ≤ C₂ * X * (Real.log X) ^ (-(1 : ℝ) / 2) →
        (Real.log X) ^ (1 / 15 : ℝ) ≤ T →
        |t₁| + 1 ≤ (Real.log X) ^ (1 / 15 : ℝ) →
        T + (Real.log X) ^ (1 / 16 : ℝ) + |t₁| ≤ X →
        0 ≤ W →
        pretDistSq (seamCoeff (ellLin g) (fun _ => 1) t₀) (costwist t₁) X
            ≤ (1 / 16) * Real.log (Real.log X) →
        5 * Real.log (Real.log (Real.log (2 * X + 16))) + C + W
            ≤ (1 / 32) * Real.log (Real.log X) →
        U ≤ (C₁ + C₂) * X *
          ((Real.log X) ^ (-(1 / Real.exp 1) / 32) + (Real.log X) ^ (-(1 : ℝ) / 2 + ε)) := by
  obtain ⟨C, hC0, hfl⟩ := Mrange_seam_floor_column
  refine ⟨C, hC0, ?_⟩
  intro g hg t₀ t₁ T X ε U Uhead Utail C₁ C₂ W hX hε hC₁ hC₂ hsplit hhead htail
    hT15 hsep htop hW hcap hgate
  exact T1_decay_conditional_final (t := 0) hg hX hε hC₁ hC₂ hsplit hhead htail
    (hfl g hg t₀ t₁ X T W hX hT15 hsep htop hW hcap hgate)

/-! ## §5 — the A-10 tree: the cap as a free dichotomy -/

/-- **THE A-10 CLOSURE (`Mrange_seam_floor_A10`).**  The ball cap need not be assumed: it is a
DICHOTOMY, and both arms land the same binder.

* cap HOLDS on the dyadic window `[X, 2X]` ⟹ §3 (`Mrange_seam_floor_of_cap`) at `x = X` — the
  datum is pretentious to `n^{it₁}`, hence far from every frequency the window sees;
* cap FAILS ⟹ `FarArm.cap_fails_floor` (the failure gives the floor at the centre itself,
  after the `50/log X` dyadic descent charge) and `FarArm.Mrange_floor_of_center_floor_radius`
  (the centre is the compact MINIMISER at a radius covering the window, so its floor
  propagates).

So on the far-arm threshold, with the minimality hypothesis the ball machinery already
produces (`SeamGate.exists_min_gate` / `FarStar.ball_sup_closed_star`, at any radius
`R ≥ T + seamRad X`), the column's `hfloor` is UNCONDITIONAL in the cap.  The remaining
inputs are the geometry (separation + height) and the slack gate. -/
theorem Mrange_seam_floor_A10 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ (t₀ t₁ X T R W : ℝ),
      farArmThreshold ≤ X →
      (Real.log X) ^ (1 / 15 : ℝ) ≤ T →
      T + seamRad X ≤ R →
      (∀ v : ℝ, |v| ≤ R →
        pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t₁) X
          ≤ pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist v) X) →
      |t₁| + 1 ≤ (Real.log X) ^ (1 / 15 : ℝ) →
      T + (Real.log X) ^ (1 / 16 : ℝ) + |t₁| ≤ X →
      0 ≤ W →
      5 * Real.log (Real.log (Real.log (2 * X + 16))) + C + W
          ≤ (1 / 32) * Real.log (Real.log X) →
      (1 / 32) * Real.log (Real.log X)
          ≤ M_range (seamCoeff f (fun _ => 1) t₀) X T := by
  obtain ⟨C, hC0, hcaparm⟩ := Mrange_seam_floor_of_cap
  refine ⟨C, hC0, ?_⟩
  intro f hf t₀ t₁ X T R W hX hT15 hR hmin hsep htop hW hgate
  have hseam : ∀ n : ℕ, ‖seamCoeff f (fun _ => 1) t₀ n‖ ≤ 1 :=
    fun n => norm_seamCoeff_le hf (fun _ => le_of_eq norm_one) t₀ n
  by_cases hcap : ∀ x : ℝ, X ≤ x → x ≤ 2 * X →
      pretDistSq (seamCoeff f (fun _ => 1) t₀) (costwist t₁) x
        ≤ (1 / 16) * Real.log (Real.log X)
  · exact hcaparm f hf t₀ t₁ X T W (farArm_exp_one_le hX) hT15 hsep htop hW
      (hcap X le_rfl (by linarith [farArm_two_le hX])) hgate
  · exact Mrange_floor_of_center_floor_radius (farArm_exp_one_le hX) hT15 hR hmin
      (cap_fails_floor hseam hX hcap)

end Salt.MR
