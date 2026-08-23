/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.DoorFloor
import Salt.MR.DoorDischarge
import Salt.MR.RegimeHead
import Salt.MR.LandauL1

/-!
# The `B₅ = 12` sweep — the W-headroom apparatus re-instantiated at `W = (log H₊)¹²`

`docs/exploration/s9-design-0726.md` ⟦AMENDMENT A⟧ ("The FULL 1500-sweep site list"):
the S9 re-freeze moves the door's sieve exponent from `B₅ = 5` to `B₅ = 12`, i.e.
`W = (log H₊)¹²`.  Tao arXiv:1509.05422v2 Prop. 2.4's W-constraint
`W ≪ min(A, (log X)^{1/125})` then reads

  `W^{125} = (log H₊)^{1500} ≤ log X_min`   (was `(log H₊)^{625}`),

and the scale arithmetic behind the threshold moves with it:

  `1500·log L ≤ L/2`  for  `L ≥ 3.6·10⁷`,  since `√(3.6·10⁷) = 6000` EXACTLY
  (`1500·log L = 3000·log √L ≤ 3000(√L − 1) ≤ 3000√L ≤ L/2` at `√L ≥ 6000`).

The `δ₀`-hypothesis of the door-floor arm moves `6250000^{-5/4} ≈ 3·10⁻⁹` ↦
`36000000^{-5/4} ≈ 3.6·10⁻¹⁰`, still ~39 orders above the spine's `δ₀ ≈ 2·10⁻⁴⁹`.

**Everything here is ADDITIVE.**  The landed `B₅ = 5` forms (`DoorFloor.lean:180/200/214`,
`DoorDischarge.lean:42`, `RegimeHead.lean:358`, and `LandauL1.lean`'s three in-statement
`w = 5` sites) are untouched and stay as the historical record; this file adds their
`B₅ = 12` twins, plus two stones the sweep newly needs:

* §2 `W_second_arm` — Prop 2.4's OTHER arm, `W ≤ H^{1/250}`, which at `B₅ = 12` is exactly
  the gate `3000·loglog H ≤ log H` (law #253: the gate is in-statement).
* §3 the parametric-`w` LandauL1 variants.  `logq_absorbed` (`LandauL1.lean:189`) is already
  `w`-general; the three consumers below it pinned `w = 5` IN-STATEMENT, so the sweep needs
  `w`-parametric twins (`door_L1_absorbed_w`, `door_L1_debit_absorbed_w`,
  `chi_floor_real_door_w`) and their `w := 12` corollaries.

MARGIN HYGIENE (the standing law of the design): the only numerals here are the ones the
design derives — `1500`, `36000000`, `6000`, `3000`, `12`, `250`.  Nothing is a function of
`δ₀`.
-/

namespace Salt.MR

open Salt.Entropy.Chowla Salt.SW

/-! ## §1 — the W-headroom chain at `1500` -/

/-- **W-1 — the scale arithmetic at `B₅ = 12`:** `1500·log L ≤ L/2` for `L ≥ 3.6·10⁷`.
The `:180` shape verbatim, with `√36000000 = 6000` exactly: `log L = 2·log √L ≤ 2√L` and
`L = √L·√L ≥ 6000·√L`. -/
theorem log_scale_threshold_1500 {L : ℝ} (hL : 36000000 ≤ L) :
    1500 * Real.log L ≤ L / 2 := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hs : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hroot : Real.sqrt (36000000 : ℝ) = 6000 := by
    rw [show (36000000 : ℝ) = 6000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq : (6000 : ℝ) ≤ Real.sqrt L := by
    have := Real.sqrt_le_sqrt hL
    rwa [hroot] at this
  have hkey : 6000 * Real.sqrt L ≤ L := by nlinarith [hs, hsq, Real.sqrt_nonneg L]
  have hlog : Real.log L = 2 * Real.log (Real.sqrt L) := by
    rw [Real.log_sqrt hLpos.le]; ring
  have hlt : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hLpos)
  rw [hlog]
  linarith [hkey, hlt]

/-- **W-2a — the `hthr` binder of `regime_W_headroom_of_floor_1500`, supplied.**  The
`:200` shape at `B₅ = 12`: the `1500·loglog H₊` term is absorbed by half of `log H₊` once
the scale clears `3.6·10⁷`, and the `ε`-side arm carries the other half. -/
theorem regime_hthr_of_scale_1500 (R : ChowlaRegime)
    (hbig : 36000000 ≤ Real.log (R.Hhi : ℝ))
    (heps : Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
        ≤ Real.log (R.Hhi : ℝ) / 2) :
    1500 * Real.log (Real.log (R.Hhi : ℝ))
        + Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
      ≤ Real.log (R.Hhi : ℝ) := by
  have h := log_scale_threshold_1500 hbig
  linarith

/-- **W-2b — S10a at `B₅ = 12` (the `(log X)^{1/125}` arm).**  `DoorDischarge.lean:42`'s
proof, re-instantiated: from the regime field `hPHheadroom` alone, once the upper endpoint
`H₊` clears the threshold `T(ε)` (stated as `hthr`), the smallest dyadic scale
`X_min = x/(2ω)` satisfies `(log H₊)^{1500} ≤ log X_min` — equivalently
`W = (log H₊)^{12} ≤ (log X_min)^{1/125}`, Tao's W-constraint at the new `B₅`. -/
theorem regime_W_headroom_of_floor_1500 (R : ChowlaRegime)
    (hthr : 1500 * Real.log (Real.log (R.Hhi : ℝ))
        + Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
        ≤ Real.log (R.Hhi : ℝ)) :
    (Real.log (R.Hhi : ℝ)) ^ (1500 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) := by
  -- basic positivity of the scale parameters
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hHhi_ge : (4000000 : ℝ) ≤ (R.Hhi : ℝ) := by
    have : (4000000 : ℕ) ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
    exact_mod_cast this
  have hHhi_pos : (0 : ℝ) < (R.Hhi : ℝ) := by linarith
  have hωpos : (0 : ℝ) < (R.ω : ℝ) := by
    have : (2 : ℕ) ≤ R.ω := R.hω
    have : (0 : ℕ) < R.ω := by omega
    exact_mod_cast this
  have hepspos : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hepssq : (0 : ℝ) < (R.eps : ℝ) ^ 2 := by positivity
  set A : ℝ := 4 * Real.log 2 * (R.eps : ℝ) ^ 2 with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  set L : ℝ := Real.log (R.Hhi : ℝ) with hLdef
  -- `L = log H₊ ≥ 1` (since `H₊ ≥ 4·10⁶ ≥ e`)
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9
    linarith
  have hLpos : 0 < L := by linarith
  -- STEP 1 : `4·log2·ε²·H₊ ≥ e³·L^1500` from the threshold.
  have hstep1 : Real.exp 3 * L ^ (1500 : ℕ) ≤ A * (R.Hhi : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hthr
    -- expand the exponential of the sum
    have hlhs : Real.exp (1500 * Real.log L
        + Real.log (1 / A) + 3)
        = L ^ (1500 : ℕ) * (1 / A) * Real.exp 3 := by
      rw [Real.exp_add, Real.exp_add]
      congr 1
      · congr 1
        · rw [show (1500 : ℝ) * Real.log L = ((1500 : ℕ) : ℝ) * Real.log L by norm_num,
            Real.exp_nat_mul, Real.exp_log hLpos]
        · rw [Real.exp_log (by positivity)]
    have hrhs : Real.exp L = (R.Hhi : ℝ) := by rw [hLdef, Real.exp_log hHhi_pos]
    rw [hlhs, hrhs] at hexp
    -- `L^1500·(1/A)·e³ ≤ H₊` ⇒ `e³·L^1500 ≤ A·H₊` (multiply through by `A > 0`)
    have hmul := mul_le_mul_of_nonneg_left hexp hApos.le
    have hrw : A * (L ^ (1500 : ℕ) * (1 / A) * Real.exp 3) = Real.exp 3 * L ^ (1500 : ℕ) := by
      field_simp
    rw [hrw] at hmul
    exact hmul
  -- STEP 2 : `(e³ − 1)·L^1500 ≥ 2·log2`, closing `A·H₊ − 2·log2 ≥ L^1500`.
  have hLpow1 : (1 : ℝ) ≤ L ^ (1500 : ℕ) := one_le_pow₀ hL1
  have hexp3 : (4 : ℝ) ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ); linarith
  have hlog2lt1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hstep2 : L ^ (1500 : ℕ) ≤ A * (R.Hhi : ℝ) - 2 * Real.log 2 := by
    have : Real.exp 3 * L ^ (1500 : ℕ) - 2 * Real.log 2 ≥ L ^ (1500 : ℕ) := by
      nlinarith [hLpow1, hexp3, hlog2lt1]
    linarith [hstep1, this]
  -- STEP 3 : `log(x/2ω) ≥ A·H₊ − 2·log2` from `hPHheadroom`.
  set m : ℕ := ⌊(R.eps : ℚ) ^ 2 * (R.Hhi : ℚ)⌋₊ with hmdef
  have hm_ge : (R.eps : ℝ) ^ 2 * (R.Hhi : ℝ) - 1 ≤ (m : ℝ) := by
    have hlt : ((R.eps : ℚ) ^ 2 * (R.Hhi : ℚ)) < (m : ℚ) + 1 := by
      rw [hmdef]; exact Nat.lt_floor_add_one _
    have : ((R.eps : ℚ) ^ 2 * (R.Hhi : ℚ) : ℝ) < (m : ℝ) + 1 := by exact_mod_cast hlt
    push_cast at this
    linarith
  -- the field, rewritten with `4^m` cast to ℝ
  set M4 : ℝ := ((4 ^ m : ℕ) : ℝ) with hM4def
  have hM4eq : M4 = (4 : ℝ) ^ m := by rw [hM4def]; push_cast; ring
  have hM4pos : 0 < M4 := by rw [hM4eq]; positivity
  have hfield : 8 * M4 ^ 2 * (R.ω : ℝ) ≤ (R.x : ℝ) := R.hPHheadroom
  have hxpos : 0 < (R.x : ℝ) := lt_of_lt_of_le (by positivity) hfield
  -- `log(x/2ω) = log x − log2 − log ω`
  have h2ωpos : (0 : ℝ) < 2 * (R.ω : ℝ) := by positivity
  have hlogdiv : Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ)))
      = Real.log (R.x : ℝ) - Real.log 2 - Real.log (R.ω : ℝ) := by
    rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt h2ωpos),
        Real.log_mul (by norm_num) (ne_of_gt hωpos)]
    ring
  -- `log x ≥ log8 + 2m·log2 + log ω`
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
  have hlogM4 : Real.log M4 = (m : ℝ) * (2 * Real.log 2) := by
    rw [hM4eq, Real.log_pow, hlog4]
  have hlogfield : Real.log (8 * M4 ^ 2 * (R.ω : ℝ))
      = 3 * Real.log 2 + 4 * (m : ℝ) * Real.log 2 + Real.log (R.ω : ℝ) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hωpos),
        Real.log_mul (by norm_num) (by positivity),
        Real.log_pow, hlog8, hlogM4]
    push_cast; ring
  have hlogx : 3 * Real.log 2 + 4 * (m : ℝ) * Real.log 2 + Real.log (R.ω : ℝ)
      ≤ Real.log (R.x : ℝ) := by
    rw [← hlogfield]
    exact Real.log_le_log (by positivity) hfield
  -- assemble : `log(x/2ω) ≥ (4m+2)·log2 ≥ A·H₊ − 2·log2`
  have hchain : A * (R.Hhi : ℝ) - 2 * Real.log 2
      ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) := by
    rw [hlogdiv]
    have h1 : A * (R.Hhi : ℝ) - 2 * Real.log 2 ≤ (4 * (m : ℝ) + 2) * Real.log 2 := by
      rw [hAdef]
      nlinarith [hm_ge, hlog2pos, hepssq, hHhi_pos]
    nlinarith [h1, hlogx, hlog2pos]
  linarith [hstep2, hchain]

/-- **W-2c — the door floor discharges Tao's W-constraint at `B₅ = 12`.**  The `:214` shape:
once the regime's upper window endpoint clears `H₀door(δ₀)` — now with `δ₀` below
`36000000^{-5/4} ≈ 3.6·10⁻¹⁰`, at the spine's `δ₀ ≈ 2·10⁻⁴⁹` still ~39 orders of slack —
S10a fires at the new exponent: `(log H₊)^{1500} ≤ log X_min`, i.e.
`W = (log H₊)^{12} ≤ (log X_min)^{1/125}`. -/
theorem regime_W_headroom_of_H0door_1500 (R : ChowlaRegime) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsmall : δ₀ ≤ (36000000 : ℝ) ^ (-(5 / 4 : ℝ)))
    (hfloor : H0door δ₀ ≤ R.Hhi)
    (heps : Real.log (1 / (4 * Real.log 2 * (R.eps : ℝ) ^ 2)) + 3
        ≤ Real.log (R.Hhi : ℝ) / 2) :
    (Real.log (R.Hhi : ℝ)) ^ (1500 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) :=
  regime_W_headroom_of_floor_1500 R
    (regime_hthr_of_scale_1500 R (le_log_of_H0door_le (by norm_num) hδ₀ hsmall hfloor) heps)

/-- **W-2d — the head, the door floor, the `g`-clearance, and Tao's W-constraint at
`B₅ = 12`, in ONE statement** (`RegimeHead.lean:358`, re-instantiated).  For any
`ε ∈ (0, 1/2]`, any door threshold `δ₀ > 0` below `36000000^{-5/4}`, any extra floor demand,
and any CHOICE-JOIN parameters, there is a regime that

* sits at `ε` and above BOTH the caller's floor and the MR door floor `H₀door δ₀`;
* clears the CHOICE-JOIN `gJoin` at its outer scale (so the A-arm fires, `s5_at_regime`); and
* satisfies `(log H₊)^{1500} ≤ log X_min`, i.e. `W = (log H₊)^{12} ≤ (log X_min)^{1/125}`.

The `ε`-arm is discharged internally by demanding `epsFloor ε` of the SAME floor slot — the
trick, unchanged, that makes the hand-off hypothesis-free. -/
theorem regime_head_W_headroom_1500 (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hsmall : δ₀ ≤ (36000000 : ℝ) ^ (-(5 / 4 : ℝ)))
    (extraFloor : ℕ) (M0 : ℝ) (X0MR : ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ extraFloor ≤ R.Hlo ∧ H0door δ₀ ≤ R.Hlo ∧
      gJoin M0 X0MR R.Hhi R.ω ≤ R.x ∧
      (Real.log (R.Hhi : ℝ)) ^ (1500 : ℕ) ≤ Real.log ((R.x : ℝ) / (2 * (R.ω : ℝ))) := by
  obtain ⟨R, hReps, hRHlo, hRg⟩ :=
    chowlaRegime_exists_param_head_gJoin eps heps heps1
      (max (max extraFloor (H0door δ₀)) (epsFloor eps)) M0 X0MR
  have hextra : extraFloor ≤ R.Hlo :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hRHlo
  have hdoor : H0door δ₀ ≤ R.Hlo :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hRHlo
  have hepsF : epsFloor R.eps ≤ R.Hhi := by
    rw [hReps]
    exact le_trans (le_trans (le_max_right _ _) hRHlo) R.hHlohi
  refine ⟨R, hReps, hextra, hdoor, hRg, ?_⟩
  exact regime_W_headroom_of_H0door_1500 R hδ₀ hsmall (le_trans hdoor R.hHlohi)
    (heps_arm_of_epsFloor hepsF)

/-! ## §2 — Prop 2.4's second arm: `W ≤ H^{1/250}` -/

/-- **W-3 — the `H`-side arm of Tao arXiv:1509.05422v2 Prop. 2.4 at `B₅ = 12`.**  The constraint
`W ≤ H^{1/250}` at `W = (log H)^{12}` is, after taking logarithms, EXACTLY the gate
`3000·loglog H ≤ log H` — since `12·loglog H ≤ (log H)/250 ⟺ 3000·loglog H ≤ log H`.

Law #253: the gate is a hypothesis of the statement, not an "eventually".  The companion
`W_second_arm_of_scale` discharges it from the same `3.6·10⁷` scale bound the `1500`-arm
uses, so BOTH arms of Prop. 2.4 are fed by one threshold. -/
theorem W_second_arm {H : ℝ} (hH : Real.exp 1 ≤ H)
    (hgate : 3000 * Real.log (Real.log H) ≤ Real.log H) :
    Real.log H ^ (12 : ℕ) ≤ H ^ ((1 : ℝ) / 250) := by
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (Real.exp_pos 1) hH
  have hL1 : (1 : ℝ) ≤ Real.log H := by
    have h := Real.log_le_log (Real.exp_pos 1) hH
    rwa [Real.log_exp] at h
  have hLpos : (0 : ℝ) < Real.log H := lt_of_lt_of_le one_pos hL1
  have hlhs : Real.log (Real.log H ^ (12 : ℕ)) = 12 * Real.log (Real.log H) := by
    rw [Real.log_pow]; push_cast; ring
  have hrhs : Real.log (H ^ ((1 : ℝ) / 250)) = (1 / 250) * Real.log H := by
    rw [Real.log_rpow hHpos]
  have hkey : Real.log (Real.log H ^ (12 : ℕ)) ≤ Real.log (H ^ ((1 : ℝ) / 250)) := by
    rw [hlhs, hrhs]; linarith
  have hexp := Real.exp_le_exp.mpr hkey
  rwa [Real.exp_log (pow_pos hLpos 12),
    Real.exp_log (Real.rpow_pos_of_pos hHpos _)] at hexp

/-- **The second arm at the sweep's own threshold.**  `36000000 ≤ log H` — the very bound
`log_scale_threshold_1500` consumes — already forces `3000·loglog H ≤ log H`, hence
`W = (log H)^{12} ≤ H^{1/250}`.  So one scale demand feeds both arms of Prop. 2.4.
(`0 < H` is carried explicitly: `Real.log` is EVEN, so a scale bound on `log H` alone does
not orient `H`.) -/
theorem W_second_arm_of_scale {H : ℝ} (hHpos : 0 < H) (hbig : 36000000 ≤ Real.log H) :
    Real.log H ^ (12 : ℕ) ≤ H ^ ((1 : ℝ) / 250) := by
  have hH : Real.exp 1 ≤ H := by
    have h := Real.exp_le_exp.mpr (show (1 : ℝ) ≤ Real.log H by linarith)
    rwa [Real.exp_log hHpos] at h
  have h := log_scale_threshold_1500 hbig
  exact W_second_arm hH (by linarith)

/-! ## §3 — the parametric-`w` LandauL1 variants

`logq_absorbed` (`LandauL1.lean:189`) is already stated at a free `w`; its three consumers
pinned `w = 5` in-statement.  These are their `w`-parametric twins, plus the `w := 12`
corollaries the `B₅ = 12` door reads.  The landed `w = 5` forms are untouched. -/

/-- **W-4a — `door_L1_absorbed` at a free door width.**  At a door pinned
`q ≤ (loglog X)^w` and a polynomial slot `L₁ = c·q^{−A}`, the cost `log(1/L₁)` is below
`ε·loglog X` past an explicit gate `G` (law #253).  `LandauL1.lean:241` is the `w = 5`
instance. -/
theorem door_L1_absorbed_w {c A ε w : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hw : 0 ≤ w) (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (X : ℝ) (q : ℕ), 1 ≤ q →
      G ≤ Real.log (Real.log X) →
      (q : ℝ) ≤ Real.log (Real.log X) ^ w →
        Real.log (1 / (c / (q : ℝ) ^ A)) ≤ ε * Real.log (Real.log X) := by
  obtain ⟨G, hG0, hG⟩ :=
    logq_absorbed (K₁ := -Real.log c) (K₂ := A) (w := w) (ε := ε) hA hw hε
  refine ⟨G, hG0, ?_⟩
  intro X q hq hGY hqY
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpow : (0 : ℝ) < (q : ℝ) ^ A := Real.rpow_pos_of_pos hq0 A
  have hrw : Real.log (1 / (c / (q : ℝ) ^ A)) = -Real.log c + A * Real.log q := by
    rw [one_div, Real.log_inv, Real.log_div (ne_of_gt hc) (ne_of_gt hpow), Real.log_rpow hq0]
    ring
  rw [hrw]
  exact hG _ q hq hGY hqY

/-- The `B₅ = 12` door's absorption, polynomial grade: `door_L1_absorbed_w` at `w := 12`. -/
theorem door_L1_absorbed_12 {c A ε : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (X : ℝ) (q : ℕ), 1 ≤ q →
      G ≤ Real.log (Real.log X) →
      (q : ℝ) ≤ Real.log (Real.log X) ^ (12 : ℝ) →
        Real.log (1 / (c / (q : ℝ) ^ A)) ≤ ε * Real.log (Real.log X) :=
  door_L1_absorbed_w hc hA (by norm_num) hε

/-- **W-4b — `door_L1_debit_absorbed` at a free door width.**  The FULL
`chi_floor_real_of_L1` debit, absorbed at a door pinned `q ≤ (loglog X)^w`.
`LandauL1.lean:367` is the `w = 5` instance; the affine-in-`log q` bound
(`debit_le_affine_log`) is `w`-free, so only the absorption kernel's `w` moves. -/
theorem door_L1_debit_absorbed_w {c A Z ε w : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hZ : 1 ≤ Z)
    (hw : 0 ≤ w) (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (X : ℝ) (q : ℕ), 1 ≤ q →
      G ≤ Real.log (Real.log X) →
      (q : ℝ) ≤ Real.log (Real.log X) ^ w →
        Real.log 2 - Real.log (c / (q : ℝ) ^ A) + 2 * Real.log 4
            + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / (c / (q : ℝ) ^ A))
          ≤ ε * Real.log (Real.log X) := by
  obtain ⟨G, hG0, hG⟩ := logq_absorbed
    (K₁ := Real.log 2 - Real.log c + 2 * Real.log 4
      + (1 / 4) * (Real.log 16 + Real.log Z + Real.log (27 / 2) + 1 - Real.log c))
    (K₂ := A + (1 / 4) * (7 / 2 + A)) (w := w) (ε := ε) (by linarith) hw hε
  refine ⟨G, hG0, ?_⟩
  intro X q hq hGY hqY
  exact le_trans (debit_le_affine_log hc hZ hq) (hG _ q hq hGY hqY)

/-- The `B₅ = 12` door's absorption of the full debit: `door_L1_debit_absorbed_w` at
`w := 12`. -/
theorem door_L1_debit_absorbed_12 {c A Z ε : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hZ : 1 ≤ Z)
    (hε : 0 < ε) :
    ∃ G : ℝ, 0 < G ∧ ∀ (X : ℝ) (q : ℕ), 1 ≤ q →
      G ≤ Real.log (Real.log X) →
      (q : ℝ) ≤ Real.log (Real.log X) ^ (12 : ℝ) →
        Real.log 2 - Real.log (c / (q : ℝ) ^ A) + 2 * Real.log 4
            + (1 / 4) * Real.log (16 * (q : ℝ) * Z * diskConst q / (c / (q : ℝ) ^ A))
          ≤ ε * Real.log (Real.log X) :=
  door_L1_debit_absorbed_w hc hA hZ (by norm_num) hε

/-- **W-4c — the ROUTE-A floor's door shape at a free door width.**
`LandauL1.lean:431` (`chi_floor_real_door`) with its in-statement `q ≤ (loglog X)⁵` lifted to
`q ≤ (loglog X)^w`: past an explicit gate `G` on `loglog X`, the bounded-band branch reads
`loglog X − (3/4)·log(1 + log X) − ε·loglog X − CH2` for ANY prescribed `ε > 0` — the whole
`L₁`/`q`/`diskConst` debit vanishing into `ε`.  Unconditional GIVEN the interface `hL`. -/
theorem chi_floor_real_door_w {c A ε w : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hA : 0 ≤ A)
    (hw : 0 ≤ w) (hε : 0 < ε) (hL : L1LowerEffective c A) :
    ∃ CH1 CH2 G : ℝ, 0 < G ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → G ≤ Real.log (Real.log X) →
        (q : ℝ) ≤ Real.log (Real.log X) ^ w →
        32 * diskConst q / (c / (q : ℝ) ^ A) ≤ Real.log X →
          min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
                - ε * Real.log (Real.log X) - CH2)
              ((Real.log (Real.log X)
                  - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                  - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                  - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
            ≤ pretDistSq (lamChi χ) (costwist t) X := by
  obtain ⟨CH1, CH2, Z, hZ1, hC⟩ := chi_floor_real_of_L1
  obtain ⟨G, hG0, hG⟩ :=
    door_L1_debit_absorbed_w (c := c) (A := A) (Z := Z) (w := w) hc hA hZ1 hw hε
  refine ⟨CH1, CH2, G, hG0, ?_⟩
  intro q _ χ hχ1 hsq X t hX hGate hqY hgate
  have hqN : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqN
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ A := Real.one_le_rpow hq1 hA
  have hpow0 : (0 : ℝ) < (q : ℝ) ^ A := lt_of_lt_of_le one_pos hpow
  have hfloor := hC q χ hχ1 hsq X t (c / (q : ℝ) ^ A) hX (div_pos hc hpow0)
    (by rw [div_le_one hpow0]; linarith) (hL q χ hχ1 hsq) hgate
  refine le_trans (min_le_min ?_ (le_refl _)) hfloor
  have := hG X q hqN hGate hqY
  linarith

/-- The ROUTE-A floor at the `B₅ = 12` door: `chi_floor_real_door_w` at `w := 12`. -/
theorem chi_floor_real_door_12 {c A ε : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hA : 0 ≤ A)
    (hε : 0 < ε) (hL : L1LowerEffective c A) :
    ∃ CH1 CH2 G : ℝ, 0 < G ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ X t : ℝ, Real.exp 1 ≤ X → G ≤ Real.log (Real.log X) →
        (q : ℝ) ≤ Real.log (Real.log X) ^ (12 : ℝ) →
        32 * diskConst q / (c / (q : ℝ) ^ A) ≤ Real.log X →
          min (Real.log (Real.log X) - (3 / 4) * Real.log (1 + Real.log X)
                - ε * Real.log (Real.log X) - CH2)
              ((Real.log (Real.log X)
                  - (3 / 4) * Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 3))
                  - 5 * Real.log (Real.log (Real.log (|((2 * orderOf χ : ℕ) : ℝ) * t| + 16)))
                  - CH1 - primeDivSum q X) / ((2 * orderOf χ : ℕ) : ℝ) ^ 2)
            ≤ pretDistSq (lamChi χ) (costwist t) X :=
  chi_floor_real_door_w hc hc1 hA (by norm_num) hε hL

end Salt.MR
