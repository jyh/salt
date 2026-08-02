/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE SHAPE-FREE TOLL — the width law over ALL decrement schedules

`TowerFlat.lean` prices ONE tower: the flat threshold `κ = H/(A·log H)`, whose
multiplier is the constant-`A` floor `⌊2·A·log H⌋₊`.  The natural question is
whether some other SHAPE of threshold evades that price.  This file answers it:
it does not.

Let `φ : ℕ → ℝ` be an arbitrary threshold SCHEDULE — a different design constant
at every level, chosen by an adversary with full knowledge of the tower — subject
only to a budget floor `A_b ≤ φ_j` (`A_b ≥ 1`).  Step

    H_0 = B,   H_{j+1} = H_j · ⌊2·φ_j·log H_j⌋₊,

and let the telescoped decrement be `S_J = Σ_{j<J} 1/(2·φ_j·log H_j)`.  Write
`L_j = log H_j`, `λ_j = log L_j`, `c_b = log (2·A_b)` (`flatC A_b`) and
`w_j = log (c_b + λ_j)` (`towerWS`).  Then, under the same base floor
`4·10⁶ ≤ B` and the same flat floor `100·(c_b + λ_0) ≤ L_0` that `TowerFlat`
carries,

* `towerShape_inv` — the floor invariant `100·(c_b + λ_j) ≤ L_j` propagates for
  EVERY schedule.  Unlike the flat case this needs no upper bound on the step:
  `Δλ_j ≤ d_j/L_j` and `100·d_j/L_j ≤ d_j` already at `L_j ≥ 100`, so an
  arbitrarily large multiplier only helps.
* `towerShape_dropSum_le` — `S_J ≤ (21/20)·(1/(2·A_b))·(w_J − w_0)`: the
  master law's upper half at the BUDGET constant.  Only the LOWER floor price
  transfers (`shapeStep_logMul_ge`: `log⌊2·φ_j·L_j⌋₊ ≥ c_b + λ_j − 1/500`, from
  `φ_j ≥ A_b` and monotonicity of `⌊·⌋₊` and `log`); the upper floor price
  `d_j ≤ c_b + λ_j` is FALSE for a large `φ_j` and is not needed — the
  width-necessity direction consumes only the lower half.
* **`towerShape_width_ge` — THE SHAPE-FREE TOLL.**  If the schedule's decrement
  ever crosses the budget, `log 2 < S_J`, then

        (c_b + λ_0)·4^{(20/21)·A_b} ≤ c_b + λ_J.

  No shape escapes: every road over the entropy mountain pays `4^{A_b}` in
  doubly-logarithmic width, at the exponent its own budget floor names.
* `towerShape_flat_le` — the extremality tie.  The CONSTANT schedule `φ ≡ A` IS
  `chowlaTowerFlat A 1 B` (`chowlaTowerShape_const`), so `towerFlat_width_le`
  supplies the matching upper bracket `(c + λ_{J_min}) ≤ (21/20)·4^A·(c + λ_0)`.

Pairing the last two: every schedule with floor `A_b` pays at least
`4^{(20/21)·A_b}`, and the flat schedule at `A = A_b` pays at most
`(21/20)·4^{A_b}` — the flat tower is extremal up to `4^{A_b/21}·(21/20)` in the
width multiplier, i.e. the exponent is determined to within `4.8%`.

## How the abstract page is reused

`TowerFlat`'s per-step pair `flatStep_dw_le`/`flatStep_dw_ge` already takes pure
reals, so nothing about the flat tower is re-proved here.  The only new abstract
ingredient is `shapeStep_dw_ge`, which drops `flatStep_dw_ge`'s upper hypothesis
`d ≤ c + λ` by a monotonicity argument: the potential increment `w' − w` is
increasing in `d`, so truncating the step at `d_0 = min d (c + λ)` — which does
satisfy both flat hypotheses — only decreases it.

Everything here is ADDITIVE: no landed declaration is touched.
-/
import Salt.Entropy.Chowla.TowerFlat

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section 1 — the schedule tower and its glyphs -/

/-- **The schedule tower.**  `H_0 = B`, `H_{j+1} = H_j·⌊2·φ_j·log H_j⌋₊` — the
    flat tower's shape with the design CONSTANT `A` replaced by an arbitrary
    threshold SCHEDULE `φ : ℕ → ℝ`. -/
noncomputable def chowlaTowerShape (φ : ℕ → ℝ) (B : ℕ) : ℕ → ℕ
  | 0 => B
  | (j + 1) => chowlaTowerShape φ B j *
      ⌊2 * φ j * Real.log (chowlaTowerShape φ B j : ℝ)⌋₊

/-- `L_j = log H_j` along the schedule tower. -/
noncomputable def towerLS (φ : ℕ → ℝ) (B j : ℕ) : ℝ :=
  Real.log (chowlaTowerShape φ B j : ℝ)

/-- `λ_j = loglog H_j` along the schedule tower. -/
noncomputable def towerLamS (φ : ℕ → ℝ) (B j : ℕ) : ℝ := Real.log (towerLS φ B j)

/-- `w_j = log (c_b + λ_j)` — the telescoping potential, at the BUDGET constant
    `c_b = flatC A_b = log (2·A_b)` rather than at the schedule's own value. -/
noncomputable def towerWS (Ab : ℝ) (φ : ℕ → ℝ) (B j : ℕ) : ℝ :=
  Real.log (flatC Ab + towerLamS φ B j)

/-- The schedule tower multiplier `⌊2·φ_j·L_j⌋₊`. -/
noncomputable def towerMulS (φ : ℕ → ℝ) (B j : ℕ) : ℕ := ⌊2 * φ j * towerLS φ B j⌋₊

/-- The schedule's telescoped per-step decrement `Σ_{j<J} 1/(2·φ_j·L_j)`. -/
noncomputable def towerDropSumShape (φ : ℕ → ℝ) (B J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, 1 / (2 * φ j * towerLS φ B j)

lemma chowlaTowerShape_zero (φ : ℕ → ℝ) (B : ℕ) : chowlaTowerShape φ B 0 = B := rfl

lemma chowlaTowerShape_succ_raw (φ : ℕ → ℝ) (B j : ℕ) :
    chowlaTowerShape φ B (j + 1)
      = chowlaTowerShape φ B j *
        ⌊2 * φ j * Real.log (chowlaTowerShape φ B j : ℝ)⌋₊ := rfl

lemma chowlaTowerShape_succ (φ : ℕ → ℝ) (B j : ℕ) :
    chowlaTowerShape φ B (j + 1) = chowlaTowerShape φ B j * towerMulS φ B j := rfl

lemma towerLS_zero (φ : ℕ → ℝ) (B : ℕ) : towerLS φ B 0 = Real.log (B : ℝ) := rfl

lemma towerLamS_zero (φ : ℕ → ℝ) (B : ℕ) :
    towerLamS φ B 0 = Real.log (Real.log (B : ℝ)) := rfl

/-! ### Section 2 — the floor furniture (verbatim transfer from the flat tower) -/

/-- Every schedule above the budget floor has multiplier `≥ 2` above the regime
    floor: the schedule tower cannot stall. -/
lemma shapeMul_ge_two {Ab p : ℝ} (hAb : 1 ≤ Ab) (hp : Ab ≤ p) {H : ℕ}
    (hH : 4000000 ≤ H) : 2 ≤ ⌊2 * p * Real.log (H : ℝ)⌋₊ :=
  flatMul_ge_two (le_trans hAb hp) hH

lemma chowlaTowerShape_base_ge {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : B ≤ chowlaTowerShape φ B j := by
  induction j with
  | zero => exact le_rfl
  | succ n ih =>
    have hfloor : 4000000 ≤ chowlaTowerShape φ B n := le_trans hB ih
    have hmult : 2 ≤ ⌊2 * φ n * Real.log ((chowlaTowerShape φ B n : ℕ) : ℝ)⌋₊ :=
      shapeMul_ge_two hAb (hφ n) hfloor
    rw [chowlaTowerShape_succ_raw]
    exact le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

lemma chowlaTowerShape_base_floor {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 4000000 ≤ chowlaTowerShape φ B j :=
  le_trans hB (chowlaTowerShape_base_ge hAb hφ hB j)

lemma towerLS_ge_fifteen {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 15 ≤ towerLS φ B j := by
  rw [towerLS]; exact (tower_log_bounds (chowlaTowerShape_base_floor hAb hφ hB j)).1

lemma towerLS_pos {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 0 < towerLS φ B j := by
  linarith [towerLS_ge_fifteen hAb hφ hB j]

lemma towerLamS_ge_two {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 2 ≤ towerLamS φ B j := by
  have hL := towerLS_ge_fifteen hAb hφ hB j
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hexp2 : Real.exp 2 ≤ 15 := by nlinarith [Real.exp_pos 1]
  rw [towerLamS, Real.le_log_iff_exp_le (by linarith)]
  linarith

lemma towerMulS_ge_two {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 2 ≤ towerMulS φ B j := by
  rw [towerMulS, towerLS]
  exact shapeMul_ge_two hAb (hφ j) (chowlaTowerShape_base_floor hAb hφ hB j)

/-- The schedule tower's `succ` step in the glyph `L`. -/
lemma towerLS_succ {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    towerLS φ B (j + 1) = towerLS φ B j + Real.log ((towerMulS φ B j : ℕ) : ℝ) := by
  have hm2 : 2 ≤ towerMulS φ B j := towerMulS_ge_two hAb hφ hB j
  have hfloor := chowlaTowerShape_base_floor hAb hφ hB j
  have hH0 : ((chowlaTowerShape φ B j : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < chowlaTowerShape φ B j := by omega
    positivity
  have hm0 : ((towerMulS φ B j : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < towerMulS φ B j := by omega
    positivity
  simp only [towerLS]
  rw [chowlaTowerShape_succ, Nat.cast_mul, Real.log_mul hH0 hm0]

/-! ### Section 3 — the floor price (lower half only) and the invariant -/

/-- Under the floor at a level, the potential's argument clears `3` — verbatim
    the flat argument, which uses only `λ ≥ 2` and `c_b ≥ log 2`. -/
lemma shapeLevel_s_ge_three {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) {j : ℕ}
    (hinv : 100 * (flatC Ab + towerLamS φ B j) ≤ towerLS φ B j) :
    3 ≤ flatC Ab + towerLamS φ B j := by
  have hlam2 : 2 ≤ towerLamS φ B j := towerLamS_ge_two hAb hφ hB j
  have hc : Real.log 2 ≤ flatC Ab := flatC_ge_log_two hAb
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL50 : 50 ≤ towerLS φ B j := by linarith
  have hlam3 : 3 ≤ towerLamS φ B j := by
    rw [towerLamS, Real.le_log_iff_exp_le (by linarith)]
    linarith [exp_three_le_fifty]
  linarith

/-- **THE FLOOR PRICE AT THE BUDGET CONSTANT (abstract).**  For any threshold
    value `p ≥ A_b` and any `L ≥ 300`,

        `c_b + log L − 1/500 ≤ log ⌊2·p·L⌋₊`,

    where `c_b = log (2·A_b)`.  The flat proof runs at `A_b` (where the floor
    `2·A_b·L ≥ 600` gives the `1/500`), and `⌊·⌋₊` and `log` are monotone, so a
    LARGER threshold only raises the left side's witness.  The companion UPPER
    price `log ⌊2·p·L⌋₊ ≤ c_b + log L` is FALSE for `p > A_b` and is not used. -/
lemma shapeStep_logMul_ge_abs {Ab p L : ℝ} (hAb : 1 ≤ Ab) (hp : Ab ≤ p) (hL : 300 ≤ L) :
    flatC Ab + Real.log L - 1 / 500 ≤ Real.log ((⌊2 * p * L⌋₊ : ℕ) : ℝ) := by
  have hLpos : (0 : ℝ) < L := by linarith
  have hX : (600 : ℝ) ≤ 2 * Ab * L := by nlinarith
  have hgt : 2 * Ab * L - 1 < ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
  have hm599 : (599 : ℝ) ≤ ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ) := by linarith
  have hmpos : (0 : ℝ) < ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ) := by linarith
  have h := log_sub_log_le (a := 2 * Ab * L) (b := ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ))
    (by linarith) hmpos
  have hfrac : (2 * Ab * L - ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ)) / ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ)
      ≤ 1 / 500 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    linarith
  rw [flatLog_prod hAb hLpos] at h
  have hmono : (⌊2 * Ab * L⌋₊ : ℕ) ≤ (⌊2 * p * L⌋₊ : ℕ) := Nat.floor_le_floor (by nlinarith)
  have hmono' : ((⌊2 * Ab * L⌋₊ : ℕ) : ℝ) ≤ ((⌊2 * p * L⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmono
  have hlog := Real.log_le_log hmpos hmono'
  linarith

/-- **The floor price along the schedule tower, lower half.** -/
lemma shapeStep_logMul_ge {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B) {j : ℕ}
    (hinv : 100 * (flatC Ab + towerLamS φ B j) ≤ towerLS φ B j) :
    flatC Ab + towerLamS φ B j - 1 / 500 ≤ Real.log ((towerMulS φ B j : ℕ) : ℝ) := by
  have hs3 := shapeLevel_s_ge_three hAb hφ hB hinv
  have hL300 : (300 : ℝ) ≤ towerLS φ B j := by linarith
  have h := shapeStep_logMul_ge_abs hAb (hφ j) hL300
  rwa [← towerLamS, ← towerMulS] at h

/-- **THE SHAPE-FREE FLOOR INVARIANT.**  `100·(c_b + λ_j) ≤ L_j` propagates up
    the schedule tower for EVERY schedule above the budget floor.  The flat proof
    needed the multiplier's upper price to keep `Δλ` small; here no upper price
    exists, and none is needed: `Δλ_j ≤ d_j/L_j` gives
    `100·(c_b + λ_{j+1}) ≤ L_j + 100·d_j/L_j ≤ L_j + d_j = L_{j+1}` as soon as
    `L_j ≥ 100`, which the invariant itself supplies (`L_j ≥ 300`).  A bigger
    multiplier is strictly better for the invariant. -/
theorem towerShape_inv {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC Ab + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (j : ℕ) :
    100 * (flatC Ab + towerLamS φ B j) ≤ towerLS φ B j := by
  induction j with
  | zero => rw [towerLS_zero, towerLamS_zero]; exact hfl
  | succ n ih =>
    have hs3 := shapeLevel_s_ge_three hAb hφ hB ih
    have hLpos : 0 < towerLS φ B n := towerLS_pos hAb hφ hB n
    have hL300 : (300 : ℝ) ≤ towerLS φ B n := by linarith
    have hm2 : 2 ≤ towerMulS φ B n := towerMulS_ge_two hAb hφ hB n
    have hd0 : (0 : ℝ) ≤ Real.log ((towerMulS φ B n : ℕ) : ℝ) := by
      refine Real.log_nonneg ?_
      have h : (1 : ℕ) ≤ towerMulS φ B n := by omega
      exact_mod_cast h
    have hsucc := towerLS_succ hAb hφ hB n
    have hL'pos : 0 < towerLS φ B (n + 1) := towerLS_pos hAb hφ hB (n + 1)
    have hsub : towerLS φ B (n + 1) - towerLS φ B n
        = Real.log ((towerMulS φ B n : ℕ) : ℝ) := by rw [hsucc]; ring
    have hstep : towerLamS φ B (n + 1) - towerLamS φ B n
        ≤ (towerLS φ B (n + 1) - towerLS φ B n) / towerLS φ B n :=
      log_sub_log_le hL'pos hLpos
    rw [hsub] at hstep
    have hcheap : 100 * (Real.log ((towerMulS φ B n : ℕ) : ℝ) / towerLS φ B n)
        ≤ Real.log ((towerMulS φ B n : ℕ) : ℝ) := by
      rw [← mul_div_assoc, div_le_iff₀ hLpos]
      nlinarith
    rw [hsucc]
    linarith

/-! ### Section 4 — the per-step law with NO upper price (abstract reals) -/

/-- **The schedule per-step law, lower half** — `(20/21)/L ≤ Δw`, with the flat
    law's upper hypothesis `d ≤ c + λ` REMOVED.

    `w' − w` is monotone increasing in the step `d`, so truncating the step at
    `d_0 = min d (c + λ)` — which satisfies both of `flatStep_dw_ge`'s price
    hypotheses — can only decrease it.  This is the one place where the schedule
    tower needs an argument the flat tower did not. -/
lemma shapeStep_dw_ge {L lam w L' lam' w' d c : ℝ}
    (hlam : lam = Real.log L) (hw : w = Real.log (c + lam))
    (hs3 : 3 ≤ c + lam) (hfloor : 100 * (c + lam) ≤ L)
    (hdlo : c + lam - 1 / 500 ≤ d)
    (hL' : L' = L + d) (hlam' : lam' = Real.log L') (hw' : w' = Real.log (c + lam')) :
    (20 / 21) / L ≤ w' - w := by
  have hLpos : (0 : ℝ) < L := by linarith
  obtain ⟨d0, hd0d, hd0hi, hd0lo⟩ :
      ∃ d0 : ℝ, d0 ≤ d ∧ d0 ≤ c + lam ∧ c + lam - 1 / 500 ≤ d0 :=
    ⟨min d (c + lam), min_le_left _ _, min_le_right _ _, le_min hdlo (by linarith)⟩
  have hbase := flatStep_dw_ge (L := L) (lam := lam) (w := w)
    (L' := L + d0) (lam' := Real.log (L + d0)) (w' := Real.log (c + Real.log (L + d0)))
    (d := d0) (c := c) hlam hw hs3 hfloor hd0lo hd0hi rfl rfl rfl
  have hL0pos : (0 : ℝ) < L + d0 := by linarith
  have hL'pos : (0 : ℝ) < L' := by rw [hL']; linarith
  have hlamge : lam ≤ Real.log (L + d0) := by
    rw [hlam]; exact Real.log_le_log hLpos (by linarith)
  have hmono1 : Real.log (L + d0) ≤ lam' := by
    rw [hlam', hL']; exact Real.log_le_log hL0pos (by linarith)
  have hmono2 : Real.log (c + Real.log (L + d0)) ≤ w' := by
    rw [hw']; exact Real.log_le_log (by linarith) (by linarith)
  linarith

/-! ### Section 5 — the per-step law along the schedule tower -/

lemma towerStepS_dw_ge {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC Ab + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (j : ℕ) :
    (20 / 21) / towerLS φ B j ≤ towerWS Ab φ B (j + 1) - towerWS Ab φ B j := by
  have hinv := towerShape_inv hAb hφ hB hfl j
  exact shapeStep_dw_ge (L := towerLS φ B j) (lam := towerLamS φ B j)
    (w := towerWS Ab φ B j) (L' := towerLS φ B (j + 1)) (lam' := towerLamS φ B (j + 1))
    (w' := towerWS Ab φ B (j + 1)) (d := Real.log ((towerMulS φ B j : ℕ) : ℝ))
    (c := flatC Ab) rfl rfl (shapeLevel_s_ge_three hAb hφ hB hinv) hinv
    (shapeStep_logMul_ge hAb hφ hB hinv) (towerLS_succ hAb hφ hB j) rfl rfl

/-! ### Section 6 — THE TELESCOPE at the budget constant -/

lemma towerDropSumShape_eq_sum (φ : ℕ → ℝ) (B J : ℕ) :
    towerDropSumShape φ B J = ∑ j ∈ Finset.range J, 1 / (2 * φ j * towerLS φ B j) := rfl

/-- **THE MASTER LAW for a schedule, upper half** (the width-necessity
    direction).  `S_J ≤ (21/20)·(1/(2·A_b))·(w_J − w_0)`: the schedule's own
    decrement is charged against the BUDGET constant's potential.  Two losses
    compose: `1/(2·φ_j·L_j) ≤ 1/(2·A_b·L_j)` (the schedule spends less per
    level than the budget allows) and the flat `21/20`. -/
theorem towerShape_dropSum_le {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC Ab + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (J : ℕ) :
    towerDropSumShape φ B J
      ≤ (21 / 20) * ((1 / (2 * Ab)) * (towerWS Ab φ B J - towerWS Ab φ B 0)) := by
  have hAbpos : (0 : ℝ) < Ab := by linarith
  have hkey : ∀ j ∈ Finset.range J,
      1 / (2 * φ j * towerLS φ B j)
        ≤ (21 / 20) * ((1 / (2 * Ab)) * (towerWS Ab φ B (j + 1) - towerWS Ab φ B j)) := by
    intro j _
    have hstep := towerStepS_dw_ge hAb hφ hB hfl j
    have hLpos : 0 < towerLS φ B j := towerLS_pos hAb hφ hB j
    have hp : Ab ≤ φ j := hφ j
    have he : 1 / (2 * Ab * towerLS φ B j)
        = (21 / 20) * ((1 / (2 * Ab)) * ((20 / 21) / towerLS φ B j)) := by
      field_simp
    calc 1 / (2 * φ j * towerLS φ B j) ≤ 1 / (2 * Ab * towerLS φ B j) :=
          one_div_le_one_div_of_le (by positivity) (by nlinarith)
      _ = (21 / 20) * ((1 / (2 * Ab)) * ((20 / 21) / towerLS φ B j)) := he
      _ ≤ (21 / 20) * ((1 / (2 * Ab)) * (towerWS Ab φ B (j + 1) - towerWS Ab φ B j)) := by
          refine mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hstep (by positivity)) ?_
          norm_num
  calc towerDropSumShape φ B J
      = ∑ j ∈ Finset.range J, 1 / (2 * φ j * towerLS φ B j) :=
        towerDropSumShape_eq_sum φ B J
    _ ≤ ∑ j ∈ Finset.range J,
          (21 / 20) * ((1 / (2 * Ab)) * (towerWS Ab φ B (j + 1) - towerWS Ab φ B j)) :=
        Finset.sum_le_sum hkey
    _ = (21 / 20) * ((1 / (2 * Ab)) * (towerWS Ab φ B J - towerWS Ab φ B 0)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub (towerWS Ab φ B) J]

/-! ### Section 7 — THE SHAPE-FREE TOLL -/

/-- **THE SHAPE-FREE TOLL.**  Let `φ` be ANY threshold schedule above the budget
    floor `A_b ≥ 1`, and let the schedule tower's telescoped decrement cross the
    entropy budget at some length `J`: `log 2 < S_J`.  Then

        `(c_b + λ_0)·4^{(20/21)·A_b} ≤ c_b + λ_J`,   `c_b = log (2·A_b)`.

    No shape of threshold evades the toll: the price is fixed by the schedule's
    own budget floor, not by its shape.  With `towerShape_flat_le` (where the
    constant schedule pays at most `(21/20)·4^{A_b}`) this makes the flat tower
    extremal to within `4^{A_b/21}·(21/20)` in the width multiplier. -/
theorem towerShape_width_ge {Ab : ℝ} (hAb : 1 ≤ Ab) {φ : ℕ → ℝ} (hφ : ∀ j, Ab ≤ φ j)
    {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC Ab + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) {J : ℕ}
    (hJcon : Real.log 2 < towerDropSumShape φ B J) :
    (flatC Ab + towerLamS φ B 0) * (4 : ℝ) ^ ((20 / 21 : ℝ) * Ab)
      ≤ flatC Ab + towerLamS φ B J := by
  have hAbpos : (0 : ℝ) < Ab := by linarith
  have hupp := towerShape_dropSum_le hAb hφ hB hfl J
  have hgap : (40 / 21) * Ab * Real.log 2 < towerWS Ab φ B J - towerWS Ab φ B 0 := by
    have h : Real.log 2
        < (21 / 20) * ((1 / (2 * Ab)) * (towerWS Ab φ B J - towerWS Ab φ B 0)) := by
      linarith
    rw [show (21 / 20 : ℝ) * ((1 / (2 * Ab)) * (towerWS Ab φ B J - towerWS Ab φ B 0))
      = 21 * (towerWS Ab φ B J - towerWS Ab φ B 0) / (40 * Ab) by field_simp; ring] at h
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 40 * Ab)] at h
    linarith
  have hinv0 := towerShape_inv hAb hφ hB hfl 0
  have hs0 : 3 ≤ flatC Ab + towerLamS φ B 0 := shapeLevel_s_ge_three hAb hφ hB hinv0
  have hinvJ := towerShape_inv hAb hφ hB hfl J
  have hsJ : 3 ≤ flatC Ab + towerLamS φ B J := shapeLevel_s_ge_three hAb hφ hB hinvJ
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ ((20 / 21 : ℝ) * Ab) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlogLHS : Real.log ((flatC Ab + towerLamS φ B 0) * (4 : ℝ) ^ ((20 / 21 : ℝ) * Ab))
      = towerWS Ab φ B 0 + ((20 / 21 : ℝ) * Ab) * Real.log 4 := by
    rw [Real.log_mul (by linarith) (ne_of_gt h4pos), Real.log_rpow (by norm_num), towerWS]
  have hlt : Real.log ((flatC Ab + towerLamS φ B 0) * (4 : ℝ) ^ ((20 / 21 : ℝ) * Ab))
      < Real.log (flatC Ab + towerLamS φ B J) := by
    rw [hlogLHS, flat_log_four]
    have hWJ : towerWS Ab φ B J = Real.log (flatC Ab + towerLamS φ B J) := rfl
    rw [← hWJ]
    linarith
  exact le_of_lt ((Real.log_lt_log_iff (by positivity) (by linarith)).mp hlt)

/-! ### Section 8 — the extremality tie: the CONSTANT schedule is the flat tower -/

/-- The constant schedule `φ ≡ A` reproduces `chowlaTowerFlat A 1 B` exactly. -/
lemma chowlaTowerShape_const (A : ℝ) (B : ℕ) (j : ℕ) :
    chowlaTowerShape (fun _ => A) B j = chowlaTowerFlat A 1 B j := by
  induction j with
  | zero => rw [chowlaTowerShape_zero, chowlaTowerFlat_zero, one_mul]
  | succ n ih => rw [chowlaTowerShape_succ_raw, chowlaTowerFlat_succ, ih]

lemma towerLS_const (A : ℝ) (B j : ℕ) : towerLS (fun _ => A) B j = towerLF A B j := by
  rw [towerLS, towerLF, chowlaTowerShape_const]

lemma towerLamS_const (A : ℝ) (B j : ℕ) : towerLamS (fun _ => A) B j = towerLamF A B j := by
  rw [towerLamS, towerLamF, towerLS_const]

lemma towerWS_const (A : ℝ) (B j : ℕ) : towerWS A (fun _ => A) B j = towerWF A B j := by
  rw [towerWS, towerWF, towerLamS_const]

lemma towerDropSumShape_const (A : ℝ) (B J : ℕ) :
    towerDropSumShape (fun _ => A) B J = towerDropSumFlat A 1 B J := by
  rw [towerDropSumShape_eq_sum, towerDropSumFlat_eq_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [towerLS_const]

/-- **THE EXTREMALITY TIE.**  The constant schedule `φ ≡ A` is the flat tower, so
    `towerFlat_width_le` reads off as a statement about schedules: at the minimal
    crossing length the CONSTANT schedule's width multiplier does not exceed
    `(21/20)·4^{A}`.

    Paired with `towerShape_width_ge` at `A_b = A` this is the extremality
    statement in full: EVERY schedule with budget floor `A` pays at least
    `4^{(20/21)·A}` in doubly-logarithmic width, and the flat schedule pays at
    most `(21/20)·4^{A}`.  The two brackets differ by the factor
    `4^{A/21}·(21/20)` — the exponent base `4` is determined, the exponent to
    within `4.8%`.  No choice of shape buys a smaller base. -/
theorem towerShape_flat_le {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) :
    flatC A + towerLamS (fun _ => A) B (towerFlatJmin A 1 B)
      ≤ (21 / 20) * ((4 : ℝ) ^ A * (flatC A + towerLamS (fun _ => A) B 0)) := by
  rw [towerLamS_const, towerLamS_const]
  exact towerFlat_width_le hA hB hfl

end Salt.Entropy.Chowla
