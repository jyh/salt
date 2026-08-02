/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# THE MASTER LAW of the FLAT-THRESHOLD tower

The landed tower (`chowlaTower`, `Regime.lean`) charges the mutual-information
threshold `κ = H/(log H · logloglog H)`, whose `logloglog H` denominator is what
puts the budget wall at HEIGHT 3.  The flat design (KAPPA-SCOPE, council v3 item
C1) replaces the third log by a design CONSTANT `A ≥ 1`:

    κ = H/(A · log H),   per-level drop 1/(2·A·log H_j),
    multiplier k_j ≥ 4·ε²·log 4·A·log H_j   (the flat `hkey`, `ε ≤ 1/2`),

so this file's tower steps by `H_{j+1} = H_j·⌊2·A·log H_j⌋₊` — the landed
`C₀ = 2` shape with the flat step — and its telescoped decrement is
`towerDropSumFlat`.  Everything here is ADDITIVE: no landed declaration is
touched, and the flat tower is a new definition beside `chowlaTower`.

## The potential and the law

Write `L_j = log H_j`, `λ_j = log L_j`, `c = log (2A)` (`flatC`) and

    w_j = log (c + λ_j)      (`towerWF`, the telescoping potential).

Because `ΔL_j = log⌊2 A L_j⌋₊ = c + λ_j − O(1/L_j)` (EXACTLY, by the two floor
bounds), one has `Δλ_j ≈ (c + λ_j)/L_j` and hence `Δw_j ≈ 1/L_j`, i.e. the
summand `1/(2 A L_j)` IS `Δw_j/(2A)`.  Summing:

* `towerDropSumFlat_ge_log_ratio` — `(1/(2A))·(w_J − w₀) ≤ S_J`, with NO loss
  (both floor prices point the same way in this direction);
* `towerDropSumFlat_le_log_ratio_mul` — `S_J ≤ (21/20)·(1/(2A))·(w_J − w₀)`,
  the `1/20` paying two second-order factors (`L' ≤ (101/100)L`,
  `c + λ' ≤ (c+λ) + 1/100`) and the floor price `1/500`.

Both directions are then read off:

* **width NECESSITY** (`towerFlat_width_ge`): the crossing `log 2 < S_J`
  (the regime field `hJcon`) forces `(λ_J + c) ≥ 4^{(20/21)·A}·(λ₀ + c)` —
  this is the master law `(λ₊+c)/(λ₋+c) ≥ 4^A` at the honest exponent;
* **width SUFFICIENCY** (`towerFlat_crossing_exists`, `towerFlatJmin_spec`):
  the crossing IS reached, at the NAMED level `J = ⌈exp (2·(λ₀+c)·4^A)⌉₊`;
* **no overshoot** (`towerFlat_width_le`): at the minimal crossing length
  `λ_J + c ≤ (21/20)·4^A·(λ₀ + c)` — the analogue of `tower_loglog_le`,
  bracketing the true width in `[4^{(20/21)A}, (21/20)·4^A]`.

## The floor

The base hypothesis is `4·10⁶ ≤ B` (the house regime floor, for `log B ≥ 15`)
together with the FLAT FLOOR

    `100·(c + λ₀) ≤ L₀`,  i.e.  `100·(log (2A) + loglog B) ≤ log B`,

which is what makes the second-order factors `1/100`-small.  It PROPAGATES up
the tower (`towerFlat_inv`) because `x ↦ x − 100·(c + log x)` is increasing past
`x = 100`.  At the flat design's own working point (`A ≈ 2·10³⁰`, so `c ≈ 70`)
the floor asks only `log B ≳ 8·10³`, astronomically below the design's own
height-1 floor `log B ≥ 2.2·10³¹` (KAPPA-SCOPE p7).
-/
import Salt.Entropy.Chowla.TowerExport

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section 1 — the flat tower, its decrement, and the glyphs -/

/-- **The flat tower.**  `H₁ = a·H₋` (index `0`), `H_{j+1} = H_j·⌊2·A·log H_j⌋₊`.
    The landed `chowlaTower`'s shape with the `logloglog H_j` factor replaced by
    the design constant `A`; the multiplier clears the flat `hkey` demand
    `k_j ≥ 4ε²·log 4·A·log H_j` for every `ε ≤ 1/2` (as `4ε²·log 4 ≤ log 4 < 2`). -/
noncomputable def chowlaTowerFlat (A : ℝ) (a Hlo : ℕ) : ℕ → ℕ
  | 0 => a * Hlo
  | (j + 1) => chowlaTowerFlat A a Hlo j *
      ⌊2 * A * Real.log (chowlaTowerFlat A a Hlo j : ℝ)⌋₊

/-- The flat telescoped per-step decrement `Σ_{j<J} 1/(2·A·log H_j)` — the flat
    threshold `κ = H/(A·log H)`'s own drop. -/
noncomputable def towerDropSumFlat (A : ℝ) (a Hlo J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, 1 / (2 * A * Real.log (chowlaTowerFlat A a Hlo j : ℝ))

lemma chowlaTowerFlat_zero (A : ℝ) (a Hlo : ℕ) : chowlaTowerFlat A a Hlo 0 = a * Hlo := rfl

lemma chowlaTowerFlat_succ (A : ℝ) (a Hlo j : ℕ) :
    chowlaTowerFlat A a Hlo (j + 1)
      = chowlaTowerFlat A a Hlo j *
        ⌊2 * A * Real.log (chowlaTowerFlat A a Hlo j : ℝ)⌋₊ := rfl

/-- `c = log (2A)` — the additive shift of the flat potential. -/
noncomputable def flatC (A : ℝ) : ℝ := Real.log (2 * A)

/-- `L_j = log H_j`. -/
noncomputable def towerLF (A : ℝ) (B j : ℕ) : ℝ := Real.log (chowlaTowerFlat A 1 B j : ℝ)

/-- `λ_j = loglog H_j`. -/
noncomputable def towerLamF (A : ℝ) (B j : ℕ) : ℝ := Real.log (towerLF A B j)

/-- `w_j = log (c + λ_j)` — the telescoping potential of the flat tower. -/
noncomputable def towerWF (A : ℝ) (B j : ℕ) : ℝ := Real.log (flatC A + towerLamF A B j)

/-- The flat tower multiplier `⌊2·A·L_j⌋₊`. -/
noncomputable def towerMulF (A : ℝ) (B j : ℕ) : ℕ := ⌊2 * A * towerLF A B j⌋₊

lemma towerLF_zero (A : ℝ) (B : ℕ) : towerLF A B 0 = Real.log (B : ℝ) := by
  rw [towerLF, chowlaTowerFlat_zero, one_mul]

lemma towerLamF_zero (A : ℝ) (B : ℕ) : towerLamF A B 0 = Real.log (Real.log (B : ℝ)) := by
  rw [towerLamF, towerLF_zero]

/-! ### Section 2 — the floor furniture -/

/-- `log 4 = 2·log 2`. -/
lemma flat_log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; push_cast; ring

lemma flatC_ge_log_two {A : ℝ} (hA : 1 ≤ A) : Real.log 2 ≤ flatC A := by
  rw [flatC]
  exact Real.log_le_log (by norm_num) (by linarith)

lemma flatC_pos {A : ℝ} (hA : 1 ≤ A) : 0 < flatC A :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) (flatC_ge_log_two hA)

/-- The flat multiplier is `≥ 2` above the regime floor (with `A ≥ 1`): strict
    growth of the flat tower. -/
lemma flatMul_ge_two {A : ℝ} (hA : 1 ≤ A) {H : ℕ} (hH : 4000000 ≤ H) :
    2 ≤ ⌊2 * A * Real.log (H : ℝ)⌋₊ := by
  have hlog := (tower_log_bounds hH).1
  have h2 : (2 : ℝ) ≤ 2 * A * Real.log (H : ℝ) := by nlinarith
  exact Nat.le_floor (by exact_mod_cast h2)

/-- **THE FLAT `hkey`.**  The flat multiplier clears the per-step demand
    `(ε²·log 4)/m ≤ 1/(4·A·L)` for every `ε ≤ 1/2`, `A ≥ 1`, `L ≥ 15` — the flat
    twin of `tower_step_of`'s multiplier arithmetic (`Tower.lean`), i.e. the
    statement that the flat tower's `⌊2·A·L⌋₊` funds the flat threshold's drop
    `1/(2·A·L)`.  (Stated over abstract reals with `m > 2AL − 1`, which is what
    `Nat.sub_one_lt_floor` supplies at the tower.) -/
lemma flat_hkey {eps A L m : ℝ} (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (hA : 1 ≤ A)
    (hL : 15 ≤ L) (hm : 2 * A * L - 1 < m) :
    eps ^ 2 * Real.log 4 / m ≤ 1 / (4 * A * L) := by
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := flat_log_four
  have heps2 : eps ^ 2 ≤ 1 / 4 := by nlinarith
  have hAL : 15 ≤ A * L := by nlinarith
  have hmpos : (0 : ℝ) < m := by nlinarith
  rw [div_le_div_iff₀ hmpos (by nlinarith : (0 : ℝ) < 4 * A * L)]
  rw [h4]
  nlinarith [mul_le_mul_of_nonneg_right heps2 hl2pos.le, hAL, hmpos]

lemma chowlaTowerFlat_base_ge {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    B ≤ chowlaTowerFlat A 1 B j := by
  induction j with
  | zero => change B ≤ 1 * B; omega
  | succ n ih =>
    have hfloor : 4000000 ≤ chowlaTowerFlat A 1 B n := le_trans hB ih
    have hmult := flatMul_ge_two hA hfloor
    rw [chowlaTowerFlat_succ]
    exact le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

lemma chowlaTowerFlat_base_floor {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    4000000 ≤ chowlaTowerFlat A 1 B j :=
  le_trans hB (chowlaTowerFlat_base_ge hA hB j)

lemma towerLF_ge_fifteen {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    15 ≤ towerLF A B j := by
  rw [towerLF]; exact (tower_log_bounds (chowlaTowerFlat_base_floor hA hB j)).1

lemma towerLF_pos {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    0 < towerLF A B j := by linarith [towerLF_ge_fifteen hA hB j]

lemma towerLamF_ge_two {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    2 ≤ towerLamF A B j := by
  have hL := towerLF_ge_fifteen hA hB j
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hexp2 : Real.exp 2 ≤ 15 := by nlinarith [Real.exp_pos 1]
  rw [towerLamF, Real.le_log_iff_exp_le (by linarith)]
  linarith

/-- `log (2·A·L) = c + log L`. -/
lemma flatLog_prod {A L : ℝ} (hA : 1 ≤ A) (hL : 0 < L) :
    Real.log (2 * A * L) = flatC A + Real.log L := by
  rw [flatC, ← Real.log_mul (by positivity) (ne_of_gt hL)]

lemma towerMulF_le {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    ((towerMulF A B j : ℕ) : ℝ) ≤ 2 * A * towerLF A B j := by
  refine Nat.floor_le ?_
  have hL := towerLF_ge_fifteen hA hB j
  nlinarith

lemma towerMulF_gt {A : ℝ} (B j : ℕ) :
    2 * A * towerLF A B j - 1 < ((towerMulF A B j : ℕ) : ℝ) :=
  Nat.sub_one_lt_floor _

lemma towerMulF_ge_two {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    2 ≤ towerMulF A B j := by
  rw [towerMulF, towerLF]
  exact flatMul_ge_two hA (chowlaTowerFlat_base_floor hA hB j)

/-- The flat tower's `succ` step in the glyph `L`. -/
lemma towerLF_succ {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    towerLF A B (j + 1) = towerLF A B j + Real.log ((towerMulF A B j : ℕ) : ℝ) := by
  have hm2 : 2 ≤ towerMulF A B j := towerMulF_ge_two hA hB j
  have hfloor := chowlaTowerFlat_base_floor hA hB j
  have hmul_eq : ⌊2 * A * Real.log ((chowlaTowerFlat A 1 B j : ℕ) : ℝ)⌋₊
      = towerMulF A B j := rfl
  have hH0 : ((chowlaTowerFlat A 1 B j : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < chowlaTowerFlat A 1 B j := by omega
    positivity
  have hm0 : ((towerMulF A B j : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < towerMulF A B j := by omega
    positivity
  rw [towerLF, towerLF, chowlaTowerFlat_succ, hmul_eq, Nat.cast_mul, Real.log_mul hH0 hm0]

/-! ### Section 3 — the flat floor invariant `100·(c + λ) ≤ L` -/

/-- Under the flat floor at a level, the potential's argument clears `3`. -/
lemma flatLevel_s_ge_three {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) {j : ℕ}
    (hinv : 100 * (flatC A + towerLamF A B j) ≤ towerLF A B j) :
    3 ≤ flatC A + towerLamF A B j := by
  have hlam2 : 2 ≤ towerLamF A B j := towerLamF_ge_two hA hB j
  have hc : Real.log 2 ≤ flatC A := flatC_ge_log_two hA
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL50 : 50 ≤ towerLF A B j := by linarith
  have hlam3 : 3 ≤ towerLamF A B j := by
    rw [towerLamF, Real.le_log_iff_exp_le (by linarith)]
    linarith [exp_three_le_fifty]
  linarith

/-- **The floor price, upper half.**  `log ⌊2AL⌋₊ ≤ c + λ`. -/
lemma flatStep_logMul_le {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    Real.log ((towerMulF A B j : ℕ) : ℝ) ≤ flatC A + towerLamF A B j := by
  have hLpos : 0 < towerLF A B j := towerLF_pos hA hB j
  have hm2 : 2 ≤ towerMulF A B j := towerMulF_ge_two hA hB j
  have hmpos : (0 : ℝ) < ((towerMulF A B j : ℕ) : ℝ) := by
    have h : (0 : ℕ) < towerMulF A B j := by omega
    exact_mod_cast h
  have h := Real.log_le_log hmpos (towerMulF_le hA hB j)
  rwa [flatLog_prod hA hLpos, ← towerLamF] at h

/-- **The floor price, lower half.**  `c + λ − 1/500 ≤ log ⌊2AL⌋₊` (the floor
    loses at most `1/m ≤ 1/599` in the log, since the flat floor forces
    `2AL ≥ 600`). -/
lemma flatStep_logMul_ge {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B) {j : ℕ}
    (hinv : 100 * (flatC A + towerLamF A B j) ≤ towerLF A B j) :
    flatC A + towerLamF A B j - 1 / 500 ≤ Real.log ((towerMulF A B j : ℕ) : ℝ) := by
  have hLpos : 0 < towerLF A B j := towerLF_pos hA hB j
  have hs3 := flatLevel_s_ge_three hA hB hinv
  have hL300 : 300 ≤ towerLF A B j := by linarith
  have hX : 600 ≤ 2 * A * towerLF A B j := by nlinarith
  have hgt := towerMulF_gt (A := A) B j
  have hm599 : (599 : ℝ) ≤ ((towerMulF A B j : ℕ) : ℝ) := by linarith
  have hmpos : (0 : ℝ) < ((towerMulF A B j : ℕ) : ℝ) := by linarith
  have h := log_sub_log_le (a := 2 * A * towerLF A B j)
    (b := ((towerMulF A B j : ℕ) : ℝ)) (by linarith) hmpos
  have hfrac : (2 * A * towerLF A B j - ((towerMulF A B j : ℕ) : ℝ))
      / ((towerMulF A B j : ℕ) : ℝ) ≤ 1 / 500 := by
    rw [div_le_div_iff₀ hmpos (by norm_num)]
    linarith
  rw [flatLog_prod hA hLpos, ← towerLamF] at h
  linarith

/-- **THE FLAT FLOOR INVARIANT.**  `100·(c + λ_j) ≤ L_j` propagates up the
    tower from the base hypothesis: the step adds `d_j ≥ 1` to `L` while adding
    at most `d_j/L_j ≤ 1/100` to `λ`. -/
lemma towerFlat_inv {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (j : ℕ) :
    100 * (flatC A + towerLamF A B j) ≤ towerLF A B j := by
  induction j with
  | zero => rw [towerLF_zero, towerLamF_zero]; exact hfl
  | succ n ih =>
    have hs3 := flatLevel_s_ge_three hA hB ih
    have hLpos : 0 < towerLF A B n := towerLF_pos hA hB n
    have hdhi := flatStep_logMul_le hA hB n
    have hdlo := flatStep_logMul_ge hA hB ih
    have hsucc := towerLF_succ hA hB n
    have hL'pos : 0 < towerLF A B (n + 1) := towerLF_pos hA hB (n + 1)
    have hsub : towerLF A B (n + 1) - towerLF A B n
        = Real.log ((towerMulF A B n : ℕ) : ℝ) := by rw [hsucc]; ring
    have hstep : towerLamF A B (n + 1) - towerLamF A B n
        ≤ (towerLF A B (n + 1) - towerLF A B n) / towerLF A B n :=
      log_sub_log_le hL'pos hLpos
    rw [hsub] at hstep
    have h100 : Real.log ((towerMulF A B n : ℕ) : ℝ) / towerLF A B n ≤ 1 / 100 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]
      linarith
    rw [hsucc]
    linarith

/-! ### Section 4 — THE PER-STEP SANDWICH (abstract reals) -/

/-- **The flat per-step law, upper half** — `Δw ≤ 1/L`, with NO error term.

Two applications of `log x ≤ x − 1`, one per glyph level:
`w' − w ≤ (λ' − λ)/(c + λ) ≤ (d/L)/(c + λ) ≤ 1/L`, using only `d ≤ c + λ` (the
floor's upper half `m ≤ 2AL`). -/
lemma flatStep_dw_le {L lam w L' lam' w' d c : ℝ}
    (hLpos : 0 < L) (hlam : lam = Real.log L) (hw : w = Real.log (c + lam))
    (hs : 0 < c + lam) (hd0 : 0 ≤ d) (hdhi : d ≤ c + lam)
    (hL' : L' = L + d) (hlam' : lam' = Real.log L') (hw' : w' = Real.log (c + lam')) :
    w' - w ≤ 1 / L := by
  have hL'pos : 0 < L' := by rw [hL']; linarith
  have hLL' : L ≤ L' := by rw [hL']; linarith
  have hll : lam ≤ lam' := by rw [hlam, hlam']; exact Real.log_le_log hLpos hLL'
  have hs' : 0 < c + lam' := by linarith
  have hsubL : L' - L = d := by rw [hL']; ring
  have c1 : lam' - lam ≤ (L' - L) / L := by
    have h := log_sub_log_le hL'pos hLpos
    rw [← hlam, ← hlam'] at h
    exact h
  rw [hsubL] at c1
  have c2 : w' - w ≤ (lam' - lam) / (c + lam) := by
    have h := log_sub_log_le hs' hs
    rw [← hw, ← hw'] at h
    have he : c + lam' - (c + lam) = lam' - lam := by ring
    rwa [he] at h
  have c1' : (lam' - lam) * L ≤ d := (le_div_iff₀ hLpos).mp c1
  have c2' : (w' - w) * (c + lam) ≤ lam' - lam := (le_div_iff₀ hs).mp c2
  have hkey : ((w' - w) * L) * (c + lam) ≤ 1 * (c + lam) := by
    nlinarith [mul_le_mul_of_nonneg_right c2' hLpos.le]
  rw [le_div_iff₀ hLpos]
  exact le_of_mul_le_mul_right hkey hs

/-- **The flat per-step law, lower half** — `(20/21)/L ≤ Δw`.

Two applications of the dual `1 − 1/x ≤ log x`, then the two second-order
factors of the flat floor (`L' ≤ (101/100)·L` and `c + λ' ≤ (c + λ) + 1/100`)
against the floor price `d ≥ (c + λ) − 1/500`.  At `c + λ ≥ 3` the honest
constant is `0.986`; `20/21 = 0.952` is what the law states. -/
lemma flatStep_dw_ge {L lam w L' lam' w' d c : ℝ}
    (hlam : lam = Real.log L) (hw : w = Real.log (c + lam))
    (hs3 : 3 ≤ c + lam) (hfloor : 100 * (c + lam) ≤ L)
    (hdlo : c + lam - 1 / 500 ≤ d) (hdhi : d ≤ c + lam)
    (hL' : L' = L + d) (hlam' : lam' = Real.log L') (hw' : w' = Real.log (c + lam')) :
    (20 / 21) / L ≤ w' - w := by
  have hs : 0 < c + lam := by linarith
  have hLpos : 0 < L := by linarith
  have hd1 : (1 : ℝ) ≤ d := by linarith
  have hL'pos : 0 < L' := by rw [hL']; linarith
  have hLL' : L ≤ L' := by rw [hL']; linarith
  have hll : lam ≤ lam' := by rw [hlam, hlam']; exact Real.log_le_log hLpos hLL'
  have hs' : 0 < c + lam' := by linarith
  have hww' : w ≤ w' := by rw [hw, hw']; exact Real.log_le_log hs (by linarith)
  have hsubL : L' - L = d := by rw [hL']; ring
  -- the second-order factors
  have hd_up : lam' - lam ≤ (L' - L) / L := by
    have h := log_sub_log_le hL'pos hLpos
    rw [← hlam, ← hlam'] at h
    exact h
  rw [hsubL] at hd_up
  have hd100 : d / L ≤ 1 / 100 := by
    rw [div_le_div_iff₀ hLpos (by norm_num)]
    linarith
  have hlam'le : c + lam' ≤ (c + lam) + 1 / 100 := by linarith
  have hL'le : L' ≤ (101 / 100) * L := by rw [hL']; linarith
  -- the lower chain
  have c1 : (L' - L) / L' ≤ lam' - lam := by
    have h := le_log_sub_log hL'pos hLpos
    rw [← hlam, ← hlam'] at h
    exact h
  rw [hsubL] at c1
  have c2 : (lam' - lam) / (c + lam') ≤ w' - w := by
    have h := le_log_sub_log hs' hs
    rw [← hw, ← hw'] at h
    have he : c + lam' - (c + lam) = lam' - lam := by ring
    rwa [he] at h
  have c1' : d ≤ (lam' - lam) * L' := (div_le_iff₀ hL'pos).mp c1
  have c2' : lam' - lam ≤ (w' - w) * (c + lam') := (div_le_iff₀ hs').mp c2
  have hstep1 : d ≤ ((w' - w) * (c + lam')) * L' :=
    le_trans c1' (mul_le_mul_of_nonneg_right c2' hL'pos.le)
  have hwnn : (0 : ℝ) ≤ w' - w := by linarith
  have hstep2 : ((w' - w) * (c + lam')) * L'
      ≤ ((w' - w) * ((c + lam) + 1 / 100)) * ((101 / 100) * L) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hlam'le hwnn) hL'le hL'pos.le ?_
    have h : (0 : ℝ) ≤ (c + lam) + 1 / 100 := by linarith
    exact mul_nonneg hwnn h
  have heq : ((w' - w) * ((c + lam) + 1 / 100)) * ((101 / 100) * L)
      = ((w' - w) * L) * (((c + lam) + 1 / 100) * (101 / 100)) := by ring
  rw [heq] at hstep2
  have hfinal : (c + lam) - 1 / 500
      ≤ ((w' - w) * L) * (((c + lam) + 1 / 100) * (101 / 100)) := by linarith
  rw [div_le_iff₀ hLpos]
  by_contra hcon
  have hcon' : (w' - w) * L < 20 / 21 := not_le.mp hcon
  have hpos : (0 : ℝ) < ((c + lam) + 1 / 100) * (101 / 100) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right hcon' hpos]

/-! ### Section 5 — the sandwich along the flat tower -/

lemma towerStepF_dw_le {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (j : ℕ) :
    towerWF A B (j + 1) - towerWF A B j ≤ 1 / towerLF A B j := by
  have hinv := towerFlat_inv hA hB hfl j
  have hs3 := flatLevel_s_ge_three hA hB hinv
  have hdlo := flatStep_logMul_ge hA hB hinv
  exact flatStep_dw_le (L := towerLF A B j) (lam := towerLamF A B j) (w := towerWF A B j)
    (L' := towerLF A B (j + 1)) (lam' := towerLamF A B (j + 1)) (w' := towerWF A B (j + 1))
    (d := Real.log ((towerMulF A B j : ℕ) : ℝ)) (c := flatC A)
    (towerLF_pos hA hB j) rfl rfl (by linarith) (by linarith)
    (flatStep_logMul_le hA hB j) (towerLF_succ hA hB j) rfl rfl

lemma towerStepF_dw_ge {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (j : ℕ) :
    (20 / 21) / towerLF A B j ≤ towerWF A B (j + 1) - towerWF A B j := by
  have hinv := towerFlat_inv hA hB hfl j
  exact flatStep_dw_ge (L := towerLF A B j) (lam := towerLamF A B j) (w := towerWF A B j)
    (L' := towerLF A B (j + 1)) (lam' := towerLamF A B (j + 1)) (w' := towerWF A B (j + 1))
    (d := Real.log ((towerMulF A B j : ℕ) : ℝ)) (c := flatC A)
    rfl rfl (flatLevel_s_ge_three hA hB hinv) hinv (flatStep_logMul_ge hA hB hinv)
    (flatStep_logMul_le hA hB j) (towerLF_succ hA hB j) rfl rfl

/-! ### Section 6 — THE MASTER LAW (the two-sided crossing law) -/

lemma towerDropSumFlat_eq_sum (A : ℝ) (B J : ℕ) :
    towerDropSumFlat A 1 B J = ∑ j ∈ Finset.range J, 1 / (2 * A * towerLF A B j) := rfl

/-- **THE MASTER LAW, lower half** (the SUFFICIENCY direction).
    `(1/(2A))·(w_J − w₀) ≤ S_J`, exactly — no relative loss. -/
theorem towerDropSumFlat_ge_log_ratio {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (J : ℕ) :
    (1 / (2 * A)) * (towerWF A B J - towerWF A B 0) ≤ towerDropSumFlat A 1 B J := by
  have hApos : (0 : ℝ) < A := by linarith
  have hkey : ∀ j ∈ Finset.range J,
      (1 / (2 * A)) * (towerWF A B (j + 1) - towerWF A B j)
        ≤ 1 / (2 * A * towerLF A B j) := by
    intro j _
    have hstep := towerStepF_dw_le hA hB hfl j
    have hLpos : 0 < towerLF A B j := towerLF_pos hA hB j
    have he : (1 / (2 * A)) * (1 / towerLF A B j) = 1 / (2 * A * towerLF A B j) := by
      field_simp
    calc (1 / (2 * A)) * (towerWF A B (j + 1) - towerWF A B j)
        ≤ (1 / (2 * A)) * (1 / towerLF A B j) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 1 / (2 * A * towerLF A B j) := he
  calc (1 / (2 * A)) * (towerWF A B J - towerWF A B 0)
      = ∑ j ∈ Finset.range J, (1 / (2 * A)) * (towerWF A B (j + 1) - towerWF A B j) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (towerWF A B) J]
    _ ≤ ∑ j ∈ Finset.range J, 1 / (2 * A * towerLF A B j) := Finset.sum_le_sum hkey
    _ = towerDropSumFlat A 1 B J := (towerDropSumFlat_eq_sum A B J).symm

/-- **THE MASTER LAW, upper half** (the WIDTH-NECESSITY direction).
    `S_J ≤ (21/20)·(1/(2A))·(w_J − w₀)`. -/
theorem towerDropSumFlat_le_log_ratio_mul {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (J : ℕ) :
    towerDropSumFlat A 1 B J ≤ (21 / 20) * ((1 / (2 * A)) * (towerWF A B J - towerWF A B 0)) := by
  have hApos : (0 : ℝ) < A := by linarith
  have hkey : ∀ j ∈ Finset.range J,
      1 / (2 * A * towerLF A B j)
        ≤ (21 / 20) * ((1 / (2 * A)) * (towerWF A B (j + 1) - towerWF A B j)) := by
    intro j _
    have hstep := towerStepF_dw_ge hA hB hfl j
    have hLpos : 0 < towerLF A B j := towerLF_pos hA hB j
    have he : 1 / (2 * A * towerLF A B j)
        = (21 / 20) * ((1 / (2 * A)) * ((20 / 21) / towerLF A B j)) := by
      field_simp
    rw [he]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep (by positivity)) ?_
    norm_num
  calc towerDropSumFlat A 1 B J = ∑ j ∈ Finset.range J, 1 / (2 * A * towerLF A B j) :=
        towerDropSumFlat_eq_sum A B J
    _ ≤ ∑ j ∈ Finset.range J,
          (21 / 20) * ((1 / (2 * A)) * (towerWF A B (j + 1) - towerWF A B j)) :=
        Finset.sum_le_sum hkey
    _ = (21 / 20) * ((1 / (2 * A)) * (towerWF A B J - towerWF A B 0)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub (towerWF A B) J]

/-! ### Section 7 — THE CROSSING IS REACHED, at a NAMED level -/

/-- Each flat step adds at least `1` to `L`, so `L_j ≥ L₀ + j`. -/
lemma towerLF_ge_add {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) (j : ℕ) :
    towerLF A B 0 + (j : ℝ) ≤ towerLF A B j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    have hinv := towerFlat_inv hA hB hfl n
    have hs3 := flatLevel_s_ge_three hA hB hinv
    have hdlo := flatStep_logMul_ge hA hB hinv
    rw [towerLF_succ hA hB n]
    push_cast
    linarith

/-- **THE NAMED CROSSING LEVEL** `J⋆ = ⌈exp (2·(c + λ₀)·4^A)⌉₊`: at `J⋆` the flat
    tower's telescoped decrement has cleared `log 2`. -/
noncomputable def towerFlatJstar (A : ℝ) (B : ℕ) : ℕ :=
  ⌈Real.exp (2 * (flatC A + Real.log (Real.log (B : ℝ))) * (4 : ℝ) ^ A)⌉₊

/-- **THE hJcon DISCHARGE.**  The flat crossing is REACHED — and at a level the
    builder can name (`towerFlatJstar`).  This is what a flat `ChowlaRegime`
    would need for its `hJcon` field. -/
theorem towerFlat_crossing_at_Jstar {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) :
    Real.log 2 < towerDropSumFlat A 1 B (towerFlatJstar A B) := by
  have hApos : (0 : ℝ) < A := by linarith
  have hinv0 := towerFlat_inv hA hB hfl 0
  have hs0 : 3 ≤ flatC A + towerLamF A B 0 := flatLevel_s_ge_three hA hB hinv0
  have hs0' : 3 ≤ flatC A + Real.log (Real.log (B : ℝ)) := by rwa [towerLamF_zero] at hs0
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have h4one : (1 : ℝ) ≤ (4 : ℝ) ^ A := Real.one_le_rpow (by norm_num) (by linarith)
  set s0 : ℝ := flatC A + Real.log (Real.log (B : ℝ)) with hs0def
  set T : ℝ := 2 * s0 * (4 : ℝ) ^ A with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  set J : ℕ := towerFlatJstar A B with hJdef
  have hJceil : Real.exp T ≤ (J : ℝ) := by
    rw [hJdef, towerFlatJstar]
    exact Nat.le_ceil _
  have hLJ : Real.exp T ≤ towerLF A B J := by
    have h := towerLF_ge_add hA hB hfl J
    have h0 : 0 < towerLF A B 0 := towerLF_pos hA hB 0
    linarith
  have hlamJ : T ≤ towerLamF A B J := by
    rw [towerLamF, Real.le_log_iff_exp_le (by linarith [Real.exp_pos T])]
    exact hLJ
  -- the potential gap
  have hcnn : 0 ≤ flatC A := (flatC_pos hA).le
  have hlogT : Real.log T = Real.log 2 + Real.log s0 + A * Real.log 4 := by
    rw [hTdef, Real.log_mul (by positivity) (ne_of_gt h4pos),
      Real.log_mul (by norm_num) (by linarith), Real.log_rpow (by norm_num)]
  have hwJ : Real.log T ≤ towerWF A B J := by
    rw [towerWF]
    exact Real.log_le_log hTpos (by linarith)
  have hw0 : towerWF A B 0 = Real.log s0 := by rw [towerWF, towerLamF_zero]
  have hgap : Real.log 2 + A * Real.log 4 ≤ towerWF A B J - towerWF A B 0 := by
    rw [hw0]; linarith
  -- the master law's lower half
  have hlow := towerDropSumFlat_ge_log_ratio hA hB hfl J
  have hid : (1 / (2 * A)) * (Real.log 2 + A * Real.log 4)
      = Real.log 2 / (2 * A) + Real.log 2 := by
    rw [flat_log_four]; field_simp
  have hpos : 0 < Real.log 2 / (2 * A) := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  calc Real.log 2 < Real.log 2 / (2 * A) + Real.log 2 := by linarith
    _ = (1 / (2 * A)) * (Real.log 2 + A * Real.log 4) := hid.symm
    _ ≤ (1 / (2 * A)) * (towerWF A B J - towerWF A B 0) :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
    _ ≤ towerDropSumFlat A 1 B J := hlow

/-! ### Section 8 — the minimal flat tower length -/

/-- The minimal flat tower length: the least `J` whose telescoped decrement
    clears `log 2`. -/
noncomputable def towerFlatJmin (A : ℝ) (a B : ℕ) : ℕ :=
  sInf {J : ℕ | Real.log 2 < towerDropSumFlat A a B J}

/-- The crossing set is nonempty (the named level `towerFlatJstar` is in it). -/
theorem towerFlat_crossing_exists {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) :
    ∃ J : ℕ, Real.log 2 < towerDropSumFlat A 1 B J :=
  ⟨towerFlatJstar A B, towerFlat_crossing_at_Jstar hA hB hfl⟩

theorem towerFlatJmin_spec {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) :
    Real.log 2 < towerDropSumFlat A 1 B (towerFlatJmin A 1 B) :=
  Nat.sInf_mem (towerFlat_crossing_exists hA hB hfl)

theorem towerDropSumFlat_le_log_two_of_lt_Jmin {A : ℝ} {a B k : ℕ}
    (hk : k < towerFlatJmin A a B) : towerDropSumFlat A a B k ≤ Real.log 2 := by
  by_contra hcon
  exact absurd (Nat.sInf_le
      (show k ∈ {J : ℕ | Real.log 2 < towerDropSumFlat A a B J} from not_le.mp hcon))
    (not_le.mpr hk)

lemma towerFlatJmin_pos {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) :
    0 < towerFlatJmin A 1 B := by
  rcases Nat.eq_zero_or_pos (towerFlatJmin A 1 B) with h | h
  · exfalso
    have hs := towerFlatJmin_spec hA hB hfl
    rw [h] at hs
    have h0 : towerDropSumFlat A 1 B 0 = 0 := by simp [towerDropSumFlat]
    rw [h0] at hs
    linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  · exact h

/-! ### Section 9 — THE WIDTH EXPORTS (both directions) -/

/-- **THE WIDTH NECESSITY** — the master law as the flat design consumes it.
    ANY crossing level `J` (in particular a flat regime's `hJcon`) forces

        `(λ₊ + c) ≥ 4^{(20/21)·A}·(λ₋ + c)`,

    the honest form of KAPPA-SCOPE's `(λ₊+c)/(λ₋+c) ≥ 4^A`; the `20/21` is the
    upper master law's relative loss. -/
theorem towerFlat_width_ge {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) {J : ℕ}
    (hJcon : Real.log 2 < towerDropSumFlat A 1 B J) :
    (flatC A + towerLamF A B 0) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A)
      ≤ flatC A + towerLamF A B J := by
  have hApos : (0 : ℝ) < A := by linarith
  have hupp := towerDropSumFlat_le_log_ratio_mul hA hB hfl J
  have hgap : (40 / 21) * A * Real.log 2 < towerWF A B J - towerWF A B 0 := by
    have h : Real.log 2 < (21 / 20) * ((1 / (2 * A)) * (towerWF A B J - towerWF A B 0)) := by
      linarith
    rw [show (21 / 20 : ℝ) * ((1 / (2 * A)) * (towerWF A B J - towerWF A B 0))
      = 21 * (towerWF A B J - towerWF A B 0) / (40 * A) by field_simp; ring] at h
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 40 * A)] at h
    linarith
  -- exponentiate
  have hinv0 := towerFlat_inv hA hB hfl 0
  have hs0 : 3 ≤ flatC A + towerLamF A B 0 := flatLevel_s_ge_three hA hB hinv0
  have hinvJ := towerFlat_inv hA hB hfl J
  have hsJ : 3 ≤ flatC A + towerLamF A B J := flatLevel_s_ge_three hA hB hinvJ
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ ((20 / 21 : ℝ) * A) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlogLHS : Real.log ((flatC A + towerLamF A B 0) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A))
      = towerWF A B 0 + ((20 / 21 : ℝ) * A) * Real.log 4 := by
    rw [Real.log_mul (by linarith) (ne_of_gt h4pos), Real.log_rpow (by norm_num), towerWF]
  have hlt : Real.log ((flatC A + towerLamF A B 0) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A))
      < Real.log (flatC A + towerLamF A B J) := by
    rw [hlogLHS, flat_log_four]
    have hWJ : towerWF A B J = Real.log (flatC A + towerLamF A B J) := rfl
    rw [← hWJ]
    linarith
  exact le_of_lt ((Real.log_lt_log_iff (by positivity) (by linarith)).mp hlt)

/-- **THE NO-OVERSHOOT COMPANION** (the analogue of `tower_loglog_le`).  At the
    MINIMAL crossing length the flat tower's width does not exceed one further
    step's worth of the law:

        `(λ₊ + c) ≤ (21/20)·4^A·(λ₋ + c)`.

    With `towerFlat_width_ge` this brackets the flat width in
    `[4^{(20/21)A}, (21/20)·4^A]` — the continuum truth `4^A` sits inside. -/
theorem towerFlat_width_le {A : ℝ} (hA : 1 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ)) :
    flatC A + towerLamF A B (towerFlatJmin A 1 B)
      ≤ (21 / 20) * ((4 : ℝ) ^ A * (flatC A + towerLamF A B 0)) := by
  have hApos : (0 : ℝ) < A := by linarith
  obtain ⟨k, hk⟩ : ∃ k, towerFlatJmin A 1 B = k + 1 :=
    ⟨towerFlatJmin A 1 B - 1, by have := towerFlatJmin_pos hA hB hfl; omega⟩
  have hSk : towerDropSumFlat A 1 B k ≤ Real.log 2 :=
    towerDropSumFlat_le_log_two_of_lt_Jmin (by omega)
  have hlow := towerDropSumFlat_ge_log_ratio hA hB hfl k
  have hwk : towerWF A B k - towerWF A B 0 ≤ 2 * A * Real.log 2 := by
    have h : (1 / (2 * A)) * (towerWF A B k - towerWF A B 0) ≤ Real.log 2 := by linarith
    rw [show (1 / (2 * A) : ℝ) * (towerWF A B k - towerWF A B 0)
      = (towerWF A B k - towerWF A B 0) / (2 * A) by ring] at h
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  -- one more step, priced at `1/L_k ≤ 1/300 ≤ 1/21 ≤ log (21/20)`
  have hinvk := towerFlat_inv hA hB hfl k
  have hs3k := flatLevel_s_ge_three hA hB hinvk
  have hLk : 300 ≤ towerLF A B k := by linarith
  have hstep := towerStepF_dw_le hA hB hfl k
  have hlast : towerWF A B (k + 1) - towerWF A B k ≤ 1 / 300 := by
    refine le_trans hstep ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hlog2120 : (1 : ℝ) / 21 ≤ Real.log (21 / 20) := by
    have h := one_sub_inv_le_log (show (0 : ℝ) < 21 / 20 by norm_num)
    norm_num at h
    linarith
  have hfinal : towerWF A B (towerFlatJmin A 1 B) - towerWF A B 0
      ≤ Real.log (21 / 20) + A * Real.log 4 := by
    rw [hk, flat_log_four]
    linarith
  -- exponentiate
  have hinv0 := towerFlat_inv hA hB hfl 0
  have hs0 : 3 ≤ flatC A + towerLamF A B 0 := flatLevel_s_ge_three hA hB hinv0
  have hinvJ := towerFlat_inv hA hB hfl (towerFlatJmin A 1 B)
  have hsJ : 3 ≤ flatC A + towerLamF A B (towerFlatJmin A 1 B) :=
    flatLevel_s_ge_three hA hB hinvJ
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hlogRHS : Real.log ((21 / 20) * ((4 : ℝ) ^ A * (flatC A + towerLamF A B 0)))
      = Real.log (21 / 20) + A * Real.log 4 + towerWF A B 0 := by
    rw [Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (ne_of_gt h4pos) (by linarith), Real.log_rpow (by norm_num), towerWF]
    ring
  have hle : Real.log (flatC A + towerLamF A B (towerFlatJmin A 1 B))
      ≤ Real.log ((21 / 20) * ((4 : ℝ) ^ A * (flatC A + towerLamF A B 0))) := by
    rw [hlogRHS]
    have hWJ : towerWF A B (towerFlatJmin A 1 B)
        = Real.log (flatC A + towerLamF A B (towerFlatJmin A 1 B)) := rfl
    rw [← hWJ]
    linarith
  exact (Real.log_le_log_iff (by linarith) (by positivity)).mp hle

end Salt.Entropy.Chowla

