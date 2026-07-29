/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The `(ε, H₋)`-parametric regime builder, node PATCH-5

`RegimeInst.lean` / `Diverge.lean` supply the anti-vacuity witness
`chowlaRegime_exists` at the PINNED parameters `ε = 1/2`, `H₋ = 4·10⁶`.  The
tower-discharge `log_chowla_two_of_door` (`TowerDischarge.lean`) then carries
three OPAQUE-constant residuals that the fixed witness cannot clear:

1. `H₀ ≤ H` — the combined producer floor sits below the decrement level (needs
   `R.Hlo` driven up to the opaque `H₀`);
2. `ε ≤ cE/(32·log 4)` — Tao's "ε small enough" (needs `ε` driven down);
3. `hbudget1` (`≈ cD3 ≳ 2(C+1)` at `ε = 1/2`) — needs `ε` driven down.

This file builds a regime at ARBITRARY `ε ∈ (0, 1/2]` and `Hlo ≥ Hlo₀` for any
floor `Hlo₀`, so all three residuals discharge by choosing `ε` small and `Hlo`
large.  The two levers are COUPLED: `hcoprime` needs `Hlo ≥ 2/ε²` and
`hPNTwindow` needs `Hlo ≥ 4/ε⁴`, so a small `ε` forces a large `Hlo`; hence the
builder re-bases the tower at the enlarged `Hlo`.

## Section A — divergence of the tower decrement at any base `B ≥ 4·10⁶`

`dropSum_exceeds_log_two` (`Diverge.lean`) is proved PINNED at base `4·10⁶`
(the base case `log 4·10⁶ ≤ 64·log 2`, the accumulation constant `32`, and
`summand_lower`'s `1/128`/`j ≥ 30`).  It is re-parametrized ABOVE the pin by
tower base-monotonicity + an index shift: `chowlaTower 2 1 B j ≤
chowlaTower 2 1 4·10⁶ (j + j⋆)` whenever `B ≤ chowlaTower 2 1 4·10⁶ j⋆` (which
exists since the tower is unbounded), so `tower_log_upper` and
`not_summable_one_div_nat_loglog` (both base-free) transfer verbatim.
-/
import Salt.Entropy.Chowla.Diverge
import Salt.Entropy.Chowla.TowerDischarge

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section A — the barely-divergent decrement clears `log 2` at any base -/

/-- Non-summability transfers up an eventual pointwise bound `a ≤ b` on `[N, ∞)`
    (a re-statement of `Diverge`'s `private` twin). -/
private lemma param_not_summable_of_le {a b : ℕ → ℝ} (N : ℕ)
    (ha : ∀ n, N ≤ n → 0 ≤ a n) (hab : ∀ n, N ≤ n → a n ≤ b n)
    (hna : ¬ Summable a) : ¬ Summable b := by
  intro hb
  apply hna
  rw [← summable_nat_add_iff N] at hb ⊢
  exact hb.of_nonneg_of_le (fun n => ha (n + N) (Nat.le_add_left N n))
    (fun n => hab (n + N) (Nat.le_add_left N n))

/-- Every value of `chowlaTower 2 1 B` (base `B ≥ 4·10⁶`) is `≥ B`
    (base `1·B`; each step multiplies by `≥ 2`). -/
lemma chowlaTower_base_ge {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    B ≤ chowlaTower 2 1 B j := by
  induction j with
  | zero => change B ≤ 1 * B; omega
  | succ n ih =>
    have hfloor : 4000000 ≤ chowlaTower 2 1 B n := le_trans hB ih
    have hmult := tower_mult_ge_two (show (2 : ℕ) ≤ 2 from le_refl 2) hfloor
    rw [chowlaTower_succ]
    exact le_trans ih (Nat.le_mul_of_pos_right _ (by omega))

/-- Hence every value of `chowlaTower 2 1 B` is `≥ 4·10⁶`. -/
lemma chowlaTower_base_floor {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    4000000 ≤ chowlaTower 2 1 B j :=
  le_trans hB (chowlaTower_base_ge hB j)

/-- The tower step `H ↦ H·⌊2·log H·logloglog H⌋₊` is monotone on `[4·10⁶, ∞)`:
    both `log` and `logloglog` are increasing there, and the floor + product are
    monotone. -/
lemma towerStep_mono {x y : ℕ} (hx : 4000000 ≤ x) (hxy : x ≤ y) :
    x * ⌊(2 : ℝ) * Real.log x * Real.log (Real.log (Real.log x))⌋₊
      ≤ y * ⌊(2 : ℝ) * Real.log y * Real.log (Real.log (Real.log y))⌋₊ := by
  have hy : 4000000 ≤ y := le_trans hx hxy
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hxyR : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
  obtain ⟨hlx, hmx⟩ := tower_log_bounds hx
  obtain ⟨hly, _⟩ := tower_log_bounds hy
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hxR hxyR
  have hlxpos : (0 : ℝ) < Real.log x := by linarith
  have hloglog : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.log_le_log hlxpos hlog
  have hllxpos : (0 : ℝ) < Real.log (Real.log x) := by
    have h15 : Real.log 15 ≤ Real.log (Real.log x) := Real.log_le_log (by norm_num) hlx
    linarith [Real.log_pos (show (1 : ℝ) < 15 by norm_num)]
  have hlll : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log (Real.log y)) :=
    Real.log_le_log hllxpos hloglog
  have hmxnn : (0 : ℝ) ≤ Real.log (Real.log (Real.log x)) := by linarith
  have hprod : (2 : ℝ) * Real.log x * Real.log (Real.log (Real.log x))
      ≤ (2 : ℝ) * Real.log y * Real.log (Real.log (Real.log y)) := by
    have h2y : (0 : ℝ) ≤ 2 * Real.log y := by linarith
    have h1 : (2 : ℝ) * Real.log x ≤ 2 * Real.log y := by linarith
    exact mul_le_mul h1 hlll hmxnn h2y
  exact Nat.mul_le_mul hxy (Nat.floor_mono hprod)

/-- **Base-shift domination.**  A tower based at `B ≥ 4·10⁶` is dominated by the
    base-`4·10⁶` tower shifted by any `jstar` with `B ≤ H_{jstar}` — by induction
    on the level, using `towerStep_mono`. -/
lemma chowlaTower_base_shift {B jstar : ℕ} (hB : 4000000 ≤ B)
    (hdom : B ≤ chowlaTower 2 1 4000000 jstar) :
    ∀ j, chowlaTower 2 1 B j ≤ chowlaTower 2 1 4000000 (j + jstar) := by
  intro j
  induction j with
  | zero =>
    have hz : chowlaTower 2 1 B 0 = B := by change 1 * B = B; omega
    rw [hz, Nat.zero_add]; exact hdom
  | succ n ih =>
    have hfloorB : 4000000 ≤ chowlaTower 2 1 B n := chowlaTower_base_floor hB n
    rw [chowlaTower_succ, show n + 1 + jstar = (n + jstar) + 1 from by omega, chowlaTower_succ]
    simp only [Nat.cast_ofNat]
    exact towerStep_mono hfloorB ih

/-- `2^j ≤ chowlaTower 2 1 4·10⁶ j` (base `2^0 = 1 ≤ 4·10⁶`; each step `≥ ×2`). -/
lemma two_pow_le_tower (j : ℕ) : 2 ^ j ≤ chowlaTower 2 1 4000000 j := by
  induction j with
  | zero => simp only [pow_zero]; change 1 ≤ 1 * 4000000; omega
  | succ n ih =>
    have hfloor : 4000000 ≤ chowlaTower 2 1 4000000 n := chowlaTower_base_floor (le_refl _) n
    have hmult := tower_mult_ge_two (show (2 : ℕ) ≤ 2 from le_refl 2) hfloor
    rw [chowlaTower_succ, pow_succ]
    exact Nat.mul_le_mul ih hmult

/-- The base-`4·10⁶` tower is unbounded: it dominates `2^jstar` at `jstar = B`. -/
lemma exists_tower_ge (B : ℕ) : ∃ jstar, B ≤ chowlaTower 2 1 4000000 jstar :=
  ⟨B, le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (two_pow_le_tower B)⟩

/-- **The upper tower bound at base `B`.**  Composing the base-shift domination
    with `Diverge`'s `tower_log_upper`: `log H_j(B) ≤ 32·(j+j⋆+2)·log(j+j⋆+2)`. -/
lemma tower_log_upper_base {B jstar : ℕ} (hB : 4000000 ≤ B)
    (hdom : B ≤ chowlaTower 2 1 4000000 jstar) (j : ℕ) :
    Real.log (chowlaTower 2 1 B j : ℝ)
      ≤ 32 * (((j + jstar : ℕ) : ℝ) + 2) * Real.log (((j + jstar : ℕ) : ℝ) + 2) := by
  have hle : chowlaTower 2 1 B j ≤ chowlaTower 2 1 4000000 (j + jstar) :=
    chowlaTower_base_shift hB hdom j
  have hpos : (0 : ℝ) < (chowlaTower 2 1 B j : ℝ) := by
    have hfl := chowlaTower_base_floor hB j
    exact_mod_cast (show 0 < chowlaTower 2 1 B j by omega)
  have h1 : Real.log (chowlaTower 2 1 B j : ℝ)
      ≤ Real.log (chowlaTower 2 1 4000000 (j + jstar) : ℝ) :=
    Real.log_le_log hpos (by exact_mod_cast hle)
  exact le_trans h1 (tower_log_upper (j + jstar))

/-- **The generic per-summand comparison.**  For any `H ≥ 4·10⁶` and `n ≥ 30`
    with `log H ≤ 32·(n+2)·log(n+2)`, the decrement summand `1/(2·log H·
    logloglog H)` dominates `(1/128)/((n+2)·log(n+2)·loglog(n+2))`.  Factored out
    of `Diverge`'s `summand_lower` so the tower enters only through the bound. -/
lemma summand_lower_gen {H n : ℕ} (hH : 4000000 ≤ H) (hn : 30 ≤ n)
    (hUp : Real.log (H : ℝ) ≤ 32 * ((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) :
    (1 / 128 : ℝ) * (1 / (((n + 2 : ℕ) : ℝ) * Real.log ((n + 2 : ℕ) : ℝ)
        * Real.log (Real.log ((n + 2 : ℕ) : ℝ))))
      ≤ 1 / (2 * Real.log (H : ℝ) * Real.log (Real.log (Real.log (H : ℝ)))) := by
  have hPeq : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hPeq]
  set P : ℝ := (n : ℝ) + 2 with hPdef
  have hnR : (30 : ℝ) ≤ n := by exact_mod_cast hn
  have hP32 : (32 : ℝ) ≤ P := by rw [hPdef]; linarith
  have hPpos : (0 : ℝ) < P := by linarith
  have hp_pos : 0 < Real.log P := Real.log_pos (by linarith)
  set p : ℝ := Real.log P with hpdef
  have hp3 : (3 : ℝ) ≤ p := by
    rw [hpdef]
    have h32 : Real.log 32 ≤ Real.log P := Real.log_le_log (by norm_num) hP32
    have hlog32_ge3 : (3 : ℝ) ≤ Real.log 32 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast; linarith [Real.log_two_gt_d9]
    linarith
  have hq_pos : 0 < Real.log p := Real.log_pos (by linarith)
  set q : ℝ := Real.log p with hqdef
  obtain ⟨hL15, hM12⟩ := tower_log_bounds hH
  set L : ℝ := Real.log (H : ℝ) with hLdef
  set M : ℝ := Real.log (Real.log (Real.log (H : ℝ))) with hMdef
  have hLpos : 0 < L := by linarith [hL15]
  have hMpos : 0 < M := by linarith [hM12]
  have hlogL_pos : 0 < Real.log L := by
    have : Real.log 15 ≤ Real.log L := Real.log_le_log (by norm_num) hL15
    linarith [Real.log_pos (show (1 : ℝ) < 15 by norm_num)]
  have hUp' : L ≤ 32 * P * p := hUp
  have h32Pp_pos : (0 : ℝ) < 32 * P * p := mul_pos (mul_pos (by norm_num) hPpos) hp_pos
  have hlog32Pp : Real.log (32 * P * p) ≤ 3 * p := by
    rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hPpos)) (ne_of_gt hp_pos),
      Real.log_mul (by norm_num) (ne_of_gt hPpos), ← hpdef, ← hqdef]
    have hlog32_le_p : Real.log 32 ≤ p := by
      rw [hpdef]; exact Real.log_le_log (by norm_num) hP32
    have hq_le_p : q ≤ p := by rw [hqdef]; exact Real.log_le_self (le_of_lt hp_pos)
    linarith
  have hM_le : M ≤ 2 * q := by
    have hMeq : M = Real.log (Real.log L) := by rw [hMdef, hLdef]
    rw [hMeq]
    have h1 : Real.log (Real.log L) ≤ Real.log (Real.log (32 * P * p)) :=
      Real.log_le_log hlogL_pos (Real.log_le_log hLpos hUp')
    have hgt1 : (1 : ℝ) < 32 * P * p := by nlinarith [hP32, hp3, hPpos, hp_pos]
    have h2 : Real.log (Real.log (32 * P * p)) ≤ Real.log (3 * p) :=
      Real.log_le_log (Real.log_pos hgt1) hlog32Pp
    have h3 : Real.log (3 * p) = Real.log 3 + q := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hp_pos), ← hqdef]
    have hlog3_le_q : Real.log 3 ≤ q := by
      rw [hqdef]; exact Real.log_le_log (by norm_num) hp3
    calc Real.log (Real.log L) ≤ Real.log (Real.log (32 * P * p)) := h1
      _ ≤ Real.log (3 * p) := h2
      _ = Real.log 3 + q := h3
      _ ≤ 2 * q := by linarith
  have hkey : L * M ≤ 64 * (P * p * q) := by
    calc L * M ≤ (32 * P * p) * (2 * q) :=
          mul_le_mul hUp' hM_le (le_of_lt hMpos) (le_of_lt h32Pp_pos)
      _ = 64 * (P * p * q) := by ring
  have hRHSpos : (0 : ℝ) < 2 * L * M := mul_pos (mul_pos (by norm_num) hLpos) hMpos
  have hdenle : 2 * L * M ≤ 128 * (P * p * q) := by nlinarith [hkey]
  have hLHS_eq : (1 / 128 : ℝ) * (1 / (P * p * q)) = 1 / (128 * (P * p * q)) := by
    rw [mul_one_div, div_div]
  rw [hLHS_eq]
  exact one_div_le_one_div_of_le hRHSpos hdenle

/-- **The barely-divergent decrement clears `log 2` at any base `B ≥ 4·10⁶`.**
    The re-based twin of `dropSum_exceeds_log_two`: nonneg summands whose series
    diverges (via the shifted comparison to `not_summable_one_div_nat_loglog`),
    so the partial sums `towerDropSum 2 1 B` tend to `+∞` and cross `log 2`. -/
theorem dropSum_exceeds_log_two_base {B : ℕ} (hB : 4000000 ≤ B) :
    ∃ J : ℕ, Real.log 2 < towerDropSum 2 1 B J := by
  obtain ⟨jstar, hdom⟩ := exists_tower_ge B
  set W : ℕ → ℝ := fun m => 1 / ((m : ℝ) * Real.log m * Real.log (Real.log m)) with hW
  set s : ℕ → ℝ := fun j => 1 / (2 * Real.log (chowlaTower 2 1 B j : ℝ)
      * Real.log (Real.log (Real.log (chowlaTower 2 1 B j : ℝ)))) with hs
  have hsum_eq : ∀ J, towerDropSum 2 1 B J = ∑ j ∈ Finset.range J, s j := fun J => rfl
  have hs_nonneg : ∀ j, 0 ≤ s j := by
    intro j
    have hge : 4000000 ≤ chowlaTower 2 1 B j := chowlaTower_base_floor hB j
    obtain ⟨hL15, hM12⟩ := tower_log_bounds hge
    have hpos : (0 : ℝ) < 2 * Real.log (chowlaTower 2 1 B j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower 2 1 B j : ℝ))) :=
      mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
    exact one_div_nonneg.mpr (le_of_lt hpos)
  have hnW : ¬ Summable W := not_summable_one_div_nat_loglog
  have hshift : ¬ Summable (fun j => W (j + (jstar + 2))) :=
    fun h => hnW ((summable_nat_add_iff (jstar + 2)).mp h)
  have hna : ¬ Summable (fun j => (1 / 128 : ℝ) * W (j + (jstar + 2))) := by
    intro hsum
    apply hshift
    have h := hsum.mul_left 128
    exact (summable_congr (fun j => by ring)).mp h
  have hs_notsummable : ¬ Summable s := by
    refine param_not_summable_of_le 30 (a := fun j => (1 / 128 : ℝ) * W (j + (jstar + 2)))
      (fun j hj => ?_) (fun j hj => ?_) hna
    · have hlp : 1 < Real.log ((j + (jstar + 2) : ℕ) : ℝ) := by
        have hP : (32 : ℝ) ≤ ((j + (jstar + 2) : ℕ) : ℝ) := by
          have : (32 : ℕ) ≤ j + (jstar + 2) := by omega
          exact_mod_cast this
        rw [Real.lt_log_iff_exp_lt (by linarith)]
        linarith [Real.exp_one_lt_d9]
      have hd : (0 : ℝ) < ((j + (jstar + 2) : ℕ) : ℝ) * Real.log ((j + (jstar + 2) : ℕ) : ℝ)
          * Real.log (Real.log ((j + (jstar + 2) : ℕ) : ℝ)) := by
        have hn0 : (0 : ℝ) < ((j + (jstar + 2) : ℕ) : ℝ) := by positivity
        exact mul_pos (mul_pos hn0 (by linarith)) (Real.log_pos hlp)
      have hWnn : (0 : ℝ) ≤ W (j + (jstar + 2)) := by
        change (0 : ℝ) ≤ 1 / (((j + (jstar + 2) : ℕ) : ℝ) * Real.log ((j + (jstar + 2) : ℕ) : ℝ)
          * Real.log (Real.log ((j + (jstar + 2) : ℕ) : ℝ)))
        exact one_div_nonneg.mpr (le_of_lt hd)
      exact mul_nonneg (by norm_num) hWnn
    · have hn30 : 30 ≤ j + jstar := le_trans hj (Nat.le_add_right j jstar)
      have hup := tower_log_upper_base hB hdom j
      exact summand_lower_gen (H := chowlaTower 2 1 B j) (n := j + jstar)
        (chowlaTower_base_floor hB j) hn30 hup
  have htend : Filter.Tendsto (fun N => ∑ j ∈ Finset.range N, s j) Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hs_nonneg).mp hs_notsummable
  have htend' : Filter.Tendsto (towerDropSum 2 1 B) Filter.atTop Filter.atTop := by
    have hfe : towerDropSum 2 1 B = fun N => ∑ j ∈ Finset.range N, s j := funext hsum_eq
    rw [hfe]; exact htend
  obtain ⟨J, hJ⟩ := (htend'.eventually_gt_atTop (Real.log 2)).exists
  exact ⟨J, hJ⟩

/-! ### Section B — the general-`ε` outer scale (`regime_outer` re-parametrized) -/

/-- **The general-`ε` outer-scale construction.**  The `ε = 1/2`-pinned
    `regime_outer` re-parametrized to arbitrary `ε ∈ (0, 1/2]`.  Given any upper
    endpoint `Hhi ≥ 4·10⁶` and any `P`, the choice `ω = (Hhi+2)^N` with the
    ceiling exponent `N = ⌈RHS/log(Hhi+2)⌉₊ + 1` (`RHS` the `hωbig` right side)
    clears the window coupling, and `x = K·ω` with `K = 8·Hhi³ + 8·P² +
    ⌈48·(1+2/ε²)/ε⌉₊` funds `hheadroom`/`hheadroom'`/`hPHheadroom`/`hxbig`.  The
    degree-`N` defining equation `ω = (Hhi+2)^N` is cleared before the arithmetic
    branches. -/
lemma regime_outer_param (eps : ℚ) (heps : 0 < eps) (_heps1 : eps ≤ 1 / 2)
    (Hhi P : ℕ) (hHhi : 4000000 ≤ Hhi) :
    ∃ x ω : ℕ, 2 ≤ x ∧ 2 ≤ ω ∧ ω ≤ x ∧ Hhi ≤ x / ω ∧
      8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ ((x / ω : ℕ) : ℝ) ∧
      8 * (P : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ) ∧
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1
        ≤ Real.log (ω : ℝ) ∧
      (ω : ℝ) * (Hhi : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) := by
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have hHhiR : (4000000 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast hHhi
  have hHhipos : (0 : ℝ) < (Hhi : ℝ) := by linarith
  have hcube : Hhi ≤ Hhi ^ 3 := Nat.le_self_pow (by norm_num) Hhi
  have hcubeR : (Hhi : ℝ) ≤ (Hhi : ℝ) ^ 3 := by exact_mod_cast hcube
  set LG : ℝ := Real.log ((Hhi : ℝ) + 2) with hLGdef
  have hLGpos : (0 : ℝ) < LG := by
    rw [hLGdef]; exact Real.log_pos (by linarith)
  -- the ceiling exponent and its scale
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N =
      ⌈((16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1) / LG⌉₊
        + 1 := ⟨_, rfl⟩
  obtain ⟨Ce, hCedef⟩ : ∃ Ce : ℕ, Ce = ⌈48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)⌉₊ := ⟨_, rfl⟩
  obtain ⟨ω, hωdef⟩ : ∃ ω, ω = (Hhi + 2) ^ N := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = 8 * Hhi ^ 3 + 8 * P ^ 2 + Ce := ⟨_, rfl⟩
  have hωpos : 0 < ω := by rw [hωdef]; positivity
  have hNpos : 0 < N := by rw [hNdef]; omega
  have hω2 : 2 ≤ ω := by
    rw [hωdef]
    calc (2 : ℕ) ≤ Hhi + 2 := by omega
      _ ≤ (Hhi + 2) ^ N := Nat.le_self_pow (by omega) _
  -- the window coupling `hωbig`, via the ceiling
  have homega : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1
      ≤ Real.log (ω : ℝ) := by
    set RHS : ℝ :=
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1 with hRdef
    have hlogω : Real.log (ω : ℝ) = (N : ℝ) * LG := by
      have hcast : (ω : ℝ) = ((Hhi : ℝ) + 2) ^ N := by rw [hωdef]; push_cast; ring
      rw [hcast, Real.log_pow, ← hLGdef]
    have hNge : RHS / LG ≤ (N : ℝ) := by
      have hce := Nat.le_ceil (RHS / LG)
      have hNR : (N : ℝ) = (⌈RHS / LG⌉₊ : ℝ) + 1 := by rw [hNdef, hRdef]; push_cast; ring
      rw [hNR]; linarith
    have hkey : RHS ≤ (N : ℝ) * LG := by
      have h2 : RHS / LG * LG ≤ (N : ℝ) * LG :=
        mul_le_mul_of_nonneg_right hNge (le_of_lt hLGpos)
      rwa [div_mul_cancel₀ RHS (ne_of_gt hLGpos)] at h2
    rw [hlogω]; exact hkey
  -- the outer-scale headroom facts, using the VALUE of K, before clearing `^N`
  have hCe : 48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (Ce : ℝ) := by
    rw [hCedef]; exact Nat.le_ceil _
  have hKR : ((K : ℕ) : ℝ) = 8 * (Hhi : ℝ) ^ 3 + 8 * (P : ℝ) ^ 2 + (Ce : ℝ) := by
    rw [hKdef]; push_cast; ring
  have hHhiK : Hhi ≤ K := by
    rw [hKdef]; nlinarith [hcube, Nat.zero_le (P ^ 2), Nat.zero_le Ce]
  have hK1 : 1 ≤ K := le_trans (by omega) hHhiK
  -- clear the degree-`N` equation so `nlinarith`/`omega` see only opaque fvars
  clear hωdef hNdef
  refine ⟨K * ω, ω, ?_, hω2, ?_, ?_, ?_, ?_, homega, ?_⟩
  · exact le_trans hω2 (Nat.le_mul_of_pos_left ω (by omega))
  · exact Nat.le_mul_of_pos_left ω (by omega)
  · rw [Nat.mul_div_cancel K hωpos]; exact hHhiK
  · rw [Nat.mul_div_cancel K hωpos]
    have hLnn : 0 ≤ Real.log (Hhi : ℝ) := Real.log_nonneg (by linarith)
    have hL : Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) := Real.log_le_self (by linarith)
    have hsq : Real.log (Hhi : ℝ) * Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) * (Hhi : ℝ) :=
      mul_le_mul hL hL hLnn (by linarith)
    have hstep : 8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ 8 * (Hhi : ℝ) ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 8 * (Hhi : ℝ) by positivity)]
    rw [hKR]
    linarith [hstep, pow_nonneg (show (0 : ℝ) ≤ (Hhi : ℝ) from Nat.cast_nonneg Hhi) 3,
      sq_nonneg (P : ℝ), show (0 : ℝ) ≤ (Ce : ℝ) from Nat.cast_nonneg Ce]
  · have hωnn : (0 : ℝ) ≤ (ω : ℝ) := Nat.cast_nonneg _
    have hPK : 8 * (P : ℝ) ^ 2 ≤ (K : ℝ) := by
      rw [hKR]
      linarith [pow_nonneg (show (0 : ℝ) ≤ (Hhi : ℝ) from Nat.cast_nonneg Hhi) 3,
        show (0 : ℝ) ≤ (Ce : ℝ) from Nat.cast_nonneg Ce]
    calc 8 * (P : ℝ) ^ 2 * (ω : ℝ) ≤ (K : ℝ) * (ω : ℝ) :=
          mul_le_mul_of_nonneg_right hPK hωnn
      _ = ((K * ω : ℕ) : ℝ) := by push_cast; ring
  · have hωnn : (0 : ℝ) ≤ (ω : ℝ) := Nat.cast_nonneg _
    have hbase : (Hhi : ℝ) + 48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (K : ℝ) := by
      rw [hKR]
      linarith [hcubeR, hCe, sq_nonneg (P : ℝ)]
    calc (ω : ℝ) * (Hhi : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        = (ω : ℝ) * ((Hhi : ℝ) + 48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)) := by ring
      _ ≤ (ω : ℝ) * (K : ℝ) := mul_le_mul_of_nonneg_left hbase hωnn
      _ = ((K * ω : ℕ) : ℝ) := by push_cast; ring

/-! ### Section C — the parametric anti-vacuity witness -/

/-- **The `(ε, H₋)`-parametric regime builder, with the tower length CHOSEN BY THE
    CALLER** (`chowlaRegime_exists_param_gen`).  Identical to
    `chowlaRegime_exists_param` below except that the tower length is supplied as a
    function `Jof` of the (internally computed) base — any `Jof` whose value at a
    base past the regime floor clears `log 2` will do — and the endpoint is
    exported EXACTLY: `R.Hhi = chowlaTower 2 1 R.Hlo (Jof R.Hlo)`.

    That third conjunct is the whole point.  The landed builder's `hfit` field is
    the INEQUALITY `chowlaTower C₀ a Hlo J ≤ Hhi`, which bounds `Hhi` from below
    and so cannot price `log log Hhi`; a consumer that needs an UPPER law on the
    endpoint (`TowerExport.tower_loglog_le`, at `Jof := towerJmin 2 1`) needs the
    equation.  `towerJmin` itself lives DOWNSTREAM of this file (it is defined in
    `TowerExport`, which imports this module), which is why the choice is a
    parameter here rather than a fixed call. -/
theorem chowlaRegime_exists_param_gen (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) (Jof : ℕ → ℕ)
    (hJof : ∀ B : ℕ, 4000000 ≤ B → Real.log 2 < towerDropSum 2 1 B (Jof B)) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧
      R.Hhi = chowlaTower 2 1 R.Hlo (Jof R.Hlo) := by
  classical
  have hepsR : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  -- the scale `m ≥ 1/ε`
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = ⌈(1 / eps : ℚ)⌉₊ := ⟨_, rfl⟩
  have hm_ge : (1 / eps : ℚ) ≤ (m : ℚ) := by rw [hmdef]; exact Nat.le_ceil _
  have hem : (1 : ℚ) ≤ eps * (m : ℚ) := by
    have h := mul_le_mul_of_nonneg_left hm_ge (le_of_lt heps)
    rwa [mul_one_div, div_self (ne_of_gt heps)] at h
  have hm1N : 1 ≤ m := by rw [hmdef]; exact Nat.ceil_pos.mpr (div_pos one_pos heps)
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm1N
  have hemR : (1 : ℝ) ≤ (eps : ℝ) * (m : ℝ) := by exact_mod_cast hem
  -- the enlarged base floor
  obtain ⟨Hlo, hHlodef⟩ : ∃ Hlo : ℕ, Hlo = max 4000000 (max Hlo₀ (4 * m ^ 4)) := ⟨_, rfl⟩
  have hHlo_floor : 4000000 ≤ Hlo := by rw [hHlodef]; exact le_max_left _ _
  have hHlo0 : Hlo₀ ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHlo4 : 4 * m ^ 4 ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hHlo4Q : (4 : ℚ) * (m : ℚ) ^ 4 ≤ (Hlo : ℚ) := by exact_mod_cast hHlo4
  have hHlo4R : (4 : ℝ) * (m : ℝ) ^ 4 ≤ (Hlo : ℝ) := by exact_mod_cast hHlo4
  -- `hcoprime : 1 ≤ ε²·Hlo/2`
  have hcop : ((1 : ℕ) : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) / 2 := by
    have hprod : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 := by
      have h1 : (1 : ℚ) ≤ (eps * (m : ℚ)) ^ 2 := by nlinarith [hem, sq_nonneg (eps * (m : ℚ) - 1)]
      have h2 : (1 : ℚ) ≤ (m : ℚ) ^ 2 := by nlinarith [hm1, sq_nonneg ((m : ℚ) - 1)]
      exact le_trans h1 (le_mul_of_one_le_right (sq_nonneg _) h2)
    have heq : (eps * (m : ℚ)) ^ 2 * (m : ℚ) ^ 2 = eps ^ 2 * (m : ℚ) ^ 4 := by ring
    have h4le : (4 : ℚ) ≤ eps ^ 2 * (Hlo : ℚ) := by
      have hmul : eps ^ 2 * (4 * (m : ℚ) ^ 4) ≤ eps ^ 2 * (Hlo : ℚ) :=
        mul_le_mul_of_nonneg_left hHlo4Q (sq_nonneg eps)
      nlinarith [hmul, hprod, heq]
    rw [Nat.cast_one]; linarith
  -- `hPNTwindow : √Hlo ≤ ε²·Hlo/2`
  have hPNT : Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) / 2 := by
    have hsqrtHlo : (2 : ℝ) * (m : ℝ) ^ 2 ≤ Real.sqrt (Hlo : ℝ) := by
      have heq : Real.sqrt (4 * (m : ℝ) ^ 4) = 2 * (m : ℝ) ^ 2 := by
        rw [show (4 : ℝ) * (m : ℝ) ^ 4 = (2 * (m : ℝ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      calc (2 : ℝ) * (m : ℝ) ^ 2 = Real.sqrt (4 * (m : ℝ) ^ 4) := heq.symm
        _ ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_le_sqrt hHlo4R
    have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (Hlo : ℝ) := Real.sqrt_nonneg _
    have hHloeq : Real.sqrt (Hlo : ℝ) * Real.sqrt (Hlo : ℝ) = (Hlo : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h2 : (2 : ℝ) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) := by
      have hstep : (eps : ℝ) ^ 2 * (2 * (m : ℝ) ^ 2) ≤ (eps : ℝ) ^ 2 * Real.sqrt (Hlo : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrtHlo (sq_nonneg _)
      nlinarith [hstep, hemR, sq_nonneg ((eps : ℝ) * (m : ℝ) - 1)]
    have h3 : 2 * Real.sqrt (Hlo : ℝ) ≤ (eps : ℝ) ^ 2 * (Hlo : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right h2 hsqrtnn
      rw [mul_assoc, hHloeq] at hh
      linarith [hh]
    linarith [h3]
  -- the tower endpoint and its divergence
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = Jof Hlo := ⟨_, rfl⟩
  have hJ : Real.log 2 < towerDropSum 2 1 Hlo J := by
    rw [hJdef]; exact hJof Hlo hHlo_floor
  obtain ⟨Hhi, hHhidef⟩ : ∃ Hhi : ℕ, Hhi = chowlaTower 2 1 Hlo J := ⟨_, rfl⟩
  have hHhi_floor : 4000000 ≤ Hhi := by rw [hHhidef]; exact chowlaTower_base_floor hHlo_floor J
  have hHlohi : Hlo ≤ Hhi := by rw [hHhidef]; exact chowlaTower_base_ge hHlo_floor J
  have hHhieq : Hhi = chowlaTower 2 1 Hlo (Jof Hlo) := by rw [hHhidef, hJdef]
  -- the outer scale at this `ε` and endpoint
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb⟩ :=
    regime_outer_param eps heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor
  exact ⟨{ x := x, ω := ω, a := 1, eps := eps, Hlo := Hlo, Hhi := Hhi, C0 := 2, J := J,
           hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1, heps := heps, heps1 := heps1,
           hHlo := le_trans (by norm_num) hHlo_floor, hHlohi := hHlohi, hC0 := le_refl 2,
           hHlo_floor := hHlo_floor, hheadroom := hhead, hcoprime := hcop, hfit := hHhidef.ge,
           hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH, hPNTwindow := hPNT,
           hωbig := homega, hxbig := hxb }, rfl, hHlo0, hHhieq⟩

/-- **The `(ε, H₋)`-parametric regime builder.**  For ANY `ε ∈ (0, 1/2]` and ANY
    floor `Hlo₀`, a `ChowlaRegime` exists with `R.eps = ε` and `R.Hlo ≥ Hlo₀`.
    The base is set to `Hlo = max(4·10⁶, Hlo₀, 4·⌈1/ε⌉₊⁴)` — large enough that
    `hcoprime` (`Hlo ≥ 2/ε²`) and `hPNTwindow` (`Hlo ≥ 4/ε⁴`) hold — and the tower
    is re-based there, with divergence supplied by `dropSum_exceeds_log_two_base`
    and the outer scale by `regime_outer_param`.  This is the single lever that
    collapses the three opaque residuals of `log_chowla_two_of_door`: residuals 2
    and 3 by driving `ε` down, residual 1 by driving `Hlo₀` (hence `R.Hlo`) up.

    Statement UNCHANGED; the construction is now `chowlaRegime_exists_param_gen`
    fired at the MINIMAL crossing length (`sInf` of the crossing set — the inlined
    `TowerExport.towerJmin`, which cannot be named here for import reasons).  The
    minimal choice is invisible to this statement and to every consumer of it. -/
theorem chowlaRegime_exists_param (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo := by
  obtain ⟨R, hReps, hRHlo, -⟩ :=
    chowlaRegime_exists_param_gen eps heps heps1 Hlo₀
      (fun B => sInf {J : ℕ | Real.log 2 < towerDropSum 2 1 B J})
      (fun _ hB => Nat.sInf_mem (dropSum_exceeds_log_two_base hB))
  exact ⟨R, hReps, hRHlo⟩

/-! ### Section D — the head-shaped builder, in-cone (REGIME-CUT)

`Salt/MR/RegimeHead.lean` already carries `regimeEnlargeX` and
`chowlaRegime_exists_param_head`; but `RegimeHead` sits in the MR cone, which
CANNOT be imported from here (`SpineFinal.lean` — the consumer of the head form
at its budget-head g-twin — is upstream of the whole MR tower).  The two items
are therefore DUPLICATED under primed names rather than relocated: relocation
would break `RegimeHead`'s open-namespace references and the axiom-ledger cites
that name the MR file.  The primed pair is byte-identical to the MR original;
keep them in sync if either ever moves. -/

/-- **The outer-scale enlargement** (in-cone twin of `Salt.MR.regimeEnlargeX`).
A regime with its outer scale `x` replaced by any `x' ≥ x`.  Legal because the
structure constrains `x` only from below: `hx : 2 ≤ x`, `hωx : ω ≤ x`,
`hheadroom : Hhi ≤ x / ω`, `hheadroom'`, `hPHheadroom`, `hxbig`
(`Regime.lean:73,75,88,103,116,133,136`).  Every other field — `eps`, `ω`, `a`,
`Hlo`, `Hhi`, `C0`, `J` — is carried VERBATIM, which is what lets the head form
inherit `R.eps = eps` and `Hlo₀ ≤ R.Hlo` from the landed builder unchanged. -/
def regimeEnlargeX' (R : ChowlaRegime) {x' : ℕ} (h : R.x ≤ x') : ChowlaRegime where
  x := x'
  ω := R.ω
  a := R.a
  eps := R.eps
  Hlo := R.Hlo
  Hhi := R.Hhi
  C0 := R.C0
  J := R.J
  hx := le_trans R.hx h
  hω := R.hω
  hωx := le_trans R.hωx h
  ha := R.ha
  heps := R.heps
  heps1 := R.heps1
  hHlo := R.hHlo
  hHlohi := R.hHlohi
  hC0 := R.hC0
  hHlo_floor := R.hHlo_floor
  hheadroom := le_trans R.hheadroom (Nat.div_le_div_right h)
  hcoprime := R.hcoprime
  hfit := R.hfit
  hJcon := R.hJcon
  hPNTwindow := R.hPNTwindow
  hωbig := R.hωbig
  hheadroom' := le_trans R.hheadroom' (by exact_mod_cast Nat.div_le_div_right h)
  hPHheadroom := le_trans R.hPHheadroom (by exact_mod_cast h)
  hxbig := le_trans R.hxbig (by exact_mod_cast h)

/-- **The head-shaped parametric regime builder** (in-cone twin of
`Salt.MR.chowlaRegime_exists_param_head`).  For ANY `ε ∈ (0, 1/2]`, ANY floor
`Hlo₀`, and ANY `g : ℕ → ℕ → ℕ`, a `ChowlaRegime` exists with `R.eps = ε`,
`Hlo₀ ≤ R.Hlo`, AND the outer-scale clearance `g R.Hhi R.ω ≤ R.x`.

Proof: run `chowlaRegime_exists_param`, then push the outer scale to
`max R.x (g R.Hhi R.ω)` by `regimeEnlargeX'` — legal because every
`x`-constraint is a one-sided lower bound, and harmless because `eps`, `Hlo`,
`Hhi`, `ω` are carried verbatim (so the `g`-argument does not move under the
enlargement).  No monotonicity hypothesis on `g` is required.

Binder discipline: `ε`, `Hlo₀`, `g` are ALL fixed before the `∃ R`, so a caller
may let `g` depend on anything fixed earlier but never on `R`. -/
theorem chowlaRegime_exists_param_head' (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x := by
  obtain ⟨R, hReps, hRHlo⟩ := chowlaRegime_exists_param eps heps heps1 Hlo₀
  exact ⟨regimeEnlargeX' R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRHlo, le_max_right _ _⟩

end Salt.Entropy.Chowla
