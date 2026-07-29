/-
Copyright (c) 2026 The Salt project contributors. Released under the Apache
License, Version 2.0; see `Salt/Entropy/LICENSE-PFR-Apache-2.0`.

# The sharp tower-crossing law and the minimal-`J` export

The tower recursion `H_{j+1} = H_j·⌊2·log H_j·logloglog H_j⌋₊` (`chowlaTower`,
`Regime.lean`) and its telescoped decrement
`S_J = Σ_{j<J} 1/(2·log H_j·logloglog H_j)` (`towerDropSum`) are landed;
`dropSum_exceeds_log_two_base` (`RegimeParam.lean`) proves — NON-constructively,
through a `Tendsto … atTop` — that `S_J` eventually crosses `log 2`.  Every
downstream consumer needs the SIZE of the tower at the crossing, which the
divergence proof does not supply: the landed accumulation constants
(`summand_lower_gen`'s `1/128`, `tower_log_upper`'s `32·(n+2)·log(n+2)`) are
lossy by a factor `c ≈ 63`, and a loss factor `c` inflates the export law to
`lnlnln H_J = 4^c·lnlnln H₀` — the loss sits in the exponent of an exponent.
This file therefore proves the SHARP two-sided crossing law from scratch, at a
relative loss `ε = 1/20`, and exports the resulting size bound.

## The continuum law and its three error sources

Write `L_j = log H_j`, `u_j = log L_j`, `v_j = log u_j`, `w_j = log v_j` (so
`v_j` is the `logloglog H_j` of the summand and `w_j` is the telescoping
potential).  Per step `ΔL_j = log⌊2 L_j v_j⌋₊ ≈ u_j`, so
`dS = dL/(2 L v) · (u/ΔL) ≈ dL/(2 L u v) = du/(2 u v) = dv/(2 v)`, i.e.

    S_J ≈ ½·log(v_J/v₀) = ½·(w_J − w₀).

The three error sources are priced separately and named:

* **(a) the floor price** — `⌊2 L v⌋₊` versus `2 L v`.  Handled EXACTLY, with no
  approximation: `L ≤ ⌊2 L v⌋₊ ≤ 2 L v` (`towerMul_ge`, `towerMul_le`), which is
  all the two chains ever use.
* **(b) the staircase sandwich** — the discrete sum versus the telescoping
  comparison.  `logStep_dw_le` / `logStep_dw_ge` bound `w' − w` between
  `(20/21)/(L v)` and `(21/20)/(L v)` using only `log x ≤ x − 1` and its dual
  `1 − 1/x ≤ log x`, applied at the three levels `L → u → v`.
* **(c) the `ΔL ≈ u` price** — `log⌊2 L v⌋₊ = log 2 + u + w + O(1)` versus `u`.
  Priced by `log_two_add_loglog_le`: `log 2 + log log u ≤ u/20` for `u ≥ 50`.
  This is the ONLY source that is not second-order, and it is what fixes the
  base floor.

## The floor and the constants

Base floor: `4·10⁶ ≤ B` (the regime floor, for the landed furniture) together
with `50 ≤ loglog B` (i.e. `B ≥ exp(exp 50)`).  This is far weaker than the
`logloglog B ≥ 20` the design brief allowed; the closing-scale consumers sit at
`loglog H₋ ≈ 432`.  Under it:

* `towerDropSum_ge_half_log_ratio` : `(1 − 1/20)·½·(w_J − w₀) ≤ S_J`;
* `towerDropSum_le_half_log_ratio_mul` : `S_J ≤ (1 + 1/20)·½·(w_J − w₀)`;
* `tower_loglog_le` : `loglog H_{Jmin} ≤ (loglog B)^5` — the export.  The honest
  exponent is `exp((40/19)·log 2 + 7/300) = 4.41`; `K = 5` is the integral
  statement it forces (the continuum truth is `4`).
* `tower_loglog_ge` : `(loglog B)^3 ≤ loglog H_{Jmin}` — the companion, honest
  exponent `exp((40/21)·log 2) = 3.74`; with the export it brackets the true
  exponent in `[3.74, 4.41]`, evidence that the law is tight around `4`.

Note where the `1/20` is actually spent.  In the LOWER law it is error (c) and
it is nearly saturated at the floor: the true per-step factor is
`1 + (log 2 + w)/u`, which is `1.041` at `u = 50` and `1.0058` at the closing
scale `u = 432`.  In the UPPER law it is the second-order factor `(1 + ρ)³` with
`ρ = (1 + 2u)/L ≤ 1/100`; the true `ρ` is `≈ 2·10⁻²⁰` at the floor, so that half
is conservative by ~18 orders and could be re-sharpened for free if a consumer
ever needs it.
-/
import Salt.Entropy.Chowla.RegimeParam

open scoped BigOperators

namespace Salt.Entropy.Chowla

/-! ### Section 0 — elementary logarithm furniture -/

/-- The dual of `Real.log_le_sub_one_of_pos`: `1 - 1/x ≤ log x` for `x > 0`
    (apply `log t ≤ t - 1` at `t = 1/x`). -/
lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / x by positivity)
  rw [one_div, Real.log_inv] at h
  rw [one_div]
  linarith

/-- **The upper log-ratio bound** `log a - log b ≤ (a - b)/b`. -/
lemma log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a - b) / b := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < a / b by positivity)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h
  have he : a / b - 1 = (a - b) / b := by field_simp
  rw [he] at h
  exact h

/-- **The lower log-ratio bound** `(a - b)/a ≤ log a - log b`. -/
lemma le_log_sub_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) / a ≤ Real.log a - Real.log b := by
  have h := one_sub_inv_le_log (show (0 : ℝ) < a / b by positivity)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h
  have he : 1 - 1 / (a / b) = (a - b) / a := by field_simp
  rw [he] at h
  exact h

/-- The shifted tangent bound `log t ≤ t/a + log a - 1` (`t, a > 0`). -/
lemma log_le_div_add_log {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    Real.log t ≤ t / a + Real.log a - 1 := by
  have h := log_sub_log_le ht ha
  have he : (t - a) / a = t / a - 1 := by field_simp
  rw [he] at h
  linarith

/-- **ERROR SOURCE (c) — the `ΔL ≈ u` price.**  For `u ≥ 50`,
    `log 2 + log (log u) ≤ u/20`.  This is the per-step relative loss of
    replacing `log⌊2 L v⌋₊ = log 2 + u + w + O(1)` by `u`; it is the term that
    fixes the base floor `50 ≤ loglog B` (the bound already holds from
    `u ≥ 44.3`).  Route: two shifted tangent bounds, at `a = 16` then `a = 4`. -/
lemma log_two_add_loglog_le {u : ℝ} (hu : 50 ≤ u) :
    Real.log 2 + Real.log (Real.log u) ≤ u / 20 := by
  have hupos : (0 : ℝ) < u := by linarith
  have hlupos : 0 < Real.log u := Real.log_pos (by linarith)
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hlu : Real.log u ≤ u / 16 + Real.log 16 - 1 := log_le_div_add_log hupos (by norm_num)
  have hllu : Real.log (Real.log u) ≤ Real.log u / 4 + Real.log 4 - 1 :=
    log_le_div_add_log hlupos (by norm_num)
  rw [h16] at hlu
  rw [h4] at hllu
  linarith

/-- `(u/4 + 1)^4 ≤ exp u` for `u ≥ 0` (four factors of `1 + x ≤ exp x`). -/
lemma quartic_le_exp {u : ℝ} (hu : 0 ≤ u) : (u / 4 + 1) ^ 4 ≤ Real.exp u := by
  have h := Real.add_one_le_exp (u / 4)
  have h4 : Real.exp u = Real.exp (u / 4) ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h4]
  have hnn : (0 : ℝ) ≤ u / 4 + 1 := by linarith
  exact pow_le_pow_left₀ hnn h 4

/-- For `u ≥ 50`, `100·(1 + 2u) ≤ exp u`: the second-order errors (b) all carry
    a factor `(1 + 2u)/L = (1 + 2u)/exp u ≤ 1/100`. -/
lemma hundred_mul_le_exp {u : ℝ} (hu : 50 ≤ u) : 100 * (1 + 2 * u) ≤ Real.exp u := by
  have h := quartic_le_exp (by linarith : (0 : ℝ) ≤ u)
  nlinarith [h, hu, sq_nonneg (u - 50), sq_nonneg u, mul_nonneg (sq_nonneg u) (sq_nonneg u)]

/-- `exp 3 ≤ 50`, i.e. `log u ≥ 3` at `u ≥ 50`. -/
lemma exp_three_le_fifty : Real.exp 3 ≤ 50 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h3]
  calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr
    _ ≤ 50 := by norm_num

/-- `3/2 < log 5`: the crossing budget `(40/19)·log 2 + 7/300 < 3/2` must fit
    under `log 5`, which is what makes `K = 5` the exported exponent. -/
lemma three_halves_lt_log_five : (3 / 2 : ℝ) < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hhalf : Real.exp (1 / 2) < 1.65 := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2), hsq, h1]
  have hsplit : Real.exp (3 / 2) = Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  nlinarith [Real.exp_pos (1 / 2), h1, hhalf]

/-- `log 3 < 6/5`: the companion (lower) export's budget. -/
lemma log_three_lt : Real.log 3 < 6 / 5 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  by_contra hc
  have hc' : Real.exp (6 / 5) ≤ 3 := not_lt.mp hc
  have h5 : Real.exp (6 / 5) ^ 5 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hup : Real.exp 6 ≤ 243 := by
    rw [← h5]
    calc Real.exp (6 / 5) ^ 5 ≤ (3 : ℝ) ^ 5 := by gcongr
      _ ≤ 243 := by norm_num
  have hlo : (243 : ℝ) < Real.exp 6 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h6]
    calc (243 : ℝ) < (2.7 : ℝ) ^ 6 := by norm_num
      _ ≤ Real.exp 1 ^ 6 := by gcongr
  linarith

/-! ### Section 1 — the tower glyphs `L → u → v → w`

`towerV` is the `logloglog H_j` of `towerDropSum`'s summand; `towerW` is the
telescoping potential (the continuum law is `S_J ≈ ½·(w_J − w₀)`). -/

/-- `L_j = log H_j`. -/
noncomputable def towerL (B j : ℕ) : ℝ := Real.log (chowlaTower 2 1 B j : ℝ)

/-- `u_j = loglog H_j`. -/
noncomputable def towerU (B j : ℕ) : ℝ := Real.log (towerL B j)

/-- `v_j = logloglog H_j` — the summand's second factor. -/
noncomputable def towerV (B j : ℕ) : ℝ := Real.log (towerU B j)

/-- `w_j = log v_j` — the telescoping potential. -/
noncomputable def towerW (B j : ℕ) : ℝ := Real.log (towerV B j)

/-- The tower multiplier `⌊2 L_j v_j⌋₊`. -/
noncomputable def towerMul (B j : ℕ) : ℕ := ⌊2 * towerL B j * towerV B j⌋₊

lemma chowlaTower_zero (C0 a Hlo : ℕ) : chowlaTower C0 a Hlo 0 = a * Hlo := rfl

lemma towerL_zero (B : ℕ) : towerL B 0 = Real.log (B : ℝ) := by
  rw [towerL, chowlaTower_zero, one_mul]

lemma towerU_zero (B : ℕ) : towerU B 0 = Real.log (Real.log (B : ℝ)) := by
  rw [towerU, towerL_zero]

/-- Every tower value has `log H_j ≥ 15` (the landed regime floor). -/
lemma towerL_ge_fifteen {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 15 ≤ towerL B j := by
  rw [towerL]; exact (tower_log_bounds (chowlaTower_base_floor hB j)).1

lemma towerL_pos {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) : 0 < towerL B j := by
  linarith [towerL_ge_fifteen hB j]

/-- The base floor `50 ≤ loglog B` propagates up the tower (`H_j ≥ B`). -/
lemma towerU_ge {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ))) (j : ℕ) :
    50 ≤ towerU B j := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    have : (4000000 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hle : (B : ℝ) ≤ (chowlaTower 2 1 B j : ℝ) := by
    exact_mod_cast chowlaTower_base_ge hB j
  have hlogB : 15 ≤ Real.log (B : ℝ) := (tower_log_bounds hB).1
  have h1 : Real.log (B : ℝ) ≤ towerL B j := Real.log_le_log hBpos hle
  rw [towerU]
  exact le_trans hu (Real.log_le_log (by linarith) h1)

lemma towerV_ge_three {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ)))
    (j : ℕ) : 3 ≤ towerV B j := by
  have h50 := towerU_ge hB hu j
  rw [towerV, Real.le_log_iff_exp_le (by linarith)]
  exact le_trans exp_three_le_fifty (by linarith)

lemma towerV_pos {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ))) (j : ℕ) :
    0 < towerV B j := by linarith [towerV_ge_three hB hu j]

/-! ### Section 2 — ERROR SOURCE (a): the floor price, handled exactly -/

/-- **(a), upper half.**  `⌊2 L v⌋₊ ≤ 2 L v`. -/
lemma towerMul_le {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    ((towerMul B j : ℕ) : ℝ) ≤ 2 * towerL B j * towerV B j := by
  refine Nat.floor_le ?_
  have hL := towerL_ge_fifteen hB j
  have hV : (1 / 2 : ℝ) ≤ towerV B j := by
    rw [towerV, towerU, towerL]
    exact (tower_log_bounds (chowlaTower_base_floor hB j)).2
  nlinarith

/-- **(a), lower half.**  `L ≤ ⌊2 L v⌋₊` — the floor never rounds below the
    base, because `2 v - 1 ≥ 5` at the floor.  These two bounds are ALL the
    crossing chains use of the floor: no `⌊·⌋₊`-vs-`·` approximation is made. -/
lemma towerMul_ge {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ))) (j : ℕ) :
    towerL B j ≤ ((towerMul B j : ℕ) : ℝ) := by
  have hL := towerL_ge_fifteen hB j
  have hV := towerV_ge_three hB hu j
  have h := Nat.lt_floor_add_one (2 * towerL B j * towerV B j)
  have hmul : towerL B j * 3 ≤ towerL B j * towerV B j :=
    mul_le_mul_of_nonneg_left hV (by linarith)
  rw [towerMul]
  linarith

/-- The `succ` step in the glyph `L`: `L_{j+1} = L_j + log ⌊2 L_j v_j⌋₊`. -/
lemma towerL_succ {B : ℕ} (hB : 4000000 ≤ B) (j : ℕ) :
    towerL B (j + 1) = towerL B j + Real.log ((towerMul B j : ℕ) : ℝ) := by
  have hfloor := chowlaTower_base_floor hB j
  have hm2 : 2 ≤ towerMul B j := by
    have h := tower_mult_ge_two (show (2 : ℕ) ≤ 2 from le_refl 2) hfloor
    simpa [towerMul, towerL, towerU, towerV] using h
  have hmul_eq :
      ⌊((2 : ℕ) : ℝ) * Real.log (chowlaTower 2 1 B j : ℝ)
        * Real.log (Real.log (Real.log (chowlaTower 2 1 B j : ℝ)))⌋₊ = towerMul B j := by
    simp [towerMul, towerL, towerU, towerV]
  have hH0 : ((chowlaTower 2 1 B j : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℕ) < chowlaTower 2 1 B j := by omega
    positivity
  have hm0 : ((towerMul B j : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℕ) < towerMul B j := by omega
    positivity
  rw [towerL, towerL, chowlaTower_succ, hmul_eq, Nat.cast_mul, Real.log_mul hH0 hm0]

/-! ### Section 3 — ERROR SOURCE (b): the staircase sandwich

The two per-step comparisons between the summand's telescoping potential
increment `w' - w` and `1/(L v)`.  Both are stated over abstract reals with the
glyph chain supplied as defining equations, so the tower enters only through
`towerL_succ` and the two floor bounds (a). -/

/-- **(b), upper half.**  `w' - w ≤ (21/20)/(L v)`.

Route (three applications of `log x ≤ x - 1`, one per glyph level):
`w' - w ≤ (v' - v)/v ≤ (u' - u)/(u v) ≤ log m/(L u v)`, then (a) and (c):
`log m ≤ log 2 + u + w ≤ u + u/20`. -/
lemma logStep_dw_le {L u v w L' u' v' w' m : ℝ}
    (hLpos : 0 < L) (hu : u = Real.log L) (hv : v = Real.log u) (hw : w = Real.log v)
    (hu50 : 50 ≤ u) (hmlo : L ≤ m) (hmhi : m ≤ 2 * L * v)
    (hL' : L' = L + Real.log m) (hu' : u' = Real.log L') (hv' : v' = Real.log u')
    (hw' : w' = Real.log v') :
    w' - w ≤ (21 / 20) / (L * v) := by
  have hupos : (0 : ℝ) < u := by linarith
  have hv3 : (3 : ℝ) ≤ v := by
    rw [hv, Real.le_log_iff_exp_le hupos]
    exact le_trans exp_three_le_fifty hu50
  have hvpos : (0 : ℝ) < v := by linarith
  have hwv : w ≤ v := by rw [hw]; exact Real.log_le_self hvpos.le
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hLpos hmlo
  -- (a): the floor price
  have hlogm_lo : u ≤ Real.log m := by rw [hu]; exact Real.log_le_log hLpos hmlo
  have hlogm_hi : Real.log m ≤ Real.log 2 + u + w := by
    have h1 : Real.log m ≤ Real.log (2 * L * v) := Real.log_le_log hmpos hmhi
    rw [Real.log_mul (by positivity) (ne_of_gt hvpos),
      Real.log_mul (two_ne_zero) (ne_of_gt hLpos), ← hu, ← hw] at h1
    linarith
  -- (c): the ΔL ≈ u price
  have hprice : Real.log 2 + w ≤ u / 20 := by
    rw [hw, hv]; exact log_two_add_loglog_le hu50
  have hm21 : Real.log m ≤ (21 / 20) * u := by linarith
  -- the primed glyphs
  have hL'pos : 0 < L' := by rw [hL']; linarith
  have hsub : L' - L = Real.log m := by rw [hL']; ring
  have hLL' : L ≤ L' := by rw [hL']; linarith
  have huu' : u ≤ u' := by rw [hu, hu']; exact Real.log_le_log hLpos hLL'
  have hu'pos : 0 < u' := by linarith
  have hvv' : v ≤ v' := by rw [hv, hv']; exact Real.log_le_log hupos huu'
  have hv'pos : 0 < v' := by linarith
  -- the three-level chain
  have c1 : u' - u ≤ Real.log m / L := by
    have h := log_sub_log_le hL'pos hLpos
    rw [← hu, ← hu', hsub] at h
    exact h
  have c2 : v' - v ≤ (u' - u) / u := by
    have h := log_sub_log_le hu'pos hupos
    rw [← hv, ← hv'] at h
    exact h
  have c3 : w' - w ≤ (v' - v) / v := by
    have h := log_sub_log_le hv'pos hvpos
    rw [← hw, ← hw'] at h
    exact h
  -- clear the denominators and chain
  have c1' : (u' - u) * L ≤ Real.log m := (le_div_iff₀ hLpos).mp c1
  have c2' : (v' - v) * u ≤ u' - u := (le_div_iff₀ hupos).mp c2
  have c3' : (w' - w) * v ≤ v' - v := (le_div_iff₀ hvpos).mp c3
  have hLvpos : (0 : ℝ) < L * v := mul_pos hLpos hvpos
  rw [le_div_iff₀ hLvpos]
  have hkey : ((w' - w) * (L * v)) * u ≤ (21 / 20) * u := by
    calc ((w' - w) * (L * v)) * u = ((w' - w) * v) * (L * u) := by ring
      _ ≤ (v' - v) * (L * u) := by
          exact mul_le_mul_of_nonneg_right c3' (by positivity)
      _ = ((v' - v) * u) * L := by ring
      _ ≤ (u' - u) * L := mul_le_mul_of_nonneg_right c2' hLpos.le
      _ ≤ Real.log m := c1'
      _ ≤ (21 / 20) * u := hm21
  exact le_of_mul_le_mul_right hkey hupos

/-- **(b), lower half.**  `(20/21)/(L v) ≤ w' - w`.

Route (three applications of the dual `1 - 1/x ≤ log x`):
`w' - w ≥ (v' - v)/v' ≥ (u' - u)/(u' v') ≥ log m/(L' u' v') ≥ u/(L' u' v')`
by (a); then the primed glyphs are within `(101/100)` of the unprimed ones,
which is the second-order error `(1 + 2u)/L ≤ 1/100` of `hundred_mul_le_exp`.
`(100/101)³ = 0.9706 ≥ 20/21 = 0.9524`. -/
lemma logStep_dw_ge {L u v w L' u' v' w' m : ℝ}
    (hLpos : 0 < L) (hu : u = Real.log L) (hv : v = Real.log u) (hw : w = Real.log v)
    (hu50 : 50 ≤ u) (hmlo : L ≤ m) (hmhi : m ≤ 2 * L * v)
    (hL' : L' = L + Real.log m) (hu' : u' = Real.log L') (hv' : v' = Real.log u')
    (hw' : w' = Real.log v') :
    (20 / 21) / (L * v) ≤ w' - w := by
  have hupos : (0 : ℝ) < u := by linarith
  have hv3 : (3 : ℝ) ≤ v := by
    rw [hv, Real.le_log_iff_exp_le hupos]
    exact le_trans exp_three_le_fifty hu50
  have hvpos : (0 : ℝ) < v := by linarith
  have hwv : w ≤ v := by rw [hw]; exact Real.log_le_self hvpos.le
  have hvu : v ≤ u := by rw [hv]; exact Real.log_le_self hupos.le
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hLpos hmlo
  -- (a): the floor price
  have hlogm_lo : u ≤ Real.log m := by rw [hu]; exact Real.log_le_log hLpos hmlo
  have hlogm_hi : Real.log m ≤ Real.log 2 + u + w := by
    have h1 : Real.log m ≤ Real.log (2 * L * v) := Real.log_le_log hmpos hmhi
    rw [Real.log_mul (by positivity) (ne_of_gt hvpos),
      Real.log_mul (two_ne_zero) (ne_of_gt hLpos), ← hu, ← hw] at h1
    linarith
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hm12 : Real.log m ≤ 1 + 2 * u := by linarith
  -- the second-order scale: L ≥ 100·(1 + 2u)
  have hLexp : L = Real.exp u := by rw [hu, Real.exp_log hLpos]
  have hLbig : 100 * (1 + 2 * u) ≤ L := by rw [hLexp]; exact hundred_mul_le_exp hu50
  -- the primed glyphs
  have hL'pos : 0 < L' := by rw [hL']; linarith
  have hsub : L' - L = Real.log m := by rw [hL']; ring
  have hLL' : L ≤ L' := by rw [hL']; linarith
  have huu' : u ≤ u' := by rw [hu, hu']; exact Real.log_le_log hLpos hLL'
  have hu'pos : 0 < u' := by linarith
  have hvv' : v ≤ v' := by rw [hv, hv']; exact Real.log_le_log hupos huu'
  have hv'pos : 0 < v' := by linarith
  have hww' : w ≤ w' := by rw [hw, hw']; exact Real.log_le_log hvpos hvv'
  -- the upper chain (for the second-order factors)
  have d1 : u' - u ≤ Real.log m / L := by
    have h := log_sub_log_le hL'pos hLpos
    rw [← hu, ← hu', hsub] at h
    exact h
  have d2 : v' - v ≤ (u' - u) / u := by
    have h := log_sub_log_le hu'pos hupos
    rw [← hv, ← hv'] at h
    exact h
  have d1' : (u' - u) * L ≤ Real.log m := (le_div_iff₀ hLpos).mp d1
  have d2' : (v' - v) * u ≤ u' - u := (le_div_iff₀ hupos).mp d2
  have hstep100 : u' - u ≤ 1 / 100 := by
    have h3 : (u' - u) * L ≤ (1 / 100 : ℝ) * L := by linarith
    exact le_of_mul_le_mul_right h3 hLpos
  have hu'le : u' ≤ (101 / 100) * u := by linarith
  have hv'le : v' ≤ (101 / 100) * v := by
    have h : (v' - v) * 50 ≤ (v' - v) * u :=
      mul_le_mul_of_nonneg_left hu50 (by linarith)
    have h2 : v' - v ≤ 1 / 5000 := by linarith
    linarith
  have hL'le : L' ≤ (101 / 100) * L := by rw [hL']; linarith
  -- the lower chain
  have c1 : Real.log m / L' ≤ u' - u := by
    have h := le_log_sub_log hL'pos hLpos
    rw [← hu, ← hu', hsub] at h
    exact h
  have c2 : (u' - u) / u' ≤ v' - v := by
    have h := le_log_sub_log hu'pos hupos
    rw [← hv, ← hv'] at h
    exact h
  have c3 : (v' - v) / v' ≤ w' - w := by
    have h := le_log_sub_log hv'pos hvpos
    rw [← hw, ← hw'] at h
    exact h
  have c1' : Real.log m ≤ (u' - u) * L' := (div_le_iff₀ hL'pos).mp c1
  have c2' : u' - u ≤ (v' - v) * u' := (div_le_iff₀ hu'pos).mp c2
  have c3' : v' - v ≤ (w' - w) * v' := (div_le_iff₀ hv'pos).mp c3
  -- assemble: u ≤ (w' - w)·(L'·u'·v') ≤ (w' - w)·(101/100)³·(L·u·v)
  have hkey : u ≤ (w' - w) * (L' * u' * v') := by
    calc u ≤ Real.log m := hlogm_lo
      _ ≤ (u' - u) * L' := c1'
      _ ≤ ((v' - v) * u') * L' := mul_le_mul_of_nonneg_right c2' hL'pos.le
      _ ≤ (((w' - w) * v') * u') * L' := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c3' hu'pos.le) hL'pos.le
      _ = (w' - w) * (L' * u' * v') := by ring
  have hprod : L' * u' * v' ≤ (1030301 / 1000000) * (L * u * v) := by
    have h1 : L' * u' ≤ ((101 / 100) * L) * ((101 / 100) * u) :=
      mul_le_mul hL'le hu'le hu'pos.le (by positivity)
    have h2 : (L' * u') * v' ≤ (((101 / 100) * L) * ((101 / 100) * u)) * ((101 / 100) * v) :=
      mul_le_mul h1 hv'le hv'pos.le (by positivity)
    nlinarith [h2]
  have hkey2 : u ≤ (w' - w) * ((1030301 / 1000000) * (L * u * v)) :=
    le_trans hkey (mul_le_mul_of_nonneg_left hprod (by linarith))
  have hLvpos : (0 : ℝ) < L * v := mul_pos hLpos hvpos
  rw [div_le_iff₀ hLvpos]
  nlinarith [hkey2, hupos, hLvpos]

/-! ### Section 4 — the per-step sandwich along the tower -/

/-- **(b) at the tower, upper half.** -/
lemma towerStep_dw_le {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ)))
    (j : ℕ) :
    towerW B (j + 1) - towerW B j ≤ (21 / 20) / (towerL B j * towerV B j) :=
  logStep_dw_le (L := towerL B j) (u := towerU B j) (v := towerV B j) (w := towerW B j)
    (L' := towerL B (j + 1)) (u' := towerU B (j + 1)) (v' := towerV B (j + 1))
    (w' := towerW B (j + 1)) (m := ((towerMul B j : ℕ) : ℝ))
    (towerL_pos hB j) rfl rfl rfl (towerU_ge hB hu j) (towerMul_ge hB hu j)
    (towerMul_le hB j) (towerL_succ hB j) rfl rfl rfl

/-- **(b) at the tower, lower half.** -/
lemma towerStep_dw_ge {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ)))
    (j : ℕ) :
    (20 / 21) / (towerL B j * towerV B j) ≤ towerW B (j + 1) - towerW B j :=
  logStep_dw_ge (L := towerL B j) (u := towerU B j) (v := towerV B j) (w := towerW B j)
    (L' := towerL B (j + 1)) (u' := towerU B (j + 1)) (v' := towerV B (j + 1))
    (w' := towerW B (j + 1)) (m := ((towerMul B j : ℕ) : ℝ))
    (towerL_pos hB j) rfl rfl rfl (towerU_ge hB hu j) (towerMul_ge hB hu j)
    (towerMul_le hB j) (towerL_succ hB j) rfl rfl rfl

/-! ### Section 5 — THE SHARP CROSSING LAW -/

lemma towerDropSum_eq_sum (B J : ℕ) :
    towerDropSum 2 1 B J = ∑ j ∈ Finset.range J, 1 / (2 * towerL B j * towerV B j) := rfl

/-- The telescoping potential difference IS the log-ratio of the summand's
    `logloglog` factor: `w_J - w₀ = log (v_J/v₀)`.  This is what makes the two
    theorems below the literal `½·log(v_J/v₀)` sandwich. -/
lemma towerW_sub_eq_log_div {B : ℕ} (hB : 4000000 ≤ B)
    (hu : 50 ≤ Real.log (Real.log (B : ℝ))) (J : ℕ) :
    towerW B J - towerW B 0 = Real.log (towerV B J / towerV B 0) := by
  rw [Real.log_div (ne_of_gt (towerV_pos hB hu J)) (ne_of_gt (towerV_pos hB hu 0))]
  rfl

/-- **THE SHARP CROSSING LAW, lower half.**  `(1 - 1/20)·½·(w_J - w₀) ≤ S_J`.

This is the direction the export consumes: at the minimal `J` it converts
`S_{J-1} ≤ log 2` into an UPPER bound on `v_{J-1}`.  The relative loss `1/20`
is error source (c) — the only first-order one. -/
theorem towerDropSum_ge_half_log_ratio {B : ℕ} (hB : 4000000 ≤ B)
    (hu : 50 ≤ Real.log (Real.log (B : ℝ))) (J : ℕ) :
    (1 - 1 / 20 : ℝ) * ((1 / 2) * (towerW B J - towerW B 0)) ≤ towerDropSum 2 1 B J := by
  have hkey : ∀ j ∈ Finset.range J,
      (19 / 40 : ℝ) * (towerW B (j + 1) - towerW B j)
        ≤ 1 / (2 * towerL B j * towerV B j) := by
    intro j _
    have hstep := towerStep_dw_le hB hu j
    have hL := towerL_ge_fifteen hB j
    have hV := towerV_ge_three hB hu j
    have hX : (0 : ℝ) < towerL B j * towerV B j := by nlinarith
    have e2 : 1 / (2 * towerL B j * towerV B j)
        = (1 / 2 : ℝ) / (towerL B j * towerV B j) := by
      field_simp
    rw [e2]
    calc (19 / 40 : ℝ) * (towerW B (j + 1) - towerW B j)
        ≤ (19 / 40 : ℝ) * ((21 / 20) / (towerL B j * towerV B j)) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = (399 / 800 : ℝ) / (towerL B j * towerV B j) := by ring
      _ ≤ (1 / 2 : ℝ) / (towerL B j * towerV B j) := by
          have hd : (1 / 2 : ℝ) / (towerL B j * towerV B j)
              - (399 / 800 : ℝ) / (towerL B j * towerV B j)
              = (1 / 800 : ℝ) / (towerL B j * towerV B j) := by ring
          have hnn : (0 : ℝ) ≤ (1 / 800 : ℝ) / (towerL B j * towerV B j) :=
            div_nonneg (by norm_num) hX.le
          linarith
  calc (1 - 1 / 20 : ℝ) * ((1 / 2) * (towerW B J - towerW B 0))
      = ∑ j ∈ Finset.range J, (19 / 40 : ℝ) * (towerW B (j + 1) - towerW B j) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (towerW B) J]; ring
    _ ≤ ∑ j ∈ Finset.range J, 1 / (2 * towerL B j * towerV B j) := Finset.sum_le_sum hkey
    _ = towerDropSum 2 1 B J := (towerDropSum_eq_sum B J).symm

/-- **THE SHARP CROSSING LAW, upper half.**  `S_J ≤ (1 + 1/20)·½·(w_J - w₀)`.

The tightness side: with the lower half it pins `S_J = ½·log(v_J/v₀)·(1 ± 1/20)`.
Here the per-step constant is EXACT — `(21/40)·(20/21) = 1/2` — the `1/20` is
spent entirely on the second-order factors of `logStep_dw_ge`. -/
theorem towerDropSum_le_half_log_ratio_mul {B : ℕ} (hB : 4000000 ≤ B)
    (hu : 50 ≤ Real.log (Real.log (B : ℝ))) (J : ℕ) :
    towerDropSum 2 1 B J ≤ (1 + 1 / 20 : ℝ) * ((1 / 2) * (towerW B J - towerW B 0)) := by
  have hkey : ∀ j ∈ Finset.range J,
      1 / (2 * towerL B j * towerV B j)
        ≤ (21 / 40 : ℝ) * (towerW B (j + 1) - towerW B j) := by
    intro j _
    have hstep := towerStep_dw_ge hB hu j
    have hL := towerL_ge_fifteen hB j
    have hV := towerV_ge_three hB hu j
    have hX : (0 : ℝ) < towerL B j * towerV B j := by nlinarith
    have e2 : 1 / (2 * towerL B j * towerV B j)
        = (1 / 2 : ℝ) / (towerL B j * towerV B j) := by
      field_simp
    rw [e2]
    calc (1 / 2 : ℝ) / (towerL B j * towerV B j)
        = (21 / 40 : ℝ) * ((20 / 21) / (towerL B j * towerV B j)) := by ring
      _ ≤ (21 / 40 : ℝ) * (towerW B (j + 1) - towerW B j) :=
          mul_le_mul_of_nonneg_left hstep (by norm_num)
  calc towerDropSum 2 1 B J = ∑ j ∈ Finset.range J, 1 / (2 * towerL B j * towerV B j) :=
        towerDropSum_eq_sum B J
    _ ≤ ∑ j ∈ Finset.range J, (21 / 40 : ℝ) * (towerW B (j + 1) - towerW B j) :=
        Finset.sum_le_sum hkey
    _ = (1 + 1 / 20 : ℝ) * ((1 / 2) * (towerW B J - towerW B 0)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (towerW B) J]; ring

/-! ### Section 6 — the MINIMAL tower length -/

/-- **The minimal tower length**: the least `J` at which the telescoped decrement
    clears `log 2`.  Total by construction (`sInf` of a set of naturals, junk
    value `0` if empty); `towerJmin_eq_find` records that it IS `Nat.find` of the
    landed existence proof, and `towerJmin_spec` consumes
    `dropSum_exceeds_log_two_base` for nonemptiness. -/
noncomputable def towerJmin (C0 a B : ℕ) : ℕ :=
  sInf {J : ℕ | Real.log 2 < towerDropSum C0 a B J}

/-- `towerJmin` is `Nat.find` of the crossing existence statement. -/
lemma towerJmin_eq_find {C0 a B : ℕ}
    (h : ∃ J : ℕ, Real.log 2 < towerDropSum C0 a B J) :
    towerJmin C0 a B = @Nat.find _ (Classical.decPred _) h :=
  Nat.sInf_def h

/-- **The crossing at the minimal `J`.** -/
theorem towerJmin_spec {B : ℕ} (hB : 4000000 ≤ B) :
    Real.log 2 < towerDropSum 2 1 B (towerJmin 2 1 B) :=
  Nat.sInf_mem (dropSum_exceeds_log_two_base hB)

/-- **Minimality**: every shorter tower stays under `log 2`. -/
theorem towerDropSum_le_log_two_of_lt_towerJmin {C0 a B k : ℕ} (hk : k < towerJmin C0 a B) :
    towerDropSum C0 a B k ≤ Real.log 2 := by
  by_contra hcon
  exact absurd (Nat.sInf_le
      (show k ∈ {J : ℕ | Real.log 2 < towerDropSum C0 a B J} from not_le.mp hcon))
    (not_le.mpr hk)

/-- The minimal `J` is positive (the empty tower has decrement `0 < log 2`). -/
lemma towerJmin_pos {B : ℕ} (hB : 4000000 ≤ B) : 0 < towerJmin 2 1 B := by
  rcases Nat.eq_zero_or_pos (towerJmin 2 1 B) with h | h
  · exfalso
    have hs := towerJmin_spec hB
    rw [h] at hs
    have h0 : towerDropSum 2 1 B 0 = 0 := by simp [towerDropSum]
    rw [h0] at hs
    linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
  · exact h

/-! ### Section 7 — THE EXPORT -/

/-- **THE EXPORT THEOREM.**  At the minimal crossing length,
    `loglog H_J ≤ (loglog B)^5`.

At `J - 1` minimality gives `S_{J-1} ≤ log 2`; the sharp crossing law's lower
half turns that into `w_{J-1} - w₀ ≤ (40/19)·log 2 ≤ 1.46`, and one more step
adds at most `(21/20)/(L·v) ≤ 7/300`.  Hence `w_J - w₀ < 3/2 < log 5`, i.e.
`v_J < 5·v₀`, i.e. `log u_J < log (u₀^5)`.  The honest exponent bound is
`exp((40/19)·log 2 + 7/300) = 4.41` (the continuum truth is `4`); `K = 5` is the
integer it forces.  With the crossing law's other half (`tower_loglog_ge`) the
true exponent is bracketed in `[3.74, 4.41]`. -/
theorem tower_loglog_le {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ))) :
    Real.log (Real.log (chowlaTower 2 1 B (towerJmin 2 1 B) : ℝ))
      ≤ (Real.log (Real.log (B : ℝ))) ^ 5 := by
  obtain ⟨k, hk⟩ : ∃ k, towerJmin 2 1 B = k + 1 :=
    ⟨towerJmin 2 1 B - 1, by have := towerJmin_pos hB; omega⟩
  -- minimality at `k`
  have hSk : towerDropSum 2 1 B k ≤ Real.log 2 :=
    towerDropSum_le_log_two_of_lt_towerJmin (by omega)
  have hlow := towerDropSum_ge_half_log_ratio hB hu k
  have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hwk : towerW B k - towerW B 0 ≤ 1.46 := by linarith
  -- the last step
  have hstep := towerStep_dw_le hB hu k
  have hL := towerL_ge_fifteen hB k
  have hV := towerV_ge_three hB hu k
  have hX : (0 : ℝ) < towerL B k * towerV B k := by nlinarith
  have hlast : towerW B (k + 1) - towerW B k ≤ 7 / 300 := by
    refine le_trans hstep ?_
    rw [div_le_iff₀ hX]
    nlinarith
  have hfinal : towerW B (towerJmin 2 1 B) - towerW B 0 < 3 / 2 := by
    rw [hk]; linarith
  -- convert to the `v` ratio, then to the `u` power
  have hv0 : (3 : ℝ) ≤ towerV B 0 := towerV_ge_three hB hu 0
  have hvJ : (3 : ℝ) ≤ towerV B (towerJmin 2 1 B) := towerV_ge_three hB hu _
  have hlog5 := three_halves_lt_log_five
  have hVlt : towerV B (towerJmin 2 1 B) < 5 * towerV B 0 := by
    rw [← Real.log_lt_log_iff (by linarith) (by linarith)]
    rw [Real.log_mul (by norm_num) (by linarith)]
    have e1 : towerW B (towerJmin 2 1 B) = Real.log (towerV B (towerJmin 2 1 B)) := rfl
    have e2 : towerW B 0 = Real.log (towerV B 0) := rfl
    rw [← e1, ← e2]
    linarith
  have hu0 : (50 : ℝ) ≤ towerU B 0 := towerU_ge hB hu 0
  have huJ : (50 : ℝ) ≤ towerU B (towerJmin 2 1 B) := towerU_ge hB hu _
  have hpow : Real.log (towerU B (towerJmin 2 1 B)) < Real.log ((towerU B 0) ^ (5 : ℕ)) := by
    rw [Real.log_pow]
    have e1 : towerV B (towerJmin 2 1 B) = Real.log (towerU B (towerJmin 2 1 B)) := rfl
    have e2 : towerV B 0 = Real.log (towerU B 0) := rfl
    rw [e1, e2] at hVlt
    push_cast
    linarith
  have hfin : towerU B (towerJmin 2 1 B) < (towerU B 0) ^ (5 : ℕ) :=
    (Real.log_lt_log_iff (by linarith) (by positivity)).mp hpow
  rw [towerU_zero] at hfin
  have e3 : towerU B (towerJmin 2 1 B)
      = Real.log (Real.log (chowlaTower 2 1 B (towerJmin 2 1 B) : ℝ)) := rfl
  rw [e3] at hfin
  exact le_of_lt hfin

/-- **THE COMPANION (tightness).**  `(loglog B)^3 ≤ loglog H_J` at the minimal
    crossing length: from `log 2 < S_J` and the crossing law's UPPER half,
    `w_J - w₀ > (40/21)·log 2 = 1.3203 > 6/5 > log 3`, so `v_J > 3·v₀` (the
    honest exponent here is `exp(1.3203) = 3.74`).  Together with
    `tower_loglog_le` this brackets the true exponent in `[3.74, 4.41]` — the
    continuum value `4` sits inside — and the exported integers in `[3, 5]`. -/
theorem tower_loglog_ge {B : ℕ} (hB : 4000000 ≤ B) (hu : 50 ≤ Real.log (Real.log (B : ℝ))) :
    (Real.log (Real.log (B : ℝ))) ^ 3
      ≤ Real.log (Real.log (chowlaTower 2 1 B (towerJmin 2 1 B) : ℝ)) := by
  have hcross := towerJmin_spec hB
  have hupp := towerDropSum_le_half_log_ratio_mul hB hu (towerJmin 2 1 B)
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl3 : Real.log 3 < 6 / 5 := log_three_lt
  have hwJ : (6 : ℝ) / 5 < towerW B (towerJmin 2 1 B) - towerW B 0 := by linarith
  have hv0 : (3 : ℝ) ≤ towerV B 0 := towerV_ge_three hB hu 0
  have hvJ : (3 : ℝ) ≤ towerV B (towerJmin 2 1 B) := towerV_ge_three hB hu _
  have hVlt : 3 * towerV B 0 < towerV B (towerJmin 2 1 B) := by
    rw [← Real.log_lt_log_iff (by linarith) (by linarith)]
    rw [Real.log_mul (by norm_num) (by linarith)]
    have e1 : towerW B (towerJmin 2 1 B) = Real.log (towerV B (towerJmin 2 1 B)) := rfl
    have e2 : towerW B 0 = Real.log (towerV B 0) := rfl
    rw [← e1, ← e2]
    linarith
  have hu0 : (50 : ℝ) ≤ towerU B 0 := towerU_ge hB hu 0
  have huJ : (50 : ℝ) ≤ towerU B (towerJmin 2 1 B) := towerU_ge hB hu _
  have hpow : Real.log ((towerU B 0) ^ (3 : ℕ)) < Real.log (towerU B (towerJmin 2 1 B)) := by
    rw [Real.log_pow]
    have e1 : towerV B (towerJmin 2 1 B) = Real.log (towerU B (towerJmin 2 1 B)) := rfl
    have e2 : towerV B 0 = Real.log (towerU B 0) := rfl
    rw [e1, e2] at hVlt
    push_cast
    linarith
  have hfin : (towerU B 0) ^ (3 : ℕ) < towerU B (towerJmin 2 1 B) :=
    (Real.log_lt_log_iff (by positivity) (by linarith)).mp hpow
  rw [towerU_zero] at hfin
  have e3 : towerU B (towerJmin 2 1 B)
      = Real.log (Real.log (chowlaTower 2 1 B (towerJmin 2 1 B) : ℝ)) := rfl
  rw [e3] at hfin
  exact le_of_lt hfin

/-! ### Section 8 — THE EXPORT, THREADED ONTO THE REGIME BUILDER

⟦THE NAMED AMENDMENT⟧ (the 2026-07-29 anchor ruling, piece 2).  A CONSTANT door
anchor is sound against a regime only if the regime exports an upper law on its
own endpoint `H₊` in terms of `H₋`; the landed `ChowlaRegime` exports none (its
`hfit` field bounds `H₊` from BELOW).  The two builders below re-point the
tower's `J` at `towerJmin` — the minimal crossing length, whose `towerJmin_spec`
supplies exactly the `hJcon` the landed builder asks of an arbitrary crossing `J`
— and carry `tower_loglog_le` out through the `∃ R` as a named conjunct.

**The conjunct is GUARDED** by `50 ≤ loglog H₋`, the base floor of the sharp
crossing law (§0's error source (c) fixes it, and `tower_loglog_le` carries it as
a hypothesis).  The guard cannot be discharged inside the builder: its base is
`max(4·10⁶, Hlo₀, 4⌈1/ε⌉₊⁴)`, whose `loglog` is `≈ 2.7` at the floor, so for a
caller that asks for nothing more the export's own side condition is simply
unavailable (the unguarded conjunct is not FALSE there — it is unproved, the
analytic input dying below the floor).  The guard IS free at every door-road call
site, where the caller's own floor (`U1floor`, the `H0scale`/arc floors) is
astronomically past `exp(exp 50)`: the consumer discharges it from its own floor
demand and reads the law off. -/

/-- **The regime builder with the tower law exported** — the landed
`chowlaRegime_exists_param` plus the guarded endpoint law
`loglog H₊ ≤ (loglog H₋)^5`.  Same `ε`, same floor lever; the only internal
change is that the tower length is `towerJmin` rather than an arbitrary crossing
witness, which is what makes `H₊` an EXACT tower value and hence priceable. -/
theorem chowlaRegime_exists_param_tower (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧
      (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) := by
  obtain ⟨R, hReps, hRHlo, hRHhi⟩ :=
    chowlaRegime_exists_param_gen eps heps heps1 Hlo₀ (towerJmin 2 1)
      (fun _ hB => towerJmin_spec hB)
  refine ⟨R, hReps, hRHlo, fun hu => ?_⟩
  rw [hRHhi]
  exact tower_loglog_le R.hHlo_floor hu

/-- **The head-shaped builder with the tower law exported** — `∃ R` carrying, in
one statement, the `ε`-pin, the floor lever, the outer-scale clearance
`g H₊ ω ≤ x` AND the guarded endpoint law.  The in-cone twin of
`chowlaRegime_exists_param_head'` (`RegimeParam.lean`), fired at the tower-pointed
builder above.

The enlargement step is what makes the conjunct survive: `regimeEnlargeX'` moves
`x` ALONE — `Hlo` and `Hhi` are carried verbatim (`RegimeParam.lean`, the
definition's field list) — so the exported law reads against the same two
endpoints after the push as before it. -/
theorem chowlaRegime_exists_param_head_tower' (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegime, R.eps = eps ∧ Hlo₀ ≤ R.Hlo ∧ g R.Hhi R.ω ≤ R.x ∧
      (50 ≤ Real.log (Real.log (R.Hlo : ℝ)) →
        Real.log (Real.log (R.Hhi : ℝ)) ≤ Real.log (Real.log (R.Hlo : ℝ)) ^ 5) := by
  obtain ⟨R, hReps, hRHlo, hRtow⟩ := chowlaRegime_exists_param_tower eps heps heps1 Hlo₀
  exact ⟨regimeEnlargeX' R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRHlo,
    le_max_right _ _, hRtow⟩

end Salt.Entropy.Chowla
