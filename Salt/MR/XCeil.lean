/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.MR.RegisterSupply
import Salt.Entropy.Chowla.TowerFlatBuilder

/-!
# `XCeil` — THE OUTER-SCALE CEILING, AND WHAT IT BUYS THE BASE-SCALE CAP

`RegisterSupply` §1 (2026-08-02) found that ⟦ITEM 3⟧'s base-scale cap
(`S16BaseScaleCap96_L_gk`) is not a wide numeric inequality: it needs an UPPER bound on the
regime's outer scale `R.x`, and `ChowlaRegime` carries only lower bounds
(`hheadroom`, `hheadroom'`, `hPHheadroom`, `hxbig`), while the terminal hands the caller a
further FLOOR `g R.Hhi R.ω ≤ R.x` at a caller-chosen `g`.  This file supplies the missing
ceiling at its source and prices what it does — and does not — discharge.

## §1 — THE CLOSED FORM THE BUILDER ACTUALLY CONSTRUCTS

`RegimeParam.regime_outer_param` builds the outer scale in closed form:

  `ω = (H₊ + 2)^N`,  `N = ⌈RHS / log(H₊+2)⌉₊ + 1`,  `RHS = (16/ε)·log(ε²H₊) + 64/ε + 1`;
  `x = K·ω`,  `K = 8·H₊³ + 8·P² + Ce`,  `Ce = ⌈48·(1 + 2/ε²)/ε⌉₊`

— and then DISCARDS it (`clear hωdef hNdef`, `RegimeParam.lean:337`), so only the eight floors
survive.  `regime_outer_param_ceiling` is the additive twin: the same eight floors plus the
CEILING

  `log x ≤ (30/ε)·log H₊ + 2·log(P + 1)`,

read off the same construction (`N ≤ RHS/log(H₊+2) + 2` by `Nat.ceil_lt_add_one`,
`log(H₊+2) ≤ log H₊ + 1`, and `K ≤ 600·H₊³·(P+1)²/ε³`).  The `P`-term is the whole story: the
flat builder instantiates `P = 4^⌊ε²H₊⌋`, so the outer scale is SINGLE-EXPONENTIAL IN THE
ENDPOINT, `log x ≈ 2·log 4·ε²·H₊`, hence `loglog(3x) ≈ log H₊` — the cap reads the ENDPOINT,
one exponential below the outer scale.

## §2 — THE THREADED EXPORTS

`chowlaRegimeFlat_exists_param_gen_ceiling` carries the ceiling in the endpoint-only form
`log R.x ≤ (31/ε)·R.H₊`, and `chowlaRegimeFlat_exists_param_head_ceiling` carries it through
the outer-scale enlargement, where it necessarily acquires the caller's `g`:

  `log R.x ≤ max ((31/ε)·R.H₊) (log (g R.Hhi R.ω))`

— the enlargement is `x ↦ max x (g H₊ ω)`, so a caller who picks a huge `g` picks a huge outer
scale, and no export can prevent it.  **The cap is therefore conditional on a `g`-bound in
every threading; that is a fact about the terminal's interface, not a gap in this file.**

## §3 — WHAT THE CEILING DISCHARGES, AND THE RESIDUAL (the honest verdict)

`s16_baseScaleCap96_L_of_xceil` closes the cap from the ceiling plus ONE endpoint window, and
`s16_baseScaleCap96_L_supplied` states that window at the lever's own numeral:

  `loglog R.Hhi ≤ K/2`   (at `K = 32000000`: `loglog H₊ ≤ 1.6·10⁷`).

**The terminal does not supply it — and the window is not merely unproven, it is FALSE at the
terminal's own regime.**  This is the file's headline, and it is kernel-pinned twice:

* `flatA_endpoint_ceiling_misses_K_half` — the terminal's exported UPPER ceiling
  `loglog R.Hhi ≤ 2·exp(3.2A/2)` is already `≈ 3.7·10^{112}` at `A = 162`, so it cannot route
  through `_supplied`;
* `flat_endpoint_loglog_gt_lever` — the decisive one.  `TowerFlat.towerFlat_width_ge` (the
  landed extremality LOWER bound: every crossing length pays
  `(log 2A + loglog H₋)·4^{(20/21)A}`) forces
  `loglog (chowlaTowerFlat A 1 H₋ Jf) > 1.6·10⁷` for EVERY `A ≥ 162` — and the flat regime's
  endpoint dominates that arm (`hfitF`).  At `A = 162` the true value is
  `≥ 3.2·162·4^{154.3} ≈ 5·10^{95}`, some 88 orders above the window.

So `s16_baseScaleCap96_L_supplied` is a correct reduction with an antecedent the flat regime
can never meet, and `RegisterSupply`'s `x`-window line is CLOSED, not merely stalled: the outer
scale is `log x ≈ 2·log 4·ε²·H₊` with `H₊` a tower whose `loglog` is `4^{(20/21)A}`-genre, so
`loglog(3x) ≈ exp(10^{95})` against a lever affording `3072·2^K·M ≈ 10^{9.6·10⁶}`.  No numeral
repair reaches it (the lever would need `K ≈ 10^{95}`).

⟦THE REDIRECT⟧ ⟦ITEM 3⟧ cannot be discharged through the regime's outer scale at all.  The
lossy step is the socket binder `(A : ℝ) ≤ 2·R.x` that `s16_baseScaleCap96_L_of_xwindow` reads
— the ONLY ceiling `SocketBaseL` puts on the base scale.  Either `SocketBaseL`'s other twelve
conjuncts pin `A + s` far below `3·R.x` (in which case W2 is a socket-side theorem, and this
file's §1–§2 exports are not on its path), or ⟦ITEM 3⟧ is false at the terminal's regime and
the cap must be re-cut.  That is a design ruling, not an executor's call; it is named here with
the arithmetic that forces it.
-/

namespace Salt.Entropy.Chowla

/-! ## §0 — the arithmetic leaves (division-free, so `linarith` sees shared atoms) -/

private lemma xceil_cube_ge {u : ℝ} (hu2 : 2 ≤ u) : (8 : ℝ) ≤ u ^ 3 := by
  have h4 : (4 : ℝ) ≤ u ^ 2 := by nlinarith [hu2]
  nlinarith [h4, mul_nonneg (by linarith : (0 : ℝ) ≤ u - 2) (sq_nonneg u)]

private lemma xceil_Ce_le {u c : ℝ} (hu2 : 2 ≤ u) (hc : c < 48 * u + 96 * u ^ 3 + 1) :
    c ≤ 109 * u ^ 3 := by
  have h4 : (4 : ℝ) ≤ u ^ 2 := by nlinarith [hu2]
  have h1 : (0 : ℝ) ≤ u * (u ^ 2 - 4) := mul_nonneg (by linarith) (by linarith)
  nlinarith [h1, hu2]

private lemma xceil_sum_le {B Q E p c : ℝ} (hB : 1 ≤ B) (hQ : 1 ≤ Q) (hE : 8 ≤ E)
    (hp : p ≤ Q) (hc : c ≤ 109 * E) : 8 * B + 8 * p + c ≤ 600 * (B * (Q * E)) := by
  have hQE : (8 : ℝ) ≤ Q * E := by nlinarith [hQ, hE]
  have hBE : (8 : ℝ) ≤ B * E := by nlinarith [hB, hE]
  have hBQ : (1 : ℝ) ≤ B * Q := by nlinarith [hB, hQ]
  have ha : 8 * B ≤ 200 * (B * (Q * E)) := by nlinarith [hQE, hB]
  have hb : 8 * p ≤ 200 * (B * (Q * E)) := by nlinarith [hBE, hQ, hp]
  have hd : c ≤ 200 * (B * (Q * E)) := by nlinarith [hBQ, hE, hc]
  linarith

/-- `⌈t/L⌉₊·L ≤ B + L` for any upper bound `B ≥ t` with `B ≥ 0` — the ceiling exponent's
one-step price, valid at negative `t` too (where the ceiling is `0`). -/
private lemma xceil_ceil_step {t B L : ℝ} (hL : 0 < L) (htB : t ≤ B) (hB : 0 ≤ B) :
    ((⌈t / L⌉₊ : ℕ) : ℝ) * L ≤ B + L := by
  by_cases h : t / L ≤ 0
  · rw [Nat.ceil_eq_zero.mpr h]
    push_cast
    linarith
  · have h' : (0 : ℝ) < t / L := not_le.mp h
    have hlt : ((⌈t / L⌉₊ : ℕ) : ℝ) < t / L + 1 := Nat.ceil_lt_add_one (le_of_lt h')
    have hmul : ((⌈t / L⌉₊ : ℕ) : ℝ) * L ≤ (t / L + 1) * L :=
      mul_le_mul_of_nonneg_right (le_of_lt hlt) (le_of_lt hL)
    rw [add_mul, div_mul_cancel₀ t (ne_of_gt hL), one_mul] at hmul
    linarith

/-- The ceiling's closing accounting: the debris `5·λ + 67·u + 7` is absorbed by
`14·(u·λ)` at `λ ≥ 14`, `u ≥ 2`. -/
private lemma xceil_arith {u l lP lK lw : ℝ} (hu2 : 2 ≤ u) (hl14 : 14 ≤ l)
    (hlw : lw ≤ 16 * (u * l) + 64 * u + 1 + 2 * (l + 1))
    (hlK : lK ≤ 6.94 + 3 * l + 2 * lP + 3 * (u - 1)) :
    lK + lw ≤ 30 * (u * l) + 2 * lP := by
  have h1 : 2 * l ≤ u * l := by nlinarith [hu2, hl14]
  have h2 : 14 * u ≤ u * l := by nlinarith [hu2, hl14]
  linarith

/-- The flat step: `30·(u·λ) + 2·lP ≤ 31·(u·H₊)` once `2·lP ≤ 0.694·H₊ + 1.39`. -/
private lemma xceil_flat_step {u H l lx lP : ℝ} (hu2 : 2 ≤ u) (hH : 4000000 ≤ H)
    (hlH : l ≤ H) (hx : lx ≤ 30 * (u * l) + 2 * lP)
    (hP : 2 * lP ≤ 0.694 * H + 1.39) : lx ≤ 31 * (u * H) := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h1 : u * l ≤ u * H := mul_le_mul_of_nonneg_left hlH hu0
  have h2 : 2 * H ≤ u * H := by nlinarith [hu2, hH]
  linarith

/-- The flat builder's own `P = 4^⌊ε²H₊⌋`, priced: `2·log(P+1) ≤ 0.694·H₊ + 1.39`. -/
private lemma xceil_flat_P {eps : ℚ} (heps : 0 < eps) (hhalf : (eps : ℝ) ≤ 1 / 2)
    (hepsR : (0 : ℝ) < (eps : ℝ)) {Hhi : ℕ} (hHhi : (4000000 : ℝ) ≤ (Hhi : ℝ)) :
    2 * Real.log (((4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1) ≤ 0.694 * (Hhi : ℝ) + 1.39 := by
  set n : ℕ := ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ with hndef
  have hnle : (n : ℝ) ≤ (eps : ℝ) ^ 2 * (Hhi : ℝ) := by
    have hQ : (n : ℚ) ≤ eps ^ 2 * (Hhi : ℚ) := by
      rw [hndef]; exact Nat.floor_le (by positivity)
    exact_mod_cast hQ
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hPcast : (((4 ^ n : ℕ) : ℝ)) = (4 : ℝ) ^ n := by push_cast; ring
  have hP1 : (1 : ℝ) ≤ (4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hlogP : Real.log (((4 ^ n : ℕ) : ℝ) + 1) ≤ Real.log 2 + (n : ℝ) * Real.log 4 := by
    have hstep : ((4 ^ n : ℕ) : ℝ) + 1 ≤ 2 * (4 : ℝ) ^ n := by rw [hPcast]; linarith
    have h2 : Real.log (((4 ^ n : ℕ) : ℝ) + 1) ≤ Real.log (2 * (4 : ℝ) ^ n) :=
      Real.log_le_log (by rw [hPcast]; linarith) hstep
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h2
  have hlog4 : Real.log 4 ≤ 1.3863 := by
    have h : Real.log ((4 : ℝ)) = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
    rw [h, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hlog2le : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]
  have heps2 : (eps : ℝ) ^ 2 ≤ 1 / 4 := by nlinarith [hhalf, hepsR]
  have hnH : (n : ℝ) ≤ (Hhi : ℝ) / 4 := by
    have h : (eps : ℝ) ^ 2 * (Hhi : ℝ) ≤ (1 / 4) * (Hhi : ℝ) :=
      mul_le_mul_of_nonneg_right heps2 (by linarith)
    linarith
  nlinarith [hlogP, hlog4, hlog2le, hnH, hnn]

/-! ## §1 — the outer-scale builder, with the ceiling kept -/

set_option maxHeartbeats 1000000 in
-- the landed proof's 25 `have`s plus the ceiling's log-arithmetic in one elaboration
/-- **THE OUTER SCALE, PRICED FROM ABOVE** (`regime_outer_param_ceiling`).  The additive twin
of `RegimeParam.regime_outer_param`: the same eight floors, plus the CEILING

  `log x ≤ (30/ε)·log H₊ + 2·log(P + 1)`

read off the construction the landed proof discards.  The three inputs are
`N ≤ RHS/log(H₊+2) + 2`, `log(H₊+2) ≤ log H₊ + 1` and `K ≤ 600·H₊³·(P+1)²/ε³`; the slack
`(14/ε − 5)·log H₊ ≥ 196/ε − 70` absorbs the additive debris at `log H₊ ≥ 14`, `1/ε ≥ 2`. -/
lemma regime_outer_param_ceiling (eps : ℚ) (heps : 0 < eps) (heps1 : eps ≤ 1 / 2)
    (Hhi P : ℕ) (hHhi : 4000000 ≤ Hhi) :
    ∃ x ω : ℕ, 2 ≤ x ∧ 2 ≤ ω ∧ ω ≤ x ∧ Hhi ≤ x / ω ∧
      8 * (Hhi : ℝ) * Real.log Hhi * Real.log Hhi ≤ ((x / ω : ℕ) : ℝ) ∧
      8 * (P : ℝ) ^ 2 * (ω : ℝ) ≤ (x : ℝ) ∧
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1
        ≤ Real.log (ω : ℝ) ∧
      (ω : ℝ) * (Hhi : ℝ) + 48 * (ω : ℝ) * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ)
        ≤ (x : ℝ) ∧
      Real.log (x : ℝ)
        ≤ 30 / (eps : ℝ) * Real.log (Hhi : ℝ) + 2 * Real.log ((P : ℝ) + 1) := by
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
  have hlogωeq : Real.log (ω : ℝ) = (N : ℝ) * LG := by
    have hcast : (ω : ℝ) = ((Hhi : ℝ) + 2) ^ N := by rw [hωdef]; push_cast; ring
    rw [hcast, Real.log_pow, ← hLGdef]
  -- the window coupling `hωbig`, via the ceiling
  have homega : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1
      ≤ Real.log (ω : ℝ) := by
    set RHS : ℝ :=
      (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1 with hRdef
    have hNge : RHS / LG ≤ (N : ℝ) := by
      have hce := Nat.le_ceil (RHS / LG)
      have hNR : (N : ℝ) = (⌈RHS / LG⌉₊ : ℝ) + 1 := by rw [hNdef, hRdef]; push_cast; ring
      rw [hNR]; linarith
    have hkey : RHS ≤ (N : ℝ) * LG := by
      have h2 : RHS / LG * LG ≤ (N : ℝ) * LG :=
        mul_le_mul_of_nonneg_right hNge (le_of_lt hLGpos)
      rwa [div_mul_cancel₀ RHS (ne_of_gt hLGpos)] at h2
    rw [hlogωeq]; exact hkey
  -- the outer-scale headroom facts, using the VALUE of K, before clearing `^N`
  have hCe : 48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) ≤ (Ce : ℝ) := by
    rw [hCedef]; exact Nat.le_ceil _
  have hKR : ((K : ℕ) : ℝ) = 8 * (Hhi : ℝ) ^ 3 + 8 * (P : ℝ) ^ 2 + (Ce : ℝ) := by
    rw [hKdef]; push_cast; ring
  have hHhiK : Hhi ≤ K := by
    rw [hKdef]; nlinarith [hcube, Nat.zero_le (P ^ 2), Nat.zero_le Ce]
  have hK1 : 1 ≤ K := le_trans (by omega) hHhiK
  -- ⟦THE CEILING⟧ the same construction, read from above
  have h2q : (2 : ℚ) * eps ≤ 1 := by linarith
  have h2r : (2 : ℝ) * (eps : ℝ) ≤ 1 := by exact_mod_cast h2q
  have hepsHalf : (eps : ℝ) ≤ 1 / 2 := by linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / (eps : ℝ) := ⟨_, rfl⟩
  have hupos : (0 : ℝ) < u := by rw [hudef]; exact div_pos one_pos hepsR
  have hu2 : (2 : ℝ) ≤ u := by rw [hudef, le_div_iff₀ hepsR]; linarith
  have hl14 : (14 : ℝ) ≤ Real.log (Hhi : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ (21 : ℕ)) ≤ Real.log (Hhi : ℝ) :=
      Real.log_le_log (by norm_num) (by norm_num; linarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith [Real.log_two_gt_d9]
  -- `log(H₊ + 2) ≤ log H₊ + 1`
  have hLGle : LG ≤ Real.log (Hhi : ℝ) + 1 := by
    have hemul : (2.7182818283 : ℝ) * (Hhi : ℝ) ≤ Real.exp 1 * (Hhi : ℝ) :=
      mul_le_mul_of_nonneg_right (le_of_lt Real.exp_one_gt_d9) (le_of_lt hHhipos)
    have h1 : (Hhi : ℝ) + 2 ≤ Real.exp 1 * (Hhi : ℝ) := by linarith
    have h2 : Real.log ((Hhi : ℝ) + 2) ≤ Real.log (Real.exp 1 * (Hhi : ℝ)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hHhipos), Real.log_exp] at h2
    rw [hLGdef]; linarith
  -- `log ω ≤ 16·(u·log H₊) + 64·u + 1 + 2·log(H₊+2)`
  have hbridgeRHS : (16 / (eps : ℝ)) * Real.log (Hhi : ℝ) + 64 / (eps : ℝ) + 1
      = 16 * (u * Real.log (Hhi : ℝ)) + 64 * u + 1 := by rw [hudef]; ring
  have hRHSle : (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) + 64 / (eps : ℝ) + 1
      ≤ 16 * (u * Real.log (Hhi : ℝ)) + 64 * u + 1 := by
    have hle : Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) ≤ Real.log (Hhi : ℝ) := by
      refine Real.log_le_log (by positivity) ?_
      have heps2 : (eps : ℝ) ^ 2 ≤ 1 := by nlinarith [hepsHalf, hepsR]
      nlinarith [heps2, hHhipos]
    have h16 : (16 : ℝ) / (eps : ℝ) = 16 * u := by rw [hudef]; ring
    have h64 : (64 : ℝ) / (eps : ℝ) = 64 * u := by rw [hudef]; ring
    have hstep : 16 * u * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ)) ≤ 16 * u * Real.log (Hhi : ℝ) :=
      mul_le_mul_of_nonneg_left hle (by linarith)
    rw [h16, h64]
    linarith [hstep]
  have hRHSnn : (0 : ℝ) ≤ 16 * (u * Real.log (Hhi : ℝ)) + 64 * u + 1 := by
    have : (0 : ℝ) ≤ u * Real.log (Hhi : ℝ) := mul_nonneg (by linarith) (by linarith)
    linarith
  have hlogωle : Real.log (ω : ℝ)
      ≤ 16 * (u * Real.log (Hhi : ℝ)) + 64 * u + 1 + 2 * (Real.log (Hhi : ℝ) + 1) := by
    have hce := xceil_ceil_step (t := (16 / (eps : ℝ)) * Real.log ((eps : ℝ) ^ 2 * (Hhi : ℝ))
      + 64 / (eps : ℝ) + 1) (B := 16 * (u * Real.log (Hhi : ℝ)) + 64 * u + 1) (L := LG)
      hLGpos hRHSle hRHSnn
    rw [hlogωeq, hNdef]
    push_cast
    linarith [hce, hLGle]
  -- `K ≤ 600·H₊³·(P+1)²·u³`
  have hB1 : (1 : ℝ) ≤ (Hhi : ℝ) ^ 3 := by nlinarith [hHhiR]
  have hQ1 : (1 : ℝ) ≤ ((P : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hE8 : (8 : ℝ) ≤ u ^ 3 := xceil_cube_ge hu2
  have hPQ : ((P : ℝ)) ^ 2 ≤ ((P : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) P]
  have hCeE : (Ce : ℝ) ≤ 109 * u ^ 3 := by
    have hCeb : (Ce : ℝ) < 48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) + 1 := by
      rw [hCedef]; exact Nat.ceil_lt_add_one (by positivity)
    have heq : 48 * (1 + 2 / (eps : ℝ) ^ 2) / (eps : ℝ) = 48 * u + 96 * u ^ 3 := by
      rw [hudef]; field_simp; ring
    rw [heq] at hCeb
    exact xceil_Ce_le hu2 hCeb
  have hKbound : ((K : ℕ) : ℝ)
      ≤ 600 * ((Hhi : ℝ) ^ 3 * (((P : ℝ) + 1) ^ 2 * u ^ 3)) := by
    rw [hKR]
    exact xceil_sum_le hB1 hQ1 hE8 hPQ hCeE
  have hlogKle : Real.log ((K : ℕ) : ℝ)
      ≤ 6.94 + 3 * Real.log (Hhi : ℝ) + 2 * Real.log ((P : ℝ) + 1) + 3 * (u - 1) := by
    have hKpos : (0 : ℝ) < ((K : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hK1
      linarith
    have hstep : Real.log ((K : ℕ) : ℝ)
        ≤ Real.log (600 * ((Hhi : ℝ) ^ 3 * (((P : ℝ) + 1) ^ 2 * u ^ 3))) :=
      Real.log_le_log hKpos hKbound
    have hH0 : ((Hhi : ℝ) ^ 3) ≠ 0 := pow_ne_zero 3 (ne_of_gt hHhipos)
    have hP0 : (((P : ℝ) + 1) ^ 2) ≠ 0 := pow_ne_zero 2 (by positivity)
    have hU0 : (u ^ 3) ≠ 0 := pow_ne_zero 3 (ne_of_gt hupos)
    have hdec : Real.log (600 * ((Hhi : ℝ) ^ 3 * (((P : ℝ) + 1) ^ 2 * u ^ 3)))
        = Real.log 600 + 3 * Real.log (Hhi : ℝ) + 2 * Real.log ((P : ℝ) + 1)
          + 3 * Real.log u := by
      rw [Real.log_mul (by norm_num) (mul_ne_zero hH0 (mul_ne_zero hP0 hU0)),
        Real.log_mul hH0 (mul_ne_zero hP0 hU0), Real.log_mul hP0 hU0,
        Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      ring
    have hlog600 : Real.log 600 ≤ 6.94 := by
      have h : Real.log (600 : ℝ) ≤ Real.log ((2 : ℝ) ^ (10 : ℕ)) :=
        Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h
      push_cast at h
      linarith [Real.log_two_lt_d9]
    have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos
    rw [hdec] at hstep
    linarith [hstep, hlog600, hlogu]
  have hxceil : Real.log (((K * ω : ℕ) : ℝ))
      ≤ 30 / (eps : ℝ) * Real.log (Hhi : ℝ) + 2 * Real.log ((P : ℝ) + 1) := by
    have hsplit : Real.log (((K * ω : ℕ) : ℝ))
        = Real.log ((K : ℕ) : ℝ) + Real.log ((ω : ℕ) : ℝ) := by
      push_cast
      exact Real.log_mul (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    have hcore := xceil_arith hu2 hl14 hlogωle hlogKle
    have hbridge : (30 : ℝ) / (eps : ℝ) * Real.log (Hhi : ℝ)
        = 30 * (u * Real.log (Hhi : ℝ)) := by rw [hudef]; ring
    rw [hsplit]
    linarith [hcore, hbridge]
  -- clear the degree-`N` equation so `nlinarith`/`omega` see only opaque fvars
  clear hωdef hNdef hlogωeq
  refine ⟨K * ω, ω, ?_, hω2, ?_, ?_, ?_, ?_, homega, ?_, hxceil⟩
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

/-! ## §2 — the flat builder, with the ceiling threaded -/

set_option maxHeartbeats 1000000 in
-- the 30-field `ChowlaRegimeFlat` structure instance is checked in one `refine`
/-- **THE FLAT BUILDER WITH THE OUTER-SCALE CEILING** — `chowlaRegimeFlat_exists_param_gen`
plus the endpoint-only ceiling `log R.x ≤ (31/ε)·R.H₊`.  The step from §1's `P`-shaped ceiling
is the builder's own instantiation `P = 4^⌊ε²H₊⌋`:
`2·log(P+1) ≤ 2·log 2 + 2·⌊ε²H₊⌋·log 4 ≤ 1.39 + 0.694·H₊` at `ε ≤ 1/2`. -/
theorem chowlaRegimeFlat_exists_param_gen_ceiling (A : ℝ) (hA : 26 ≤ A) (eps : ℚ)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
  classical
  have hA1 : (1 : ℝ) ≤ A := by linarith
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
  -- ⟦THE RE-BASED BASE⟧
  obtain ⟨Hlo, hHlodef⟩ : ∃ Hlo : ℕ,
      Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * m ^ 4)) := ⟨_, rfl⟩
  have hHloDF : flatDesignFloor A ≤ Hlo := by rw [hHlodef]; exact le_max_left _ _
  have hHlo_floor : 4000000 ≤ Hlo := le_trans (flatDesignFloor_house A) hHloDF
  have hHlo0 : Hlo₀ ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hHlo4 : 4 * m ^ 4 ≤ Hlo := by
    rw [hHlodef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hHlo4Q : (4 : ℚ) * (m : ℚ) ^ 4 ≤ (Hlo : ℚ) := by exact_mod_cast hHlo4
  have hHlo4R : (4 : ℝ) * (m : ℝ) ^ 4 ≤ (Hlo : ℝ) := by exact_mod_cast hHlo4
  have hHlocap : Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) := by
    rw [hHlodef, hmdef]
  -- ⟦THE DESIGN LAW⟧ and the two floors it and `flatBase` supply
  have hflat : 3.2 * A ≤ Real.log (Real.log (Hlo : ℝ)) := flatDesignFloor_design hHloDF
  have hfl : 100 * (flatC A + Real.log (Real.log (Hlo : ℝ))) ≤ Real.log (Hlo : ℝ) :=
    flatFloor_of_design hA hHlo_floor hflat
  have h50 : (50 : ℝ) ≤ Real.log (Real.log (Hlo : ℝ)) := by linarith
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
  -- ⟦THE TWO TOWERS⟧ at their minimal crossings, and the endpoint that hosts both
  obtain ⟨J, hJdef⟩ : ∃ J : ℕ, J = towerJmin 2 1 Hlo := ⟨_, rfl⟩
  obtain ⟨Jf, hJfdef⟩ : ∃ Jf : ℕ, Jf = towerFlatJmin A 1 Hlo := ⟨_, rfl⟩
  have hJ : Real.log 2 < towerDropSum 2 1 Hlo J := by
    rw [hJdef]; exact towerJmin_spec hHlo_floor
  have hJf : Real.log 2 < towerDropSumFlat A 1 Hlo Jf := by
    rw [hJfdef]; exact towerFlatJmin_spec hA1 hHlo_floor hfl
  obtain ⟨Hhi, hHhidef⟩ : ∃ Hhi : ℕ,
      Hhi = max (chowlaTower 2 1 Hlo J) (chowlaTowerFlat A 1 Hlo Jf) := ⟨_, rfl⟩
  have hfitL : chowlaTower 2 1 Hlo J ≤ Hhi := by rw [hHhidef]; exact le_max_left _ _
  have hfitFl : chowlaTowerFlat A 1 Hlo Jf ≤ Hhi := by rw [hHhidef]; exact le_max_right _ _
  have hHlohi : Hlo ≤ Hhi := le_trans (chowlaTower_base_ge hHlo_floor J) hfitL
  have hHhi_floor : 4000000 ≤ Hhi := le_trans hHlo_floor hHlohi
  -- ⟦THE WIDTH EXPORT⟧ at the flat shape, on both arms of the endpoint
  have hwidth : Real.log (Real.log (Hhi : ℝ))
      ≤ Real.exp (Real.log (Real.log (Hlo : ℝ)) / 2) := by
    rw [hHhidef, hJdef, hJfdef]
    rcases le_total (chowlaTower 2 1 Hlo (towerJmin 2 1 Hlo))
        (chowlaTowerFlat A 1 Hlo (towerFlatJmin A 1 Hlo)) with h | h
    · rw [max_eq_right h]
      exact towerFlat_width_export hA hHlo_floor hflat
    · rw [max_eq_left h]
      exact le_trans (tower_loglog_le_45 hHlo_floor h50) (pow_nine_halves_le_exp_half h50)
  -- the outer scale at this `ε` and endpoint, WITH THE CEILING
  obtain ⟨x, ω, hx2, hω2, hωx, hhead, hhead', hPH, homega, hxb, hxceil⟩ :=
    regime_outer_param_ceiling eps heps heps1 Hhi (4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊) hHhi_floor
  -- ⟦THE CEILING AT THE BUILDER'S OWN `P`⟧
  have h2q : (2 : ℚ) * eps ≤ 1 := by linarith
  have h2r : (2 : ℝ) * (eps : ℝ) ≤ 1 := by exact_mod_cast h2q
  have hepsHalf : (eps : ℝ) ≤ 1 / 2 := by linarith
  have hHhiR : (4000000 : ℝ) ≤ (Hhi : ℝ) := by exact_mod_cast hHhi_floor
  have hHhipos : (0 : ℝ) < (Hhi : ℝ) := by linarith
  have hxceil' : Real.log ((x : ℕ) : ℝ) ≤ 31 / (eps : ℝ) * (Hhi : ℝ) := by
    obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / (eps : ℝ) := ⟨_, rfl⟩
    have hu2 : (2 : ℝ) ≤ u := by rw [hudef, le_div_iff₀ hepsR]; linarith
    have hbr30 : (30 : ℝ) / (eps : ℝ) * Real.log (Hhi : ℝ)
        = 30 * (u * Real.log (Hhi : ℝ)) := by rw [hudef]; ring
    have hbr31 : (31 : ℝ) / (eps : ℝ) * (Hhi : ℝ) = 31 * (u * (Hhi : ℝ)) := by
      rw [hudef]; ring
    have hxu : Real.log ((x : ℕ) : ℝ)
        ≤ 30 * (u * Real.log (Hhi : ℝ))
          + 2 * Real.log (((4 ^ ⌊eps ^ 2 * (Hhi : ℚ)⌋₊ : ℕ) : ℝ) + 1) := by
      linarith [hxceil, hbr30]
    have hPterm := xceil_flat_P heps hepsHalf hepsR hHhiR
    have hlogself : Real.log (Hhi : ℝ) ≤ (Hhi : ℝ) := Real.log_le_self (by linarith)
    have hfin := xceil_flat_step hu2 hHhiR hlogself hxu hPterm
    linarith [hfin, hbr31]
  refine ⟨{ x := x, ω := ω, a := 1, eps := eps, Hlo := Hlo, Hhi := Hhi, C0 := 2, J := J,
            hx := hx2, hω := hω2, hωx := hωx, ha := le_refl 1, heps := heps, heps1 := heps1,
            hHlo := le_trans (by norm_num) hHlo_floor, hHlohi := hHlohi, hC0 := le_refl 2,
            hHlo_floor := hHlo_floor, hheadroom := hhead, hcoprime := hcop, hfit := hfitL,
            hJcon := hJ, hheadroom' := hhead', hPHheadroom := hPH, hPNTwindow := hPNT,
            hωbig := homega, hxbig := hxb,
            A := A, hA := hA, hflat := hflat, Jf := Jf,
            hfitF := by simpa using hfitFl, hJconF := by simpa using hJf },
    rfl, rfl, hHlo0, hHlocap, hwidth, hxceil'⟩

/-- **THE HEAD-SHAPED FLAT BUILDER, WITH THE CEILING** — `chowlaRegimeFlat_exists_param_head`
plus the ceiling threaded through the outer-scale enlargement.  The enlargement is
`x ↦ max x (g H₊ ω)`, so the exported ceiling is the MAX of the builder's own closed form and
the caller's own `g` — the `g`-dependence is unavoidable, and is stated, not hidden. -/
theorem chowlaRegimeFlat_exists_param_head_ceiling (A : ℝ) (hA : 26 ≤ A) (eps : ℚ)
    (heps : 0 < eps) (heps1 : eps ≤ 1 / 2) (Hlo₀ : ℕ) (g : ℕ → ℕ → ℕ) :
    ∃ R : ChowlaRegimeFlat, R.eps = eps ∧ R.A = A ∧ Hlo₀ ≤ R.Hlo ∧
      g R.Hhi R.ω ≤ R.x ∧
      R.Hlo = max (flatDesignFloor A) (max Hlo₀ (4 * ⌈(1 / eps : ℚ)⌉₊ ^ 4)) ∧
      Real.log (Real.log (R.Hhi : ℝ))
        ≤ Real.exp (Real.log (Real.log (R.Hlo : ℝ)) / 2) ∧
      Real.log ((R.x : ℕ) : ℝ)
        ≤ max (31 / (eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
            (Real.log ((g R.Hhi R.ω : ℕ) : ℝ)) := by
  obtain ⟨R, hReps, hRA, hRHlo, hRcap, hRwid, hRx⟩ :=
    chowlaRegimeFlat_exists_param_gen_ceiling A hA eps heps heps1 Hlo₀
  refine ⟨regimeFlatEnlargeX R (le_max_left R.x (g R.Hhi R.ω)), hReps, hRA, hRHlo,
    le_max_right _ _, hRcap, hRwid, ?_⟩
  simp only [regimeFlatEnlargeX_x, regimeFlatEnlargeX_Hhi, regimeFlatEnlargeX_omega]
  rcases le_total R.x (g R.Hhi R.ω) with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h]; exact le_trans hRx (le_max_left _ _)

/-! ## §2b — the endpoint window is UNREACHABLE (the decisive lower bound) -/

/-- **⟦THE WINDOW IS FALSE, NOT UNPROVEN⟧** (`flat_endpoint_loglog_gt_lever`).
`towerFlat_width_ge` is the flat schedule's landed extremality LOWER bound: at any crossing
length `J`, `(log 2A + loglog H₋)·4^{(20/21)A} ≤ log 2A + loglog H_J`.  With the design law
`3.2A ≤ loglog H₋` and `A ≥ 162` this puts the endpoint's `loglog` above
`3.2·162·10^{10} ≈ 5·10^{12}` (a deliberately crude read of `4^{(20/21)A} ≥ 4^{100}`) — already
five orders above the lever window `K/2 = 1.6·10⁷` that
`s16_baseScaleCap96_L_supplied` asks for (the sharp value at `A = 162`, with the true exponent
`4^{154.3}`, is `≈ 5·10^{95}`).  The flat builder's endpoint dominates this arm (`hfitF`), so
NO flat regime at `A ≥ 162` satisfies the window. -/
theorem flat_endpoint_loglog_gt_lever {A : ℝ} (hA : 162 ≤ A) {B : ℕ} (hB : 4000000 ≤ B)
    (hfl : 100 * (flatC A + Real.log (Real.log (B : ℝ))) ≤ Real.log (B : ℝ))
    (hdesign : 3.2 * A ≤ Real.log (Real.log (B : ℝ)))
    {J : ℕ} (hJcon : Real.log 2 < towerDropSumFlat A 1 B J) :
    (32000000 : ℝ) / 2 < Real.log (Real.log (chowlaTowerFlat A 1 B J : ℝ)) := by
  have hA1 : (1 : ℝ) ≤ A := by linarith
  have hge := towerFlat_width_ge hA1 hB hfl hJcon
  rw [towerLamF_zero] at hge
  have hgoal : Real.log (Real.log (chowlaTowerFlat A 1 B J : ℝ)) = towerLamF A B J := rfl
  rw [hgoal]
  have hcpos : (0 : ℝ) < flatC A := flatC_pos hA1
  have hcle : flatC A ≤ 2 * A := Real.log_le_self (by linarith)
  have hS : 3.2 * A ≤ flatC A + Real.log (Real.log (B : ℝ)) := by linarith
  have hpow : (10000000000 : ℝ) ≤ (4 : ℝ) ^ ((20 / 21 : ℝ) * A) := by
    have h1 : ((100 : ℕ) : ℝ) ≤ (20 / 21 : ℝ) * A := by push_cast; linarith
    have h2 : (4 : ℝ) ^ ((100 : ℕ) : ℝ) ≤ (4 : ℝ) ^ ((20 / 21 : ℝ) * A) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    rw [Real.rpow_natCast] at h2
    have h3 : (10000000000 : ℝ) ≤ (4 : ℝ) ^ (100 : ℕ) := by norm_num
    linarith
  have hmul : 3.2 * A * 10000000000
      ≤ (flatC A + Real.log (Real.log (B : ℝ))) * (4 : ℝ) ^ ((20 / 21 : ℝ) * A) :=
    mul_le_mul hS hpow (by norm_num) (by linarith)
  have hnum : (32000000 : ℝ) / 2 + 2 * A < 3.2 * A * 10000000000 := by linarith
  linarith [hge, hmul, hnum, hcle]

end Salt.Entropy.Chowla

namespace Salt.MR

open Salt.Entropy.Chowla

/-! ## §3 — the base-scale cap, discharged from the ceiling -/

/-- **⟦THE CAP FROM THE CEILING⟧** (`s16_baseScaleCap96_L_of_xceil`).  §2's ceiling
`log R.x ≤ (31/ε)·H₊` turns `RegisterSupply`'s `x`-window into an ENDPOINT window:
`log(3x) ≤ (32/ε)·H₊`, hence `loglog(3x) ≤ log H₊ + log(1/ε) + log 32`.  So ⟦ITEM 3⟧ needs
only `log H₊ + log(1/ε) + 5 ≤ 𝒢K` — the endpoint, not the outer scale. -/
theorem s16_baseScaleCap96_L_of_xceil (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (hx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
    (hw : Real.log ((R.Hhi : ℕ) : ℝ) + Real.log (1 / (R.eps : ℝ)) + 5
      ≤ ((s13GK K M : ℕ) : ℝ)) :
    S16BaseScaleCap96_L_gk K R M := by
  refine s16_baseScaleCap96_L_of_x_small K hM ?_
  have hHhiN : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhiN
  have hHhipos : (0 : ℝ) < ((R.Hhi : ℕ) : ℝ) := by linarith
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have h2q : (2 : ℚ) * R.eps ≤ 1 := by linarith [R.heps1]
  have h2r : (2 : ℝ) * (R.eps : ℝ) ≤ 1 := by exact_mod_cast h2q
  have hupos : (0 : ℝ) < 1 / (R.eps : ℝ) := div_pos one_pos hepsR
  have hu2 : (2 : ℝ) ≤ 1 / (R.eps : ℝ) := by rw [le_div_iff₀ hepsR]; linarith
  have hx2 : (2 : ℝ) ≤ ((R.x : ℕ) : ℝ) := by exact_mod_cast R.hx
  have hxpos : (0 : ℝ) < ((R.x : ℕ) : ℝ) := by linarith
  have hbig : (2 : ℝ) * 4000000 ≤ 1 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) :=
    mul_le_mul hu2 hHhiR (by norm_num) (le_of_lt hupos)
  -- `log(3x) ≤ (32/ε)·H₊`
  have hbr31 : (31 : ℝ) / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)
      = 31 * (1 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) := by ring
  have hbr32 : (32 : ℝ) / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)
      = 32 * (1 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) := by ring
  have hlog3 : Real.log 3 ≤ 2 := by
    have h : Real.log (3 : ℝ) ≤ Real.log ((2 : ℝ) ^ (2 : ℕ)) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h
    push_cast at h
    linarith [Real.log_two_lt_d9]
  have hstep : Real.log (3 * ((R.x : ℕ) : ℝ)) ≤ 32 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)]
    linarith [hx, hbig, hlog3, hbr31, hbr32]
  have hlogpos : (1 : ℝ) < Real.log (3 * ((R.x : ℕ) : ℝ)) := by
    have h1 : Real.exp 1 < 3 * ((R.x : ℕ) : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.log (Real.exp 1) < Real.log (3 * ((R.x : ℕ) : ℝ)) :=
      Real.log_lt_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h2
  have hll : Real.log (Real.log (3 * ((R.x : ℕ) : ℝ)))
      ≤ Real.log (32 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ)) :=
    Real.log_le_log (by linarith) hstep
  have heq : Real.log (32 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
      = Real.log 32 + Real.log (1 / (R.eps : ℝ)) + Real.log ((R.Hhi : ℕ) : ℝ) := by
    rw [hbr32, Real.log_mul (by norm_num)
        (mul_ne_zero (ne_of_gt hupos) (ne_of_gt hHhipos)),
      Real.log_mul (ne_of_gt hupos) (ne_of_gt hHhipos)]
    ring
  have hlog32 : Real.log 32 ≤ 5 := by
    have h : Real.log ((32 : ℝ)) = Real.log ((2 : ℝ) ^ (5 : ℕ)) := by norm_num
    rw [h, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  linarith [hll, heq.le, heq.ge, hlog32, hw]

/-- **⟦THE CAP, SUPPLIED⟧** (`s16_baseScaleCap96_L_supplied`).  ⟦ITEM 3⟧ at the linear door and
socket from THREE facts about the regime: the outer-scale ceiling of §2, the terminal's own
`ε ≥ 1/500`, and ONE endpoint window stated at the lever's own numeral,

  `loglog R.Hhi ≤ K/2`.

At `K = 32000000` the window admits every endpoint below `exp exp (1.6·10⁷)`.  The proof is
`log H₊ = exp(loglog H₊) ≤ exp(K/2) ≤ 2^K`, against `𝒢K = 3072·2^K·M ≥ 2^K + 3071`. -/
theorem s16_baseScaleCap96_L_supplied (K : ℕ) {R : ChowlaRegime} {M : ℕ} (hM : 1 ≤ M)
    (heps500 : (1 : ℚ) / 500 ≤ R.eps)
    (hx : Real.log ((R.x : ℕ) : ℝ) ≤ 31 / (R.eps : ℝ) * ((R.Hhi : ℕ) : ℝ))
    (hHhi : Real.log (Real.log ((R.Hhi : ℕ) : ℝ)) ≤ (K : ℝ) / 2) :
    S16BaseScaleCap96_L_gk K R M := by
  refine s16_baseScaleCap96_L_of_xceil K hM hx ?_
  have hHhiN : 4000000 ≤ R.Hhi := le_trans R.hHlo_floor R.hHlohi
  have hHhiR : (4000000 : ℝ) ≤ ((R.Hhi : ℕ) : ℝ) := by exact_mod_cast hHhiN
  have hepsR : (0 : ℝ) < (R.eps : ℝ) := by exact_mod_cast R.heps
  have hupos : (0 : ℝ) < 1 / (R.eps : ℝ) := div_pos one_pos hepsR
  -- the `ε`-term
  have h5q : (1 : ℚ) ≤ 500 * R.eps := by linarith
  have h5r : (1 : ℝ) ≤ 500 * (R.eps : ℝ) := by exact_mod_cast h5q
  have hinv500 : 1 / (R.eps : ℝ) ≤ 500 := by rw [div_le_iff₀ hepsR]; linarith
  have hinvle : Real.log (1 / (R.eps : ℝ)) ≤ 7 := by
    have h : Real.log (1 / (R.eps : ℝ)) ≤ Real.log ((2 : ℝ) ^ (9 : ℕ)) := by
      refine Real.log_le_log hupos ?_
      rw [show ((2 : ℝ) ^ (9 : ℕ)) = 512 by norm_num]
      linarith
    rw [Real.log_pow] at h
    push_cast at h
    linarith [Real.log_two_lt_d9]
  -- the endpoint term
  have hlogHhipos : (0 : ℝ) < Real.log ((R.Hhi : ℕ) : ℝ) := by
    have h : Real.log 1 < Real.log ((R.Hhi : ℕ) : ℝ) :=
      Real.log_lt_log one_pos (by linarith)
    simpa using h
  have hlogHhi_le : Real.log ((R.Hhi : ℕ) : ℝ) ≤ Real.exp ((K : ℝ) / 2) := by
    calc Real.log ((R.Hhi : ℕ) : ℝ)
        = Real.exp (Real.log (Real.log ((R.Hhi : ℕ) : ℝ))) := (Real.exp_log hlogHhipos).symm
      _ ≤ Real.exp ((K : ℝ) / 2) := Real.exp_le_exp.mpr hHhi
  -- `exp (K/2) ≤ 2^K`
  have h2K : (2 : ℝ) ^ K = Real.exp ((K : ℝ) * Real.log 2) := by
    conv_rhs => rw [← Real.log_pow]
    exact (Real.exp_log (by positivity)).symm
  have hexp2K : Real.exp ((K : ℝ) / 2) ≤ (2 : ℝ) ^ K := by
    rw [h2K]
    refine Real.exp_le_exp.mpr ?_
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
    nlinarith [Real.log_two_gt_d9, hKnn]
  have h2Kpos : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hGK : ((s13GK K M : ℕ) : ℝ) = 3072 * (2 : ℝ) ^ K * (M : ℝ) := by
    rw [s13GK]; push_cast; ring
  have hGKlb : 3072 * (2 : ℝ) ^ K ≤ ((s13GK K M : ℕ) : ℝ) := by
    rw [hGK]
    nlinarith [hM1, h2Kpos]
  linarith [hlogHhi_le, hexp2K, hinvle, hGKlb, h2Kpos]

/-- **⟦THE MISS, PINNED⟧** (`flatA_endpoint_ceiling_misses_K_half`).  The terminal's own
endpoint ceiling is `loglog R.Hhi ≤ 2·exp(3.2A/2)` at `A ≥ 162`;
`s16_baseScaleCap96_L_supplied` asks for `≤ K/2`.  At the terminal's lever `K = 32000000` the
two do not meet — and not narrowly: `2·e^{259.2} ≈ 3.7·10^{112}` against `1.6·10⁷`.  This is
the residual named in the module header: ⟦ITEM 3⟧ is true at the terminal's parameters and
unreachable from the landed width laws. -/
theorem flatA_endpoint_ceiling_misses_K_half :
    (32000000 : ℝ) / 2 < 2 * Real.exp (3.2 * 162 / 2) := by
  have h1 : (65.8 : ℝ) ≤ Real.exp 64.8 := by linarith [Real.add_one_le_exp (64.8 : ℝ)]
  have hpos : (0 : ℝ) < Real.exp 64.8 := Real.exp_pos _
  have h2 : Real.exp (3.2 * 162 / 2)
      = Real.exp 64.8 * Real.exp 64.8 * (Real.exp 64.8 * Real.exp 64.8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  have hsq : (65.8 : ℝ) * 65.8 ≤ Real.exp 64.8 * Real.exp 64.8 := by nlinarith [h1, hpos]
  rw [h2]
  nlinarith [hsq]

end Salt.MR
