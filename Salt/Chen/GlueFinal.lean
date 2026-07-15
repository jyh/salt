/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.Assembly
import Salt.Chen.GlueNormalized
import Salt.Chen.SqrtDFold
import Salt.Chen.WindowMembership

/-!
# GLU-2 — the operating-point package: STEP 0 inventory, ★ CATCH #64 ★, and the F1 row bundle

Design: the H-glue discharge map (`docs/blueprints/chen.md`) and the GLU-1/GLU-2 boundary
(`Salt/Chen/RazorClose.lean`, `Salt/Chen/GlueNormalized.lean`).  This node's mandate was the
full H-package of `chen_of_hypotheses` (`Salt/Chen/Assembly.lean`) at the operating point —
`chen_headline`.  STEP 0 (the mandated obligation inventory, below) found the windowed-BV
terminal's threshold list **jointly unsatisfiable at every boundary box of the operating
point** (CATCH #64, machine-checked in Part 1), so the summit and the F2 floor
(`hBVblocks_at_op` → the `hA3` line) are BLOCKED pending a Fable-tier statement repair.
This file lands the catch as Lean theorems plus the F1 numeric-row bundle (Part 2).

## STEP 0 — the obligation inventory (from the LANDED docstrings, in mandate order)

The H-package per threshold `X` (at `x := max x₀ (2X + 2)`, `z = ⌊x^{1/8}⌋`, `y = ⌊x^{1/3}⌋`,
`D = ⌊x^{1/2−9/10⁵}⌋`, `Dlev ~ x^{1/2}`, `P = ∏_{p<z} p`, `Ps = ∏_{w₀≤p<y} p`):

| # | slot (consumer) | supplier chain | status after STEP 0 |
|---|---|---|---|
| 1 | `X ≤ x/2`, `2 ≤ x`, `2 ≤ z` | arithmetic at `x = max x₀ (2X+2)` | row (F2) |
| 2 | `hyx : x < (y+1)³` (`chen_of_hypotheses`) | floor bracketing | **LANDED** (`hyx_at_op`) |
| 3 | `hPfull` (`chen_positivity`) | `P = ∏_{p<z} p` | **LANDED** (`sievePrimorial_dvd`) |
| 4 | `hA1 : mainA1 ≤ A1primeSum` | `TwinSharp.twin_A1_lower_B` + `SuperClose.fchain_A1_final` ∘ `WindowMembership.logRatio_A1_mem` + `WLower.W_twinA1_ge` | razor side, open (F2) |
| 5 | `hA2 : omegaPrimeSum ≤ mainA2` | `TwinA2.twin_A2_upper` + `A2Weighted.A2grid_sharp_le` at `Cmass = 43/75` | razor side, open (F2) |
| 6 | `hA3 : triplePrimeSum ≤ mainA3` | `SwitchBlocks.mainA3_of_block_remainders` ← `hBVblocks` ← (`SqrtDFold.hNum_at_op_sqrtD` → `hBlock_of_window_prices` → `hHDblocks_of_perBlock` → `hBVblocks_of_generalBV`) with per-box prices from `medium_survivor_price_sqrtD` | ★ **BLOCKED — CATCH #64** ★ |
| 7 | `hledger` | `GlueNormalized.normalized_package` → `RazorClose.hledger_at_certs`; open slot `hEbundle ≤ 1/200` (errors `O(1/log z)`, `W_twinA1_ge` for the `R/X_W` crumbs) | razor side, open (F2) |
| 8 | `hw0`-guards (`Hyp4`, `w0R ε = exp(40/log(1+ε))`, `ε = 2·10⁻⁸ ⇒ w0R ≈ exp(2·10⁹)`) | `z = x^{1/8} ≥ w0R ε` at `log x₀ ≥ 1.6·10^{10}` | row (F2; sets the `x₀` scale) |
| 9 | `hDsq : D < (N+1)²` (`general_BV_cutoff_sqrtD` via `hDsq_of_carrier_floor`) | numeric row `D < (y+1)²` | **LANDED** (`hDsq_row`) |
| 10 | `habs : 4(1+log D)·D ≤ N·M/L^A` | numeric row at `N·M ≥ x^{7/8}/8` (boundary pieces) | **LANDED** (numeric core, `habs_row`) |
| 11 | `hfloor : (3/log2)⁸·x^{1/6}·Lb^{A+5} ≤ √F`, `F = z·y`, `Lb = log 4x` (`medium_survivor_price_sqrtD`) | numeric row | **LANDED** (`hfloor_row`, at `A = 13`) |
| 12 | `logRatio` memberships (M4F) | `logRatio_A1_mem` / `logRatio_A3_mem` (landed) + the shifted-`Dlev` variant needed by the level rows (finding 2 below) | **LANDED** (`logRatio_A3_mem_range`) |
| 13 | the per-box `D0`-window rows (`hD0lo_main`, `hD0N'`, per-`e` `herr_D0E`) | — | ★ **INFEASIBLE — CATCH #64** ★ |
| 14 | `hSum`/`hNum`/`hiX` budget rows (`Kerr = 2^{A+5}·Kβ′ + 15360 + 1`) | blocked behind #13 | blocked |
| 15 | `hCE` (`GlueBV.hCE_discharge`'s `hcount` residual) | `w₀`-scale crude count | open (F2, behind #13) |

## ★ CATCH #64 — the `D0`-window of the windowed-BV terminal is EMPTY at every boundary box ★

Every landed terminal variant (`WindowSmallChi.general_BV_cutoff_unconditional`,
`GlueBV.cutoff_BV_at_op`, `SqrtDFold.general_BV_cutoff_sqrtD`/`general_BV_cutoff_closed_sqrtD`,
`MediumFloor.medium_survivor_price`, `SqrtDFold.medium_survivor_price_sqrtD`) hypothesizes,
for the SAME `C0` (with `hCge : A + 2 ≤ C0` and `hA : 0 < A`, hence `C0 > 2`):

* `hD0lo_main : L^{C0} ≤ 2·2^{k0}` — i.e. `D0 = 2^{k0} ≥ L^{C0}/2`, where `L = log(X·M)`
  (consumed by `EnergyClose.four_term_scale_le`'s T4 tail `√(13(X+1))·√(13(M+1))·(2/2^{k0})`);
* `hD0N' : D0 ≤ (log N)^{C0}` — the SW small-conductor range at the block-prime scale `N`
  (consumed by `WindowSmallChi.hSmallCut_discharge` → `interval_prime_twist_SW`).

Jointly: `(L / log N)^{C0} ≤ 2`, i.e. `log N ≥ L/2^{1/C0} > L/√2 ≈ 0.707·L`.

But at the operating point the ONLY boxes needing an analytic price are the `dyadicBoundary`
survivors (`MediumFloor.box_disc_three_way`; all other sub-boxes cancel), and membership
`i ∈ dyadicBoundary N M (x/2+1) x (z·y) K` FORCES both
* `X·M > x/2` (clause 3, `X = 2^{i+1}−1`, the catch-#61 level resolution), so
  `L > log x − log 2`, and
* `(N+1)·(z·y) < 2x` (clauses 1+2), so with `z·y ≥ x^{11/24}/4` (the operating floors)
  `N < 8·x^{13/24}`, i.e. `log N < log 8 + (13/24)·log x ≈ 0.5417·log x`.

Hence `log N / L → 13/24 ≈ 0.5417 < 0.707 ≤ 1/2^{1/C0}` — the window
`[L^{C0}/2, (log N)^{C0}]` for `D0` is EMPTY, **for every** `C0 > 2` (so for every `A > 0`,
before the budget's `A ≥ 12` even enters), **at every** `x ≥ e^{200}` (the deficit is the
asymptotically constant factor `2·(13/24 + o(1))^{C0} < 2·(14/25)² = 392/625 < 1`; at the
concrete `A = 12, C0 = 14, log x = 2·10^{10}` it is `≈ 2680×`).  No choice of `x₀`, `A`,
`C0`, `B`, `D0`, `Dlev` or piece re-indexing repairs it: `N ≤ x^{13/24}`-scale is forced by
the cutoff (`m·n ≤ x`, `m ≥ z·y`) and `X·M > x/2` by the honest-difference boundary.  The
per-`e` row `herr_D0E : D0 ≤ (log⌊X/e⌋·M)^{C0}` pinches even harder (at `e ~ D` the dilated
log is `≈ L/2`).

**Root cause and the (Fable-tier) repair.**  `four_term_scale_le` only NEEDS
`D0 ≥ L^{A+2}/2` (its use of `hD0lo` is `2/2^{k0} ≤ 4/L^{C0} ≤ 4/L^{A+2}`), but the landed
STATEMENT demands the full `L^{C0} ≤ 2·2^{k0}` with the SW exponent `C0`.  Decoupling the two
exponents (`hD0lo` at `A + 2`, keeping `hD0N'` at `C0`, choosing e.g. `C0 ≥ A + 5`) restores
a nonempty window `D0 ∈ [L^{A+2}/2, ((7/16)·log x)^{C0}]` with power-of-`log` room:
`GBV3`'s STEP 0 (the `TransposedBV` header) had already silently used this `A+4`-shaped
reading ("T4 … cleared by the D0 cut `2^{k0} ≥ L^{A+4}`").  Statement changes to the landed
`four_term_scale_le` → `hMainEnergy_cutoff_discharge` → `general_BV_cutoff_final` →
`…_closed`/`…_unconditional`/`…_sqrtD` chain are Iron-Rule-1 / Fable-tier; NOT attempted here.

**Finding 2 (resolvable, no statement change needed).**  The M4F convention
`Dlev = ⌊x^{1/2}⌋` violates the box-level rows `hDscale : D ≤ √(X·M)/L^B` and
`herr_lev : D·L^{A+5} ≤ √(X·M)` at boundary boxes (`√(X·M) ≤ 2√x` but `D ~ Q·Dlev ~ √x`,
deficit `L^B`).  `Dlev` must sit a polylog BELOW `√x`; the switch-window value certificate
tolerates it — `logRatio_A3_mem_range` (landed below) gives membership in
`[149/100, 151/100]` for EVERY `Dlev ∈ [x^{497/1000}, x^{1/2}]`, which contains
`√x/L^{B+…}` for all large `x`.  Use it in place of `logRatio_A3_mem` after the catch-#64
repair.

## What this file lands (sorry-free, axiom-clean; NEW file, no landed file touched)

* **Part 1 — CATCH #64, machine-checked**: `catch64_D0_window_empty` (the pure-parameter
  pinch), `catch64_L_bound`/`catch64_logN_bound`/`catch64_ratio_at_op` (the boundary-box
  scale extraction), `catch64_no_admissible_D0` (assembled), `zy_floor_ge`/`zy_floor_pos`
  (the operating `z·y` floor), and the headline `catch64_op_boundary_infeasible`: at the
  operating point, ANY `dyadicBoundary` application of the terminal's `D0` rows is `False`.
* **Part 2 — the F1 numeric rows** (each its own lemma, explicit margins in comments):
  `hyx_at_op`, `sievePrimorial`/`sievePrimorial_dvd`, `hDsq_row` (room `x^{1/9}`),
  `hfloor_row` (room `x^{1/16}`, threshold `e^{4000}`), `habs_row` (room `x^{0.3}`),
  `logRatio_A3_mem_range` (the shifted-`Dlev` membership, threshold `10⁴⁸`).

No `sorry`, no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Real

/-! ## Part 0 — shared numeric helpers -/

/-- `⌊t⌋ ≥ t/2` once `t ≥ 2` (from `t < ⌊t⌋ + 1`). -/
private lemma floor_ge_half {t : ℝ} (h2 : 2 ≤ t) : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
  have h1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  linarith

/-- `exp e ≤ x^c` whenever `e ≤ c·log x` (`x > 0`). -/
private lemma exp_le_rpow {x c e : ℝ} (hx : 0 < x) (h : e ≤ c * Real.log x) :
    Real.exp e ≤ x ^ c := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.mpr (h.trans_eq (mul_comm c (Real.log x)))

/-- `(27/10)^n ≤ exp n` — the crude `e ≥ 2.7` power bound for numeric exp-vs-numeral rows. -/
private lemma pow27_le_exp (n : ℕ) : ((27 : ℝ) / 10) ^ n ≤ Real.exp n := by
  have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h1 : ((27 : ℝ) / 10) ≤ Real.exp 1 := by
    have : (27 : ℝ) / 10 ≤ 2.7182818283 := by norm_num
    linarith
  calc ((27 : ℝ) / 10) ^ n ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) h1 n
    _ = Real.exp n := by rw [← Real.exp_nat_mul, mul_one]

/-- Polylog-beats-poly core: `(log u)^n ≤ 1000^n · u^{n/1000}` for `u ≥ 1`
(via `Real.log_le_rpow_div` at `ε = 1/1000`). -/
private lemma log_rpow_le_poly {u : ℝ} (hu : 1 ≤ u) (n : ℕ) :
    (Real.log u) ^ ((n : ℝ)) ≤ (1000 : ℝ) ^ n * u ^ ((n : ℝ) / 1000) := by
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hlog_nn : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : Real.log u ≤ 1000 * u ^ ((1 : ℝ) / 1000) := by
    have h := Real.log_le_rpow_div hu0 (by norm_num : (0 : ℝ) < 1 / 1000)
    calc Real.log u ≤ u ^ ((1 : ℝ) / 1000) / (1 / 1000) := h
      _ = 1000 * u ^ ((1 : ℝ) / 1000) := by ring
  calc (Real.log u) ^ ((n : ℝ))
      ≤ (1000 * u ^ ((1 : ℝ) / 1000)) ^ ((n : ℝ)) :=
        Real.rpow_le_rpow hlog_nn h1 (by positivity)
    _ = (1000 : ℝ) ^ ((n : ℝ)) * (u ^ ((1 : ℝ) / 1000)) ^ ((n : ℝ)) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hu0 _)
    _ = (1000 : ℝ) ^ n * u ^ ((n : ℝ) / 1000) := by
        rw [Real.rpow_natCast (1000 : ℝ) n, ← Real.rpow_mul hu0,
          show (1 : ℝ) / 1000 * (n : ℝ) = (n : ℝ) / 1000 by ring]

/-! ## Part 1 — ★ CATCH #64 ★, machine-checked

The `D0`-window rows of the windowed-BV terminal family are jointly unsatisfiable at every
`dyadicBoundary` box of the operating point.  See the module header for the full trace. -/

/-- **The pure-parameter pinch.**  If `L^{C0} ≤ 2·D0` (the `hD0lo_main` row) and
`D0 ≤ LN^{C0}` (the `hD0N'` row) with `C0 ≥ 2` and `LN ≤ (14/25)·L`, then `False`:
`L^{C0} ≤ 2·((14/25)·L)^{C0} ≤ 2·(14/25)²·L^{C0} = (392/625)·L^{C0} < L^{C0}`. -/
theorem catch64_D0_window_empty {L LN C0 D0 : ℝ}
    (hLpos : 0 < L) (hC0 : 2 ≤ C0) (hLN0 : 0 ≤ LN) (hLN : LN ≤ (14 / 25) * L)
    (hD0lo : L ^ C0 ≤ 2 * D0) (hD0hi : D0 ≤ LN ^ C0) : False := by
  have hC0nn : (0 : ℝ) ≤ C0 := by linarith
  have h1 : LN ^ C0 ≤ ((14 / 25) * L) ^ C0 := Real.rpow_le_rpow hLN0 hLN hC0nn
  have h2 : ((14 / 25) * L) ^ C0 = (14 / 25 : ℝ) ^ C0 * L ^ C0 :=
    Real.mul_rpow (by norm_num) hLpos.le
  have h3 : (14 / 25 : ℝ) ^ C0 ≤ (14 / 25 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hC0
  have h4 : (14 / 25 : ℝ) ^ (2 : ℝ) = 196 / 625 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hLC0 : (0 : ℝ) < L ^ C0 := Real.rpow_pos_of_pos hLpos _
  have h5 : (14 / 25 : ℝ) ^ C0 * L ^ C0 ≤ (196 / 625) * L ^ C0 :=
    mul_le_mul_of_nonneg_right (h4 ▸ h3) hLC0.le
  have hchain : L ^ C0 ≤ (392 / 625) * L ^ C0 := by
    calc L ^ C0 ≤ 2 * D0 := hD0lo
      _ ≤ 2 * LN ^ C0 := by linarith
      _ ≤ 2 * ((14 / 25 : ℝ) ^ C0 * L ^ C0) := by rw [← h2]; linarith
      _ ≤ 2 * ((196 / 625) * L ^ C0) := by linarith
      _ = (392 / 625) * L ^ C0 := by ring
  linarith

/-- **The boundary ratio.**  At the operating scales — `LN ≤ log 8 + (13/24)·t` (the block
floor) and `L ≥ t − log 2` (the cutoff mass), `t = log x ≥ 200` — the pinch ratio holds:
`LN ≤ (14/25)·L`.  Margin: `(14/25 − 13/24)·t = (11/600)·t ≥ 3.67 > (3 + 14/25)·log 2 ≈ 2.47`. -/
theorem catch64_ratio_at_op {t LN L : ℝ} (ht : 200 ≤ t)
    (hLN : LN ≤ Real.log 8 + (13 / 24) * t) (hL : t - Real.log 2 ≤ L) :
    LN ≤ (14 / 25) * L := by
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast; ring
  have h2le : Real.log 2 ≤ 6931472 / 10000000 := log_two_le
  have h2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  linarith

/-- **The cutoff-mass leg.**  Boundary clause 3 (`x/2 + 1 < X·M`) forces
`L = log(X·M) ≥ log x − log 2`. -/
theorem catch64_L_bound {x X M : ℕ} (hx : 2 ≤ x) (hXM : x / 2 + 1 < X * M) :
    Real.log x - Real.log 2 ≤ Real.log ((X : ℝ) * (M : ℝ)) := by
  have h1 : x < (x / 2 + 1) * 2 := by omega
  have h2 : x / 2 + 1 ≤ X * M := by omega
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hXMR : (x : ℝ) / 2 < (X : ℝ) * (M : ℝ) := by
    have h1R : (x : ℝ) < ((x / 2 + 1 : ℕ) : ℝ) * 2 := by exact_mod_cast h1
    have h2R : ((x / 2 + 1 : ℕ) : ℝ) ≤ ((X * M : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h1R h2R
    linarith
  have hlog : Real.log ((x : ℝ) / 2) ≤ Real.log ((X : ℝ) * (M : ℝ)) :=
    Real.log_le_log (by linarith) hXMR.le
  rwa [Real.log_div (ne_of_gt (by linarith : (0 : ℝ) < (x : ℝ))) (by norm_num)] at hlog

/-- **The block-floor leg.**  Boundary clauses 1+2 (`(N+1)·zy < 2x`) with the operating
floor `zy ≥ x^{11/24}/4` force `N < 8·x^{13/24}`, hence
`log N ≤ log 8 + (13/24)·log x`. -/
theorem catch64_logN_bound {x N zy : ℕ} (hx1 : 1 ≤ x)
    (hzy : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ (zy : ℝ))
    (hscale : (N + 1) * zy < 2 * x) :
    Real.log N ≤ Real.log 8 + (13 / 24) * Real.log x := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx1
  have hrpos : (0 : ℝ) < (x : ℝ) ^ ((11 : ℝ) / 24) := Real.rpow_pos_of_pos hxpos _
  have hrpos13 : (0 : ℝ) < (x : ℝ) ^ ((13 : ℝ) / 24) := Real.rpow_pos_of_pos hxpos _
  have hNle : ((N : ℝ) + 1) * (zy : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hscale.le
  -- (N+1)·(x^{11/24}/4) ≤ 2x, so (N+1)·x^{11/24} ≤ 8x = 8·x^{13/24}·x^{11/24}
  have h1 : ((N : ℝ) + 1) * ((x : ℝ) ^ ((11 : ℝ) / 24) / 4) ≤ 2 * (x : ℝ) := by
    calc ((N : ℝ) + 1) * ((x : ℝ) ^ ((11 : ℝ) / 24) / 4)
        ≤ ((N : ℝ) + 1) * (zy : ℝ) := by
          exact mul_le_mul_of_nonneg_left hzy (by positivity)
      _ ≤ 2 * (x : ℝ) := hNle
  have h2 : ((N : ℝ) + 1) * (x : ℝ) ^ ((11 : ℝ) / 24)
      ≤ (8 * (x : ℝ) ^ ((13 : ℝ) / 24)) * (x : ℝ) ^ ((11 : ℝ) / 24) := by
    calc ((N : ℝ) + 1) * (x : ℝ) ^ ((11 : ℝ) / 24)
        = 4 * (((N : ℝ) + 1) * ((x : ℝ) ^ ((11 : ℝ) / 24) / 4)) := by ring
      _ ≤ 4 * (2 * (x : ℝ)) := by linarith
      _ = 8 * (x : ℝ) := by ring
      _ = (8 * (x : ℝ) ^ ((13 : ℝ) / 24)) * (x : ℝ) ^ ((11 : ℝ) / 24) := by
          rw [mul_assoc, ← Real.rpow_add hxpos,
            show (13 : ℝ) / 24 + 11 / 24 = 1 by norm_num, Real.rpow_one]
  have hN8 : (N : ℝ) ≤ 8 * (x : ℝ) ^ ((13 : ℝ) / 24) := by
    have := le_of_mul_le_mul_right h2 hrpos
    linarith
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Nat.cast_zero, Real.log_zero]
    have h8nn : (0 : ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have hxnn : (0 : ℝ) ≤ Real.log x := Real.log_natCast_nonneg x
    linarith
  · have hlog := Real.log_le_log (by exact_mod_cast hNpos) hN8
    rwa [Real.log_mul (by norm_num) (ne_of_gt hrpos13), Real.log_rpow hxpos] at hlog

/-- **CATCH #64, assembled at the row shapes.**  For any application carrying the boundary
scales (`X·M > x/2`, `(N+1)·zy < 2x` with `zy ≥ x^{11/24}/4`) at `x ≥ e^{200}`, the terminal's
`D0`-window rows `hD0lo_main : L^{C0} ≤ 2·2^{k0}` and `hD0N' : D0 ≤ (log N)^{C0}` (with
`D0 = 2^{k0}`, `A > 0`, `A + 2 ≤ C0` — the exact `general_BV_cutoff_sqrtD` /
`medium_survivor_price_sqrtD` shapes) are contradictory. -/
theorem catch64_no_admissible_D0 {x zy N M X D0 k0 : ℕ} {A C0 : ℝ}
    (hx : Real.exp 200 ≤ (x : ℝ))
    (hzy : (x : ℝ) ^ ((11 : ℝ) / 24) / 4 ≤ (zy : ℝ))
    (hNscale : (N + 1) * zy < 2 * x)
    (hXM : x / 2 + 1 < X * M)
    (hA : 0 < A) (hCge : A + 2 ≤ C0)
    (hD0eq : D0 = 2 ^ k0)
    (hD0lo : (Real.log ((X : ℝ) * (M : ℝ))) ^ C0 ≤ 2 * (2 : ℝ) ^ k0)
    (hD0N : (D0 : ℝ) ≤ (Real.log N) ^ C0) : False := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos 200) hx
  have ht : (200 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 200) hx
    rwa [Real.log_exp] at this
  have hx2 : 2 ≤ x := by
    have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hmono : Real.exp 1 ≤ Real.exp 200 := Real.exp_le_exp.mpr (by norm_num)
    have h2R : (2 : ℝ) < (x : ℝ) := by linarith
    exact_mod_cast h2R.le
  have hx1 : 1 ≤ x := by omega
  have h2le : Real.log 2 ≤ 6931472 / 10000000 := log_two_le
  have hL := catch64_L_bound hx2 hXM
  have hLN := catch64_logN_bound hx1 hzy hNscale
  have hratio := catch64_ratio_at_op ht hLN hL
  have hLpos : (0 : ℝ) < Real.log ((X : ℝ) * (M : ℝ)) := by linarith
  have hD0cast : (2 : ℝ) ^ k0 = (D0 : ℝ) := by rw [hD0eq]; push_cast; ring
  rw [hD0cast] at hD0lo
  exact catch64_D0_window_empty hLpos (by linarith) (Real.log_natCast_nonneg N)
    hratio hD0lo hD0N

/-- The operating `z·y` floor: `⌊x^{1/8}⌋·⌊x^{1/3}⌋ ≥ x^{11/24}/4` for `x ≥ e^{200}`. -/
theorem zy_floor_ge {x : ℕ} (hx : Real.exp 200 ≤ (x : ℝ)) :
    (x : ℝ) ^ ((11 : ℝ) / 24) / 4
      ≤ ((⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos 200) hx
  have ht : (200 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 200) hx
    rwa [Real.log_exp] at this
  have hz2 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    have h1 : Real.exp 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := exp_le_rpow hxpos (by linarith)
    have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    linarith
  have hy2 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have h1 : Real.exp 1 ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := exp_le_rpow hxpos (by linarith)
    have h9 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    linarith
  have hzge := floor_ge_half hz2
  have hyge := floor_ge_half hy2
  push_cast
  calc (x : ℝ) ^ ((11 : ℝ) / 24) / 4
      = ((x : ℝ) ^ ((1 : ℝ) / 8) / 2) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 2) := by
        rw [div_mul_div_comm, ← Real.rpow_add hxpos,
          show (1 : ℝ) / 8 + 1 / 3 = 11 / 24 by norm_num]
        norm_num
    _ ≤ (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ : ℝ) * (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) :=
        mul_le_mul hzge hyge (by positivity) (by positivity)

/-- ★ **CATCH #64 — the headline.** ★  At the operating point (`z = ⌊x^{1/8}⌋`,
`y = ⌊x^{1/3}⌋`, `x ≥ e^{200}` — in particular at and beyond every conceivable `x₀`), EVERY
`dyadicBoundary` price application of `general_BV_cutoff_sqrtD` / `medium_survivor_price_sqrtD`
(at the mandated `X = 2^{i+1} − 1`, the box's own `N`, `M`) has an EMPTY `D0`-window: the rows
`hD0lo_main` and `hD0N'` cannot both hold.  Since the boundary boxes are exactly the boxes the
three-way split does NOT cancel, `hBVblocks` is NOT dischargeable through the landed terminal
family, and the `hA3` line — hence F2/F3 of GLU-2 — is blocked pending the statement repair
described in the module header. -/
theorem catch64_op_boundary_infeasible {x N M K i X D0 k0 : ℕ} {A C0 : ℝ}
    (hx : Real.exp 200 ≤ (x : ℝ))
    (hi : i ∈ dyadicBoundary N M (x / 2 + 1) x
        (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊) K)
    (hXsub : X = 2 ^ (i + 1) - 1)
    (hA : 0 < A) (hCge : A + 2 ≤ C0) (hD0eq : D0 = 2 ^ k0)
    (hD0lo : (Real.log ((X : ℝ) * (M : ℝ))) ^ C0 ≤ 2 * (2 : ℝ) ^ k0)
    (hD0N : (D0 : ℝ) ≤ (Real.log N) ^ C0) : False := by
  rw [dyadicBoundary, Finset.mem_filter] at hi
  obtain ⟨-, hcorner, hfloor', hcutoff⟩ := hi
  -- clauses 1+2 → (N+1)·zy < 2x
  have hNscale : (N + 1) * (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊) < 2 * x := by
    calc (N + 1) * (⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
        < (N + 1) * 2 ^ (i + 1) :=
          mul_lt_mul_of_pos_left hfloor' (by omega : 0 < N + 1)
      _ = 2 * (2 ^ i * (N + 1)) := by rw [pow_succ]; ring
      _ ≤ 2 * x := Nat.mul_le_mul (le_refl 2) hcorner
  -- clause 3 → X·M > x/2
  have hXM : x / 2 + 1 < X * M := by rw [hXsub]; exact hcutoff
  exact catch64_no_admissible_D0 hx (zy_floor_ge hx) hNscale hXM hA hCge hD0eq hD0lo hD0N

/-! ## Part 2 — the F1 numeric-row bundle

Each row is its own lemma at an explicit threshold, in the exact slot shape its consumer
names (see the STEP 0 table).  Margins in the docstrings.  Convention: `A := 13` (so the
`hfloor` exponent is `A + 5 = 18` and the `habs` exponent is `A = 13`); the budget row
family wanted `A ≥ 12`, and `A = 13` keeps a spare log for `L`-scale SW constants. -/

/-- **The `hyx` row.**  `x < (y+1)³` at `y = ⌊x^{1/3}⌋` — the `chen_of_hypotheses` window
hypothesis, for every `x ≥ 1` (no threshold needed: pure floor bracketing). -/
theorem hyx_at_op (x : ℕ) (hx : 1 ≤ x) :
    x < (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1) ^ 3 := by
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have h1 : (x : ℝ) ^ ((1 : ℝ) / 3) < (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h3 : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ)
      < ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1) ^ (3 : ℕ) :=
    pow_lt_pow_left₀ h1 h0 (by norm_num)
  have hcube : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (x : ℝ) := by
    rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul (by linarith),
      show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one]
  rw [hcube] at h3
  exact_mod_cast h3

/-- **The sifting modulus** `P = ∏_{p < z} p` — the canonical `hPfull` witness. -/
def sievePrimorial (z : ℕ) : ℕ := ∏ p ∈ (Finset.range z).filter Nat.Prime, p

/-- **The `hPfull` row.**  Every prime `q < z` divides `sievePrimorial z` — the exact
`hPfull` slot of `chen_positivity` / `chen_of_hypotheses` at `P = sievePrimorial z`. -/
theorem sievePrimorial_dvd (z : ℕ) : ∀ q, q.Prime → q < z → q ∣ sievePrimorial z :=
  fun q hq hqz =>
    show q ∣ sievePrimorial z from
      Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqz, hq⟩)

/-- **The `hDsq` row.**  Any level `D ≤ x^{5/9}` (covering `Q·Dlev ~ √x·polylog` with
`x^{1/18}` to spare) satisfies `D < (y+1)²` at `y = ⌊x^{1/3}⌋` — the single numeric row
`hDsq_of_carrier_floor` (SqrtDFold) consumes.  Margin: `(y+1)² > x^{2/3} = x^{5/9}·x^{1/9}`. -/
theorem hDsq_row {x : ℕ} (hx : 10 ^ 48 ≤ x) {D : ℕ}
    (hD : (D : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 9)) :
    D < (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1) * (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ + 1) := by
  have hxR : ((10 : ℝ)) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hxR
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hxR
  have hy1 : (x : ℝ) ^ ((1 : ℝ) / 3) < (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h0 : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hxpos.le _
  have hsq : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ)
      < ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ hy1 h0 (by norm_num)
  have hsq_eq : ((x : ℝ) ^ ((1 : ℝ) / 3)) ^ (2 : ℕ) = (x : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast ((x : ℝ) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hxpos.le,
      show (1 : ℝ) / 3 * ((2 : ℕ) : ℝ) = 2 / 3 by push_cast; ring]
  have hone : (1 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 9) := by
    calc (1 : ℝ) = (1 : ℝ) ^ ((1 : ℝ) / 9) := (Real.one_rpow _).symm
      _ ≤ (x : ℝ) ^ ((1 : ℝ) / 9) := Real.rpow_le_rpow (by norm_num) hx1 (by norm_num)
  have h59 : (x : ℝ) ^ ((5 : ℝ) / 9) ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := by
    calc (x : ℝ) ^ ((5 : ℝ) / 9) = (x : ℝ) ^ ((5 : ℝ) / 9) * 1 := (mul_one _).symm
      _ ≤ (x : ℝ) ^ ((5 : ℝ) / 9) * (x : ℝ) ^ ((1 : ℝ) / 9) :=
          mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg hxpos.le _)
      _ = (x : ℝ) ^ ((2 : ℝ) / 3) := by
          rw [← Real.rpow_add hxpos, show (5 : ℝ) / 9 + 1 / 9 = 2 / 3 by norm_num]
  have hchain : (D : ℝ) < ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1)
      * ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1) := by
    calc (D : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 9) := hD
      _ ≤ (x : ℝ) ^ ((2 : ℝ) / 3) := h59
      _ < ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1) ^ (2 : ℕ) := hsq_eq ▸ hsq
      _ = ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1)
          * ((⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) + 1) := by ring
  exact_mod_cast hchain

/-- **The `hfloor` row (at `A = 13`, exponent `A + 5 = 18`).**  For `x ≥ e^{4000}`:
`(3/log 2)⁸ · x^{1/6} · (log 4x)^{18} ≤ √(⌊x^{1/8}⌋·⌊x^{1/3}⌋)` — the exact
`medium_survivor_price_sqrtD` `hfloor` slot at `F = z·y`, `Lb = log(4x)`.
Margin: LHS `≤ 5·10⁵⁹·x^{1/6 + 18/1000}`, RHS `≥ x^{11/48}/2`, and
`x^{11/48 − 1/6 − 18/1000} = x^{89/2000} ≥ e^{178} ≥ 2.7^{178} > 2·5·10⁵⁹` (`x^{1/16}`-scale
power room; the threshold `e^{4000}` is dwarfed by the `w₀`-guard's `x₀ ≈ e^{1.6·10^{10}}`). -/
theorem hfloor_row {x : ℕ} (hx : Real.exp 4000 ≤ (x : ℝ)) :
    ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6)
        * (Real.log (4 * (x : ℝ))) ^ ((18 : ℝ))
      ≤ Real.sqrt ((⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos 4000) hx
  have ht : (4000 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 4000) hx
    rwa [Real.log_exp] at this
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.exp 4000 := by
      have := Real.add_one_le_exp (4000 : ℝ); linarith
    linarith
  -- ① the constant: (3/log 2)⁸ ≤ 125000
  have hC3 : ((3 : ℝ) / Real.log 2) ^ 8 ≤ 125000 := by
    have h2lo : (6931471 : ℝ) / 10000000 ≤ Real.log 2 := le_log_two
    have h2pos : (0 : ℝ) < Real.log 2 := by linarith
    have hdiv : (3 : ℝ) / Real.log 2 ≤ 433 / 100 := by
      rw [div_le_div_iff₀ h2pos (by norm_num)]
      linarith
    calc ((3 : ℝ) / Real.log 2) ^ 8 ≤ (433 / 100 : ℝ) ^ 8 :=
          pow_le_pow_left₀ (by positivity) hdiv 8
      _ ≤ 125000 := by norm_num
  -- ② the log-power: (log 4x)^{18} ≤ 1000^{18}·4·x^{18/1000}
  have h4x1 : (1 : ℝ) ≤ 4 * (x : ℝ) := by linarith
  have hlog18 : (Real.log (4 * (x : ℝ))) ^ ((18 : ℝ))
      ≤ (1000 : ℝ) ^ 18 * (4 * (x : ℝ) ^ ((18 : ℝ) / 1000)) := by
    have h := log_rpow_le_poly h4x1 18
    push_cast at h
    refine h.trans ?_
    have hsplit : (4 * (x : ℝ)) ^ ((18 : ℝ) / 1000) ≤ 4 * (x : ℝ) ^ ((18 : ℝ) / 1000) := by
      rw [Real.mul_rpow (by norm_num) hxpos.le]
      have h4 : (4 : ℝ) ^ ((18 : ℝ) / 1000) ≤ 4 := by
        calc (4 : ℝ) ^ ((18 : ℝ) / 1000) ≤ (4 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := Real.rpow_one 4
      exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hxpos.le _)
    exact mul_le_mul_of_nonneg_left hsplit (by positivity)
  -- ③ LHS ≤ (500000·1000^{18})·(x^{1/6}·x^{18/1000})
  have hx16nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg hxpos.le _
  have hLnn : (0 : ℝ) ≤ Real.log (4 * (x : ℝ)) := Real.log_nonneg h4x1
  have hLHS : ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6)
        * (Real.log (4 * (x : ℝ))) ^ ((18 : ℝ))
      ≤ (500000 * (1000 : ℝ) ^ 18)
          * ((x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((18 : ℝ) / 1000)) := by
    have hlog_nn : (0 : ℝ) ≤ (Real.log (4 * (x : ℝ))) ^ ((18 : ℝ)) := Real.rpow_nonneg hLnn _
    calc ((3 : ℝ) / Real.log 2) ^ 8 * (x : ℝ) ^ ((1 : ℝ) / 6)
          * (Real.log (4 * (x : ℝ))) ^ ((18 : ℝ))
        ≤ 125000 * (x : ℝ) ^ ((1 : ℝ) / 6)
            * ((1000 : ℝ) ^ 18 * (4 * (x : ℝ) ^ ((18 : ℝ) / 1000))) := by
          refine mul_le_mul ?_ hlog18 hlog_nn (by positivity)
          exact mul_le_mul_of_nonneg_right hC3 hx16nn
      _ = (500000 * (1000 : ℝ) ^ 18)
            * ((x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((18 : ℝ) / 1000)) := by ring
  -- ④ 10^{60} ≤ x^{89/2000}
  have hx89 : (10 : ℝ) ^ 60 ≤ (x : ℝ) ^ ((89 : ℝ) / 2000) := by
    have h27 : ((27 : ℝ) / 10) ^ (178 : ℕ) ≤ Real.exp ((178 : ℕ) : ℝ) := pow27_le_exp 178
    have hexp : Real.exp ((178 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((89 : ℝ) / 2000) := by
      apply exp_le_rpow hxpos
      push_cast
      linarith
    have hnum : (10 : ℝ) ^ 60 ≤ ((27 : ℝ) / 10) ^ (178 : ℕ) := by norm_num
    linarith
  -- ⑤ RHS ≥ x^{11/48}/2 and close
  have hzy := zy_floor_ge (le_trans (Real.exp_le_exp.mpr (by norm_num : (200 : ℝ) ≤ 4000)) hx)
  have hsq_eq : ((x : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ (2 : ℕ) = (x : ℝ) ^ ((11 : ℝ) / 24) / 4 := by
    rw [div_pow, ← Real.rpow_natCast ((x : ℝ) ^ ((11 : ℝ) / 48)) 2, ← Real.rpow_mul hxpos.le,
      show (11 : ℝ) / 48 * ((2 : ℕ) : ℝ) = 11 / 24 by push_cast; ring]
    norm_num
  have hsqrt_ge : (x : ℝ) ^ ((11 : ℝ) / 48) / 2
      ≤ Real.sqrt ((⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) := by
    calc (x : ℝ) ^ ((11 : ℝ) / 48) / 2
        = Real.sqrt (((x : ℝ) ^ ((11 : ℝ) / 48) / 2) ^ (2 : ℕ)) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt ((⌊(x : ℝ) ^ ((1 : ℝ) / 8)⌋₊ * ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by rw [hsq_eq]; exact hzy)
  refine hLHS.trans (le_trans ?_ hsqrt_ge)
  have hu_eq : (x : ℝ) ^ ((1 : ℝ) / 6) * (x : ℝ) ^ ((18 : ℝ) / 1000)
      = (x : ℝ) ^ ((1 : ℝ) / 6 + 18 / 1000) := (Real.rpow_add hxpos _ _).symm
  have hsplit48 : (x : ℝ) ^ ((11 : ℝ) / 48)
      = (x : ℝ) ^ ((89 : ℝ) / 2000) * (x : ℝ) ^ ((1 : ℝ) / 6 + 18 / 1000) := by
    rw [← Real.rpow_add hxpos,
      show (89 : ℝ) / 2000 + (1 / 6 + 18 / 1000) = 11 / 48 by norm_num]
  rw [hu_eq, hsplit48]
  have hunn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 6 + 18 / 1000) := Real.rpow_nonneg hxpos.le _
  have hkey := mul_le_mul_of_nonneg_right hx89 hunn
  linarith [hkey]

/-- **The `habs` row (at `A = 13`, numeric core).**  For `x ≥ e^{4000}`, any level
`D ≤ x^{5/9}` and any box log `0 ≤ L ≤ log 4x` (boundary boxes have `X·M ≤ 4x`):
`4(1 + log D)·D·L^{13} ≤ x^{7/8}/8`.  Feeds the `habs : 4(1+log D)·D ≤ N·M/L^A` slot of
`general_BV_cutoff_sqrtD` at any boundary box, since there `N·M ≥ N² ≥ x/(8z) ≥ x^{7/8}/8`.
Margin: `x^{7/8 − 5/9 − 14/1000} = x^{2749/9000} ≥ e^{1221}` versus a `< 10⁴⁵` constant. -/
theorem habs_row {x : ℕ} (hx : Real.exp 4000 ≤ (x : ℝ)) {D : ℕ}
    (hD : (D : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 9)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log (4 * (x : ℝ))) :
    4 * (1 + Real.log D) * (D : ℝ) * L ^ ((13 : ℝ)) ≤ (x : ℝ) ^ ((7 : ℝ) / 8) / 8 := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (Real.exp_pos 4000) hx
  have ht : (4000 : ℝ) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 4000) hx
    rwa [Real.log_exp] at this
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have h1 : (1 : ℝ) ≤ Real.exp 4000 := by
      have := Real.add_one_le_exp (4000 : ℝ); linarith
    linarith
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  -- 1 + log D ≤ log x ≤ 1000·x^{1/1000}
  have hlogD : Real.log D ≤ 5 / 9 * Real.log x := by
    rcases Nat.eq_zero_or_pos D with h0 | hDpos
    · subst h0
      simp only [Nat.cast_zero, Real.log_zero]
      have : (0 : ℝ) ≤ Real.log x := by linarith
      positivity
    · have := Real.log_le_log (by exact_mod_cast hDpos) hD
      rwa [Real.log_rpow hxpos] at this
  have h1D : 1 + Real.log D ≤ Real.log x := by linarith
  have hlogx1000 : Real.log (x : ℝ) ≤ 1000 * (x : ℝ) ^ ((1 : ℝ) / 1000) := by
    have h := Real.log_le_rpow_div hxpos.le (by norm_num : (0 : ℝ) < 1 / 1000)
    calc Real.log (x : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 1000) / (1 / 1000) := h
      _ = 1000 * (x : ℝ) ^ ((1 : ℝ) / 1000) := by ring
  -- L^{13} ≤ 1000^{13}·4·x^{13/1000}
  have hL13 : L ^ ((13 : ℝ)) ≤ (1000 : ℝ) ^ 13 * (4 * (x : ℝ) ^ ((13 : ℝ) / 1000)) := by
    have h1 : L ^ ((13 : ℝ)) ≤ (Real.log (4 * (x : ℝ))) ^ ((13 : ℝ)) :=
      Real.rpow_le_rpow hL0 hL (by norm_num)
    have h2 := log_rpow_le_poly (by linarith : (1 : ℝ) ≤ 4 * (x : ℝ)) 13
    push_cast at h2
    refine h1.trans (h2.trans ?_)
    have hsplit : (4 * (x : ℝ)) ^ ((13 : ℝ) / 1000) ≤ 4 * (x : ℝ) ^ ((13 : ℝ) / 1000) := by
      rw [Real.mul_rpow (by norm_num) hxpos.le]
      have h4 : (4 : ℝ) ^ ((13 : ℝ) / 1000) ≤ 4 := by
        calc (4 : ℝ) ^ ((13 : ℝ) / 1000) ≤ (4 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := Real.rpow_one 4
      exact mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hxpos.le _)
    exact mul_le_mul_of_nonneg_left hsplit (by positivity)
  -- assemble the three factors
  have hstep : 4 * (1 + Real.log D) * (D : ℝ) * L ^ ((13 : ℝ))
      ≤ 4 * (1000 * (x : ℝ) ^ ((1 : ℝ) / 1000)) * (x : ℝ) ^ ((5 : ℝ) / 9)
          * ((1000 : ℝ) ^ 13 * (4 * (x : ℝ) ^ ((13 : ℝ) / 1000))) := by
    have hfac1 : 4 * (1 + Real.log D) ≤ 4 * (1000 * (x : ℝ) ^ ((1 : ℝ) / 1000)) :=
      mul_le_mul_of_nonneg_left (le_trans h1D hlogx1000) (by norm_num)
    have hfac2 : 4 * (1 + Real.log D) * (D : ℝ)
        ≤ 4 * (1000 * (x : ℝ) ^ ((1 : ℝ) / 1000)) * (x : ℝ) ^ ((5 : ℝ) / 9) :=
      mul_le_mul hfac1 hD hDnn (by positivity)
    exact mul_le_mul hfac2 hL13 (Real.rpow_nonneg hL0 _) (by positivity)
  refine hstep.trans ?_
  -- the numeric close: 16·10^{42}·x^{5/9 + 14/1000} ≤ x^{7/8}/8
  have hxsum : (x : ℝ) ^ ((1 : ℝ) / 1000 + 5 / 9 + 13 / 1000)
      = (x : ℝ) ^ ((1 : ℝ) / 1000) * (x : ℝ) ^ ((5 : ℝ) / 9) * (x : ℝ) ^ ((13 : ℝ) / 1000) := by
    rw [Real.rpow_add hxpos, Real.rpow_add hxpos]
  have hx_pow : (128 * 10 ^ 42 : ℝ) ≤ (x : ℝ) ^ ((2749 : ℝ) / 9000) := by
    have h27 : ((27 : ℝ) / 10) ^ (110 : ℕ) ≤ Real.exp ((110 : ℕ) : ℝ) := pow27_le_exp 110
    have hexp : Real.exp ((110 : ℕ) : ℝ) ≤ (x : ℝ) ^ ((2749 : ℝ) / 9000) := by
      apply exp_le_rpow hxpos
      push_cast
      linarith
    have hnum : (128 * 10 ^ 42 : ℝ) ≤ ((27 : ℝ) / 10) ^ (110 : ℕ) := by norm_num
    linarith
  have hsplit78 : (x : ℝ) ^ ((7 : ℝ) / 8)
      = (x : ℝ) ^ ((2749 : ℝ) / 9000) * (x : ℝ) ^ ((1 : ℝ) / 1000 + 5 / 9 + 13 / 1000) := by
    rw [← Real.rpow_add hxpos,
      show (2749 : ℝ) / 9000 + (1 / 1000 + 5 / 9 + 13 / 1000) = 7 / 8 by norm_num]
  have hu_nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 1000 + 5 / 9 + 13 / 1000) :=
    Real.rpow_nonneg hxpos.le _
  have hkey := mul_le_mul_of_nonneg_right hx_pow hu_nn
  calc 4 * (1000 * (x : ℝ) ^ ((1 : ℝ) / 1000)) * (x : ℝ) ^ ((5 : ℝ) / 9)
        * ((1000 : ℝ) ^ 13 * (4 * (x : ℝ) ^ ((13 : ℝ) / 1000)))
      = (4 * 1000 * 1000 ^ 13 * 4 : ℝ)
          * (x : ℝ) ^ ((1 : ℝ) / 1000 + 5 / 9 + 13 / 1000) := by
        rw [hxsum]; ring
    _ ≤ (x : ℝ) ^ ((7 : ℝ) / 8) / 8 := by
        rw [hsplit78]
        linarith [hkey]

/-! ### The shifted-`Dlev` switch-window membership (finding 2's enabler)

Local copies of M4F's (private) floor-bracketing pair, then the range-form membership:
the `logRatio y Dlev ∈ [149/100, 151/100]` certificate for EVERY `Dlev ∈ [x^{497/1000}, √x]`
— so the level rows (`hDscale`, `herr_lev`) can push `Dlev` a polylog below `√x` without
touching the landed `FchainPoint.Fchain_switch_le` window. -/

/-- Local copy of M4F's floor bracketing (that one is `private`): for `x ≥ 10⁴⁸`, `γ ≥ 1/8`,
`⌊x^γ⌋ ≥ 10⁶` and `γ·log x − 1/999999 ≤ log ⌊x^γ⌋ ≤ γ·log x`. -/
private lemma glue_floor_bounds (x : ℕ) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) {γ : ℝ}
    (hγ : (1 / 8 : ℝ) ≤ γ) :
    (10 : ℝ) ^ 6 ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ)
      ∧ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ γ * Real.log (x : ℝ)
      ∧ γ * Real.log (x : ℝ) - 1 / 999999 ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
  have hX1 : (1 : ℝ) ≤ (x : ℝ) := le_trans (by norm_num) hx
  have hXpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hx
  have hpow48 : ((10 : ℝ) ^ (48 : ℕ)) ^ ((1 : ℝ) / 8) = (10 : ℝ) ^ 6 := by
    have h6 : ((48 : ℕ) : ℝ) * (1 / 8) = ((6 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_natCast (10 : ℝ) 48, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10), h6,
      Real.rpow_natCast]
  have hstep1 : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← hpow48]; exact Real.rpow_le_rpow (by positivity) hx (by norm_num)
  have hstep2 : (x : ℝ) ^ ((1 : ℝ) / 8) ≤ (x : ℝ) ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hX1 hγ
  have hApow : (10 : ℝ) ^ 6 ≤ (x : ℝ) ^ γ := le_trans hstep1 hstep2
  have hA6 : (1000000 : ℝ) ≤ (x : ℝ) ^ γ := le_trans (by norm_num) hApow
  have hXγnn : (0 : ℝ) ≤ (x : ℝ) ^ γ := Real.rpow_nonneg hXpos.le γ
  have hfloor_ge : (10 : ℝ) ^ 6 ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    have h1 : ((1000000 : ℕ) : ℝ) ≤ (x : ℝ) ^ γ := by
      rw [show ((1000000 : ℕ) : ℝ) = (10 : ℝ) ^ 6 by norm_num]; exact hApow
    have h2 : (1000000 : ℕ) ≤ ⌊(x : ℝ) ^ γ⌋₊ := Nat.le_floor h1
    calc (10 : ℝ) ^ 6 = ((1000000 : ℕ) : ℝ) := by norm_num
      _ ≤ (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by exact_mod_cast h2
  have hfloor_le : (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ (x : ℝ) ^ γ := Nat.floor_le hXγnn
  have hfloor_gt : (x : ℝ) ^ γ - 1 < (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    linarith [Nat.lt_floor_add_one ((x : ℝ) ^ γ)]
  have hzfpos : (0 : ℝ) < (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := lt_of_lt_of_le (by norm_num) hfloor_ge
  have hXγ1pos : (0 : ℝ) < (x : ℝ) ^ γ - 1 := by linarith [hA6]
  have hlogXγ : Real.log ((x : ℝ) ^ γ) = γ * Real.log (x : ℝ) := Real.log_rpow hXpos γ
  have hlog_le : Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) ≤ γ * Real.log (x : ℝ) := by
    rw [← hlogXγ]; exact Real.log_le_log hzfpos hfloor_le
  have hratio : (x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1) ≤ 1000000 / 999999 := by
    rw [div_le_div_iff₀ hXγ1pos (by norm_num : (0 : ℝ) < 999999)]
    nlinarith [hA6]
  have hcorr : Real.log ((x : ℝ) ^ γ) - Real.log ((x : ℝ) ^ γ - 1) ≤ 1 / 999999 := by
    have h1 : Real.log ((x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1)) ≤ (x : ℝ) ^ γ / ((x : ℝ) ^ γ - 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hXγ1pos)] at h1
    linarith [h1, hratio]
  have hlog_ge : γ * Real.log (x : ℝ) - 1 / 999999 ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) := by
    have hlog_floor_ge : Real.log ((x : ℝ) ^ γ - 1) ≤ Real.log (⌊(x : ℝ) ^ γ⌋₊ : ℝ) :=
      Real.log_le_log hXγ1pos (le_of_lt hfloor_gt)
    rw [hlogXγ] at hcorr
    linarith [hlog_floor_ge, hcorr]
  exact ⟨hfloor_ge, hlog_le, hlog_ge⟩

/-- Local copy of M4F's `log 10 ≥ 2` corollary: `log x ≥ 96` for `x ≥ 10⁴⁸`. -/
private lemma glue_log_ge_96 (x : ℕ) (hx : (10 : ℝ) ^ 48 ≤ (x : ℝ)) :
    (96 : ℝ) ≤ Real.log (x : ℝ) := by
  have hlog10 : (2 : ℝ) ≤ Real.log 10 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [he]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
  have hmono : Real.log ((10 : ℝ) ^ 48) ≤ Real.log (x : ℝ) := Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at hmono
  push_cast at hmono
  linarith [hmono, hlog10]

/-- **The range-form switch-window membership (finding 2's enabler).**  For `x ≥ 10⁴⁸` and
ANY `Dlev ∈ [x^{497/1000}, x^{1/2}]`, the switch operating point lands in the landed
`Fchain_switch_le` window:  `logRatio ⌊x^{1/3}⌋ Dlev ∈ [149/100, 151/100]`.
Margins: lower `(497/1000 − 149/300)·t = t/3000`; upper `t/300 − 151/(100·999999)`.
This is `WindowMembership.logRatio_A3_mem` generalized so the H-glue can take
`Dlev = ⌊√x/(log 4x)^{B+6}⌋`-shaped levels (which satisfy `Dlev ≥ x^{497/1000}` for all
large `x`), as required by the level rows `hDscale`/`herr_lev` at boundary boxes. -/
theorem logRatio_A3_mem_range {x : ℕ} (hx : 10 ^ 48 ≤ x) {Dlev : ℕ}
    (hDlo : (x : ℝ) ^ ((497 : ℝ) / 1000) ≤ (Dlev : ℝ))
    (hDhi : (Dlev : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2)) :
    logRatio ⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ Dlev ∈ Set.Icc (149 / 100 : ℝ) (151 / 100 : ℝ) := by
  have hxR : (10 : ℝ) ^ 48 ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by norm_num) hxR
  obtain ⟨hy6, hy_le, hy_ge⟩ := glue_floor_bounds x hxR (γ := 1 / 3) (by norm_num)
  have hL96 := glue_log_ge_96 x hxR
  have hlogy_pos : (0 : ℝ) < Real.log (⌊(x : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < (10 : ℝ) ^ 6) hy6)
  have hDpos : (0 : ℝ) < (Dlev : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hDlo
  have hlogD_le : Real.log (Dlev : ℝ) ≤ 1 / 2 * Real.log x := by
    have := Real.log_le_log hDpos hDhi
    rwa [Real.log_rpow hxpos] at this
  have hlogD_ge : 497 / 1000 * Real.log x ≤ Real.log (Dlev : ℝ) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hxpos _) hDlo
    rwa [Real.log_rpow hxpos] at this
  rw [Set.mem_Icc]
  constructor
  · rw [logRatio, le_div_iff₀ hlogy_pos]
    linarith [hy_le, hlogD_ge, hL96]
  · rw [logRatio, div_le_iff₀ hlogy_pos]
    linarith [hy_ge, hlogD_le, hL96]

/-! ## Composition sanity — the consumers and suppliers this node names -/

section CompositionSanity

-- the H-package terminal and the razor side (GLU-1, landed)
#check @Salt.Chen.chen_of_hypotheses
#check @Salt.Chen.chen_positivity
#check @Salt.Chen.normalized_package
#check @Salt.Chen.hledger_at_certs
-- the A₃/BV side (landed; blocked at the D0-window per CATCH #64)
#check @Salt.Chen.mainA3_of_block_remainders
#check @Salt.Chen.general_BV_cutoff_sqrtD
#check @Salt.Chen.medium_survivor_price_sqrtD
#check @Salt.Chen.hNum_at_op_sqrtD
#check @Salt.Chen.dyadicBoundary
-- the value certificates the F1 rows serve
#check @Salt.Chen.logRatio_A1_mem
#check @Salt.Chen.logRatio_A3_mem
-- this file
#check @Salt.Chen.catch64_op_boundary_infeasible
#check @Salt.Chen.catch64_no_admissible_D0
#check @Salt.Chen.hyx_at_op
#check @Salt.Chen.sievePrimorial_dvd
#check @Salt.Chen.hDsq_row
#check @Salt.Chen.hfloor_row
#check @Salt.Chen.habs_row
#check @Salt.Chen.logRatio_A3_mem_range

end CompositionSanity

end Salt.Chen
