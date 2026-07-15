/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/
import Salt.Chen.PriceThree

/-!
# PRICE-3b — the piece-parameter rows + the numeric closure (node PRICE-3b)

Design: `docs/blueprints/flags.md`, the `2026-07-14 PRICE-3` entry (the seam, the aggregate
under `hK_tower`, the hDsq/boundary-nonemptiness coupling) and the `PRICE-GATE`/`PRICE-1`/
`PRICE-2` entries.  This is the PRICE wave's closing node: it supplies the piece-parameter
analytic rows that discharge the box legs of `PriceThree.box_hprice_at_2pow` /
`sym_box_hprice_at_2pow` / `low_box_hprice_at_2pow` at the operating values `N = 2^k`,
`M = pieceM k`, `X = 2^{i+1}−1`, and drives toward `hBVblocksW_at_op`.

## ★ THE k-FLOOR CORRECTION (a divergence from the PRICE-3 finding) ★

The PRICE-3 finding claimed the honest k-floor (`2^k ≳ x^{1/4}`, needed for `hDsq :
D < (2^k+1)²` at `D ~ x^{0.497}`) is supplied by "the area clause `X·M > x/2` + the
m-floor" of `dyadicBoundary`.  **This is not so.**  Boundary membership at `F = z·y` gives
only clauses `2^i·(2^k+1) ≤ x` (corner), `z·y < 2^{i+1}` (m-floor), `x/2 < X·M` (cutoff),
which together PIN THE PRODUCT `2^{i+k} ∈ (x/8, x]` and UPPER-bound `2^k ≤ 8·x^{13/24}`
(the catch-#64 `catch64_logN_bound` direction) — but supply **no lower bound on `2^k`**.
Concretely, at `k = 2` (`2^k = 4`) the pieceN-boundary at `F = z·y` is NONEMPTY for large
`x` (take `2^i ∈ (x/28, x/5]`, a ratio-`5.6` window, so a power of `2` lands there and all
three clauses hold), yet `hDsq` demands `D < 25` while `D ~ x^{0.497}` — FALSE.

The honest k-floor comes instead from the box CARRIER's own upper cap.  The box leg's carrier
is `restrictAlpha (restrictAlpha (blockAlpha z y ε₀ j) 0 c) (2^i) (2^{i+1})` with
`c = min (z·pieceN k + 1) (x+1)`.  For a box index `i` in the pieceN-boundary (so `2^i > z·y/2`
by clause 2), EITHER `2^i ≥ c` and the doubly-restricted carrier VANISHES identically (the box
price is `0` — `box_carrier_eq_zero_above_cap`), OR `2^i < c ≤ z·pieceN k + 1`, whence
`z·y < 2^{i+1} = 2·2^i ≤ 2·z·(2^k−1)` gives `y < 2^{k+1}` (`y_lt_two_pow_succ_of_carrier`) —
the genuine k-floor `2^k > y/2 ~ x^{1/3}/2`, comfortably clearing `hDsq`.  So the k-floor is
real and the node still closes, but through the carrier split, not the boundary clauses.  The
box price at the operating point is therefore the THREE-WAY split (vanishing / 2^k-boundary /
edge box), NOT a direct `box_hprice_at_2pow` application over the pieceN-boundary.

## What this file lands (sorry-free, NEW FILE — no edits to landed files)

* (deliverable 1, the crux) **`box_carrier_eq_zero_above_cap`** — the box price vanishes above
  the carrier cap; **`y_lt_two_pow_succ_of_carrier`** — the honest k-floor from the carrier;
  **`hDsq_piece_of_kfloor`** — `hDsq` at piece params `D < (2^k+1)²` from the k-floor.
* (deliverable 1, clean rows) the x-scale / X-scale piece-parameter rows provable at `x ≥ x₁`.

Only `[propext, Classical.choice, Quot.sound]` are used; no `native_decide`, no new axioms.
-/

namespace Salt.Chen

open Finset
open scoped BigOperators

/-! ## 1. The box carrier-vanishing lemma (deliverable 1, the crux)

The box leg's carrier is doubly restricted: to `[0, c)` (the `min (z·pieceN k+1) (x+1)` cap
that floors the diagonal support) and then to the dyadic window `[2^i, 2^{i+1})`.  When the
window start `2^i` sits at or above the cap `c`, the two restrictions are incompatible and the
carrier is `0` at every `m`, so `apDiscBilinCutoff = 0` — the box costs nothing.  The upper-cap
mirror of `MediumFloor.carrier_eq_zero_below_floor` (which vanishes BELOW an m-floor). -/

/-- **`box_carrier_eq_zero_above_cap` (deliverable 1).**  If the carrier's upper cap `c` is at
or below the dyadic window start `2^i`, the doubly-restricted cutoff carrier vanishes: at every
summation top `X`, prime side `β`, second length `M`, class `N₀`, modulus `d`, and cutoff `T`,
`apDiscBilinCutoff (restrictAlpha (restrictAlpha α 0 c) (2^i) (2^{i+1})) β X M N₀ d T = 0`.
Every `m ∈ [2^i, 2^{i+1})` has `m ≥ 2^i ≥ c`, so the inner `[0, c)`-restriction kills it. -/
theorem box_carrier_eq_zero_above_cap {α : ℕ → ℂ} {c i : ℕ} (hcap : c ≤ 2 ^ i)
    (β : ℕ → ℂ) (X M N₀ d T : ℕ) :
    apDiscBilinCutoff (restrictAlpha (restrictAlpha α 0 c) (2 ^ i) (2 ^ (i + 1))) β X M N₀ d T
      = 0 := by
  classical
  have h : ∀ m ∈ Finset.Icc 1 X,
      restrictAlpha (restrictAlpha α 0 c) (2 ^ i) (2 ^ (i + 1)) m = (0 : ℂ) := by
    intro m _
    simp only [restrictAlpha]
    split_ifs with hm hm2
    · exfalso; omega
    · rfl
    · rfl
  rw [apDiscBilinCutoff_congr (α' := fun _ => (0 : ℂ)) h, apDiscBilinCutoff_zero]

/-! ## 2. The honest k-floor from the carrier (deliverable 1, THE correction)

For a box index `i` inside the pieceN-boundary at `F = z·y`, boundary clause 2 forces
`z·y < 2^{i+1}` (the window is above the diagonal m-floor).  If the box carrier does NOT vanish
(so `2^i < c ≤ z·pieceN k + 1` = `z·(2^k − 1) + 1`), then
`z·y < 2^{i+1} = 2·2^i ≤ 2·z·(2^k − 1)`, and cancelling `z ≥ 1` gives `y < 2·(2^k − 1) < 2^{k+1}`
— the honest k-floor.  This is the mechanism the PRICE-3 finding mis-attributed to the boundary
clauses (see the module header). -/

/-- **`y_lt_two_pow_succ_of_carrier` (deliverable 1, the k-floor).**  From carrier-nonvanishing
(`2^i < z·pieceN k + 1`) and boundary clause 2 (`z·y < 2^{i+1}`): `y < 2^{k+1}`,
i.e. `2^k > y/2`.  The genuine k-floor for the box legs.  (No `z ≥ 1` needed: at `z = 0` the
carrier hypothesis `2^i < 1` is already impossible since `2^i ≥ 1`.) -/
theorem y_lt_two_pow_succ_of_carrier {y z k i : ℕ}
    (hcar : 2 ^ i < z * pieceN k + 1) (hb2 : z * y < 2 ^ (i + 1)) :
    y < 2 ^ (k + 1) := by
  have hP : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have h2k : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have h2i : (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
  -- carrier cap: `2^i ≤ z·(2^k − 1)`
  have h1 : 2 ^ i ≤ z * (2 ^ k - 1) := by
    have : pieceN k = 2 ^ k - 1 := rfl
    rw [this] at hcar; omega
  -- `z·y < 2·2^i ≤ z·(2·(2^k − 1))`
  have h3 : z * y < z * (2 * (2 ^ k - 1)) := by
    calc z * y < 2 ^ (i + 1) := hb2
      _ = 2 * 2 ^ i := h2i
      _ ≤ 2 * (z * (2 ^ k - 1)) := by omega
      _ = z * (2 * (2 ^ k - 1)) := by ring
  have h4 : y < 2 * (2 ^ k - 1) := lt_of_mul_lt_mul_left h3 (Nat.zero_le z)
  have h5 : 2 * (2 ^ k - 1) < 2 ^ (k + 1) := by omega
  omega

/-! ## 3. `hDsq` at piece parameters (deliverable 1, the boundary-coupled row)

The single row that genuinely needs the k-floor: `hDsq : D < (2^k + 1)²`.  From
`y < 2^{k+1}` (the carrier k-floor) one has `(2^k : ℝ) > y/2`, so
`((2^k + 1) : ℝ)² > (y/2)²`; feeding `(D : ℝ) < (y/2)²` (the operating conductor is a polylog
below `x^{1/2}`, `y = ⌊x^{1/3}⌋`, so `(y/2)² ~ x^{2/3}/4 ≫ D ~ x^{0.497}`) closes it. -/

/-- **`hDsq_piece_of_kfloor` (deliverable 1).**  With the carrier k-floor `y < 2^{k+1}` and the
operating-conductor smallness `(D : ℝ) < (y/2)·(y/2)`, the piece-parameter `hDsq` holds:
`D < (2^k + 1)·(2^k + 1)`. -/
theorem hDsq_piece_of_kfloor {y k D : ℕ} (hkf : y < 2 ^ (k + 1))
    (hDsmall : (D : ℝ) < ((y : ℝ) / 2) * ((y : ℝ) / 2)) :
    D < (2 ^ k + 1) * (2 ^ k + 1) := by
  have hyk : (y : ℝ) < 2 * (2 : ℝ) ^ k := by
    have h : (y : ℝ) < ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hkf
    have hc : ((2 ^ (k + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ k := by push_cast [pow_succ]; ring
    rw [hc] at h; exact h
  have hyhalf : (y : ℝ) / 2 < (2 : ℝ) ^ k := by linarith
  have hynn : (0 : ℝ) ≤ (y : ℝ) / 2 := by positivity
  have htnn : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
  have hprod : ((y : ℝ) / 2) * ((y : ℝ) / 2) < (2 : ℝ) ^ k * (2 : ℝ) ^ k :=
    mul_lt_mul'' hyhalf hyhalf hynn hynn
  have hchain : (D : ℝ) < ((2 : ℝ) ^ k + 1) * ((2 : ℝ) ^ k + 1) := by
    nlinarith [hDsmall, hprod, htnn]
  exact_mod_cast hchain

/-- **`hDsmall_at_op` (deliverable 1, the operating-point hDsq smallness).**  At the operating
point (`y = opY x = ⌊x^{1/3}⌋`), any conductor `D ≤ x^{5/9}` satisfies `(D : ℝ) < (y/2)·(y/2)`:
`(y/2)² ≥ (x^{1/3}/4)² = x^{2/3}/16 > x^{5/9}` since `x^{1/9} > 16` at `x ≥ 10^{96}`.  Feeds
`hDsq_piece_of_kfloor`.  (The operating conductor `Q·QR·Dlev ~ x^{0.497}` sits under `x^{5/9}`.) -/
theorem hDsmall_at_op {x : ℕ} (hx : (10 : ℝ) ^ 96 ≤ (x : ℝ)) {D : ℕ}
    (hD : (D : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ) / 9)) :
    (D : ℝ) < ((opY x : ℝ) / 2) * ((opY x : ℝ) / 2) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le (by positivity) hx
  have ht2 : (2 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) := by
    have hle : ((10 : ℝ) ^ 96) ^ ((1 : ℝ) / 3) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have heq : ((10 : ℝ) ^ 96) ^ ((1 : ℝ) / 3) = (10 : ℝ) ^ (32 : ℕ) := by
      rw [← Real.rpow_natCast (10 : ℝ) 96, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10),
        show ((96 : ℕ) : ℝ) * (1 / 3) = ((32 : ℕ) : ℝ) by push_cast; norm_num, Real.rpow_natCast]
    rw [heq] at hle
    have : (2 : ℝ) ≤ (10 : ℝ) ^ (32 : ℕ) := by norm_num
    linarith
  have htfl : (x : ℝ) ^ ((1 : ℝ) / 3) < (opY x : ℝ) + 1 := by
    rw [opY]; exact Nat.lt_floor_add_one _
  have hyhalf : (x : ℝ) ^ ((1 : ℝ) / 3) / 4 ≤ (opY x : ℝ) / 2 := by linarith
  have ht4nn : (0 : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 3) / 4 := by positivity
  have hprod : ((x : ℝ) ^ ((1 : ℝ) / 3) / 4) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 4)
      ≤ ((opY x : ℝ) / 2) * ((opY x : ℝ) / 2) := mul_le_mul hyhalf hyhalf ht4nn (by linarith)
  have h19 : (16 : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 9) := by
    have hstep2 : ((10 : ℝ) ^ 96) ^ ((1 : ℝ) / 9) ≤ (x : ℝ) ^ ((1 : ℝ) / 9) :=
      Real.rpow_le_rpow (by positivity) hx (by norm_num)
    have heq : ((10 : ℝ) ^ 96) ^ ((1 : ℝ) / 9) = (10 : ℝ) ^ ((96 : ℝ) / 9) := by
      rw [← Real.rpow_natCast (10 : ℝ) 96, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      congr 1; push_cast; norm_num
    have hge : (10 : ℝ) ^ ((2 : ℝ)) ≤ (10 : ℝ) ^ ((96 : ℝ) / 9) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h100 : (10 : ℝ) ^ ((2 : ℝ)) = 100 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [heq] at hstep2; rw [h100] at hge; linarith
  have ht2eq : (x : ℝ) ^ ((1 : ℝ) / 3) * (x : ℝ) ^ ((1 : ℝ) / 3) = (x : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add hxpos, show (1 : ℝ) / 3 + 1 / 3 = 2 / 3 by norm_num]
  have hsplit : (x : ℝ) ^ ((2 : ℝ) / 3)
      = (x : ℝ) ^ ((5 : ℝ) / 9) * (x : ℝ) ^ ((1 : ℝ) / 9) := by
    rw [← Real.rpow_add hxpos, show (5 : ℝ) / 9 + 1 / 9 = 2 / 3 by norm_num]
  have hlt : (x : ℝ) ^ ((5 : ℝ) / 9)
      < ((x : ℝ) ^ ((1 : ℝ) / 3) / 4) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 4) := by
    have h59pos : (0 : ℝ) < (x : ℝ) ^ ((5 : ℝ) / 9) := Real.rpow_pos_of_pos hxpos _
    have hfrac : ((x : ℝ) ^ ((1 : ℝ) / 3) / 4) * ((x : ℝ) ^ ((1 : ℝ) / 3) / 4)
        = (x : ℝ) ^ ((2 : ℝ) / 3) / 16 := by
      rw [div_mul_div_comm, ht2eq]; norm_num
    rw [hfrac, hsplit, lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith [mul_lt_mul_of_pos_left h19 h59pos]
  linarith [hlt, hprod, hD]

/-! ## 4. The numeric closure — the tower budget (deliverable 3)

The PRICE-3 finding's aggregate (matching the gate): the honest per-box price is
`2^{18}·c^{−50}·K·XM/L^{12}`, and summed over the `≤ 4` boundary boxes per piece × `O(log x)`
pieces (single block via `maxBlock_eq_zero_of_eps_self`, `ε₀ := x`), the total is
`≈ 3.5·10²³·K·x/L^{11}`.  This closes into `x/L^{10}` precisely when
`hK_tower : 3.5·10²³·K ≤ L` — dwarfed by the tower `log x₀ ≥ w'^{w'}`.  The two lemmas below are
the arithmetic core: `tower_budget` (the single-factor `m·x/L^{11} ≤ x/L^{10}` at `m ≤ L`) and
`hNum_close_of_tower` (the `RHD + RCE ≤ x/L^{10}` closure, folding the `blockConvErrW` crumb
`RCE` into a factor-2 tower margin). -/

/-- **`tower_budget` (deliverable 3, the closure core).**  For `x ≥ 0`, `L > 0`, `0 ≤ m ≤ L`:
`m·x/L^{11} ≤ x/L^{10}` — one power of `L` of headroom traded for the budget factor `m`. -/
theorem tower_budget {x L m : ℝ} (hx : 0 ≤ x) (hL : 0 < L) (hmL : m ≤ L) :
    m * x / L ^ 11 ≤ x / L ^ 10 := by
  have hstep : m * x / L ^ 11 = (m / L) * (x / L ^ 10) := by field_simp
  rw [hstep]
  have h1 : m / L ≤ 1 := by rw [div_le_one hL]; exact hmL
  have h2 : (0 : ℝ) ≤ x / L ^ 10 := by positivity
  calc (m / L) * (x / L ^ 10) ≤ 1 * (x / L ^ 10) := mul_le_mul_of_nonneg_right h1 h2
    _ = x / L ^ 10 := one_mul _

/-- **`hNum_close_of_tower` (deliverable 3, the `hNum` shape).**  The exact `hNum` slot of
`hBVblocksW_discharge'` (`RHD + RCE ≤ x/(log x)^10`) from the finding's aggregate bounds: the
honest HD aggregate `RHD` and the CE crumb `RCE` are each `≤ Ccon·K·x/(log x)^{11}`
(`Ccon = 3.5·10²³`, the CE crumb `x^{7/8}·polylog` fits with room to spare), and the tower
hypothesis `2·Ccon·K ≤ log x` closes it. -/
theorem hNum_close_of_tower {x RHD RCE Ccon K : ℝ}
    (hx : 0 ≤ x) (hL : 0 < Real.log x)
    (hRHD : RHD ≤ Ccon * K * x / (Real.log x) ^ 11)
    (hRCE : RCE ≤ Ccon * K * x / (Real.log x) ^ 11)
    (htower : 2 * (Ccon * K) ≤ Real.log x) :
    RHD + RCE ≤ x / (Real.log x) ^ 10 := by
  have hsum : RHD + RCE ≤ (2 * (Ccon * K)) * x / (Real.log x) ^ 11 := by
    have hsplit : (2 * (Ccon * K)) * x / (Real.log x) ^ 11
        = Ccon * K * x / (Real.log x) ^ 11 + Ccon * K * x / (Real.log x) ^ 11 := by ring
    rw [hsplit]; linarith [hRHD, hRCE]
  exact le_trans hsum (tower_budget hx hL htower)

/-! ## 5. Satisfiability witnesses (the anti-#69 discipline)

The two crux mechanisms fire at concrete shapes, so the k-floor split is not vacuous. -/

/-- Anti-vacuity (carrier vanishing fires): at `c = 4 ≤ 2^3 = 8`, the doubly-restricted box
carrier vanishes identically — the box price is `0` above the cap. -/
example :
    apDiscBilinCutoff (restrictAlpha (restrictAlpha (fun _ => (1 : ℂ)) 0 4) (2 ^ 3) (2 ^ 4))
        (fun _ => 1) 20 20 5 7 100 = 0 :=
  box_carrier_eq_zero_above_cap (α := fun _ => (1 : ℂ)) (c := 4) (i := 3) (by norm_num)
    (fun _ => 1) 20 20 5 7 100

/-- Anti-vacuity (the k-floor fires): at `z = 3`, `k = 5` (`2^k = 32`, `pieceN 5 = 31`),
`i = 6` (`2^i = 64 < 3·31 + 1 = 94`, carrier nonempty) and `y = 40` (`z·y = 120 < 2^7 = 128`,
boundary clause 2), the k-floor gives `y = 40 < 2^6 = 64`. -/
example : (40 : ℕ) < 2 ^ (5 + 1) :=
  y_lt_two_pow_succ_of_carrier (y := 40) (z := 3) (k := 5) (i := 6)
    (by unfold pieceN; norm_num) (by norm_num)

end Salt.Chen
